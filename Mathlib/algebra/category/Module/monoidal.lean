/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.braided
import Mathlib.algebra.category.Module.basic
import Mathlib.linear_algebra.tensor_product
import Mathlib.PostPort

universes u u_1 u_2 u_3 u_4 u_5 u_6 

namespace Mathlib

/-!
# The symmetric monoidal category structure on R-modules

Mostly this uses existing machinery in `linear_algebra.tensor_product`.
We just need to provide a few small missing pieces to build the
`monoidal_category` instance and then the `symmetric_category` instance.

If you're happy using the bundled `Module R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/

namespace Module


namespace monoidal_category


-- The definitions inside this namespace are essentially private.

-- After we build the `monoidal_category (Module R)` instance,

-- you should use that API.

/-- (implementation) tensor product of R-modules -/
/-- (implementation) tensor product of morphisms R-modules -/
def tensor_obj {R : Type u} [comm_ring R] (M : Module R) (N : Module R) : Module R :=
  of R (tensor_product R ↥M ↥N)

def tensor_hom {R : Type u} [comm_ring R] {M : Module R} {N : Module R} {M' : Module R} {N' : Module R} (f : M ⟶ N) (g : M' ⟶ N') : tensor_obj M M' ⟶ tensor_obj N N' :=
  tensor_product.map f g

theorem tensor_id {R : Type u} [comm_ring R] (M : Module R) (N : Module R) : tensor_hom 𝟙 𝟙 = 𝟙 :=
  tensor_product.ext fun (x : ↥M) (y : ↥N) => Eq.refl (coe_fn (tensor_hom 𝟙 𝟙) (tensor_product.tmul R x y))

theorem tensor_comp {R : Type u} [comm_ring R] {X₁ : Module R} {Y₁ : Module R} {Z₁ : Module R} {X₂ : Module R} {Y₂ : Module R} {Z₂ : Module R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) : tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensor_hom f₁ f₂ ≫ tensor_hom g₁ g₂ :=
  tensor_product.ext
    fun (x : ↥X₁) (y : ↥X₂) => Eq.refl (coe_fn (tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂)) (tensor_product.tmul R x y))

/-- (implementation) the associator for R-modules -/
def associator {R : Type u} [comm_ring R] (M : Module R) (N : Module R) (K : Module R) : tensor_obj (tensor_obj M N) K ≅ tensor_obj M (tensor_obj N K) :=
  linear_equiv.to_Module_iso (tensor_product.assoc R ↥M ↥N ↥K)

/-! The `associator_naturality` and `pentagon` lemmas below are very slow to elaborate.

We give them some help by expressing the lemmas first non-categorically, then using
`convert _aux using 1` to have the elaborator work as little as possible. -/

theorem associator_naturality {R : Type u} [comm_ring R] {X₁ : Module R} {X₂ : Module R} {X₃ : Module R} {Y₁ : Module R} {Y₂ : Module R} {Y₃ : Module R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) : tensor_hom (tensor_hom f₁ f₂) f₃ ≫ category_theory.iso.hom (associator Y₁ Y₂ Y₃) =
  category_theory.iso.hom (associator X₁ X₂ X₃) ≫ tensor_hom f₁ (tensor_hom f₂ f₃) := sorry

theorem pentagon {R : Type u} [comm_ring R] (W : Module R) (X : Module R) (Y : Module R) (Z : Module R) : tensor_hom (category_theory.iso.hom (associator W X Y)) 𝟙 ≫
    category_theory.iso.hom (associator W (tensor_obj X Y) Z) ≫
      tensor_hom 𝟙 (category_theory.iso.hom (associator X Y Z)) =
  category_theory.iso.hom (associator (tensor_obj W X) Y Z) ≫ category_theory.iso.hom (associator W X (tensor_obj Y Z)) := sorry

/-- (implementation) the left unitor for R-modules -/
def left_unitor {R : Type u} [comm_ring R] (M : Module R) : of R (tensor_product R R ↥M) ≅ M :=
  linear_equiv.to_Module_iso (tensor_product.lid R ↥M) ≪≫ of_self_iso M

theorem left_unitor_naturality {R : Type u} [comm_ring R] {M : Module R} {N : Module R} (f : M ⟶ N) : tensor_hom 𝟙 f ≫ category_theory.iso.hom (left_unitor N) = category_theory.iso.hom (left_unitor M) ≫ f := sorry

/-- (implementation) the right unitor for R-modules -/
def right_unitor {R : Type u} [comm_ring R] (M : Module R) : of R (tensor_product R (↥M) R) ≅ M :=
  linear_equiv.to_Module_iso (tensor_product.rid R ↥M) ≪≫ of_self_iso M

theorem right_unitor_naturality {R : Type u} [comm_ring R] {M : Module R} {N : Module R} (f : M ⟶ N) : tensor_hom f 𝟙 ≫ category_theory.iso.hom (right_unitor N) = category_theory.iso.hom (right_unitor M) ≫ f := sorry

theorem triangle {R : Type u} [comm_ring R] (M : Module R) (N : Module R) : category_theory.iso.hom (associator M (of R R) N) ≫ tensor_hom 𝟙 (category_theory.iso.hom (left_unitor N)) =
  tensor_hom (category_theory.iso.hom (right_unitor M)) 𝟙 := sorry

end monoidal_category


protected instance Module.monoidal_category {R : Type u} [comm_ring R] : category_theory.monoidal_category (Module R) :=
  category_theory.monoidal_category.mk monoidal_category.tensor_obj monoidal_category.tensor_hom (of R R)
    monoidal_category.associator monoidal_category.left_unitor monoidal_category.right_unitor

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative ring. -/
protected instance category_theory.monoidal_category.tensor_unit.comm_ring {R : Type u} [comm_ring R] : comm_ring ↥𝟙_ :=
  _inst_1

namespace monoidal_category


@[simp] theorem hom_apply {R : Type u} [comm_ring R] {K : Module R} {L : Module R} {M : Module R} {N : Module R} (f : K ⟶ L) (g : M ⟶ N) (k : ↥K) (m : ↥M) : coe_fn (f ⊗ g) (tensor_product.tmul R k m) = tensor_product.tmul R (coe_fn f k) (coe_fn g m) :=
  rfl

@[simp] theorem left_unitor_hom_apply {R : Type u} [comm_ring R] {M : Module R} (r : R) (m : ↥M) : coe_fn (category_theory.iso.hom λ_) (tensor_product.tmul R r m) = r • m :=
  tensor_product.lid_tmul m r

@[simp] theorem right_unitor_hom_apply {R : Type u} [comm_ring R] {M : Module R} (m : ↥M) (r : R) : coe_fn (category_theory.iso.hom ρ_) (tensor_product.tmul R m r) = r • m :=
  tensor_product.rid_tmul m r

@[simp] theorem associator_hom_apply {R : Type u} [comm_ring R] {M : Module R} {N : Module R} {K : Module R} (m : ↥M) (n : ↥N) (k : ↥K) : coe_fn (category_theory.iso.hom α_) (tensor_product.tmul R (tensor_product.tmul R m n) k) =
  tensor_product.tmul R m (tensor_product.tmul R n k) :=
  rfl

end monoidal_category


/-- (implementation) the braiding for R-modules -/
def braiding {R : Type u} [comm_ring R] (M : Module R) (N : Module R) : monoidal_category.tensor_obj M N ≅ monoidal_category.tensor_obj N M :=
  linear_equiv.to_Module_iso (tensor_product.comm R ↥M ↥N)

@[simp] theorem braiding_naturality {R : Type u} [comm_ring R] {X₁ : Module R} {X₂ : Module R} {Y₁ : Module R} {Y₂ : Module R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f ⊗ g) ≫ category_theory.iso.hom (braiding Y₁ Y₂) = category_theory.iso.hom (braiding X₁ X₂) ≫ (g ⊗ f) :=
  tensor_product.ext
    fun (x : ↥X₁) (y : ↥X₂) =>
      Eq.refl (coe_fn ((f ⊗ g) ≫ category_theory.iso.hom (braiding Y₁ Y₂)) (tensor_product.tmul R x y))

@[simp] theorem hexagon_forward {R : Type u} [comm_ring R] (X : Module R) (Y : Module R) (Z : Module R) : category_theory.iso.hom α_ ≫ category_theory.iso.hom (braiding X (Y ⊗ Z)) ≫ category_theory.iso.hom α_ =
  (category_theory.iso.hom (braiding X Y) ⊗ 𝟙) ≫
    category_theory.iso.hom α_ ≫ (𝟙 ⊗ category_theory.iso.hom (braiding X Z)) := sorry

@[simp] theorem hexagon_reverse {R : Type u} [comm_ring R] (X : Module R) (Y : Module R) (Z : Module R) : category_theory.iso.inv α_ ≫ category_theory.iso.hom (braiding (X ⊗ Y) Z) ≫ category_theory.iso.inv α_ =
  (𝟙 ⊗ category_theory.iso.hom (braiding Y Z)) ≫
    category_theory.iso.inv α_ ≫ (category_theory.iso.hom (braiding X Z) ⊗ 𝟙) := sorry

/-- The symmetric monoidal structure on `Module R`. -/
protected instance Module.symmetric_category {R : Type u} [comm_ring R] : category_theory.symmetric_category (Module R) :=
  category_theory.symmetric_category.mk

namespace monoidal_category


@[simp] theorem braiding_hom_apply {R : Type u} [comm_ring R] {M : Module R} {N : Module R} (m : ↥M) (n : ↥N) : coe_fn (category_theory.iso.hom β_) (tensor_product.tmul R m n) = tensor_product.tmul R n m :=
  rfl

@[simp] theorem braiding_inv_apply {R : Type u} [comm_ring R] {M : Module R} {N : Module R} (m : ↥M) (n : ↥N) : coe_fn (category_theory.iso.inv β_) (tensor_product.tmul R n m) = tensor_product.tmul R m n :=
  rfl

