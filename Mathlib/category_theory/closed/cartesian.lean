/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers, Thomas Read. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers, Thomas Read
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.finite_products
import Mathlib.category_theory.limits.preserves.shapes.binary_products
import Mathlib.category_theory.closed.monoidal
import Mathlib.category_theory.monoidal.of_has_finite_products
import Mathlib.category_theory.adjunction.default
import Mathlib.category_theory.adjunction.mates
import Mathlib.category_theory.epi_mono
import Mathlib.PostPort

universes v u u₂ 

namespace Mathlib

/-!
# Cartesian closed categories

Given a category with finite products, the cartesian monoidal structure is provided by the local
instance `monoidal_of_has_finite_products`.

We define exponentiable objects to be closed objects with respect to this monoidal structure,
i.e. `(X × -)` is a left adjoint.

We say a category is cartesian closed if every object is exponentiable
(equivalently, that the category equipped with the cartesian monoidal structure is closed monoidal).

Show that exponential forms a difunctor and define the exponential comparison morphisms.

## TODO
Some of the results here are true more generally for closed objects and
for closed monoidal categories, and these could be generalised.
-/

namespace category_theory


/--
An object `X` is *exponentiable* if `(X × -)` is a left adjoint.
We define this as being `closed` in the cartesian monoidal structure.
-/
def exponentiable {C : Type u} [category C] [limits.has_finite_products C] (X : C)  :=
  closed X

/--
If `X` and `Y` are exponentiable then `X ⨯ Y` is.
This isn't an instance because it's not usually how we want to construct exponentials, we'll usually
prove all objects are exponential uniformly.
-/
def binary_product_exponentiable {C : Type u} [category C] [limits.has_finite_products C] {X : C} {Y : C} (hX : exponentiable X) (hY : exponentiable Y) : exponentiable (X ⨯ Y) :=
  closed.mk (adjunction.left_adjoint_of_nat_iso (iso.symm (monoidal_category.tensor_left_tensor X Y)))

/--
The terminal object is always exponentiable.
This isn't an instance because most of the time we'll prove cartesian closed for all objects
at once, rather than just for this one.
-/
def terminal_exponentiable {C : Type u} [category C] [limits.has_finite_products C] : exponentiable (⊤_C) :=
  unit_closed

/--
A category `C` is cartesian closed if it has finite products and every object is exponentiable.
We define this as `monoidal_closed` with respect to the cartesian monoidal structure.
-/
def cartesian_closed (C : Type u) [category C] [limits.has_finite_products C]  :=
  monoidal_closed C

/-- This is (-)^A. -/
def exp {C : Type u} [category C] (A : C) [limits.has_finite_products C] [exponentiable A] : C ⥤ C :=
  is_left_adjoint.right (monoidal_category.tensor_left A)

/-- The adjunction between A ⨯ - and (-)^A. -/
def exp.adjunction {C : Type u} [category C] (A : C) [limits.has_finite_products C] [exponentiable A] : functor.obj limits.prod.functor A ⊣ exp A :=
  is_left_adjoint.adj

/-- The evaluation natural transformation. -/
def ev {C : Type u} [category C] (A : C) [limits.has_finite_products C] [exponentiable A] : exp A ⋙ functor.obj limits.prod.functor A ⟶ 𝟭 :=
  adjunction.counit is_left_adjoint.adj

/-- The coevaluation natural transformation. -/
def coev {C : Type u} [category C] (A : C) [limits.has_finite_products C] [exponentiable A] : 𝟭 ⟶ functor.obj limits.prod.functor A ⋙ exp A :=
  adjunction.unit is_left_adjoint.adj

@[simp] theorem exp_adjunction_counit {C : Type u} [category C] (A : C) [limits.has_finite_products C] [exponentiable A] : adjunction.counit (exp.adjunction A) = ev A :=
  rfl

@[simp] theorem exp_adjunction_unit {C : Type u} [category C] (A : C) [limits.has_finite_products C] [exponentiable A] : adjunction.unit (exp.adjunction A) = coev A :=
  rfl

@[simp] theorem ev_naturality {C : Type u} [category C] (A : C) [limits.has_finite_products C] [exponentiable A] {X : C} {Y : C} (f : X ⟶ Y) : limits.prod.map 𝟙 (functor.map (exp A) f) ≫ nat_trans.app (ev A) Y = nat_trans.app (ev A) X ≫ f :=
  nat_trans.naturality (ev A) f

@[simp] theorem coev_naturality_assoc {C : Type u} [category C] (A : C) [limits.has_finite_products C] [exponentiable A] {X : C} {Y : C} (f : X ⟶ Y) {X' : C} (f' : functor.obj (functor.obj limits.prod.functor A ⋙ exp A) Y ⟶ X') : f ≫ nat_trans.app (coev A) Y ≫ f' = nat_trans.app (coev A) X ≫ functor.map (exp A) (limits.prod.map 𝟙 f) ≫ f' := sorry

@[simp] theorem ev_coev {C : Type u} [category C] (A : C) (B : C) [limits.has_finite_products C] [exponentiable A] : limits.prod.map 𝟙 (nat_trans.app (coev A) B) ≫ nat_trans.app (ev A) (A ⨯ B) = 𝟙 :=
  adjunction.left_triangle_components (exp.adjunction A)

@[simp] theorem coev_ev {C : Type u} [category C] (A : C) (B : C) [limits.has_finite_products C] [exponentiable A] : nat_trans.app (coev A) (functor.obj (exp A) B) ≫ functor.map (exp A) (nat_trans.app (ev A) B) = 𝟙 :=
  adjunction.right_triangle_components (exp.adjunction A)

protected instance obj.limits.preserves_colimits {C : Type u} [category C] (A : C) [limits.has_finite_products C] [exponentiable A] : limits.preserves_colimits (functor.obj limits.prod.functor A) :=
  adjunction.left_adjoint_preserves_colimits (exp.adjunction A)

-- Wrap these in a namespace so we don't clash with the core versions.

namespace cartesian_closed


/-- Currying in a cartesian closed category. -/
def curry {C : Type u} [category C] {A : C} {X : C} {Y : C} [limits.has_finite_products C] [exponentiable A] : (A ⨯ Y ⟶ X) → (Y ⟶ functor.obj (exp A) X) :=
  equiv.to_fun (adjunction.hom_equiv is_left_adjoint.adj Y X)

/-- Uncurrying in a cartesian closed category. -/
def uncurry {C : Type u} [category C] {A : C} {X : C} {Y : C} [limits.has_finite_products C] [exponentiable A] : (Y ⟶ functor.obj (exp A) X) → (A ⨯ Y ⟶ X) :=
  equiv.inv_fun (adjunction.hom_equiv is_left_adjoint.adj Y X)

end cartesian_closed


theorem curry_natural_left_assoc {C : Type u} [category C] {A : C} {X : C} {X' : C} {Y : C} [limits.has_finite_products C] [exponentiable A] (f : X ⟶ X') (g : A ⨯ X' ⟶ Y) : ∀ {X'_1 : C} (f' : functor.obj (exp A) Y ⟶ X'_1),
  cartesian_closed.curry (limits.prod.map 𝟙 f ≫ g) ≫ f' = f ≫ cartesian_closed.curry g ≫ f' := sorry

theorem curry_natural_right_assoc {C : Type u} [category C] {A : C} {X : C} {Y : C} {Y' : C} [limits.has_finite_products C] [exponentiable A] (f : A ⨯ X ⟶ Y) (g : Y ⟶ Y') {X' : C} (f' : functor.obj (exp A) Y' ⟶ X') : cartesian_closed.curry (f ≫ g) ≫ f' = cartesian_closed.curry f ≫ functor.map (exp A) g ≫ f' := sorry

theorem uncurry_natural_right {C : Type u} [category C] {A : C} {X : C} {Y : C} {Y' : C} [limits.has_finite_products C] [exponentiable A] (f : X ⟶ functor.obj (exp A) Y) (g : Y ⟶ Y') : cartesian_closed.uncurry (f ≫ functor.map (exp A) g) = cartesian_closed.uncurry f ≫ g :=
  adjunction.hom_equiv_naturality_right_symm is_left_adjoint.adj f g

theorem uncurry_natural_left {C : Type u} [category C] {A : C} {X : C} {X' : C} {Y : C} [limits.has_finite_products C] [exponentiable A] (f : X ⟶ X') (g : X' ⟶ functor.obj (exp A) Y) : cartesian_closed.uncurry (f ≫ g) = limits.prod.map 𝟙 f ≫ cartesian_closed.uncurry g :=
  adjunction.hom_equiv_naturality_left_symm is_left_adjoint.adj f g

@[simp] theorem uncurry_curry {C : Type u} [category C] {A : C} {X : C} {Y : C} [limits.has_finite_products C] [exponentiable A] (f : A ⨯ X ⟶ Y) : cartesian_closed.uncurry (cartesian_closed.curry f) = f :=
  equiv.left_inv (adjunction.hom_equiv is_left_adjoint.adj X Y) f

@[simp] theorem curry_uncurry {C : Type u} [category C] {A : C} {X : C} {Y : C} [limits.has_finite_products C] [exponentiable A] (f : X ⟶ functor.obj (exp A) Y) : cartesian_closed.curry (cartesian_closed.uncurry f) = f :=
  equiv.right_inv (adjunction.hom_equiv is_left_adjoint.adj X Y) f

theorem curry_eq_iff {C : Type u} [category C] {A : C} {X : C} {Y : C} [limits.has_finite_products C] [exponentiable A] (f : A ⨯ Y ⟶ X) (g : Y ⟶ functor.obj (exp A) X) : cartesian_closed.curry f = g ↔ f = cartesian_closed.uncurry g :=
  adjunction.hom_equiv_apply_eq is_left_adjoint.adj f g

theorem eq_curry_iff {C : Type u} [category C] {A : C} {X : C} {Y : C} [limits.has_finite_products C] [exponentiable A] (f : A ⨯ Y ⟶ X) (g : Y ⟶ functor.obj (exp A) X) : g = cartesian_closed.curry f ↔ cartesian_closed.uncurry g = f :=
  adjunction.eq_hom_equiv_apply is_left_adjoint.adj f g

-- I don't think these two should be simp.

theorem uncurry_eq {C : Type u} [category C] {A : C} {X : C} {Y : C} [limits.has_finite_products C] [exponentiable A] (g : Y ⟶ functor.obj (exp A) X) : cartesian_closed.uncurry g = limits.prod.map 𝟙 g ≫ nat_trans.app (ev A) X :=
  adjunction.hom_equiv_counit is_left_adjoint.adj

theorem curry_eq {C : Type u} [category C] {A : C} {X : C} {Y : C} [limits.has_finite_products C] [exponentiable A] (g : A ⨯ Y ⟶ X) : cartesian_closed.curry g = nat_trans.app (coev A) Y ≫ functor.map (exp A) g :=
  adjunction.hom_equiv_unit is_left_adjoint.adj

theorem uncurry_id_eq_ev {C : Type u} [category C] [limits.has_finite_products C] (A : C) (X : C) [exponentiable A] : cartesian_closed.uncurry 𝟙 = nat_trans.app (ev A) X := sorry

theorem curry_id_eq_coev {C : Type u} [category C] [limits.has_finite_products C] (A : C) (X : C) [exponentiable A] : cartesian_closed.curry 𝟙 = nat_trans.app (coev A) X := sorry

theorem curry_injective {C : Type u} [category C] {A : C} {X : C} {Y : C} [limits.has_finite_products C] [exponentiable A] : function.injective cartesian_closed.curry :=
  equiv.injective (adjunction.hom_equiv is_left_adjoint.adj Y X)

theorem uncurry_injective {C : Type u} [category C] {A : C} {X : C} {Y : C} [limits.has_finite_products C] [exponentiable A] : function.injective cartesian_closed.uncurry :=
  equiv.injective (equiv.symm (adjunction.hom_equiv is_left_adjoint.adj Y X))

/--
Show that the exponential of the terminal object is isomorphic to itself, i.e. `X^1 ≅ X`.

The typeclass argument is explicit: any instance can be used.
-/
def exp_terminal_iso_self {C : Type u} [category C] {X : C} [limits.has_finite_products C] [exponentiable (⊤_C)] : functor.obj (exp (⊤_C)) X ≅ X :=
  yoneda.ext (functor.obj (exp (⊤_C)) X) X
    (fun (Y : C) (f : Y ⟶ functor.obj (exp (⊤_C)) X) => iso.inv (limits.prod.left_unitor Y) ≫ cartesian_closed.uncurry f)
    (fun (Y : C) (f : Y ⟶ X) => cartesian_closed.curry (iso.hom (limits.prod.left_unitor Y) ≫ f)) sorry sorry sorry

/-- The internal element which points at the given morphism. -/
def internalize_hom {C : Type u} [category C] {A : C} {Y : C} [limits.has_finite_products C] [exponentiable A] (f : A ⟶ Y) : ⊤_C ⟶ functor.obj (exp A) Y :=
  cartesian_closed.curry (limits.prod.fst ≫ f)

/-- Pre-compose an internal hom with an external hom. -/
def pre {C : Type u} [category C] {A : C} {B : C} [limits.has_finite_products C] [exponentiable A] (f : B ⟶ A) [exponentiable B] : exp A ⟶ exp B :=
  coe_fn (transfer_nat_trans_self (exp.adjunction A) (exp.adjunction B)) (functor.map limits.prod.functor f)

theorem prod_map_pre_app_comp_ev {C : Type u} [category C] {A : C} {B : C} [limits.has_finite_products C] [exponentiable A] (f : B ⟶ A) [exponentiable B] (X : C) : limits.prod.map 𝟙 (nat_trans.app (pre f) X) ≫ nat_trans.app (ev B) X = limits.prod.map f 𝟙 ≫ nat_trans.app (ev A) X :=
  transfer_nat_trans_self_counit (exp.adjunction A) (exp.adjunction B) (functor.map limits.prod.functor f) X

theorem uncurry_pre {C : Type u} [category C] {A : C} {B : C} [limits.has_finite_products C] [exponentiable A] (f : B ⟶ A) [exponentiable B] (X : C) : cartesian_closed.uncurry (nat_trans.app (pre f) X) = limits.prod.map f 𝟙 ≫ nat_trans.app (ev A) X := sorry

theorem coev_app_comp_pre_app {C : Type u} [category C] {A : C} {B : C} {X : C} [limits.has_finite_products C] [exponentiable A] (f : B ⟶ A) [exponentiable B] : nat_trans.app (coev A) X ≫ nat_trans.app (pre f) (A ⨯ X) =
  nat_trans.app (coev B) X ≫ functor.map (exp B) (limits.prod.map f 𝟙) :=
  unit_transfer_nat_trans_self is_left_adjoint.adj (exp.adjunction B) (functor.map limits.prod.functor f) X

@[simp] theorem pre_id {C : Type u} [category C] [limits.has_finite_products C] (A : C) [exponentiable A] : pre 𝟙 = 𝟙 := sorry

@[simp] theorem pre_map {C : Type u} [category C] [limits.has_finite_products C] {A₁ : C} {A₂ : C} {A₃ : C} [exponentiable A₁] [exponentiable A₂] [exponentiable A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) : pre (f ≫ g) = pre g ≫ pre f := sorry

/-- The internal hom functor given by the cartesian closed structure. -/
def internal_hom {C : Type u} [category C] [limits.has_finite_products C] [cartesian_closed C] : Cᵒᵖ ⥤ C ⥤ C :=
  functor.mk (fun (X : Cᵒᵖ) => exp (opposite.unop X)) fun (X Y : Cᵒᵖ) (f : X ⟶ Y) => pre (has_hom.hom.unop f)

/-- If an initial object `I` exists in a CCC, then `A ⨯ I ≅ I`. -/
@[simp] theorem zero_mul_hom {C : Type u} [category C] {A : C} [limits.has_finite_products C] [exponentiable A] {I : C} (t : limits.is_initial I) : iso.hom (zero_mul t) = limits.prod.snd :=
  Eq.refl (iso.hom (zero_mul t))

/-- If an initial object `0` exists in a CCC, then `0 ⨯ A ≅ 0`. -/
def mul_zero {C : Type u} [category C] {A : C} [limits.has_finite_products C] [exponentiable A] {I : C} (t : limits.is_initial I) : I ⨯ A ≅ I :=
  limits.prod.braiding I A ≪≫ zero_mul t

/-- If an initial object `0` exists in a CCC then `0^B ≅ 1` for any `B`. -/
def pow_zero {C : Type u} [category C] (B : C) [limits.has_finite_products C] {I : C} (t : limits.is_initial I) [cartesian_closed C] : functor.obj (exp I) B ≅ ⊤_C :=
  iso.mk Inhabited.default (cartesian_closed.curry (iso.hom (mul_zero t) ≫ limits.is_initial.to t B))

-- TODO: Generalise the below to its commutated variants.

-- TODO: Define a distributive category, so that zero_mul and friends can be derived from this.

/-- In a CCC with binary coproducts, the distribution morphism is an isomorphism. -/
def prod_coprod_distrib {C : Type u} [category C] [limits.has_finite_products C] [limits.has_binary_coproducts C] [cartesian_closed C] (X : C) (Y : C) (Z : C) : Z ⨯ X ⨿ (Z ⨯ Y) ≅ Z ⨯ (X ⨿ Y) :=
  iso.mk (limits.coprod.desc (limits.prod.map 𝟙 limits.coprod.inl) (limits.prod.map 𝟙 limits.coprod.inr))
    (cartesian_closed.uncurry
      (limits.coprod.desc (cartesian_closed.curry limits.coprod.inl) (cartesian_closed.curry limits.coprod.inr)))

/--
If an initial object `I` exists in a CCC then it is a strict initial object,
i.e. any morphism to `I` is an iso.
This actually shows a slightly stronger version: any morphism to an initial object from an
exponentiable object is an isomorphism.
-/
def strict_initial {C : Type u} [category C] {A : C} [limits.has_finite_products C] [exponentiable A] {I : C} (t : limits.is_initial I) (f : A ⟶ I) : is_iso f :=
  is_iso_of_mono_of_split_epi f

protected instance to_initial_is_iso {C : Type u} [category C] {A : C} [limits.has_finite_products C] [exponentiable A] [limits.has_initial C] (f : A ⟶ ⊥_C) : is_iso f :=
  strict_initial limits.initial_is_initial f

/-- If an initial object `0` exists in a CCC then every morphism from it is monic. -/
theorem initial_mono {C : Type u} [category C] [limits.has_finite_products C] {I : C} (B : C) (t : limits.is_initial I) [cartesian_closed C] : mono (limits.is_initial.to t B) :=
  mono.mk
    fun (B_1 : C) (g h : B_1 ⟶ I) (_x : g ≫ limits.is_initial.to t B = h ≫ limits.is_initial.to t B) =>
      eq_of_inv_eq_inv (limits.is_initial.hom_ext t (inv g) (inv h))

protected instance initial.mono_to {C : Type u} [category C] [limits.has_finite_products C] [limits.has_initial C] (B : C) [cartesian_closed C] : mono (limits.initial.to B) :=
  initial_mono B limits.initial_is_initial

/--
Transport the property of being cartesian closed across an equivalence of categories.

Note we didn't require any coherence between the choice of finite products here, since we transport
along the `prod_comparison` isomorphism.
-/
def cartesian_closed_of_equiv {C : Type u} [category C] [limits.has_finite_products C] {D : Type u₂} [category D] [limits.has_finite_products D] (e : C ≌ D) [h : cartesian_closed C] : cartesian_closed D :=
  monoidal_closed.mk
    fun (X : D) =>
      closed.mk
        (adjunction.left_adjoint_of_nat_iso
          (iso_whisker_right (equivalence.counit_iso e)
              (functor.obj limits.prod.functor X ⋙ equivalence.inverse e ⋙ equivalence.functor e) ≪≫
            id (iso_whisker_left (functor.obj limits.prod.functor X) (equivalence.counit_iso e))))

