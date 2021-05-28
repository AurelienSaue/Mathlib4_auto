/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.equivalence
import Mathlib.data.equiv.basic
import PostPort

universes v₁ v₂ u₁ u₂ l u₃ v₃ 

namespace Mathlib

namespace category_theory


-- declare the `v`'s first; see `category_theory.category` for an explanation

/--
`F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

To construct an `adjunction` between two functors, it's often easier to instead use the
constructors `mk_of_hom_equiv` or `mk_of_unit_counit`. To construct a left adjoint,
there are also constructors `left_adjoint_of_equiv` and `adjunction_of_equiv_left` (as
well as their duals) which can be simpler in practice.

Uniqueness of adjoints is shown in `category_theory.adjunction.opposites`.

See https://stacks.math.columbia.edu/tag/0037.
-/
structure adjunction {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) (G : D ⥤ C) 
where
  hom_equiv : (X : C) → (Y : D) → (functor.obj F X ⟶ Y) ≃ (X ⟶ functor.obj G Y)
  unit : 𝟭 ⟶ F ⋙ G
  counit : G ⋙ F ⟶ 𝟭
  hom_equiv_unit' : autoParam
  (∀ {X : C} {Y : D} {f : functor.obj F X ⟶ Y}, coe_fn (hom_equiv X Y) f = nat_trans.app unit X ≫ functor.map G f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  hom_equiv_counit' : autoParam
  (∀ {X : C} {Y : D} {g : X ⟶ functor.obj G Y},
    coe_fn (equiv.symm (hom_equiv X Y)) g = functor.map F g ≫ nat_trans.app counit Y)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

infixl:15 " ⊣ " => Mathlib.category_theory.adjunction

/-- A class giving a chosen right adjoint to the functor `left`. -/
class is_left_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] (left : C ⥤ D) 
where
  right : D ⥤ C
  adj : left ⊣ right

/-- A class giving a chosen left adjoint to the functor `right`. -/
class is_right_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] (right : D ⥤ C) 
where
  left : C ⥤ D
  adj : left ⊣ right

/-- Extract the left adjoint from the instance giving the chosen adjoint. -/
def left_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [is_right_adjoint R] : C ⥤ D :=
  is_right_adjoint.left R

/-- Extract the right adjoint from the instance giving the chosen adjoint. -/
def right_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] (L : C ⥤ D) [is_left_adjoint L] : D ⥤ C :=
  is_left_adjoint.right L

/-- The adjunction associated to a functor known to be a left adjoint. -/
def adjunction.of_left_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] (left : C ⥤ D) [is_left_adjoint left] : left ⊣ right_adjoint left :=
  is_left_adjoint.adj

/-- The adjunction associated to a functor known to be a right adjoint. -/
def adjunction.of_right_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] (right : C ⥤ D) [is_right_adjoint right] : left_adjoint right ⊣ right :=
  is_right_adjoint.adj

namespace adjunction


@[simp] theorem hom_equiv_unit {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (c : F ⊣ G) {X : C} {Y : D} {f : functor.obj F X ⟶ Y} : coe_fn (hom_equiv c X Y) f = nat_trans.app (unit c) X ≫ functor.map G f := sorry

@[simp] theorem hom_equiv_counit {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (c : F ⊣ G) {X : C} {Y : D} {g : X ⟶ functor.obj G Y} : coe_fn (equiv.symm (hom_equiv c X Y)) g = functor.map F g ≫ nat_trans.app (counit c) Y := sorry

@[simp] theorem hom_equiv_naturality_left_symm {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X' : C} {X : C} {Y : D} (f : X' ⟶ X) (g : X ⟶ functor.obj G Y) : coe_fn (equiv.symm (hom_equiv adj X' Y)) (f ≫ g) = functor.map F f ≫ coe_fn (equiv.symm (hom_equiv adj X Y)) g := sorry

@[simp] theorem hom_equiv_naturality_left {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X' : C} {X : C} {Y : D} (f : X' ⟶ X) (g : functor.obj F X ⟶ Y) : coe_fn (hom_equiv adj X' Y) (functor.map F f ≫ g) = f ≫ coe_fn (hom_equiv adj X Y) g := sorry

@[simp] theorem hom_equiv_naturality_right {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : C} {Y : D} {Y' : D} (f : functor.obj F X ⟶ Y) (g : Y ⟶ Y') : coe_fn (hom_equiv adj X Y') (f ≫ g) = coe_fn (hom_equiv adj X Y) f ≫ functor.map G g := sorry

@[simp] theorem hom_equiv_naturality_right_symm {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : C} {Y : D} {Y' : D} (f : X ⟶ functor.obj G Y) (g : Y ⟶ Y') : coe_fn (equiv.symm (hom_equiv adj X Y')) (f ≫ functor.map G g) = coe_fn (equiv.symm (hom_equiv adj X Y)) f ≫ g := sorry

@[simp] theorem left_triangle {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : whisker_right (unit adj) F ≫ whisker_left F (counit adj) = nat_trans.id (𝟭 ⋙ F) := sorry

@[simp] theorem right_triangle {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : whisker_left G (unit adj) ≫ whisker_right (counit adj) G = nat_trans.id (G ⋙ 𝟭) := sorry

@[simp] theorem left_triangle_components_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : C} {X' : D} (f' : functor.obj 𝟭 (functor.obj F X) ⟶ X') : functor.map F (nat_trans.app (unit adj) X) ≫ nat_trans.app (counit adj) (functor.obj F X) ≫ f' = f' := sorry

@[simp] theorem right_triangle_components {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {Y : D} : nat_trans.app (unit adj) (functor.obj G Y) ≫ functor.map G (nat_trans.app (counit adj) Y) = 𝟙 :=
  congr_arg (fun (t : nat_trans (G ⋙ 𝟭) (G ⋙ 𝟭)) => nat_trans.app t Y) (right_triangle adj)

@[simp] theorem counit_naturality {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : D} {Y : D} (f : X ⟶ Y) : functor.map F (functor.map G f) ≫ nat_trans.app (counit adj) Y = nat_trans.app (counit adj) X ≫ f :=
  nat_trans.naturality (counit adj) f

@[simp] theorem unit_naturality {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : C} {Y : C} (f : X ⟶ Y) : nat_trans.app (unit adj) X ≫ functor.map G (functor.map F f) = f ≫ nat_trans.app (unit adj) Y :=
  Eq.symm (nat_trans.naturality (unit adj) f)

theorem hom_equiv_apply_eq {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : C} {B : D} (f : functor.obj F A ⟶ B) (g : A ⟶ functor.obj G B) : coe_fn (hom_equiv adj A B) f = g ↔ f = coe_fn (equiv.symm (hom_equiv adj A B)) g := sorry

theorem eq_hom_equiv_apply {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : C} {B : D} (f : functor.obj F A ⟶ B) (g : A ⟶ functor.obj G B) : g = coe_fn (hom_equiv adj A B) f ↔ coe_fn (equiv.symm (hom_equiv adj A B)) g = f := sorry

end adjunction


namespace adjunction


/--
This is an auxiliary data structure useful for constructing adjunctions.
See `adjunction.mk_of_hom_equiv`.
This structure won't typically be used anywhere else.
-/
structure core_hom_equiv {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) (G : D ⥤ C) 
where
  hom_equiv : (X : C) → (Y : D) → (functor.obj F X ⟶ Y) ≃ (X ⟶ functor.obj G Y)
  hom_equiv_naturality_left_symm' : autoParam
  (∀ {X' X : C} {Y : D} (f : X' ⟶ X) (g : X ⟶ functor.obj G Y),
    coe_fn (equiv.symm (hom_equiv X' Y)) (f ≫ g) = functor.map F f ≫ coe_fn (equiv.symm (hom_equiv X Y)) g)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  hom_equiv_naturality_right' : autoParam
  (∀ {X : C} {Y Y' : D} (f : functor.obj F X ⟶ Y) (g : Y ⟶ Y'),
    coe_fn (hom_equiv X Y') (f ≫ g) = coe_fn (hom_equiv X Y) f ≫ functor.map G g)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

namespace core_hom_equiv


@[simp] theorem hom_equiv_naturality_left_symm {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (c : core_hom_equiv F G) {X' : C} {X : C} {Y : D} (f : X' ⟶ X) (g : X ⟶ functor.obj G Y) : coe_fn (equiv.symm (hom_equiv c X' Y)) (f ≫ g) = functor.map F f ≫ coe_fn (equiv.symm (hom_equiv c X Y)) g := sorry

@[simp] theorem hom_equiv_naturality_right {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (c : core_hom_equiv F G) {X : C} {Y : D} {Y' : D} (f : functor.obj F X ⟶ Y) (g : Y ⟶ Y') : coe_fn (hom_equiv c X Y') (f ≫ g) = coe_fn (hom_equiv c X Y) f ≫ functor.map G g := sorry

@[simp] theorem hom_equiv_naturality_left {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : core_hom_equiv F G) {X' : C} {X : C} {Y : D} (f : X' ⟶ X) (g : functor.obj F X ⟶ Y) : coe_fn (hom_equiv adj X' Y) (functor.map F f ≫ g) = f ≫ coe_fn (hom_equiv adj X Y) g := sorry

@[simp] theorem hom_equiv_naturality_right_symm {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : core_hom_equiv F G) {X : C} {Y : D} {Y' : D} (f : X ⟶ functor.obj G Y) (g : Y ⟶ Y') : coe_fn (equiv.symm (hom_equiv adj X Y')) (f ≫ functor.map G g) = coe_fn (equiv.symm (hom_equiv adj X Y)) f ≫ g := sorry

end core_hom_equiv


/--
This is an auxiliary data structure useful for constructing adjunctions.
See `adjunction.mk_of_hom_equiv`.
This structure won't typically be used anywhere else.
-/
structure core_unit_counit {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) (G : D ⥤ C) 
where
  unit : 𝟭 ⟶ F ⋙ G
  counit : G ⋙ F ⟶ 𝟭
  left_triangle' : autoParam (whisker_right unit F ≫ iso.hom (functor.associator F G F) ≫ whisker_left F counit = nat_trans.id (𝟭 ⋙ F))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  right_triangle' : autoParam (whisker_left G unit ≫ iso.inv (functor.associator G F G) ≫ whisker_right counit G = nat_trans.id (G ⋙ 𝟭))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

namespace core_unit_counit


@[simp] theorem left_triangle {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (c : core_unit_counit F G) : whisker_right (unit c) F ≫ iso.hom (functor.associator F G F) ≫ whisker_left F (counit c) = nat_trans.id (𝟭 ⋙ F) := sorry

@[simp] theorem right_triangle {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (c : core_unit_counit F G) : whisker_left G (unit c) ≫ iso.inv (functor.associator G F G) ≫ whisker_right (counit c) G = nat_trans.id (G ⋙ 𝟭) := sorry

end core_unit_counit


/-- Construct an adjunction between `F` and `G` out of a natural bijection between each
`F.obj X ⟶ Y` and `X ⟶ G.obj Y`. -/
@[simp] theorem mk_of_hom_equiv_counit_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : core_hom_equiv F G) (Y : D) : nat_trans.app (counit (mk_of_hom_equiv adj)) Y =
  equiv.inv_fun (core_hom_equiv.hom_equiv adj (functor.obj G Y) (functor.obj 𝟭 Y)) 𝟙 :=
  Eq.refl (nat_trans.app (counit (mk_of_hom_equiv adj)) Y)

/-- Construct an adjunction between functors `F` and `G` given a unit and counit for the adjunction
satisfying the triangle identities. -/
@[simp] theorem mk_of_unit_counit_counit {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : core_unit_counit F G) : counit (mk_of_unit_counit adj) = core_unit_counit.counit adj :=
  Eq.refl (counit (mk_of_unit_counit adj))

/-- The adjunction between the identity functor on a category and itself. -/
def id {C : Type u₁} [category C] : 𝟭 ⊣ 𝟭 :=
  mk (fun (X Y : C) => equiv.refl (functor.obj 𝟭 X ⟶ Y)) 𝟙 𝟙

-- Satisfy the inhabited linter.

protected instance inhabited {C : Type u₁} [category C] : Inhabited (𝟭 ⊣ 𝟭) :=
  { default := id }

/-- If F and G are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simp] theorem equiv_homset_left_of_nat_iso_symm_apply {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D} (g : functor.obj F' X ⟶ Y) : coe_fn (equiv.symm (equiv_homset_left_of_nat_iso iso)) g = nat_trans.app (iso.hom iso) X ≫ g :=
  Eq.refl (coe_fn (equiv.symm (equiv_homset_left_of_nat_iso iso)) g)

/-- If G and H are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simp] theorem equiv_homset_right_of_nat_iso_apply {C : Type u₁} [category C] {D : Type u₂} [category D] {G : D ⥤ C} {G' : D ⥤ C} (iso : G ≅ G') {X : C} {Y : D} (f : X ⟶ functor.obj G Y) : coe_fn (equiv_homset_right_of_nat_iso iso) f = f ≫ nat_trans.app (iso.hom iso) Y :=
  Eq.refl (coe_fn (equiv_homset_right_of_nat_iso iso) f)

/-- Transport an adjunction along an natural isomorphism on the left. -/
def of_nat_iso_left {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H :=
  mk_of_hom_equiv
    (core_hom_equiv.mk
      fun (X : C) (Y : D) => equiv.trans (equiv_homset_left_of_nat_iso (iso.symm iso)) (hom_equiv adj X Y))

/-- Transport an adjunction along an natural isomorphism on the right. -/
def of_nat_iso_right {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) : F ⊣ H :=
  mk_of_hom_equiv
    (core_hom_equiv.mk fun (X : C) (Y : D) => equiv.trans (hom_equiv adj X Y) (equiv_homset_right_of_nat_iso iso))

/-- Transport being a right adjoint along a natural isomorphism. -/
def right_adjoint_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [r : is_right_adjoint F] : is_right_adjoint G :=
  is_right_adjoint.mk (is_right_adjoint.left F) (of_nat_iso_right is_right_adjoint.adj h)

/-- Transport being a left adjoint along a natural isomorphism. -/
def left_adjoint_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [r : is_left_adjoint F] : is_left_adjoint G :=
  is_left_adjoint.mk (is_left_adjoint.right F) (of_nat_iso_left is_left_adjoint.adj h)

/--
Composition of adjunctions.

See https://stacks.math.columbia.edu/tag/0DV0.
-/
def comp {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} {E : Type u₃} [ℰ : category E] (H : D ⥤ E) (I : E ⥤ D) (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) : F ⋙ H ⊣ I ⋙ G :=
  mk (fun (X : C) (Z : E) => equiv.trans (hom_equiv adj₂ (functor.obj F X) Z) (hom_equiv adj₁ X (functor.obj I Z)))
    (unit adj₁ ≫ whisker_left F (whisker_right (unit adj₂) G) ≫ iso.inv (functor.associator F (H ⋙ I) G))
    (iso.hom (functor.associator I G (F ⋙ H)) ≫ whisker_left I (whisker_right (counit adj₁) H) ≫ counit adj₂)

/-- If `F` and `G` are left adjoints then `F ⋙ G` is a left adjoint too. -/
protected instance left_adjoint_of_comp {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [Fl : is_left_adjoint F] [Gl : is_left_adjoint G] : is_left_adjoint (F ⋙ G) :=
  is_left_adjoint.mk (is_left_adjoint.right G ⋙ is_left_adjoint.right F)
    (comp G (is_left_adjoint.right G) is_left_adjoint.adj is_left_adjoint.adj)

/-- If `F` and `G` are right adjoints then `F ⋙ G` is a right adjoint too. -/
protected instance right_adjoint_of_comp {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [ℰ : category E] {F : C ⥤ D} {G : D ⥤ E} [Fr : is_right_adjoint F] [Gr : is_right_adjoint G] : is_right_adjoint (F ⋙ G) :=
  is_right_adjoint.mk (is_right_adjoint.left G ⋙ is_right_adjoint.left F)
    (comp (is_right_adjoint.left F) F is_right_adjoint.adj is_right_adjoint.adj)

-- Construction of a left adjoint. In order to construct a left

-- adjoint to a functor G : D → C, it suffices to give the object part

-- of a functor F : C → D together with isomorphisms Hom(FX, Y) ≃

-- Hom(X, GY) natural in Y. The action of F on morphisms can be

-- constructed from this data.

/-- Construct a left adjoint functor to `G`, given the functor's value on objects `F_obj` and
a bijection `e` between `F_obj X ⟶ Y` and `X ⟶ G.obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g`.
Dual to `right_adjoint_of_equiv`. -/
@[simp] theorem left_adjoint_of_equiv_obj {C : Type u₁} [category C] {D : Type u₂} [category D] {G : D ⥤ C} {F_obj : C → D} (e : (X : C) → (Y : D) → (F_obj X ⟶ Y) ≃ (X ⟶ functor.obj G Y)) (he : ∀ (X : C) (Y Y' : D) (g : Y ⟶ Y') (h : F_obj X ⟶ Y), coe_fn (e X Y') (h ≫ g) = coe_fn (e X Y) h ≫ functor.map G g) : ∀ (ᾰ : C), functor.obj (left_adjoint_of_equiv e he) ᾰ = F_obj ᾰ :=
  fun (ᾰ : C) => Eq.refl (functor.obj (left_adjoint_of_equiv e he) ᾰ)

/-- Show that the functor given by `left_adjoint_of_equiv` is indeed left adjoint to `G`. Dual
to `adjunction_of_equiv_right`. -/
@[simp] theorem adjunction_of_equiv_left_hom_equiv {C : Type u₁} [category C] {D : Type u₂} [category D] {G : D ⥤ C} {F_obj : C → D} (e : (X : C) → (Y : D) → (F_obj X ⟶ Y) ≃ (X ⟶ functor.obj G Y)) (he : ∀ (X : C) (Y Y' : D) (g : Y ⟶ Y') (h : F_obj X ⟶ Y), coe_fn (e X Y') (h ≫ g) = coe_fn (e X Y) h ≫ functor.map G g) (X : C) (Y : D) : hom_equiv (adjunction_of_equiv_left e he) X Y = e X Y :=
  Eq.refl (e X Y)

-- Construction of a right adjoint, analogous to the above.

/-- Construct a right adjoint functor to `F`, given the functor's value on objects `G_obj` and
a bijection `e` between `F.obj X ⟶ Y` and `X ⟶ G_obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X' Y (F.map f ≫ g) = f ≫ e X Y g`.
Dual to `left_adjoint_of_equiv`. -/
@[simp] theorem right_adjoint_of_equiv_obj {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G_obj : D → C} (e : (X : C) → (Y : D) → (functor.obj F X ⟶ Y) ≃ (X ⟶ G_obj Y)) (he : ∀ (X' X : C) (Y : D) (f : X' ⟶ X) (g : functor.obj F X ⟶ Y),
  coe_fn (e X' Y) (functor.map F f ≫ g) = f ≫ coe_fn (e X Y) g) : ∀ (ᾰ : D), functor.obj (right_adjoint_of_equiv e he) ᾰ = G_obj ᾰ :=
  fun (ᾰ : D) => Eq.refl (functor.obj (right_adjoint_of_equiv e he) ᾰ)

/-- Show that the functor given by `right_adjoint_of_equiv` is indeed right adjoint to `F`. Dual
to `adjunction_of_equiv_left`. -/
@[simp] theorem adjunction_of_equiv_right_counit_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G_obj : D → C} (e : (X : C) → (Y : D) → (functor.obj F X ⟶ Y) ≃ (X ⟶ G_obj Y)) (he : ∀ (X' X : C) (Y : D) (f : X' ⟶ X) (g : functor.obj F X ⟶ Y),
  coe_fn (e X' Y) (functor.map F f ≫ g) = f ≫ coe_fn (e X Y) g) (Y : D) : nat_trans.app (counit (adjunction_of_equiv_right e he)) Y = coe_fn (equiv.symm (e (G_obj Y) Y)) 𝟙 :=
  Eq.refl (coe_fn (equiv.symm (e (G_obj Y) Y)) 𝟙)

/--
If the unit and counit of a given adjunction are (pointwise) isomorphisms, then we can upgrade the
adjunction to an equivalence.
-/
@[simp] theorem to_equivalence_functor {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [(X : C) → is_iso (nat_trans.app (unit adj) X)] [(Y : D) → is_iso (nat_trans.app (counit adj) Y)] : equivalence.functor (to_equivalence adj) = F :=
  Eq.refl (equivalence.functor (to_equivalence adj))

/--
If the unit and counit for the adjunction corresponding to a right adjoint functor are (pointwise)
isomorphisms, then the functor is an equivalence of categories.
-/
@[simp] theorem is_right_adjoint_to_is_equivalence_unit_iso_inv_app {C : Type u₁} [category C] {D : Type u₂} [category D] {G : D ⥤ C} [is_right_adjoint G] [(X : C) → is_iso (nat_trans.app (unit (of_right_adjoint G)) X)] [(Y : D) → is_iso (nat_trans.app (counit (of_right_adjoint G)) Y)] (X : D) : nat_trans.app (iso.inv is_equivalence.unit_iso) X = nat_trans.app (counit (of_right_adjoint G)) X :=
  Eq.refl (nat_trans.app (counit (of_right_adjoint G)) X)

end adjunction


namespace equivalence


/-- The adjunction given by an equivalence of categories. (To obtain the opposite adjunction,
simply use `e.symm.to_adjunction`. -/
def to_adjunction {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D) : functor e ⊣ inverse e :=
  adjunction.mk_of_unit_counit (adjunction.core_unit_counit.mk (unit e) (counit e))

end equivalence


namespace functor


/-- An equivalence `E` is left adjoint to its inverse. -/
def adjunction {C : Type u₁} [category C] {D : Type u₂} [category D] (E : C ⥤ D) [is_equivalence E] : E ⊣ inv E :=
  equivalence.to_adjunction (as_equivalence E)

/-- If `F` is an equivalence, it's a left adjoint. -/
protected instance left_adjoint_of_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} [is_equivalence F] : is_left_adjoint F :=
  is_left_adjoint.mk (inv F) (adjunction F)

@[simp] theorem right_adjoint_of_is_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} [is_equivalence F] : right_adjoint F = inv F :=
  rfl

/-- If `F` is an equivalence, it's a right adjoint. -/
protected instance right_adjoint_of_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} [is_equivalence F] : is_right_adjoint F :=
  is_right_adjoint.mk (inv F) (adjunction (inv F))

@[simp] theorem left_adjoint_of_is_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} [is_equivalence F] : left_adjoint F = inv F :=
  rfl

