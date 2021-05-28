/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.isomorphism_classes
import Mathlib.category_theory.thin
import Mathlib.PostPort

universes v₁ u₁ v₂ u₂ l u₃ v₃ 

namespace Mathlib

/-!
# Skeleton of a category

Define skeletal categories as categories in which any two isomorphic objects are equal.

Construct the skeleton of a thin category as a partial ordering, and (noncomputably) show it is
a skeleton of the original category. The advantage of this special case being handled separately
is that lemmas and definitions about orderings can be used directly, for example for the subobject
lattice (TODO). In addition, some of the commutative diagrams about the functors commute
definitionally on the nose which is convenient in practice.

(TODO): Construct the skeleton of a general category using choice, and show it is a skeleton.
-/

namespace category_theory


/-- A category is skeletal if isomorphic objects are equal. -/
def skeletal (C : Type u₁) [category C]  :=
  ∀ {X Y : C}, is_isomorphic X Y → X = Y

/--
`is_skeleton_of C D F` says that `F : D ⥤ C` exhibits `D` as a skeletal full subcategory of `C`,
in particular `F` is a (strong) equivalence and `D` is skeletal.
-/
structure is_skeleton_of (C : Type u₁) [category C] (D : Type u₂) [category D] (F : D ⥤ C) 
where
  skel : skeletal D
  eqv : is_equivalence F

/-- If `C` is thin and skeletal, then any naturally isomorphic functors to `C` are equal. -/
theorem functor.eq_of_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F₁ : D ⥤ C} {F₂ : D ⥤ C} [∀ (X Y : C), subsingleton (X ⟶ Y)] (hC : skeletal C) (hF : F₁ ≅ F₂) : F₁ = F₂ := sorry

/--
If `C` is thin and skeletal, `D ⥤ C` is skeletal.
`category_theory.functor_thin` shows it is thin also.
-/
theorem functor_skeletal {C : Type u₁} [category C] {D : Type u₂} [category D] [∀ (X Y : C), subsingleton (X ⟶ Y)] (hC : skeletal C) : skeletal (D ⥤ C) :=
  fun (F₁ F₂ : D ⥤ C) (h : is_isomorphic F₁ F₂) => nonempty.elim h (functor.eq_of_iso hC)

/--
Construct the skeleton category by taking the quotient of objects. This construction gives a
preorder with nice definitional properties, but is only really appropriate for thin categories.
-/
def thin_skeleton (C : Type u₁) [category C]  :=
  quotient (is_isomorphic_setoid C)

protected instance inhabited_thin_skeleton (C : Type u₁) [category C] [Inhabited C] : Inhabited (thin_skeleton C) :=
  { default := quotient.mk Inhabited.default }

protected instance thin_skeleton.preorder (C : Type u₁) [category C] : preorder (thin_skeleton C) :=
  preorder.mk (quotient.lift₂ (fun (X Y : C) => Nonempty (X ⟶ Y)) sorry)
    (fun (a b : thin_skeleton C) =>
      quotient.lift₂ (fun (X Y : C) => Nonempty (X ⟶ Y)) sorry a b ∧
        ¬quotient.lift₂ (fun (X Y : C) => Nonempty (X ⟶ Y)) sorry b a)
    sorry sorry

/-- The functor from a category to its thin skeleton. -/
@[simp] theorem to_thin_skeleton_obj (C : Type u₁) [category C] (a : C) : functor.obj (to_thin_skeleton C) a = quotient.mk a :=
  Eq.refl (functor.obj (to_thin_skeleton C) a)

/-!
The constructions here are intended to be used when the category `C` is thin, even though
some of the statements can be shown without this assumption.
-/

namespace thin_skeleton


/-- The thin skeleton is thin. -/
protected instance thin (C : Type u₁) [category C] {X : thin_skeleton C} {Y : thin_skeleton C} : subsingleton (X ⟶ Y) :=
  subsingleton.intro
    fun (a b : X ⟶ Y) =>
      ulift.cases_on a
        fun (a : plift (X ≤ Y)) =>
          plift.cases_on a
            fun (f₁ : X ≤ Y) =>
              ulift.cases_on b
                fun (b : plift (X ≤ Y)) => plift.cases_on b fun (f₂ : X ≤ Y) => Eq.refl (ulift.up (plift.up f₁))

/-- A functor `C ⥤ D` computably lowers to a functor `thin_skeleton C ⥤ thin_skeleton D`. -/
def map {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) : thin_skeleton C ⥤ thin_skeleton D :=
  functor.mk (quotient.map (functor.obj F) sorry)
    fun (X Y : thin_skeleton C) =>
      quotient.rec_on_subsingleton₂ X Y fun (x y : C) (k : quotient.mk x ⟶ quotient.mk y) => hom_of_le sorry

theorem comp_to_thin_skeleton {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) : F ⋙ to_thin_skeleton D = to_thin_skeleton C ⋙ map F :=
  rfl

/-- Given a natural transformation `F₁ ⟶ F₂`, induce a natural transformation `map F₁ ⟶ map F₂`.-/
def map_nat_trans {C : Type u₁} [category C] {D : Type u₂} [category D] {F₁ : C ⥤ D} {F₂ : C ⥤ D} (k : F₁ ⟶ F₂) : map F₁ ⟶ map F₂ :=
  nat_trans.mk fun (X : thin_skeleton C) => quotient.rec_on_subsingleton X fun (x : C) => ulift.up (plift.up sorry)

-- TODO: state the lemmas about what happens when you compose with `to_thin_skeleton`

/-- A functor `C ⥤ D ⥤ E` computably lowers to a functor
`thin_skeleton C ⥤ thin_skeleton D ⥤ thin_skeleton E` -/
@[simp] theorem map₂_obj_obj {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] (F : C ⥤ D ⥤ E) (x : thin_skeleton C) (y : thin_skeleton D) : functor.obj (functor.obj (map₂ F) x) y =
  quotient.map₂ (fun (X : C) (Y : D) => functor.obj (functor.obj F X) Y) (map₂._proof_1 F) x y :=
  Eq.refl (functor.obj (functor.obj (map₂ F) x) y)

protected instance to_thin_skeleton_faithful (C : Type u₁) [category C] [∀ (X Y : C), subsingleton (X ⟶ Y)] : faithful (to_thin_skeleton C) :=
  faithful.mk

/-- Use `quotient.out` to create a functor out of the thin skeleton. -/
@[simp] theorem from_thin_skeleton_map (C : Type u₁) [category C] [∀ (X Y : C), subsingleton (X ⟶ Y)] (x : thin_skeleton C) (y : thin_skeleton C) : ∀ (ᾰ : x ⟶ y),
  functor.map (from_thin_skeleton C) ᾰ =
    quotient.rec_on_subsingleton₂ x y
      (fun (X Y : C) (f : quotient.mk X ⟶ quotient.mk Y) =>
        iso.hom (nonempty.some (from_thin_skeleton._proof_2 C X)) ≫
          nonempty.some (from_thin_skeleton._proof_3 C X Y f) ≫
            iso.inv (nonempty.some (from_thin_skeleton._proof_4 C Y)))
      ᾰ :=
  fun (ᾰ : x ⟶ y) => Eq.refl (functor.map (from_thin_skeleton C) ᾰ)

protected instance from_thin_skeleton_equivalence (C : Type u₁) [category C] [∀ (X Y : C), subsingleton (X ⟶ Y)] : is_equivalence (from_thin_skeleton C) :=
  is_equivalence.mk' (to_thin_skeleton C)
    (nat_iso.of_components (fun (x : thin_skeleton C) => quotient.rec_on_subsingleton x fun (X : C) => eq_to_iso sorry)
      sorry)
    (nat_iso.of_components (fun (X : C) => nonempty.some sorry) sorry)

theorem equiv_of_both_ways {C : Type u₁} [category C] [∀ (X Y : C), subsingleton (X ⟶ Y)] {X : C} {Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y :=
  Nonempty.intro (iso_of_both_ways f g)

protected instance thin_skeleton_partial_order {C : Type u₁} [category C] [∀ (X Y : C), subsingleton (X ⟶ Y)] : partial_order (thin_skeleton C) :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

theorem skeletal {C : Type u₁} [category C] [∀ (X Y : C), subsingleton (X ⟶ Y)] : skeletal (thin_skeleton C) := sorry

theorem map_comp_eq {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] [∀ (X Y : C), subsingleton (X ⟶ Y)] (F : E ⥤ D) (G : D ⥤ C) : map (F ⋙ G) = map F ⋙ map G := sorry

theorem map_id_eq {C : Type u₁} [category C] [∀ (X Y : C), subsingleton (X ⟶ Y)] : map 𝟭 = 𝟭 := sorry

theorem map_iso_eq {C : Type u₁} [category C] {D : Type u₂} [category D] [∀ (X Y : C), subsingleton (X ⟶ Y)] {F₁ : D ⥤ C} {F₂ : D ⥤ C} (h : F₁ ≅ F₂) : map F₁ = map F₂ :=
  functor.eq_of_iso skeletal (iso.mk (map_nat_trans (iso.hom h)) (map_nat_trans (iso.inv h)))

/-- `from_thin_skeleton C` exhibits the thin skeleton as a skeleton. -/
def thin_skeleton_is_skeleton {C : Type u₁} [category C] [∀ (X Y : C), subsingleton (X ⟶ Y)] : is_skeleton_of C (thin_skeleton C) (from_thin_skeleton C) :=
  is_skeleton_of.mk sorry (thin_skeleton.from_thin_skeleton_equivalence C)

protected instance is_skeleton_of_inhabited {C : Type u₁} [category C] [∀ (X Y : C), subsingleton (X ⟶ Y)] : Inhabited (is_skeleton_of C (thin_skeleton C) (from_thin_skeleton C)) :=
  { default := thin_skeleton_is_skeleton }

