/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.limits
import Mathlib.category_theory.thin
import Mathlib.PostPort

universes v l u 

namespace Mathlib

/-!
# Wide pullbacks

We define the category `wide_pullback_shape`, (resp. `wide_pushout_shape`) which is the category
obtained from a discrete category of type `J` by adjoining a terminal (resp. initial) element.
Limits of this shape are wide pullbacks (pushouts).
The convenience method `wide_cospan` (`wide_span`) constructs a functor from this category, hitting
the given morphisms.

We use `wide_pullback_shape` to define ordinary pullbacks (pushouts) by using `J := walking_pair`,
which allows easy proofs of some related lemmas.
Furthermore, wide pullbacks are used to show the existence of limits in the slice category.
Namely, if `C` has wide pullbacks then `C/B` has limits for any object `B` in `C`.

Typeclasses `has_wide_pullbacks` and `has_finite_wide_pullbacks` assert the existence of wide
pullbacks and finite wide pullbacks.
-/

namespace category_theory.limits


/-- A wide pullback shape for any type `J` can be written simply as `option J`. -/
def wide_pullback_shape (J : Type v) := Option J

/-- A wide pushout shape for any type `J` can be written simply as `option J`. -/
def wide_pushout_shape (J : Type v) := Option J

namespace wide_pullback_shape


/-- The type of arrows for the shape indexing a wide pullback. -/
inductive hom {J : Type v} : wide_pullback_shape J → wide_pullback_shape J → Type v where
| id : (X : wide_pullback_shape J) → hom X X
| term : (j : J) → hom (some j) none

protected instance struct {J : Type v} : category_struct (wide_pullback_shape J) := sorry

protected instance hom.inhabited {J : Type v} : Inhabited (hom none none) :=
  { default := hom.id none }

protected instance subsingleton_hom {J : Type v} (j : wide_pullback_shape J)
    (j' : wide_pullback_shape J) : subsingleton (j ⟶ j') :=
  sorry

protected instance category {J : Type v} : small_category (wide_pullback_shape J) := thin_category

@[simp] theorem hom_id {J : Type v} (X : wide_pullback_shape J) : hom.id X = 𝟙 := rfl

/--
Construct a functor out of the wide pullback shape given a J-indexed collection of arrows to a
fixed object.
-/
@[simp] theorem wide_cospan_map {J : Type v} {C : Type u} [category C] (B : C) (objs : J → C)
    (arrows : (j : J) → objs j ⟶ B) (X : wide_pullback_shape J) (Y : wide_pullback_shape J)
    (f : X ⟶ Y) :
    functor.map (wide_cospan B objs arrows) f =
        hom.cases_on f
          (fun (f_1 : wide_pullback_shape J) (H_1 : X = f_1) =>
            Eq._oldrec
              (fun (H_2 : Y = X) =>
                Eq._oldrec
                  (fun (f : X ⟶ X) (H_3 : f == hom.id X) =>
                    Eq._oldrec 𝟙 (wide_cospan._proof_1 X f H_3))
                  (wide_cospan._proof_2 X Y H_2) f)
              H_1)
          (fun (j : J) (H_1 : X = some j) =>
            Eq._oldrec
              (fun (f : some j ⟶ Y) (H_2 : Y = none) =>
                Eq._oldrec
                  (fun (f : some j ⟶ none) (H_3 : f == hom.term j) =>
                    Eq._oldrec (arrows j) (wide_cospan._proof_3 j f H_3))
                  (wide_cospan._proof_4 Y H_2) f)
              (wide_cospan._proof_5 X j H_1) f)
          (wide_cospan._proof_6 X) (wide_cospan._proof_7 Y) (wide_cospan._proof_8 X Y f) :=
  Eq.refl (functor.map (wide_cospan B objs arrows) f)

/-- Every diagram is naturally isomorphic (actually, equal) to a `wide_cospan` -/
def diagram_iso_wide_cospan {J : Type v} {C : Type u} [category C] (F : wide_pullback_shape J ⥤ C) :
    F ≅
        wide_cospan (functor.obj F none) (fun (j : J) => functor.obj F (some j))
          fun (j : J) => functor.map F (hom.term j) :=
  nat_iso.of_components (fun (j : wide_pullback_shape J) => eq_to_iso sorry) sorry

end wide_pullback_shape


namespace wide_pushout_shape


/-- The type of arrows for the shape indexing a wide psuhout. -/
inductive hom {J : Type v} : wide_pushout_shape J → wide_pushout_shape J → Type v where
| id : (X : wide_pushout_shape J) → hom X X
| init : (j : J) → hom none (some j)

protected instance struct {J : Type v} : category_struct (wide_pushout_shape J) := sorry

protected instance hom.inhabited {J : Type v} : Inhabited (hom none none) :=
  { default := hom.id none }

protected instance subsingleton_hom {J : Type v} (j : wide_pushout_shape J)
    (j' : wide_pushout_shape J) : subsingleton (j ⟶ j') :=
  sorry

protected instance category {J : Type v} : small_category (wide_pushout_shape J) := thin_category

@[simp] theorem hom_id {J : Type v} (X : wide_pushout_shape J) : hom.id X = 𝟙 := rfl

/--
Construct a functor out of the wide pushout shape given a J-indexed collection of arrows from a
fixed object.
-/
@[simp] theorem wide_span_map {J : Type v} {C : Type u} [category C] (B : C) (objs : J → C)
    (arrows : (j : J) → B ⟶ objs j) (X : wide_pushout_shape J) (Y : wide_pushout_shape J)
    (f : X ⟶ Y) :
    functor.map (wide_span B objs arrows) f =
        hom.cases_on f
          (fun (f_1 : wide_pushout_shape J) (H_1 : X = f_1) =>
            Eq._oldrec
              (fun (H_2 : Y = X) =>
                Eq._oldrec
                  (fun (f : X ⟶ X) (H_3 : f == hom.id X) =>
                    Eq._oldrec 𝟙 (wide_span._proof_1 X f H_3))
                  (wide_span._proof_2 X Y H_2) f)
              H_1)
          (fun (j : J) (H_1 : X = none) =>
            Eq._oldrec
              (fun (f : none ⟶ Y) (H_2 : Y = some j) =>
                Eq._oldrec
                  (fun (f : none ⟶ some j) (H_3 : f == hom.init j) =>
                    Eq._oldrec (arrows j) (wide_span._proof_3 j f H_3))
                  (wide_span._proof_4 Y j H_2) f)
              (wide_span._proof_5 X H_1) f)
          (wide_span._proof_6 X) (wide_span._proof_7 Y) (wide_span._proof_8 X Y f) :=
  Eq.refl (functor.map (wide_span B objs arrows) f)

/-- Every diagram is naturally isomorphic (actually, equal) to a `wide_span` -/
def diagram_iso_wide_span {J : Type v} {C : Type u} [category C] (F : wide_pushout_shape J ⥤ C) :
    F ≅
        wide_span (functor.obj F none) (fun (j : J) => functor.obj F (some j))
          fun (j : J) => functor.map F (hom.init j) :=
  nat_iso.of_components (fun (j : wide_pushout_shape J) => eq_to_iso sorry) sorry

end wide_pushout_shape


/-- `has_wide_pullbacks` represents a choice of wide pullback for every collection of morphisms -/
def has_wide_pullbacks (C : Type u) [category C] :=
  ∀ (J : Type v), has_limits_of_shape (wide_pullback_shape J) C

/-- `has_wide_pushouts` represents a choice of wide pushout for every collection of morphisms -/
def has_wide_pushouts (C : Type u) [category C] :=
  ∀ (J : Type v), has_colimits_of_shape (wide_pushout_shape J) C

end Mathlib