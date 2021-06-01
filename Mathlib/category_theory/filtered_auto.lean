/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.fin_category
import Mathlib.category_theory.limits.cones
import Mathlib.category_theory.adjunction.basic
import Mathlib.order.bounded_lattice
import Mathlib.PostPort

universes v u l v₁ u₁ 

namespace Mathlib

/-!
# Filtered categories

A category is filtered if every finite diagram admits a cocone.
We give a simple characterisation of this condition as
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

Filtered colimits are often better behaved than arbitrary colimits.
See `category_theory/limits/types` for some details.

Filtered categories are nice because colimits indexed by filtered categories tend to be
easier to describe than general colimits (and often often preserved by functors).

In this file we show that any functor from a finite category to a filtered category admits a cocone:
* `cocone_nonempty [fin_category J] [is_filtered C] (F : J ⥤ C) : nonempty (cocone F)`
More generally,
for any finite collection of objects and morphisms between them in a filtered category
(even if not closed under composition) there exists some object `Z` receiving maps from all of them,
so that all the triangles (one edge from the finite set, two from morphisms to `Z`) commute.
This formulation is often more useful in practice. We give two variants,
`sup_exists'`, which takes a single finset of objects, and a finset of morphisms
(bundled with their sources and targets), and
`sup_exists`, which takes a finset of objects, and an indexed family (indexed by source and target)
of finsets of morphisms.

## Future work
* Finite limits commute with filtered colimits
* Forgetful functors for algebraic categories typically preserve filtered colimits.
-/

namespace category_theory


/--
A category `is_filtered_or_empty` if
1. for every pair of objects there exists another object "to the right", and
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal.
-/
class is_filtered_or_empty (C : Type u) [category C] where
  cocone_objs : ∀ (X Y : C), ∃ (Z : C), ∃ (f : X ⟶ Z), ∃ (g : Y ⟶ Z), True
  cocone_maps : ∀ {X Y : C} (f g : X ⟶ Y), ∃ (Z : C), ∃ (h : Y ⟶ Z), f ≫ h = g ≫ h

/--
A category `is_filtered` if
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

See https://stacks.math.columbia.edu/tag/002V. (They also define a diagram being filtered.)
-/
class is_filtered (C : Type u) [category C] extends is_filtered_or_empty C where
  nonempty : Nonempty C

protected instance is_filtered_or_empty_of_semilattice_sup (α : Type u) [semilattice_sup α] :
    is_filtered_or_empty α :=
  is_filtered_or_empty.mk
    (fun (X Y : α) =>
      Exists.intro (X ⊔ Y)
        (Exists.intro (hom_of_le le_sup_left) (Exists.intro (hom_of_le le_sup_right) trivial)))
    fun (X Y : α) (f g : X ⟶ Y) =>
      Exists.intro Y
        (Exists.intro 𝟙
          (ulift.ext (f ≫ 𝟙) (g ≫ 𝟙) (plift.ext (ulift.down (f ≫ 𝟙)) (ulift.down (g ≫ 𝟙)))))

protected instance is_filtered_of_semilattice_sup_top (α : Type u) [semilattice_sup_top α] :
    is_filtered α :=
  is_filtered.mk

namespace is_filtered


/--
`max j j'` is an arbitrary choice of object to the right of both `j` and `j'`,
whose existence is ensured by `is_filtered`.
-/
def max {C : Type u} [category C] [is_filtered C] (j : C) (j' : C) : C := Exists.some sorry

/--
`left_to_max j j'` is an arbitrarily choice of morphism from `j` to `max j j'`,
whose existence is ensured by `is_filtered`.
-/
def left_to_max {C : Type u} [category C] [is_filtered C] (j : C) (j' : C) : j ⟶ max j j' :=
  Exists.some sorry

/--
`right_to_max j j'` is an arbitrarily choice of morphism from `j'` to `max j j'`,
whose existence is ensured by `is_filtered`.
-/
def right_to_max {C : Type u} [category C] [is_filtered C] (j : C) (j' : C) : j' ⟶ max j j' :=
  Exists.some sorry

/--
`coeq f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of object
which admits a morphism `coeq_hom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
Its existence is ensured by `is_filtered`.
-/
def coeq {C : Type u} [category C] [is_filtered C] {j : C} {j' : C} (f : j ⟶ j') (f' : j ⟶ j') :
    C :=
  Exists.some sorry

/--
`coeq_hom f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of morphism
`coeq_hom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
Its existence is ensured by `is_filtered`.
-/
def coeq_hom {C : Type u} [category C] [is_filtered C] {j : C} {j' : C} (f : j ⟶ j') (f' : j ⟶ j') :
    j' ⟶ coeq f f' :=
  Exists.some sorry

/--
`coeq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
-/
@[simp] theorem coeq_condition_assoc {C : Type u} [category C] [is_filtered C] {j : C} {j' : C}
    (f : j ⟶ j') (f' : j ⟶ j') {X' : C} :
    ∀ (f'_1 : coeq f f' ⟶ X'), f ≫ coeq_hom f f' ≫ f'_1 = f' ≫ coeq_hom f f' ≫ f'_1 :=
  sorry

/--
Any finite collection of objects in a filtered category has an object "to the right".
-/
theorem sup_objs_exists {C : Type u} [category C] [is_filtered C] (O : finset C) :
    ∃ (S : C), ∀ {X : C}, X ∈ O → Nonempty (X ⟶ S) :=
  sorry

/--
Given any `finset` of objects `{X, ...}` and
indexed collection of `finset`s of morphisms `{f, ...}` in `C`,
there exists an object `S`, with a morphism `T X : X ⟶ S` from each `X`,
such that the triangles commute: `f ≫ T X = T Y`, for `f : X ⟶ Y` in the `finset`.
-/
theorem sup_exists {C : Type u} [category C] [is_filtered C] (O : finset C)
    (H :
      finset
        (psigma
          fun (X : C) =>
            psigma fun (Y : C) => psigma fun (mX : X ∈ O) => psigma fun (mY : Y ∈ O) => X ⟶ Y)) :
    ∃ (S : C),
        ∃ (T : {X : C} → X ∈ O → (X ⟶ S)),
          ∀ {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y},
            psigma.mk X (psigma.mk Y (psigma.mk mX (psigma.mk mY f))) ∈ H → f ≫ T mY = T mX :=
  sorry

/--
An arbitrary choice of object "to the right" of a finite collection of objects `O` and morphisms `H`,
making all the triangles commute.
-/
def sup {C : Type u} [category C] [is_filtered C] (O : finset C)
    (H :
      finset
        (psigma
          fun (X : C) =>
            psigma fun (Y : C) => psigma fun (mX : X ∈ O) => psigma fun (mY : Y ∈ O) => X ⟶ Y)) :
    C :=
  Exists.some (sup_exists O H)

/--
The morphisms to `sup O H`.
-/
def to_sup {C : Type u} [category C] [is_filtered C] (O : finset C)
    (H :
      finset
        (psigma
          fun (X : C) =>
            psigma fun (Y : C) => psigma fun (mX : X ∈ O) => psigma fun (mY : Y ∈ O) => X ⟶ Y))
    {X : C} (m : X ∈ O) : X ⟶ sup O H :=
  Exists.some sorry X m

/--
The triangles of consisting of a morphism in `H` and the maps to `sup O H` commute.
-/
theorem to_sup_commutes {C : Type u} [category C] [is_filtered C] (O : finset C)
    (H :
      finset
        (psigma
          fun (X : C) =>
            psigma fun (Y : C) => psigma fun (mX : X ∈ O) => psigma fun (mY : Y ∈ O) => X ⟶ Y))
    {X : C} {Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y}
    (mf : psigma.mk X (psigma.mk Y (psigma.mk mX (psigma.mk mY f))) ∈ H) :
    f ≫ to_sup O H mY = to_sup O H mX :=
  Exists.some_spec (Exists.some_spec (sup_exists O H)) X Y mX mY f mf

/--
If we have `is_filtered C`, then for any functor `F : J ⥤ C` with `fin_category J`,
there exists a cocone over `F`.
-/
theorem cocone_nonempty {C : Type u} [category C] [is_filtered C] {J : Type v} [small_category J]
    [fin_category J] (F : J ⥤ C) : Nonempty (limits.cocone F) :=
  sorry

/--
An arbitrary choice of cocone over `F : J ⥤ C`, for `fin_category J` and `is_filtered C`.
-/
def cocone {C : Type u} [category C] [is_filtered C] {J : Type v} [small_category J]
    [fin_category J] (F : J ⥤ C) : limits.cocone F :=
  nonempty.some (cocone_nonempty F)

/--
If `C` is filtered, and we have a functor `R : C ⥤ D` with a left adjoint, then `D` is filtered.
-/
theorem of_right_adjoint {C : Type u} [category C] [is_filtered C] {D : Type u₁} [category D]
    {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R) : is_filtered D :=
  mk

/-- If `C` is filtered, and we have a right adjoint functor `R : C ⥤ D`, then `D` is filtered. -/
theorem of_is_right_adjoint {C : Type u} [category C] [is_filtered C] {D : Type u₁} [category D]
    (R : C ⥤ D) [is_right_adjoint R] : is_filtered D :=
  of_right_adjoint (adjunction.of_right_adjoint R)

/-- Being filtered is preserved by equivalence of categories. -/
theorem of_equivalence {C : Type u} [category C] [is_filtered C] {D : Type u₁} [category D]
    (h : C ≌ D) : is_filtered D :=
  of_right_adjoint (equivalence.to_adjunction (equivalence.symm h))

end Mathlib