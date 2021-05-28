/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.category_theory.fin_category
import Mathlib.category_theory.limits.shapes.products
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.PostPort

universes v u u_1 

namespace Mathlib

/-!
# Categories with finite limits.

A typeclass for categories with all finite (co)limits.
-/

namespace category_theory.limits


/--
A category has all finite limits if every functor `J ⥤ C` with a `fin_category J` instance
has a limit.

This is often called 'finitely complete'.
-/
-- We can't just made this an `abbreviation`

-- because of https://github.com/leanprover-community/lean/issues/429

def has_finite_limits (C : Type u) [category C]  :=
  ∀ (J : Type v) [𝒥 : small_category J] [_inst_2 : fin_category J], has_limits_of_shape J C

protected instance has_limits_of_shape_of_has_finite_limits (C : Type u) [category C] (J : Type v) [small_category J] [fin_category J] [has_finite_limits C] : has_limits_of_shape J C :=
  _inst_4 J

/-- If `C` has all limits, it has finite limits. -/
theorem has_finite_limits_of_has_limits (C : Type u) [category C] [has_limits C] : has_finite_limits C :=
  fun (J : Type v) (𝒥₁ : small_category J) (𝒥₂ : fin_category J) => limits.has_limits_of_shape_of_has_limits

/--
A category has all finite colimits if every functor `J ⥤ C` with a `fin_category J` instance
has a colimit.

This is often called 'finitely cocomplete'.
-/
def has_finite_colimits (C : Type u) [category C]  :=
  ∀ (J : Type v) [𝒥 : small_category J] [_inst_2 : fin_category J], has_colimits_of_shape J C

protected instance has_colimits_of_shape_of_has_finite_colimits (C : Type u) [category C] (J : Type v) [small_category J] [fin_category J] [has_finite_colimits C] : has_colimits_of_shape J C :=
  _inst_4 J

/-- If `C` has all colimits, it has finite colimits. -/
theorem has_finite_colimits_of_has_colimits (C : Type u) [category C] [has_colimits C] : has_finite_colimits C :=
  fun (J : Type v) (𝒥₁ : small_category J) (𝒥₂ : fin_category J) => limits.has_colimits_of_shape_of_has_colimits

protected instance fintype_walking_parallel_pair : fintype walking_parallel_pair :=
  fintype.mk (list.to_finset [walking_parallel_pair.zero, walking_parallel_pair.one]) sorry

protected instance walking_parallel_pair_hom.fintype (j : walking_parallel_pair) (j' : walking_parallel_pair) : fintype (walking_parallel_pair_hom j j') :=
  fintype.mk
    (walking_parallel_pair.rec_on j
      (walking_parallel_pair.rec_on j' (list.to_finset [walking_parallel_pair_hom.id walking_parallel_pair.zero])
        (list.to_finset [walking_parallel_pair_hom.left, walking_parallel_pair_hom.right]))
      (walking_parallel_pair.rec_on j' ∅ (list.to_finset [walking_parallel_pair_hom.id walking_parallel_pair.one])))
    sorry

protected instance walking_parallel_pair.category_theory.fin_category : fin_category walking_parallel_pair :=
  fin_category.mk

/-- Equalizers are finite limits, so if `C` has all finite limits, it also has all equalizers -/
/-- Coequalizers are finite colimits, of if `C` has all finite colimits, it also has all
    coequalizers -/
namespace wide_pullback_shape


protected instance fintype_obj {J : Type v} [fintype J] : fintype (wide_pullback_shape J) :=
  eq.mpr sorry option.fintype

protected instance fintype_hom {J : Type v} [DecidableEq J] (j : wide_pullback_shape J) (j' : wide_pullback_shape J) : fintype (j ⟶ j') :=
  fintype.mk
    (option.cases_on j' (option.cases_on j (singleton (hom.id none)) fun (j : J) => singleton (hom.term j))
      fun (j' : J) =>
        dite (some j' = j) (fun (h : some j' = j) => eq.mpr sorry (singleton (hom.id j))) fun (h : ¬some j' = j) => ∅)
    sorry

end wide_pullback_shape


namespace wide_pushout_shape


protected instance fintype_obj {J : Type v} [fintype J] : fintype (wide_pushout_shape J) :=
  eq.mpr sorry option.fintype

protected instance fintype_hom {J : Type v} [DecidableEq J] (j : wide_pushout_shape J) (j' : wide_pushout_shape J) : fintype (j ⟶ j') :=
  fintype.mk
    (option.cases_on j (option.cases_on j' (singleton (hom.id none)) fun (j' : J) => singleton (hom.init j'))
      fun (j : J) =>
        dite (some j = j') (fun (h : some j = j') => eq.mpr sorry (singleton (hom.id j'))) fun (h : ¬some j = j') => ∅)
    sorry

end wide_pushout_shape


protected instance fin_category_wide_pullback {J : Type v} [DecidableEq J] [fintype J] : fin_category (wide_pullback_shape J) :=
  fin_category.mk

protected instance fin_category_wide_pushout {J : Type v} [DecidableEq J] [fintype J] : fin_category (wide_pushout_shape J) :=
  fin_category.mk

/--
`has_finite_wide_pullbacks` represents a choice of wide pullback
for every finite collection of morphisms
-/
-- We can't just made this an `abbreviation`

-- because of https://github.com/leanprover-community/lean/issues/429

def has_finite_wide_pullbacks (C : Type u) [category C]  :=
  ∀ (J : Type v) [_inst_2 : DecidableEq J] [_inst_3 : fintype J], has_limits_of_shape (wide_pullback_shape J) C

protected instance has_limits_of_shape_wide_pullback_shape (C : Type u) [category C] (J : Type v) [fintype J] [has_finite_wide_pullbacks C] : has_limits_of_shape (wide_pullback_shape J) C :=
  _inst_3 J

/--
`has_finite_wide_pushouts` represents a choice of wide pushout
for every finite collection of morphisms
-/
def has_finite_wide_pushouts (C : Type u) [category C]  :=
  ∀ (J : Type v) [_inst_2 : DecidableEq J] [_inst_3 : fintype J], has_colimits_of_shape (wide_pushout_shape J) C

protected instance has_colimits_of_shape_wide_pushout_shape (C : Type u) [category C] (J : Type v) [fintype J] [has_finite_wide_pushouts C] : has_colimits_of_shape (wide_pushout_shape J) C :=
  _inst_3 J

/--
Finite wide pullbacks are finite limits, so if `C` has all finite limits,
it also has finite wide pullbacks
-/
theorem has_finite_wide_pullbacks_of_has_finite_limits (C : Type u) [category C] [has_finite_limits C] : has_finite_wide_pullbacks C :=
  fun (J : Type v) (_x : DecidableEq J) (_x_1 : fintype J) =>
    limits.has_limits_of_shape_of_has_finite_limits C (wide_pullback_shape J)

/--
Finite wide pushouts are finite colimits, so if `C` has all finite colimits,
it also has finite wide pushouts
-/
theorem has_finite_wide_pushouts_of_has_finite_limits (C : Type u) [category C] [has_finite_colimits C] : has_finite_wide_pushouts C :=
  fun (J : Type v) (_x : DecidableEq J) (_x_1 : fintype J) =>
    limits.has_colimits_of_shape_of_has_finite_colimits C (wide_pushout_shape J)

protected instance fintype_walking_pair : fintype walking_pair :=
  fintype.mk (insert walking_pair.left (singleton walking_pair.right)) sorry

