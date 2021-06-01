/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.finite_limits
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.limits.shapes.terminal
import Mathlib.PostPort

universes v u 

namespace Mathlib

namespace category_theory.limits


/--
A category has finite products if there is a chosen limit for every diagram
with shape `discrete J`, where we have `[decidable_eq J]` and `[fintype J]`.
-/
-- We can't simply make this an abbreviation, as we do with other `has_Xs` limits typeclasses,

-- because of https://github.com/leanprover-community/lean/issues/429

def has_finite_products (C : Type u) [category C] :=
  ∀ (J : Type v) [_inst_2 : DecidableEq J] [_inst_3 : fintype J], has_limits_of_shape (discrete J) C

protected instance has_limits_of_shape_discrete (C : Type u) [category C] (J : Type v) [fintype J]
    [has_finite_products C] : has_limits_of_shape (discrete J) C :=
  _inst_3 J

/-- If `C` has finite limits then it has finite products. -/
theorem has_finite_products_of_has_finite_limits (C : Type u) [category C] [has_finite_limits C] :
    has_finite_products C :=
  fun (J : Type v) (𝒥₁ : DecidableEq J) (𝒥₂ : fintype J) =>
    limits.has_limits_of_shape_of_has_finite_limits C (discrete J)

/--
If a category has all products then in particular it has finite products.
-/
theorem has_finite_products_of_has_products (C : Type u) [category C] [has_products C] :
    has_finite_products C :=
  id fun (J : Type v) => _inst_2 J

/--
A category has finite coproducts if there is a chosen colimit for every diagram
with shape `discrete J`, where we have `[decidable_eq J]` and `[fintype J]`.
-/
def has_finite_coproducts (C : Type u) [category C] :=
  ∀ (J : Type v) [_inst_2 : DecidableEq J] [_inst_3 : fintype J],
    has_colimits_of_shape (discrete J) C

protected instance has_colimits_of_shape_discrete (C : Type u) [category C] (J : Type v) [fintype J]
    [has_finite_coproducts C] : has_colimits_of_shape (discrete J) C :=
  _inst_3 J

/-- If `C` has finite colimits then it has finite coproducts. -/
theorem has_finite_coproducts_of_has_finite_colimits (C : Type u) [category C]
    [has_finite_colimits C] : has_finite_coproducts C :=
  fun (J : Type v) (𝒥₁ : DecidableEq J) (𝒥₂ : fintype J) =>
    limits.has_colimits_of_shape_of_has_finite_colimits C (discrete J)

/--
If a category has all coproducts then in particular it has finite coproducts.
-/
theorem has_finite_coproducts_of_has_coproducts (C : Type u) [category C] [has_coproducts C] :
    has_finite_coproducts C :=
  id fun (J : Type v) => _inst_2 J

end Mathlib