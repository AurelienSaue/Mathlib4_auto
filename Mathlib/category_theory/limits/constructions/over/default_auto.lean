/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.constructions.over.products
import Mathlib.category_theory.limits.constructions.over.connected
import Mathlib.category_theory.limits.constructions.limits_of_products_and_equalizers
import Mathlib.category_theory.limits.constructions.equalizers
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# Limits in the over category

Declare instances for limits in the over category: If `C` has finite wide pullbacks, `over B` has
finite limits, and if `C` has arbitrary wide pullbacks then `over B` has limits.
-/

namespace category_theory.over


/-- Make sure we can derive pullbacks in `over B`. -/
/-- Make sure we can derive equalizers in `over B`. -/
protected instance has_finite_limits {C : Type u} [category C] {B : C}
    [limits.has_finite_wide_pullbacks C] : limits.has_finite_limits (over B) :=
  limits.finite_limits_from_equalizers_and_finite_products

protected instance has_limits {C : Type u} [category C] {B : C} [limits.has_wide_pullbacks C] :
    limits.has_limits (over B) :=
  limits.limits_from_equalizers_and_products

end Mathlib