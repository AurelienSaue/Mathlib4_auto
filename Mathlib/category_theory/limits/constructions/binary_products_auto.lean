/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.terminal
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# Constructing binary product from pullbacks and terminal object.

If a category has pullbacks and a terminal object, then it has binary products.

TODO: provide the dual result.
-/

/-- Any category with pullbacks and terminal object has binary products. -/
-- This is not an instance, as it is not always how one wants to construct binary products!

theorem has_binary_products_of_terminal_and_pullbacks (C : Type u) [𝒞 : category_theory.category C]
    [category_theory.limits.has_terminal C] [category_theory.limits.has_pullbacks C] :
    category_theory.limits.has_binary_products C :=
  sorry

end Mathlib