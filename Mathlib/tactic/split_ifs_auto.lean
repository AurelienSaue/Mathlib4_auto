/-
Copyright (c) 2018 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner.

Tactic to split if-then-else-expressions.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.hint
import PostPort

namespace Mathlib

namespace tactic


namespace interactive


/-- Splits all if-then-else-expressions into multiple goals.

Given a goal of the form `g (if p then x else y)`, `split_ifs` will produce
two goals: `p ⊢ g x` and `¬p ⊢ g y`.

If there are multiple ite-expressions, then `split_ifs` will split them all,
starting with a top-most one whose condition does not contain another
ite-expression.

`split_ifs at *` splits all ite-expressions in all hypotheses as well as the goal.

`split_ifs with h₁ h₂ h₃` overrides the default names for the hypotheses.
-/
