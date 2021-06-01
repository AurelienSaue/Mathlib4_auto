/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.nth_rewrite.default
import Mathlib.tactic.rewrite_search.types
import Mathlib.PostPort

namespace Mathlib

/-!
# Generating a list of rewrites to use as steps in rewrite search.
-/

namespace tactic.rewrite_search


/--
Convert a list of expressions into a list of rules. The difference is that a rule
includes a flag for direction, so this simply includes each expression twice,
once in each direction.
-/
end Mathlib