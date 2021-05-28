/-
Copyright (c) 2018 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.basic
import PostPort

namespace Mathlib

/-!
# `pi_instance`

Automation for creating instances of mathematical structures for pi types
-/

namespace tactic


/-- Attempt to clear a goal obtained by refining a `pi_instance` goal. -/
/--
`pi_instance` constructs an instance of `my_class (Π i : I, f i)`
where we know `Π i, my_class (f i)`. If an order relation is required,
it defaults to `pi.partial_order`. Any field of the instance that
`pi_instance` cannot construct is left untouched and generated as a new goal.
-/
