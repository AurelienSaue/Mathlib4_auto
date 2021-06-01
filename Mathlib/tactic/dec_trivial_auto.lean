/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.interactive
import Mathlib.PostPort

namespace Mathlib

/-!
# `dec_trivial` tactic

The `dec_trivial` tactic tries to use decidability to prove a goal.
It is basically a glorified wrapper around `exact dec_trivial`.

There is an extra option to make it a little bit smarter:
`dec_trivial!` will revert all hypotheses on which the target depends,
before it tries `exact dec_trivial`.
-/

/-- `dec_trivial` tries to use decidability to prove a goal
(i.e., using `exact dec_trivial`).
The variant `dec_trivial!` will revert all hypotheses on which the target depends,
before it tries `exact dec_trivial`.

Example:
```lean
example (n : ℕ) (h : n < 2) : n = 0 ∨ n = 1 :=
by dec_trivial!
```
-/
end Mathlib