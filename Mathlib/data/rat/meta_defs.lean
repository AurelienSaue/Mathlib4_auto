/-
Copyright (c) 2019 Robert Y. Lewis . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.rat.basic
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

/-!
# Meta operations on ℚ

This file defines functions for dealing with rational numbers as expressions.

They are not defined earlier in the hierarchy, in the `tactic` or `meta` folders, since we do not
want to import `data.rat.basic` there.

## Main definitions

* `rat.mk_numeral` embeds a rational `q` as a numeral expression into a type supporting the needed
  operations. It does not need a tactic state.
* `rat.reflect` specializes `rat.mk_numeral` to `ℚ`.
* `expr.of_rat` behaves like `rat.mk_numeral`, but uses the tactic state to infer the needed
  structure on the target type.

* `expr.to_rat` evaluates a normal numeral expression as a rat.
* `expr.eval_rat` evaluates a numeral expression with arithmetic operations as a rat.

-/

/--
`rat.mk_numeral q` embeds `q` as a numeral expression inside a type with 0, 1, +, -, and /

`type`: an expression representing the target type. This must live in Type 0.
`has_zero`, `has_one`, `has_add`: expressions of the type `has_zero %%type`, etc.

This function is similar to `expr.of_rat` but takes more hypotheses and is not tactic valued.
 -/
