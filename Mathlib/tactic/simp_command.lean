/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

/-!
## #simp
A user command to run the simplifier.
-/

namespace tactic


/-- Strip all annotations of non local constants in the passed `expr`. (This is required in an
incantation later on in order to make the C++ simplifier happy.) -/
/-- `simp_arg_type.to_pexpr` retrieves the `pexpr` underlying the given `simp_arg_type`, if there is
one. -/
/-- Incantation which prepares a `pexpr` in a `simp_arg_type` for use by the simplifier after
`expr.replace_subexprs` as been called to replace some of its local variables. -/
/-- `simp_arg_type.replace_subexprs` calls `expr.replace_subexprs` on the underlying `pexpr`, if
there is one, and then prepares the result for use by the simplifier. -/
/- Turn off the messages if the result is exactly `true` with this option. -/

/--
The basic usage is `#simp e`, where `e` is an expression,
which will print the simplified form of `e`.

You can specify additional simp lemmas as usual for example using
`#simp [f, g] : e`, or `#simp with attr : e`.
(The colon is optional, but helpful for the parser.)

`#simp` understands local variables, so you can use them to
introduce parameters.
-/
