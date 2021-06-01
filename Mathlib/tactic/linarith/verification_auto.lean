/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.linarith.elimination
import Mathlib.tactic.linarith.parsing
import Mathlib.PostPort

namespace Mathlib

/-!
# Deriving a proof of false

`linarith` uses an untrusted oracle to produce a certificate of unsatisfiability.
It needs to do some proof reconstruction work to turn this into a proof term.
This file implements the reconstruction.

## Main declarations

The public facing declaration in this file is `prove_false_by_linarith`.
-/

namespace linarith


/-! ### Auxiliary functions for assembling proofs -/

/--
`mul_expr n e` creates a `pexpr` representing `n*e`.
When elaborated, the coefficient will be a native numeral of the same type as `e`.
-/
end Mathlib