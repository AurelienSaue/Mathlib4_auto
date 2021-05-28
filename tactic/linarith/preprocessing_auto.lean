/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.linarith.datatypes
import Mathlib.tactic.zify
import Mathlib.tactic.cancel_denoms
import PostPort

namespace Mathlib

/-!
# Linarith preprocessing

This file contains methods used to preprocess inputs to `linarith`.

In particular, `linarith` works over comparisons of the form `t R 0`, where `R ∈ {<,≤,=}`.
It assumes that expressions in `t` have integer coefficients and that the type of `t` has
well-behaved subtraction.

## Implementation details

A `global_preprocessor` is a function `list expr → tactic(list expr)`. Users can add custom
preprocessing steps by adding them to the `linarith_config` object. `linarith.default_preprocessors`
is the main list, and generally none of these should be skipped unless you know what you're doing.
-/

namespace linarith


/-! ### Preprocessing -/

/--
If `prf` is a proof of `¬ e`, where `e` is a comparison,
`rem_neg prf e` flips the comparison in `e` and returns a proof.
For example, if `prf : ¬ a < b`, ``rem_neg prf `(a < b)`` returns a proof of `a ≥ b`.
-/
