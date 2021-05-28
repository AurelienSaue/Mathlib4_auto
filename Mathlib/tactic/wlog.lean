/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Without loss of generality tactic.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.perm
import Mathlib.PostPort

namespace Mathlib

namespace tactic


namespace interactive


/-- Without loss of generality: reduces to one goal under variables permutations.

Given a goal of the form `g xs`, a predicate `p` over a set of variables, as well as variable
permutations `xs_i`. Then `wlog` produces goals of the form

The case goal, i.e. the permutation `xs_i` covers all possible cases:
  `⊢ p xs_0 ∨ ⋯ ∨ p xs_n`
The main goal, i.e. the goal reduced to `xs_0`:
  `(h : p xs_0) ⊢ g xs_0`
The invariant goals, i.e. `g` is invariant under `xs_i`:
  `(h : p xs_i) (this : g xs_0) ⊢ gs xs_i`

Either the permutation is provided, or a proof of the disjunction is provided to compute the
permutation. The disjunction need to be in assoc normal form, e.g. `p₀ ∨ (p₁ ∨ p₂)`. In many cases
the invariant goals can be solved by AC rewriting using `cc` etc.

Example:
  On a state `(n m : ℕ) ⊢ p n m` the tactic `wlog h : n ≤ m using [n m, m n]` produces the following
  states:
    `(n m : ℕ) ⊢ n ≤ m ∨ m ≤ n`
    `(n m : ℕ) (h : n ≤ m) ⊢ p n m`
    `(n m : ℕ) (h : m ≤ n) (this : p n m) ⊢ p m n`

`wlog` supports different calling conventions. The name `h` is used to give a name to the introduced
case hypothesis. If the name is avoided, the default will be `case`.

(1) `wlog : p xs0 using [xs0, …, xsn]`
  Results in the case goal `p xs0 ∨ ⋯ ∨ ps xsn`, the main goal `(case : p xs0) ⊢ g xs0` and the
  invariance goals `(case : p xsi) (this : g xs0) ⊢ g xsi`.

(2) `wlog : p xs0 := r using xs0`
  The expression `r` is a proof of the shape `p xs0 ∨ ⋯ ∨ p xsi`, it is also used to compute the
  variable permutations.

(3) `wlog := r using xs0`
  The expression `r` is a proof of the shape `p xs0 ∨ ⋯ ∨ p xsi`, it is also used to compute the
  variable permutations. This is not as stable as (2), for example `p` cannot be a disjunction.

(4) `wlog : R x y using x y` and `wlog : R x y`
  Produces the case `R x y ∨ R y x`. If `R` is ≤, then the disjunction discharged using linearity.
  If `using x y` is avoided then `x` and `y` are the last two variables appearing in the
  expression `R x y`. -/
