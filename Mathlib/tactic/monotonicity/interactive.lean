/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.monotonicity.basic
import Mathlib.control.traversable.default
import Mathlib.control.traversable.derive
import Mathlib.Lean3Lib.data.dlist
import Mathlib.PostPort

universes u v u_1 u_2 l 

namespace Mathlib

namespace tactic.interactive


/--
`(prefix,left,right,suffix) ← match_assoc unif l r` finds the
longest prefix and suffix common to `l` and `r` and
returns them along with the differences  -/
def apply_rel {α : Sort u} (R : α → α → Sort v) {x : α} {y : α} (x' : α) (y' : α) (h : R x y) (hx : x = x') (hy : y = y') : R x' y' :=
  eq.mpr sorry (eq.mpr sorry h)

/-- tactic-facing function, similar to `interactive.tactic.generalize` with the
exception that meta variables -/
def list.minimum_on {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) : List α → List α :=
  sorry

/--
- `mono` applies a monotonicity rule.
- `mono*` applies monotonicity rules repetitively.
- `mono with x ≤ y` or `mono with [0 ≤ x,0 ≤ y]` creates an assertion for the listed
  propositions. Those help to select the right monotonicity rule.
- `mono left` or `mono right` is useful when proving strict orderings:
   for `x + y < w + z` could be broken down into either
    - left:  `x ≤ w` and `y < z` or
    - right: `x < w` and `y ≤ z`
- `mono using [rule1,rule2]` calls `simp [rule1,rule2]` before applying mono.
- The general syntax is `mono '*'? ('with' hyp | 'with' [hyp1,hyp2])? ('using' [hyp1,hyp2])? mono_cfg?

To use it, first import `tactic.monotonicity`.

Here is an example of mono:

```lean
example (x y z k : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y) :
  (k + 3 + x) - y ≤ (k + 4 + x) - z :=
begin
  mono, -- unfold `(-)`, apply add_le_add
  { -- ⊢ k + 3 + x ≤ k + 4 + x
    mono, -- apply add_le_add, refl
    -- ⊢ k + 3 ≤ k + 4
    mono },
  { -- ⊢ -y ≤ -z
    mono /- apply neg_le_neg -/ }
end
```

More succinctly, we can prove the same goal as:

```lean
example (x y z k : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y) :
  (k + 3 + x) - y ≤ (k + 4 + x) - z :=
by mono*
```

-/
/--
transforms a goal of the form `f x ≼ f y` into `x ≤ y` using lemmas
marked as `monotonic`.

Special care is taken when `f` is the repeated application of an
associative operator and if the operator is commutative
-/
/-- (repeat_until_or_at_most n t u): repeat tactic `t` at most n times or until u succeeds -/
inductive rep_arity 
where
| one : rep_arity
| exactly : ℕ → rep_arity
| many : rep_arity

/--

`ac_mono` reduces the `f x ⊑ f y`, for some relation `⊑` and a
monotonic function `f` to `x ≺ y`.

`ac_mono*` unwraps monotonic functions until it can't.

`ac_mono^k`, for some literal number `k` applies monotonicity `k`
times.

`ac_mono h`, with `h` a hypothesis, unwraps monotonic functions and
uses `h` to solve the remaining goal. Can be combined with `*` or `^k`:
`ac_mono* h`

`ac_mono : p` asserts `p` and uses it to discharge the goal result
unwrapping a series of monotonic functions. Can be combined with * or
^k: `ac_mono* : p`

In the case where `f` is an associative or commutative operator,
`ac_mono` will consider any possible permutation of its arguments and
use the one the minimizes the difference between the left-hand side
and the right-hand side.

To use it, first import `tactic.monotonicity`.

`ac_mono` can be used as follows:

```lean
example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y) :
  (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono,
  -- ⊢ (m + x + n) * z ≤ z * (y + n + m)
  ac_mono,
  -- ⊢ m + x + n ≤ y + n + m
  ac_mono,
end
```

As with `mono*`, `ac_mono*` solves the goal in one go and so does
`ac_mono* h₁`. The latter syntax becomes especially interesting in the
following example:

```lean
example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : m + x + n ≤ y + n + m) :
  (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by ac_mono* h₁.
```

By giving `ac_mono` the assumption `h₁`, we are asking `ac_refl` to
stop earlier than it would normally would.
-/
/-
TODO(Simon): with `ac_mono h` and `ac_mono : p` split the remaining
  gaol if the provided rule does not solve it completely.
-/

