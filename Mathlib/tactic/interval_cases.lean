/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison

Case bashing on variables in finite intervals.

In particular, `interval_cases n`
1) inspects hypotheses looking for lower and upper bounds of the form `a ≤ n` and `n < b`
   (although in `ℕ`, `ℤ`, and `ℕ+` bounds of the form `a < n` and `n ≤ b` are also allowed),
   and also makes use of lower and upper bounds found via `le_top` and `bot_le`
   (so for example if `n : ℕ`, then the bound `0 ≤ n` is found automatically), then
2) calls `fin_cases` on the synthesised hypothesis `n ∈ set.Ico a b`,
   assuming an appropriate `fintype` instance can be found for the type of `n`.

The variable `n` can belong to any type `α`, with the following restrictions:
* only bounds on which `expr.to_rat` succeeds will be considered "explicit" (TODO: generalise this?)
* an instance of `decidable_eq α` is available,
* an explicit lower bound can be found amongst the hypotheses, or from `bot_le n`,
* an explicit upper bound can be found amongst the hypotheses, or from `le_top n`,
* if multiple bounds are located, an instance of `linear_order α` is available, and
* an instance of `fintype set.Ico l u` is available for the relevant bounds.

You can also explicitly specify a lower and upper bound to use, as `interval_cases using hl hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ set.Ico a b`.

-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.fin_cases
import Mathlib.data.fintype.intervals
import Mathlib.PostPort

universes u_1 

namespace Mathlib

namespace tactic


namespace interval_cases


/--
If `e` easily implies `(%%n < %%b)`
for some explicit `b`,
return that proof.
-/
-- We use `expr.to_rat` merely to decide if an `expr` is an explicit number.

-- It would be more natural to use `expr.to_int`, but that hasn't been implemented.

/--
If `e` easily implies `(%%n ≥ %%b)`
for some explicit `b`,
return that proof.
-/
/-- Combine two upper bounds. -/
/-- Combine two lower bounds. -/
/-- Inspect a given expression, using it to update a set of upper and lower bounds on `n`. -/
/--
Attempt to find a lower bound for the variable `n`, by evaluating `bot_le n`.
-/
/--
Attempt to find an upper bound for the variable `n`, by evaluating `le_top n`.
-/
/-- Inspect the local hypotheses for upper and lower bounds on a variable `n`. -/
/-- The finset of elements of a set `s` for which we have `fintype s`. -/
def set_elems {α : Type u_1} [DecidableEq α] (s : set α) [fintype ↥s] : finset α :=
  finset.image subtype.val (fintype.elems ↥s)

/-- Each element of `s` is a member of `set_elems s`. -/
theorem mem_set_elems {α : Type u_1} [DecidableEq α] (s : set α) [fintype ↥s] {a : α} (h : a ∈ s) : a ∈ set_elems s :=
  iff.mpr finset.mem_image
    (Exists.intro { val := a, property := h } (Exists.intro (fintype.complete { val := a, property := h }) rfl))

end interval_cases


/-- Call `fin_cases` on membership of the finset built from
an `Ico` interval corresponding to a lower and an upper bound.

Here `hl` should be an expression of the form `a ≤ n`, for some explicit `a`, and
`hu` should be of the form `n < b`, for some explicit `b`.

By default `interval_cases_using` automatically generates a name for the new hypothesis. The name can be specified via the optional argument `n`.
-/
namespace interactive


/--
`interval_cases n` searches for upper and lower bounds on a variable `n`,
and if bounds are found,
splits into separate cases for each possible value of `n`.

As an example, in
```
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
begin
  interval_cases n,
  all_goals {simp}
end
```
after `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also explicitly specify a lower and upper bound to use,
as `interval_cases using hl hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ set.Ico a b`.

You can specify a name `h` for the new hypothesis,
as `interval_cases n with h` or `interval_cases n using hl hu with h`.
-/
/--
`interval_cases n` searches for upper and lower bounds on a variable `n`,
