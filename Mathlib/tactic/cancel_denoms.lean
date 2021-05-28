/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.rat.meta_defs
import Mathlib.tactic.norm_num
import Mathlib.data.tree
import Mathlib.meta.expr
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# A tactic for canceling numeric denominators

This file defines tactics that cancel numeric denominators from field expressions.

As an example, we want to transform a comparison `5*(a/3 + b/4) < c/3` into the equivalent
`5*(4*a + 3*b) < 4*c`.

## Implementation notes

The tooling here was originally written for `linarith`, not intended as an interactive tactic.
The interactive version has been split off because it is sometimes convenient to use on its own.
There are likely some rough edges to it.

Improving this tactic would be a good project for someone interested in learning tactic programming.
-/

namespace cancel_factors


/-! ### Lemmas used in the procedure -/

theorem mul_subst {α : Type u_1} [comm_ring α] {n1 : α} {n2 : α} {k : α} {e1 : α} {e2 : α} {t1 : α} {t2 : α} (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2) (h3 : n1 * n2 = k) : k * (e1 * e2) = t1 * t2 := sorry

theorem div_subst {α : Type u_1} [field α] {n1 : α} {n2 : α} {k : α} {e1 : α} {e2 : α} {t1 : α} (h1 : n1 * e1 = t1) (h2 : n2 / e2 = 1) (h3 : n1 * n2 = k) : k * (e1 / e2) = t1 := sorry

theorem cancel_factors_eq_div {α : Type u_1} [field α] {n : α} {e : α} {e' : α} (h : n * e = e') (h2 : n ≠ 0) : e = e' / n :=
  eq_div_of_mul_eq h2 (eq.mp (Eq._oldrec (Eq.refl (n * e = e')) (mul_comm n e)) h)

theorem add_subst {α : Type u_1} [ring α] {n : α} {e1 : α} {e2 : α} {t1 : α} {t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) : n * (e1 + e2) = t1 + t2 := sorry

theorem sub_subst {α : Type u_1} [ring α] {n : α} {e1 : α} {e2 : α} {t1 : α} {t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) : n * (e1 - e2) = t1 - t2 := sorry

theorem neg_subst {α : Type u_1} [ring α] {n : α} {e : α} {t : α} (h1 : n * e = t) : n * -e = -t := sorry

theorem cancel_factors_lt {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {ad : α} {bd : α} {a' : α} {b' : α} {gcd : α} (ha : ad * a = a') (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) : a < b = (1 / gcd * (bd * a') < 1 / gcd * (ad * b')) := sorry

theorem cancel_factors_le {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {ad : α} {bd : α} {a' : α} {b' : α} {gcd : α} (ha : ad * a = a') (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) : a ≤ b = (1 / gcd * (bd * a') ≤ 1 / gcd * (ad * b')) := sorry

theorem cancel_factors_eq {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {ad : α} {bd : α} {a' : α} {b' : α} {gcd : α} (ha : ad * a = a') (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) : a = b = (1 / gcd * (bd * a') = 1 / gcd * (ad * b')) := sorry

/-! ### Computing cancelation factors -/

/--
`find_cancel_factor e` produces a natural number `n`, such that multiplying `e` by `n` will
be able to cancel all the numeric denominators in `e`. The returned `tree` describes how to
distribute the value `n` over products inside `e`.
-/
/--
`mk_prod_prf n tr e` produces a proof of `n*e = e'`, where numeric denominators have been
canceled in `e'`, distributing `n` proportionally according to `tr`.
-/
/--
Given `e`, a term with rational division, produces a natural number `n` and a proof of `n*e = e'`,
where `e'` has no division. Assumes "well-behaved" division.
-/
/--
Given `e`, a term with rational divison, produces a natural number `n` and a proof of `e = e' / n`,
where `e'` has no divison. Assumes "well-behaved" division.
-/
/--
`find_comp_lemma e` arranges `e` in the form `lhs R rhs`, where `R ∈ {<, ≤, =}`, and returns
`lhs`, `rhs`, and the `cancel_factors` lemma corresponding to `R`.
-/
/--
`cancel_denominators_in_type h` assumes that `h` is of the form `lhs R rhs`,
where `R ∈ {<, ≤, =, ≥, >}`.
It produces an expression `h'` of the form `lhs' R rhs'` and a proof that `h = h'`.
Numeric denominators have been canceled in `lhs'` and `rhs'`.
-/
end cancel_factors


/-! ### Interactive version -/

/--
`cancel_denoms` attempts to remove numerals from the denominators of fractions.
It works on propositions that are field-valued inequalities.

```lean
variables {α : Type} [linear_ordered_field α] (a b c : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c :=
begin
  cancel_denoms at h,
  exact h
end

example (h : a > 0) : a / 5 > 0 :=
begin
  cancel_denoms,
  exact h
end
```
-/
