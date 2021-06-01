/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.default
import Mathlib.field_theory.finite.basic
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# The Chevalley–Warning theorem

This file contains a proof of the Chevalley–Warning theorem.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Main results

1. Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
   such that the total degree of `f` is less than `(q-1)` times the cardinality of `σ`.
   Then the evaluation of `f` on all points of `σ → K` (aka `K^σ`) sums to `0`.
   (`sum_mv_polynomial_eq_zero`)
2. The Chevalley–Warning theorem (`char_dvd_card_solutions`).
   Let `f i` be a finite family of multivariate polynomials
   in finitely many variables (`X s`, `s : σ`) such that
   the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
   Then the number of common solutions of the `f i`
   is divisible by the characteristic of `K`.

## Notation

- `K` is a finite field
- `q` is notation for the cardinality of `K`
- `σ` is the indexing type for the variables of a multivariate polynomial ring over `K`

-/

theorem mv_polynomial.sum_mv_polynomial_eq_zero {K : Type u_1} {σ : Type u_2} [fintype K] [field K]
    [fintype σ] [DecidableEq σ] (f : mv_polynomial σ K)
    (h : mv_polynomial.total_degree f < (fintype.card K - 1) * fintype.card σ) :
    (finset.sum finset.univ fun (x : σ → K) => coe_fn (mv_polynomial.eval x) f) = 0 :=
  sorry

/-- The Chevalley–Warning theorem.
Let `(f i)` be a finite family of multivariate polynomials
in finitely many variables (`X s`, `s : σ`) over a finite field of characteristic `p`.
Assume that the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
Then the number of common solutions of the `f i` is divisible by `p`. -/
theorem char_dvd_card_solutions_family {K : Type u_1} {σ : Type u_2} [fintype K] [field K]
    [fintype σ] [DecidableEq K] [DecidableEq σ] (p : ℕ) [char_p K p] {ι : Type u_3} {s : finset ι}
    {f : ι → mv_polynomial σ K}
    (h : (finset.sum s fun (i : ι) => mv_polynomial.total_degree (f i)) < fintype.card σ) :
    p ∣
        fintype.card
          (Subtype fun (x : σ → K) => ∀ (i : ι), i ∈ s → coe_fn (mv_polynomial.eval x) (f i) = 0) :=
  sorry

/-- The Chevalley–Warning theorem.
Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
over a finite field of characteristic `p`.
Assume that the total degree of `f` is less than the cardinality of `σ`.
Then the number of solutions of `f` is divisible by `p`.
See `char_dvd_card_solutions_family` for a version that takes a family of polynomials `f i`. -/
theorem char_dvd_card_solutions {K : Type u_1} {σ : Type u_2} [fintype K] [field K] [fintype σ]
    [DecidableEq K] [DecidableEq σ] (p : ℕ) [char_p K p] {f : mv_polynomial σ K}
    (h : mv_polynomial.total_degree f < fintype.card σ) :
    p ∣ fintype.card (Subtype fun (x : σ → K) => coe_fn (mv_polynomial.eval x) f = 0) :=
  sorry

end Mathlib