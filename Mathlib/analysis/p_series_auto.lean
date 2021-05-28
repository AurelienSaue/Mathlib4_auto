/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.special_functions.pow
import PostPort

universes u_1 

namespace Mathlib

/-!
# Convergence of `p`-series

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test): `∑ k, f k`
converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. We prove this test in
`nnreal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to prove
`summable_one_div_rpow`. After this transformation, a `p`-series turns into a geometric series.

## TODO

It should be easy to generalize arguments to Schlömilch's generalization of the Cauchy condensation
test once we need it.

## Tags

p-series, Cauchy condensation test
-/

/-!
### Cauchy condensation test

In this section we prove the Cauchy condensation test: for `f : ℕ → ℝ≥0` or `f : ℕ → ℝ`,
`∑ k, f k` converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. Instead of giving a monolithic
proof, we split it into a series of lemmas with explicit estimates of partial sums of each series in
terms of the partial sums of the other series.
-/

namespace finset


theorem le_sum_condensed' {M : Type u_1} [ordered_add_comm_monoid M] {f : ℕ → M} (hf : ∀ {m n : ℕ}, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) : (finset.sum (Ico 1 (bit0 1 ^ n)) fun (k : ℕ) => f k) ≤ finset.sum (range n) fun (k : ℕ) => bit0 1 ^ k •ℕ f (bit0 1 ^ k) := sorry

theorem le_sum_condensed {M : Type u_1} [ordered_add_comm_monoid M] {f : ℕ → M} (hf : ∀ {m n : ℕ}, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) : (finset.sum (range (bit0 1 ^ n)) fun (k : ℕ) => f k) ≤
  f 0 + finset.sum (range n) fun (k : ℕ) => bit0 1 ^ k •ℕ f (bit0 1 ^ k) := sorry

theorem sum_condensed_le' {M : Type u_1} [ordered_add_comm_monoid M] {f : ℕ → M} (hf : ∀ {m n : ℕ}, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) : (finset.sum (range n) fun (k : ℕ) => bit0 1 ^ k •ℕ f (bit0 1 ^ (k + 1))) ≤
  finset.sum (Ico (bit0 1) (bit0 1 ^ n + 1)) fun (k : ℕ) => f k := sorry

theorem sum_condensed_le {M : Type u_1} [ordered_add_comm_monoid M] {f : ℕ → M} (hf : ∀ {m n : ℕ}, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) : (finset.sum (range (n + 1)) fun (k : ℕ) => bit0 1 ^ k •ℕ f (bit0 1 ^ k)) ≤
  f 1 + bit0 1 •ℕ finset.sum (Ico (bit0 1) (bit0 1 ^ n + 1)) fun (k : ℕ) => f k := sorry

end finset


namespace ennreal


theorem le_tsum_condensed {f : ℕ → ennreal} (hf : ∀ {m n : ℕ}, 0 < m → m ≤ n → f n ≤ f m) : (tsum fun (k : ℕ) => f k) ≤ f 0 + tsum fun (k : ℕ) => bit0 1 ^ k * f (bit0 1 ^ k) := sorry

theorem tsum_condensed_le {f : ℕ → ennreal} (hf : ∀ {m n : ℕ}, 1 < m → m ≤ n → f n ≤ f m) : (tsum fun (k : ℕ) => bit0 1 ^ k * f (bit0 1 ^ k)) ≤ f 1 + bit0 1 * tsum fun (k : ℕ) => f k := sorry

end ennreal


namespace nnreal


/-- Cauchy condensation test for a series of `nnreal` version. -/
theorem summable_condensed_iff {f : ℕ → nnreal} (hf : ∀ {m n : ℕ}, 0 < m → m ≤ n → f n ≤ f m) : (summable fun (k : ℕ) => bit0 1 ^ k * f (bit0 1 ^ k)) ↔ summable f := sorry

end nnreal


/-- Cauchy condensation test for series of nonnegative real numbers. -/
theorem summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ (n : ℕ), 0 ≤ f n) (h_mono : ∀ {m n : ℕ}, 0 < m → m ≤ n → f n ≤ f m) : (summable fun (k : ℕ) => bit0 1 ^ k * f (bit0 1 ^ k)) ↔ summable f := sorry

/-!
### Convergence of the `p`-series

In this section we prove that for a real number `p`, the series `∑' n : ℕ, 1 / (n ^ p)` converges if
and only if `1 < p`. There are many different proofs of this fact. The proof in this file uses the
Cauchy condensation test we formalized above. This test implies that `∑ n, 1 / (n ^ p)` converges if
and only if `∑ n, 2 ^ n / ((2 ^ n) ^ p)` converges, and the latter series is a geometric series with
common ratio `2 ^ {1 - p}`. -/

/-- Test for congergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp] theorem real.summable_nat_rpow_inv {p : ℝ} : (summable fun (n : ℕ) => ↑n ^ p⁻¹) ↔ 1 < p := sorry

/-- Test for congergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem real.summable_one_div_nat_rpow {p : ℝ} : (summable fun (n : ℕ) => 1 / ↑n ^ p) ↔ 1 < p := sorry

/-- Test for congergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp] theorem real.summable_nat_pow_inv {p : ℕ} : (summable fun (n : ℕ) => ↑n ^ p⁻¹) ↔ 1 < p := sorry

/-- Test for congergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem real.summable_one_div_nat_pow {p : ℕ} : (summable fun (n : ℕ) => 1 / ↑n ^ p) ↔ 1 < p := sorry

/-- Harmonic series is not unconditionally summable. -/
theorem real.not_summable_nat_cast_inv : ¬summable fun (n : ℕ) => ↑n⁻¹ := sorry

/-- Harmonic series is not unconditionally summable. -/
theorem real.not_summable_one_div_nat_cast : ¬summable fun (n : ℕ) => 1 / ↑n := sorry

/-- Harmonic series diverges. -/
theorem real.tendsto_sum_range_one_div_nat_succ_at_top : filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => 1 / (↑i + 1)) filter.at_top filter.at_top := sorry

@[simp] theorem nnreal.summable_one_rpow_inv {p : ℝ} : (summable fun (n : ℕ) => ↑n ^ p⁻¹) ↔ 1 < p := sorry

theorem nnreal.summable_one_div_rpow {p : ℝ} : (summable fun (n : ℕ) => 1 / ↑n ^ p) ↔ 1 < p := sorry

