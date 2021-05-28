/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.continued_fractions.computation.translations
import Mathlib.algebra.continued_fractions.continuants_recurrence
import Mathlib.algebra.continued_fractions.terminated_stable
import Mathlib.data.nat.fib
import PostPort

universes u_1 

namespace Mathlib

/-!
# Approximations for Continued Fraction Computations (`gcf.of`)

## Summary

Let us write `gcf` for `generalized_continued_fraction`. This file contains useful approximations
for the values involved in the continued fractions computation `gcf.of`.

## Main Theorems

- `gcf.of_part_num_eq_one`: shows that all partial numerators `aᵢ` are equal to one.
- `gcf.exists_int_eq_of_part_denom`: shows that all partial denominators `bᵢ` correspond to an integer.
- `gcf.one_le_of_nth_part_denom`: shows that `1 ≤ bᵢ`.
- `gcf.succ_nth_fib_le_of_nth_denom`: shows that the `n`th denominator `Bₙ` is greater than or equal to
  the `n + 1`th fibonacci number `nat.fib (n + 1)`.
- `gcf.le_of_succ_nth_denom`: shows that `Bₙ₊₁ ≥ bₙ * Bₙ`, where `bₙ` is the `n`th partial denominator
  of the continued fraction.

## References

- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]
-/

namespace generalized_continued_fraction


/-
We begin with some lemmas about the stream of `int_fract_pair`s, which presumably are not
of great interest for the end user.
-/

namespace int_fract_pair


/-- Shows that the fractional parts of the stream are in `[0,1)`. -/
theorem nth_stream_fr_nonneg_lt_one {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] {ifp_n : int_fract_pair K} (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) : 0 ≤ fr ifp_n ∧ fr ifp_n < 1 := sorry

/-- Shows that the fractional parts of the stream are nonnegative. -/
theorem nth_stream_fr_nonneg {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] {ifp_n : int_fract_pair K} (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) : 0 ≤ fr ifp_n :=
  and.left (nth_stream_fr_nonneg_lt_one nth_stream_eq)

/-- Shows that the fractional parts of the stream smaller than one. -/
theorem nth_stream_fr_lt_one {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] {ifp_n : int_fract_pair K} (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) : fr ifp_n < 1 :=
  and.right (nth_stream_fr_nonneg_lt_one nth_stream_eq)

/-- Shows that the integer parts of the stream are at least one. -/
theorem one_le_succ_nth_stream_b {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] {ifp_succ_n : int_fract_pair K} (succ_nth_stream_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n) : 1 ≤ b ifp_succ_n := sorry

/--
Shows that the `n + 1`th integer part `bₙ₊₁` of the stream is smaller or equal than the inverse of
the `n`th fractional part `frₙ` of the stream.
This result is straight-forward as `bₙ₊₁` is defined as the floor of `1 / frₙ`
-/
theorem succ_nth_stream_b_le_nth_stream_fr_inv {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] {ifp_n : int_fract_pair K} {ifp_succ_n : int_fract_pair K} (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) (succ_nth_stream_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n) : ↑(b ifp_succ_n) ≤ (fr ifp_n⁻¹) := sorry

end int_fract_pair


/-
Next we translate above results about the stream of `int_fract_pair`s to the computed continued
fraction `gcf.of`.
-/

/-- Shows that the integer parts of the continued fraction are at least one. -/
theorem of_one_le_nth_part_denom {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] {b : K} (nth_part_denom_eq : seq.nth (partial_denominators (generalized_continued_fraction.of v)) n = some b) : 1 ≤ b := sorry

/--
Shows that the partial numerators `aᵢ` of the continued fraction are equal to one and the partial
denominators `bᵢ` correspond to integers.
-/
theorem of_part_num_eq_one_and_exists_int_part_denom_eq {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] {gp : pair K} (nth_s_eq : seq.nth (s (generalized_continued_fraction.of v)) n = some gp) : pair.a gp = 1 ∧ ∃ (z : ℤ), pair.b gp = ↑z := sorry

/-- Shows that the partial numerators `aᵢ` are equal to one. -/
theorem of_part_num_eq_one {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] {a : K} (nth_part_num_eq : seq.nth (partial_numerators (generalized_continued_fraction.of v)) n = some a) : a = 1 := sorry

/-- Shows that the partial denominators `bᵢ` correspond to an integer. -/
theorem exists_int_eq_of_part_denom {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] {b : K} (nth_part_denom_eq : seq.nth (partial_denominators (generalized_continued_fraction.of v)) n = some b) : ∃ (z : ℤ), b = ↑z := sorry

/-
One of our next goals is to show that `Bₙ₊₁ ≥ bₙ * Bₙ`. For this, we first show that the partial
denominators `Bₙ` are bounded from below by the fibonacci sequence `nat.fib`. This then implies that
`0 ≤ Bₙ` and hence `Bₙ₊₂ = bₙ₊₁ * Bₙ₊₁ + Bₙ ≥ bₙ₊₁ * Bₙ₊₁ + 0 = bₙ₊₁ * Bₙ₊₁`.
-/

-- open `nat` as we will make use of fibonacci numbers.

theorem fib_le_of_continuants_aux_b {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] : n ≤ 1 ∨ ¬terminated_at (generalized_continued_fraction.of v) (n - bit0 1) →
  ↑(nat.fib n) ≤ pair.b (continuants_aux (generalized_continued_fraction.of v) n) := sorry

/-- Shows that the `n`th denominator is greater than or equal to the `n + 1`th fibonacci number,
that is `nat.fib (n + 1) ≤ Bₙ`. -/
theorem succ_nth_fib_le_of_nth_denom {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] (hyp : n = 0 ∨ ¬terminated_at (generalized_continued_fraction.of v) (n - 1)) : ↑(nat.fib (n + 1)) ≤ denominators (generalized_continued_fraction.of v) n := sorry

/- As a simple consequence, we can now derive that all denominators are nonnegative. -/

theorem zero_le_of_continuants_aux_b {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] : 0 ≤ pair.b (continuants_aux (generalized_continued_fraction.of v) n) := sorry

/-- Shows that all denominators are nonnegative. -/
theorem zero_le_of_denom {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] : 0 ≤ denominators (generalized_continued_fraction.of v) n := sorry

theorem le_of_succ_succ_nth_continuants_aux_b {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] {b : K} (nth_part_denom_eq : seq.nth (partial_denominators (generalized_continued_fraction.of v)) n = some b) : b * pair.b (continuants_aux (generalized_continued_fraction.of v) (n + 1)) ≤
  pair.b (continuants_aux (generalized_continued_fraction.of v) (n + bit0 1)) := sorry

/-- Shows that `Bₙ₊₁ ≥ bₙ * Bₙ`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction. -/
theorem le_of_succ_nth_denom {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] {b : K} (nth_part_denom_eq : seq.nth (partial_denominators (generalized_continued_fraction.of v)) n = some b) : b * denominators (generalized_continued_fraction.of v) n ≤ denominators (generalized_continued_fraction.of v) (n + 1) := sorry

/-- Shows that the sequence of denominators is monotonically increasing, that is `Bₙ ≤ Bₙ₊₁`. -/
theorem of_denom_mono {K : Type u_1} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K] : denominators (generalized_continued_fraction.of v) n ≤ denominators (generalized_continued_fraction.of v) (n + 1) := sorry

