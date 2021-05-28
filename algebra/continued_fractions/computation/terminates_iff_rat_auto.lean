/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.continued_fractions.computation.approximations
import Mathlib.algebra.continued_fractions.computation.correctness_terminating
import Mathlib.data.rat.default
import PostPort

universes u_1 

namespace Mathlib

/-!
# Termination of Continued Fraction Computations (`gcf.of`)

## Summary
We show that the continued fraction for a value `v`, as defined in
`algebra.continued_fractions.computation.basic`, terminates if and only if `v` corresponds to a
rational number, that is `↑v = q` for some `q : ℚ`.

## Main Theorems

- `gcf.coe_of_rat` shows that `gcf.of v = gcf.of q` for `v : α` given that `↑v = q` and `q : ℚ`.
- `gcf.terminates_iff_rat` shows that `gcf.of v` terminates if and only if `↑v = q` for some
  `q : ℚ`.

## Tags

rational, continued fraction, termination
-/

namespace generalized_continued_fraction


/-
We will have to constantly coerce along our structures in the following proofs using their provided
map functions.
-/

/-!
We want to show that the computation of a continued fraction `gcf.of v` terminates if and only if
`v ∈ ℚ`. In the next section, we show the implication from left to right.

We first show that every finite convergent corresponds to a rational number `q` and then use the
finite correctness proof (`of_correctness_of_terminates`) of `gcf.of` to show that `v = ↑q`.
-/

theorem exists_gcf_pair_rat_eq_of_nth_conts_aux {K : Type u_1} [linear_ordered_field K] [floor_ring K] (v : K) (n : ℕ) : ∃ (conts : pair ℚ), continuants_aux (generalized_continued_fraction.of v) n = pair.map coe conts := sorry

theorem exists_gcf_pair_rat_eq_nth_conts {K : Type u_1} [linear_ordered_field K] [floor_ring K] (v : K) (n : ℕ) : ∃ (conts : pair ℚ), continuants (generalized_continued_fraction.of v) n = pair.map coe conts := sorry

theorem exists_rat_eq_nth_numerator {K : Type u_1} [linear_ordered_field K] [floor_ring K] (v : K) (n : ℕ) : ∃ (q : ℚ), numerators (generalized_continued_fraction.of v) n = ↑q := sorry

theorem exists_rat_eq_nth_denominator {K : Type u_1} [linear_ordered_field K] [floor_ring K] (v : K) (n : ℕ) : ∃ (q : ℚ), denominators (generalized_continued_fraction.of v) n = ↑q := sorry

/-- Every finite convergent corresponds to a rational number. -/
theorem exists_rat_eq_nth_convergent {K : Type u_1} [linear_ordered_field K] [floor_ring K] (v : K) (n : ℕ) : ∃ (q : ℚ), convergents (generalized_continued_fraction.of v) n = ↑q := sorry

/-- Every terminating continued fraction corresponds to a rational number. -/
theorem exists_rat_eq_of_terminates {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} (terminates : terminates (generalized_continued_fraction.of v)) : ∃ (q : ℚ), v = ↑q := sorry

/-!
Before we can show that the continued fraction of a rational number terminates, we have to prove
some technical translation lemmas. More precisely, in this section, we show that, given a rational
number `q : ℚ` and value `v : K` with `v = ↑q`, the continued fraction of `q` and `v` coincide.
In particular, we show that `(↑(gcf.of q : gcf ℚ) : gcf K) = gcf.of v` in `gcf.coe_of_rat`.

To do this, we proceed bottom-up, showing the correspondence between the basic functions involved in
the computation first and then lift the results step-by-step.
-/

/- The lifting works for arbitrary linear ordered, archimedean fields with a floor function. -/

/-! First, we show the correspondence for the very basic functions in `gcf.int_fract_pair`. -/

namespace int_fract_pair


theorem coe_of_rat_eq {K : Type u_1} [linear_ordered_field K] [floor_ring K] [archimedean K] {v : K} {q : ℚ} (v_eq_q : v = ↑q) : mapFr coe (int_fract_pair.of q) = int_fract_pair.of v := sorry

theorem coe_stream_nth_rat_eq {K : Type u_1} [linear_ordered_field K] [floor_ring K] [archimedean K] {v : K} {q : ℚ} (v_eq_q : v = ↑q) (n : ℕ) : option.map (mapFr coe) (int_fract_pair.stream q n) = int_fract_pair.stream v n := sorry

theorem coe_stream_rat_eq {K : Type u_1} [linear_ordered_field K] [floor_ring K] [archimedean K] {v : K} {q : ℚ} (v_eq_q : v = ↑q) : stream.map (option.map (mapFr coe)) (int_fract_pair.stream q) = int_fract_pair.stream v :=
  funext fun (n : ℕ) => coe_stream_nth_rat_eq v_eq_q n

end int_fract_pair


/-! Now we lift the coercion results to the continued fraction computation. -/

theorem coe_of_h_rat_eq {K : Type u_1} [linear_ordered_field K] [floor_ring K] [archimedean K] {v : K} {q : ℚ} (v_eq_q : v = ↑q) : ↑(h (generalized_continued_fraction.of q)) = h (generalized_continued_fraction.of v) := sorry

theorem coe_of_s_nth_rat_eq {K : Type u_1} [linear_ordered_field K] [floor_ring K] [archimedean K] {v : K} {q : ℚ} (v_eq_q : v = ↑q) (n : ℕ) : option.map (pair.map coe) (seq.nth (s (generalized_continued_fraction.of q)) n) =
  seq.nth (s (generalized_continued_fraction.of v)) n := sorry

theorem coe_of_s_rat_eq {K : Type u_1} [linear_ordered_field K] [floor_ring K] [archimedean K] {v : K} {q : ℚ} (v_eq_q : v = ↑q) : seq.map (pair.map coe) (s (generalized_continued_fraction.of q)) = s (generalized_continued_fraction.of v) := sorry

/-- Given `(v : K), (q : ℚ), and v = q`, we have that `gcf.of q = gcf.of v` -/
theorem coe_of_rat_eq {K : Type u_1} [linear_ordered_field K] [floor_ring K] [archimedean K] {v : K} {q : ℚ} (v_eq_q : v = ↑q) : mk (↑(h (generalized_continued_fraction.of q))) (seq.map (pair.map coe) (s (generalized_continued_fraction.of q))) =
  generalized_continued_fraction.of v := sorry

theorem of_terminates_iff_of_rat_terminates {K : Type u_1} [linear_ordered_field K] [floor_ring K] [archimedean K] {v : K} {q : ℚ} (v_eq_q : v = ↑q) : terminates (generalized_continued_fraction.of v) ↔ terminates (generalized_continued_fraction.of q) := sorry

/-!
Finally, we show that the continued fraction of a rational number terminates.

The crucial insight is that, given any `q : ℚ` with `0 < q < 1`, the numerator of `fract q` is
smaller than the numerator of `q`. As the continued fraction computation recursively operates on
the fractional part of a value `v` and `0 ≤ fract v < 1`, we infer that the numerator of the
fractional part in the computation decreases by at least one in each step. As `0 ≤ fract v`,
this process must stop after finite number of steps, and the computation hence terminates.
-/

namespace int_fract_pair


/--
Shows that for any `q : ℚ` with `0 < q < 1`, the numerator of the fractional part of
`int_fract_pair.of q⁻¹` is smaller than the numerator of `q`.
-/
theorem of_inv_fr_num_lt_num_of_pos {q : ℚ} (q_pos : 0 < q) : rat.num (fr (int_fract_pair.of (q⁻¹))) < rat.num q :=
  rat.fract_inv_num_lt_num_of_pos q_pos

/-- Shows that the sequence of numerators of the fractional parts of the stream is strictly
monotonically decreasing. -/
theorem stream_succ_nth_fr_num_lt_nth_fr_num_rat {q : ℚ} {n : ℕ} {ifp_n : int_fract_pair ℚ} {ifp_succ_n : int_fract_pair ℚ} (stream_nth_eq : int_fract_pair.stream q n = some ifp_n) (stream_succ_nth_eq : int_fract_pair.stream q (n + 1) = some ifp_succ_n) : rat.num (fr ifp_succ_n) < rat.num (fr ifp_n) := sorry

theorem stream_nth_fr_num_le_fr_num_sub_n_rat {q : ℚ} {n : ℕ} {ifp_n : int_fract_pair ℚ} : int_fract_pair.stream q n = some ifp_n → rat.num (fr ifp_n) ≤ rat.num (fr (int_fract_pair.of q)) - ↑n := sorry

theorem exists_nth_stream_eq_none_of_rat (q : ℚ) : ∃ (n : ℕ), int_fract_pair.stream q n = none := sorry

end int_fract_pair


/-- The continued fraction of a rational number terminates. -/
theorem terminates_of_rat (q : ℚ) : terminates (generalized_continued_fraction.of q) := sorry

/-- The continued fraction `gcf.of v` terminates if and only if `v ∈ ℚ`. -/
theorem terminates_iff_rat {K : Type u_1} [linear_ordered_field K] [floor_ring K] [archimedean K] (v : K) : terminates (generalized_continued_fraction.of v) ↔ ∃ (q : ℚ), v = ↑q := sorry

