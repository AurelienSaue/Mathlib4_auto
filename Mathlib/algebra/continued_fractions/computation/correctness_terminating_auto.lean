/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.continued_fractions.computation.translations
import Mathlib.algebra.continued_fractions.terminated_stable
import Mathlib.algebra.continued_fractions.continuants_recurrence
import Mathlib.order.filter.at_top_bot
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Correctness of Terminating Continued Fraction Computations (`gcf.of`)

## Summary

Let us write `gcf` for `generalized_continued_fraction`. We show the correctness of the
algorithm computing continued fractions (`gcf.of`) in case of termination in the following sense:

At every step `n : ℕ`, we can obtain the value `v` by adding a specific residual term to the last
denominator of the fraction described by `(gcf.of v).convergents' n`. The residual term will be zero
exactly when the continued fraction terminated; otherwise, the residual term will be given by the
fractional part stored in `gcf.int_fract_pair.stream v n`.

For an example, refer to `gcf.comp_exact_value_correctness_of_stream_eq_some` and for more
information about the computation process, refer to `algebra.continued_fraction.computation.basic`.

## Main definitions

- `gcf.comp_exact_value` can be used to compute the exact value approximated by the continued
  fraction `gcf.of v` by adding a residual term as described in the summary.

## Main Theorems

- `gcf.comp_exact_value_correctness_of_stream_eq_some` shows that `gcf.comp_exact_value` indeed
  returns the value `v` when given the convergent and fractional part as described in the summary.
- `gcf.of_correctness_of_terminated_at` shows the equality `v = (gcf.of v).convergents n`
  if `gcf.of v` terminated at position `n`.
-/

namespace generalized_continued_fraction


/--
Given two continuants `pconts` and `conts` and a value `fr`, this function returns
- `conts.a / conts.b` if `fr = 0`
- `exact_conts.a / exact_conts.b` where `exact_conts = next_continuants 1 fr⁻¹ pconts conts` otherwise.

This function can be used to compute the exact value approxmated by a continued fraction `gcf.of v`
as described in lemma `comp_exact_value_correctness_of_stream_eq_some`.
-/
-- if the fractional part is zero, we exactly approximated the value by the last continuants

protected def comp_exact_value {K : Type u_1} [linear_ordered_field K] (pconts : pair K)
    (conts : pair K) (fr : K) : K :=
  ite (fr = 0) (pair.a conts / pair.b conts)
    (let exact_conts : pair K := next_continuants 1 (fr⁻¹) pconts conts;
    pair.a exact_conts / pair.b exact_conts)

-- otherwise, we have to include the fractional part in a final continuants step.

/-- Just a computational lemma we need for the next main proof. -/
protected theorem comp_exact_value_correctness_of_stream_eq_some_aux_comp {K : Type u_1}
    [linear_ordered_field K] [floor_ring K] {a : K} (b : K) (c : K)
    (fract_a_ne_zero : fract a ≠ 0) : (↑(floor a) * b + c) / fract a + b = (b * a + c) / fract a :=
  sorry

/--
Shows the correctness of `comp_exact_value` in case the continued fraction `gcf.of v` did not
terminate at position `n`. That is, we obtain the value `v` if we pass the two successive
(auxiliary) continuants at positions `n` and `n + 1` as well as the fractional part at
`int_fract_pair.stream n` to `comp_exact_value`.

The correctness might be seen more readily if one uses `convergents'` to evaluate the continued
fraction. Here is an example to illustrate the idea:

Let `(v : ℚ) := 3.4`. We have
- `gcf.int_fract_pair.stream v 0 = some ⟨3, 0.4⟩`, and
- `gcf.int_fract_pair.stream v 1 = some ⟨2, 0.5⟩`.
Now `(gcf.of v).convergents' 1 = 3 + 1/2`, and our fractional term at position `2` is `0.5`. We hence
have `v = 3 + 1/(2 + 0.5) = 3 + 1/2.5 = 3.4`. This computation corresponds exactly to the one using
the recurrence equation in `comp_exact_value`.
-/
theorem comp_exact_value_correctness_of_stream_eq_some {K : Type u_1} [linear_ordered_field K]
    {v : K} {n : ℕ} [floor_ring K] {ifp_n : int_fract_pair K} :
    int_fract_pair.stream v n = some ifp_n →
        v =
          generalized_continued_fraction.comp_exact_value
            (continuants_aux (generalized_continued_fraction.of v) n)
            (continuants_aux (generalized_continued_fraction.of v) (n + 1))
            (int_fract_pair.fr ifp_n) :=
  sorry

/-- The convergent of `gcf.of v` at step `n - 1` is exactly `v` if the `int_fract_pair.stream` of
the corresponding continued fraction terminated at step `n`. -/
theorem of_correctness_of_nth_stream_eq_none {K : Type u_1} [linear_ordered_field K] {v : K} {n : ℕ}
    [floor_ring K] (nth_stream_eq_none : int_fract_pair.stream v n = none) :
    v = convergents (generalized_continued_fraction.of v) (n - 1) :=
  sorry

/-- If `gcf.of v` terminated at step `n`, then the `n`th convergent is exactly `v`. -/
theorem of_correctness_of_terminated_at {K : Type u_1} [linear_ordered_field K] {v : K} {n : ℕ}
    [floor_ring K] (terminated_at_n : terminated_at (generalized_continued_fraction.of v) n) :
    v = convergents (generalized_continued_fraction.of v) n :=
  (fun (this : int_fract_pair.stream v (n + 1) = none) => of_correctness_of_nth_stream_eq_none this)
    (iff.elim_left of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none terminated_at_n)

/-- If `gcf.of v` terminates, then there is `n : ℕ` such that the `n`th convergent is exactly `v`. -/
theorem of_correctness_of_terminates {K : Type u_1} [linear_ordered_field K] {v : K} [floor_ring K]
    (terminates : terminates (generalized_continued_fraction.of v)) :
    ∃ (n : ℕ), v = convergents (generalized_continued_fraction.of v) n :=
  exists.elim terminates
    fun (n : ℕ) (terminated_at_n : seq.terminated_at (s (generalized_continued_fraction.of v)) n) =>
      exists.intro n (of_correctness_of_terminated_at terminated_at_n)

/-- If `gcf.of v` terminates, then its convergents will eventually always be `v`. -/
theorem of_correctness_at_top_of_terminates {K : Type u_1} [linear_ordered_field K] {v : K}
    [floor_ring K] (terminates : terminates (generalized_continued_fraction.of v)) :
    filter.eventually (fun (n : ℕ) => v = convergents (generalized_continued_fraction.of v) n)
        filter.at_top :=
  sorry

end Mathlib