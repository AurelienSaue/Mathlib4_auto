/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.continued_fractions.computation.basic
import Mathlib.algebra.continued_fractions.translations
import PostPort

universes u_1 

namespace Mathlib

/-!
# Basic Translation Lemmas Between Structures Defined for Computing Continued Fractions

## Summary

This is a collection of simple lemmas between the different structures used for the computation
of continued fractions defined in `algebra.continued_fractions.computation.basic`. The file consists
of three sections:
1. Recurrences and inversion lemmas for `int_fract_pair.stream`: these lemmas give us inversion
   rules and recurrences for the computation of the stream of integer and fractional parts of a value.
2. Translation lemmas for the head term: these lemmas show us that the head term of the computed
   continued fraction of a value `v` is `⌊v⌋` and how this head term is moved along the structures
   used in the computation process.
3. Translation lemmas for the sequence: these lemmas show how the sequences of the involved
   structures (`int_fract_pair.stream`, `int_fract_pair.seq1`, and `generalized_continued_fraction.of`)
   are connected, i.e. how the values are moved along the structures and the termination of one
   sequence implies the termination of another sequence.

## Main Theorems

- `succ_nth_stream_eq_some_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of non-termination.
- `succ_nth_stream_eq_none_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of termination.
- `nth_of_eq_some_of_succ_nth_int_fract_pair_stream` and
  `nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero` show how the entries of the sequence
  of the computed continued fraction can be obtained from the stream of integer and fractional parts.
-/

namespace generalized_continued_fraction


/- Fix a discrete linear ordered floor field and a value `v`. -/

namespace int_fract_pair


/-!
### Recurrences and Inversion Lemmas for `int_fract_pair.stream`

Here we state some lemmas that give us inversion rules and recurrences for the computation of the
stream of integer and fractional parts of a value.
-/

theorem stream_eq_none_of_fr_eq_zero {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} {n : ℕ} {ifp_n : int_fract_pair K} (stream_nth_eq : int_fract_pair.stream v n = some ifp_n) (nth_fr_eq_zero : fr ifp_n = 0) : int_fract_pair.stream v (n + 1) = none := sorry

/--
Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of termination.
-/
theorem succ_nth_stream_eq_none_iff {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} {n : ℕ} : int_fract_pair.stream v (n + 1) = none ↔
  int_fract_pair.stream v n = none ∨ ∃ (ifp : int_fract_pair K), int_fract_pair.stream v n = some ifp ∧ fr ifp = 0 := sorry

/--
Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of non-termination.
-/
theorem succ_nth_stream_eq_some_iff {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} {n : ℕ} {ifp_succ_n : int_fract_pair K} : int_fract_pair.stream v (n + 1) = some ifp_succ_n ↔
  ∃ (ifp_n : int_fract_pair K),
    int_fract_pair.stream v n = some ifp_n ∧ fr ifp_n ≠ 0 ∧ int_fract_pair.of (fr ifp_n⁻¹) = ifp_succ_n := sorry

theorem exists_succ_nth_stream_of_fr_zero {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} {n : ℕ} {ifp_succ_n : int_fract_pair K} (stream_succ_nth_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n) (succ_nth_fr_eq_zero : fr ifp_succ_n = 0) : ∃ (ifp_n : int_fract_pair K), int_fract_pair.stream v n = some ifp_n ∧ fr ifp_n⁻¹ = ↑(floor (fr ifp_n⁻¹)) := sorry

end int_fract_pair


/-!
### Translation of the Head Term

Here we state some lemmas that show us that the head term of the computed continued fraction of a
value `v` is `⌊v⌋` and how this head term is moved along the structures used in the computation
process.
-/

/-- The head term of the sequence with head of `v` is just the integer part of `v`. -/
@[simp] theorem int_fract_pair.seq1_fst_eq_of {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} : prod.fst (int_fract_pair.seq1 v) = int_fract_pair.of v :=
  rfl

theorem of_h_eq_int_fract_pair_seq1_fst_b {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} : h (generalized_continued_fraction.of v) = ↑(int_fract_pair.b (prod.fst (int_fract_pair.seq1 v))) := sorry

/-- The head term of the gcf of `v` is `⌊v⌋`. -/
@[simp] theorem of_h_eq_floor {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} : h (generalized_continued_fraction.of v) = ↑(floor v) := sorry

/-!
### Translation of the Sequences

Here we state some lemmas that show how the sequences of the involved structures
(`int_fract_pair.stream`, `int_fract_pair.seq1`, and `generalized_continued_fraction.of`) are
connected, i.e. how the values are moved along the structures and how the termination of one sequence
implies the termination of another sequence.
-/

theorem int_fract_pair.nth_seq1_eq_succ_nth_stream {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} {n : ℕ} : seq.nth (prod.snd (int_fract_pair.seq1 v)) n = int_fract_pair.stream v (n + 1) :=
  rfl

/-!
#### Translation of the Termination of the Sequences

Let's first show how the termination of one sequence implies the termination of another sequence.
-/

theorem of_terminated_at_iff_int_fract_pair_seq1_terminated_at {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} {n : ℕ} : terminated_at (generalized_continued_fraction.of v) n ↔ seq.terminated_at (prod.snd (int_fract_pair.seq1 v)) n := sorry

theorem of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} {n : ℕ} : terminated_at (generalized_continued_fraction.of v) n ↔ int_fract_pair.stream v (n + 1) = none := sorry

/-!
#### Translation of the Values of the Sequence

Now let's show how the values of the sequences correspond to one another.
-/

theorem int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} {n : ℕ} {gp_n : pair K} (s_nth_eq : seq.nth (s (generalized_continued_fraction.of v)) n = some gp_n) : ∃ (ifp : int_fract_pair K), int_fract_pair.stream v (n + 1) = some ifp ∧ ↑(int_fract_pair.b ifp) = pair.b gp_n := sorry

/--
Shows how the entries of the sequence of the computed continued fraction can be obtained by the
integer parts of the stream of integer and fractional parts.
-/
theorem nth_of_eq_some_of_succ_nth_int_fract_pair_stream {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} {n : ℕ} {ifp_succ_n : int_fract_pair K} (stream_succ_nth_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n) : seq.nth (s (generalized_continued_fraction.of v)) n = some (pair.mk 1 ↑(int_fract_pair.b ifp_succ_n)) := sorry

/--
Shows how the entries of the sequence of the computed continued fraction can be obtained by the
fractional parts of the stream of integer and fractional parts.
-/
theorem nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero {K : Type u_1} [linear_ordered_field K] [floor_ring K] {v : K} {n : ℕ} {ifp_n : int_fract_pair K} (stream_nth_eq : int_fract_pair.stream v n = some ifp_n) (nth_fr_ne_zero : int_fract_pair.fr ifp_n ≠ 0) : seq.nth (s (generalized_continued_fraction.of v)) n =
  some (pair.mk 1 ↑(int_fract_pair.b (int_fract_pair.of (int_fract_pair.fr ifp_n⁻¹)))) := sorry

