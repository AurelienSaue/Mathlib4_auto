/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.continued_fractions.continuants_recurrence
import Mathlib.algebra.continued_fractions.terminated_stable
import Mathlib.tactic.linarith.default
import Mathlib.tactic.field_simp
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Equivalence of Recursive and Direct Computations of `gcf` Convergents

## Summary

We show the equivalence of two computations of convergents (recurrence relation (`convergents`) vs.
direct evaluation (`convergents'`)) for `gcf`s on linear ordered fields. We follow the proof from
[hardy2008introduction], Chapter 10. Here's a sketch:

Let `c` be a continued fraction `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`, visually:
                                a₀
                h + ---------------------------
                                  a₁
                      b₀ + --------------------
                                    a₂
                            b₁ + --------------
                                        a₃
                                  b₂ + --------
                                      b₃ + ...

One can compute the convergents of `c` in two ways:
1. Directly evaluating the fraction described by `c` up to a given `n` (`convergents'`)
2. Using the recurrence (`convergents`):
  - `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
  - `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

To show the equivalence of the computations in the main theorem of this file
`convergents_eq_convergents'`, we proceed by induction. The case `n = 0` is trivial.

For `n + 1`, we first "squash" the `n + 1`th position of `c` into the `n`th position to obtain
another continued fraction
  `c' := [h; (a₀, b₀),..., (aₙ-₁, bₙ-₁), (aₙ, bₙ + aₙ₊₁ / bₙ₊₁), (aₙ₊₁, bₙ₊₁),...]`.
This squashing process is formalised in section `squash`. Note that directly evaluating `c` up to
position `n + 1` is equal to evaluating `c'` up to `n`. This is shown in lemma
`succ_nth_convergent'_eq_squash_gcf_nth_convergent'`.

By the inductive hypothesis, the two computations for the `n`th convergent of `c` coincide.
So all that is left to show is that the recurrence relation for `c` at `n + 1` and and `c'` at
`n` coincide. This can be shown by another induction.
The corresponding lemma in this file is `succ_nth_convergent_eq_squash_gcf_nth_convergent`.

## Main Theorems

- `generalized_continued_fraction.convergents_eq_convergents'` shows the equivalence under a strict
positivity restriction on the sequence.
- `continued_fractions.convergents_eq_convergents'` shows the equivalence for (regular) continued
fractions.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction
- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

## Tags

fractions, recurrence, equivalence
-/

namespace generalized_continued_fraction


/-!
We will show the equivalence of the computations by induction. To make the induction work, we need
to be able to *squash* the nth and (n + 1)th value of a sequence. This squashing itself and the
lemmas about it are not very interesting. As a reader, you hence might want to skip this section.
-/

/--
Given a sequence of gcf.pairs `s = [(a₀, bₒ), (a₁, b₁), ...]`, `squash_seq s n`
combines `⟨aₙ, bₙ⟩` and `⟨aₙ₊₁, bₙ₊₁⟩` at position `n` to `⟨aₙ, bₙ + aₙ₊₁ / bₙ₊₁⟩`. For example,
`squash_seq s 0 = [(a₀, bₒ + a₁ / b₁), (a₁, b₁),...]`.
If `s.terminated_at (n + 1)`, then `squash_seq s n = s`.
-/
def squash_seq {K : Type u_1} [division_ring K] (s : seq (pair K)) (n : ℕ) : seq (pair K) :=
  sorry

/-! We now prove some simple lemmas about the squashed sequence -/

/-- If the sequence already terminated at position `n + 1`, nothing gets squashed. -/
theorem squash_seq_eq_self_of_terminated {K : Type u_1} {n : ℕ} {s : seq (pair K)} [division_ring K] (terminated_at_succ_n : seq.terminated_at s (n + 1)) : squash_seq s n = s := sorry

/-- If the sequence has not terminated before position `n + 1`, the value at `n + 1` gets
squashed into position `n`. -/
theorem squash_seq_nth_of_not_terminated {K : Type u_1} {n : ℕ} {s : seq (pair K)} [division_ring K] {gp_n : pair K} {gp_succ_n : pair K} (s_nth_eq : seq.nth s n = some gp_n) (s_succ_nth_eq : seq.nth s (n + 1) = some gp_succ_n) : seq.nth (squash_seq s n) n = some (pair.mk (pair.a gp_n) (pair.b gp_n + pair.a gp_succ_n / pair.b gp_succ_n)) := sorry

/-- The values before the squashed position stay the same. -/
theorem squash_seq_nth_of_lt {K : Type u_1} {n : ℕ} {s : seq (pair K)} [division_ring K] {m : ℕ} (m_lt_n : m < n) : seq.nth (squash_seq s n) m = seq.nth s m := sorry

/-- Squashing at position `n + 1` and taking the tail is the same as squashing the tail of the
sequence at position `n`. -/
theorem squash_seq_succ_n_tail_eq_squash_seq_tail_n {K : Type u_1} {n : ℕ} {s : seq (pair K)} [division_ring K] : seq.tail (squash_seq s (n + 1)) = squash_seq (seq.tail s) n := sorry

/-- The auxiliary function `convergents'_aux` returns the same value for a sequence and the
corresponding squashed sequence at the squashed position. -/
theorem succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squash_seq {K : Type u_1} {n : ℕ} {s : seq (pair K)} [division_ring K] : convergents'_aux s (n + bit0 1) = convergents'_aux (squash_seq s n) (n + 1) := sorry

/-! Let us now lift the squashing operation to gcfs. -/

/--
Given a gcf `g = [h; (a₀, bₒ), (a₁, b₁), ...]`, we have
- `squash_nth.gcf g 0 = [h + a₀ / b₀); (a₀, bₒ), ...]`,
- `squash_nth.gcf g (n + 1) = ⟨g.h, squash_seq g.s n⟩`
-/
def squash_gcf {K : Type u_1} [division_ring K] (g : generalized_continued_fraction K) : ℕ → generalized_continued_fraction K :=
  sorry

/-! Again, we derive some simple lemmas that are not really of interest. This time for the
squashed gcf. -/

/-- If the gcf already terminated at position `n`, nothing gets squashed. -/
theorem squash_gcf_eq_self_of_terminated {K : Type u_1} {n : ℕ} {g : generalized_continued_fraction K} [division_ring K] (terminated_at_n : terminated_at g n) : squash_gcf g n = g := sorry

/-- The values before the squashed position stay the same. -/
theorem squash_gcf_nth_of_lt {K : Type u_1} {n : ℕ} {g : generalized_continued_fraction K} [division_ring K] {m : ℕ} (m_lt_n : m < n) : seq.nth (s (squash_gcf g (n + 1))) m = seq.nth (s g) m := sorry

/-- `convergents'` returns the same value for a gcf and the corresponding squashed gcf at the
squashed position. -/
theorem succ_nth_convergent'_eq_squash_gcf_nth_convergent' {K : Type u_1} {n : ℕ} {g : generalized_continued_fraction K} [division_ring K] : convergents' g (n + 1) = convergents' (squash_gcf g n) n := sorry

/-- The auxiliary continuants before the squashed position stay the same. -/
theorem continuants_aux_eq_continuants_aux_squash_gcf_of_le {K : Type u_1} {n : ℕ} {g : generalized_continued_fraction K} [division_ring K] {m : ℕ} : m ≤ n → continuants_aux g m = continuants_aux (squash_gcf g n) m := sorry

/-- The convergents coincide in the expected way at the squashed position if the partial denominator
at the squashed position is not zero. -/
theorem succ_nth_convergent_eq_squash_gcf_nth_convergent {K : Type u_1} {n : ℕ} {g : generalized_continued_fraction K} [field K] (nth_part_denom_ne_zero : ∀ {b : K}, seq.nth (partial_denominators g) n = some b → b ≠ 0) : convergents g (n + 1) = convergents (squash_gcf g n) n := sorry

/-- Shows that the recurrence relation (`convergents`) and direct evaluation (`convergents'`) of the
gcf coincide at position `n` if the sequence of fractions contains strictly positive values only.
Requiring positivity of all values is just one possible condition to obtain this result.
For example, the dual - sequences with strictly negative values only - would also work.

In practice, one most commonly deals with (regular) continued fractions, which satisfy the
positivity criterion required here. The analogous result for them
(see `continued_fractions.convergents_eq_convergents`) hence follows directly from this theorem.
-/
theorem convergents_eq_convergents' {K : Type u_1} {n : ℕ} {g : generalized_continued_fraction K} [linear_ordered_field K] (s_pos : ∀ {gp : pair K} {m : ℕ}, m < n → seq.nth (s g) m = some gp → 0 < pair.a gp ∧ 0 < pair.b gp) : convergents g n = convergents' g n := sorry

end generalized_continued_fraction


namespace continued_fraction


/-- Shows that the recurrence relation (`convergents`) and direct evaluation (`convergents'`) of a
(regular) continued fraction coincide. -/
theorem convergents_eq_convergents' {K : Type u_1} [linear_ordered_field K] {c : continued_fraction K} : generalized_continued_fraction.convergents ↑c = generalized_continued_fraction.convergents' ↑c := sorry

