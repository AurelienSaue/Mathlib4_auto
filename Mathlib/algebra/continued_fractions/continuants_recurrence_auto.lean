/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.continued_fractions.translations
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Recurrence Lemmas for the `continuants` Function of Continued Fractions.

## Summary

Given a generalized continued fraction `g`, for all `n ≥ 1`, we prove that the `continuants`
function indeed satisfies the following recurrences:
- `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`, and
- `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.
-/

namespace generalized_continued_fraction


theorem continuants_aux_recurrence {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ}
    [division_ring K] {gp : pair K} {ppred : pair K} {pred : pair K}
    (nth_s_eq : seq.nth (s g) n = some gp) (nth_conts_aux_eq : continuants_aux g n = ppred)
    (succ_nth_conts_aux_eq : continuants_aux g (n + 1) = pred) :
    continuants_aux g (n + bit0 1) =
        pair.mk (pair.b gp * pair.a pred + pair.a gp * pair.a ppred)
          (pair.b gp * pair.b pred + pair.a gp * pair.b ppred) :=
  sorry

theorem continuants_recurrence_aux {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ}
    [division_ring K] {gp : pair K} {ppred : pair K} {pred : pair K}
    (nth_s_eq : seq.nth (s g) n = some gp) (nth_conts_aux_eq : continuants_aux g n = ppred)
    (succ_nth_conts_aux_eq : continuants_aux g (n + 1) = pred) :
    continuants g (n + 1) =
        pair.mk (pair.b gp * pair.a pred + pair.a gp * pair.a ppred)
          (pair.b gp * pair.b pred + pair.a gp * pair.b ppred) :=
  sorry

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂` and `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
theorem continuants_recurrence {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ}
    [division_ring K] {gp : pair K} {ppred : pair K} {pred : pair K}
    (succ_nth_s_eq : seq.nth (s g) (n + 1) = some gp) (nth_conts_eq : continuants g n = ppred)
    (succ_nth_conts_eq : continuants g (n + 1) = pred) :
    continuants g (n + bit0 1) =
        pair.mk (pair.b gp * pair.a pred + pair.a gp * pair.a ppred)
          (pair.b gp * pair.b pred + pair.a gp * pair.b ppred) :=
  continuants_recurrence_aux succ_nth_s_eq
    (eq.mp (Eq._oldrec (Eq.refl (continuants g n = ppred)) nth_cont_eq_succ_nth_cont_aux)
      nth_conts_eq)
    (eq.mp (Eq._oldrec (Eq.refl (continuants g (n + 1) = pred)) nth_cont_eq_succ_nth_cont_aux)
      succ_nth_conts_eq)

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`. -/
theorem numerators_recurrence {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ}
    [division_ring K] {gp : pair K} {ppredA : K} {predA : K}
    (succ_nth_s_eq : seq.nth (s g) (n + 1) = some gp) (nth_num_eq : numerators g n = ppredA)
    (succ_nth_num_eq : numerators g (n + 1) = predA) :
    numerators g (n + bit0 1) = pair.b gp * predA + pair.a gp * ppredA :=
  sorry

/-- Shows that `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
theorem denominators_recurrence {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ}
    [division_ring K] {gp : pair K} {ppredB : K} {predB : K}
    (succ_nth_s_eq : seq.nth (s g) (n + 1) = some gp) (nth_denom_eq : denominators g n = ppredB)
    (succ_nth_denom_eq : denominators g (n + 1) = predB) :
    denominators g (n + bit0 1) = pair.b gp * predB + pair.a gp * ppredB :=
  sorry

end Mathlib