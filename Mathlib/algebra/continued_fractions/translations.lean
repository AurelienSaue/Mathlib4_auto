/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.continued_fractions.basic
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Basic Translation Lemmas Between Functions Defined for Continued Fractions

## Summary

Some simple translation lemmas between the different definitions of functions defined in
`algebra.continued_fractions.basic`.
-/

namespace generalized_continued_fraction


/-!
### Translations Between General Access Functions

Here we give some basic translations that hold by definition between the various methods that allow
us to access the numerators and denominators of a continued fraction.
-/

theorem terminated_at_iff_s_terminated_at {α : Type u_1} {g : generalized_continued_fraction α} {n : ℕ} : terminated_at g n ↔ seq.terminated_at (s g) n :=
  iff.refl (terminated_at g n)

theorem terminated_at_iff_s_none {α : Type u_1} {g : generalized_continued_fraction α} {n : ℕ} : terminated_at g n ↔ seq.nth (s g) n = none :=
  iff.refl (terminated_at g n)

theorem part_num_none_iff_s_none {α : Type u_1} {g : generalized_continued_fraction α} {n : ℕ} : seq.nth (partial_numerators g) n = none ↔ seq.nth (s g) n = none := sorry

theorem terminated_at_iff_part_num_none {α : Type u_1} {g : generalized_continued_fraction α} {n : ℕ} : terminated_at g n ↔ seq.nth (partial_numerators g) n = none := sorry

theorem part_denom_none_iff_s_none {α : Type u_1} {g : generalized_continued_fraction α} {n : ℕ} : seq.nth (partial_denominators g) n = none ↔ seq.nth (s g) n = none := sorry

theorem terminated_at_iff_part_denom_none {α : Type u_1} {g : generalized_continued_fraction α} {n : ℕ} : terminated_at g n ↔ seq.nth (partial_denominators g) n = none := sorry

theorem part_num_eq_s_a {α : Type u_1} {g : generalized_continued_fraction α} {n : ℕ} {gp : pair α} (s_nth_eq : seq.nth (s g) n = some gp) : seq.nth (partial_numerators g) n = some (pair.a gp) := sorry

theorem part_denom_eq_s_b {α : Type u_1} {g : generalized_continued_fraction α} {n : ℕ} {gp : pair α} (s_nth_eq : seq.nth (s g) n = some gp) : seq.nth (partial_denominators g) n = some (pair.b gp) := sorry

theorem exists_s_a_of_part_num {α : Type u_1} {g : generalized_continued_fraction α} {n : ℕ} {a : α} (nth_part_num_eq : seq.nth (partial_numerators g) n = some a) : ∃ (gp : pair α), seq.nth (s g) n = some gp ∧ pair.a gp = a := sorry

theorem exists_s_b_of_part_denom {α : Type u_1} {g : generalized_continued_fraction α} {n : ℕ} {b : α} (nth_part_denom_eq : seq.nth (partial_denominators g) n = some b) : ∃ (gp : pair α), seq.nth (s g) n = some gp ∧ pair.b gp = b := sorry

/-!
### Translations Between Computational Functions

Here we  give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/

theorem nth_cont_eq_succ_nth_cont_aux {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} [division_ring K] : continuants g n = continuants_aux g (n + 1) :=
  rfl

theorem num_eq_conts_a {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} [division_ring K] : numerators g n = pair.a (continuants g n) :=
  rfl

theorem denom_eq_conts_b {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} [division_ring K] : denominators g n = pair.b (continuants g n) :=
  rfl

theorem convergent_eq_num_div_denom {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} [division_ring K] : convergents g n = numerators g n / denominators g n :=
  rfl

theorem convergent_eq_conts_a_div_conts_b {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} [division_ring K] : convergents g n = pair.a (continuants g n) / pair.b (continuants g n) :=
  rfl

theorem exists_conts_a_of_num {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} [division_ring K] {A : K} (nth_num_eq : numerators g n = A) : ∃ (conts : pair K), continuants g n = conts ∧ pair.a conts = A :=
  eq.mpr (id (propext exists_eq_left')) nth_num_eq

theorem exists_conts_b_of_denom {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} [division_ring K] {B : K} (nth_denom_eq : denominators g n = B) : ∃ (conts : pair K), continuants g n = conts ∧ pair.b conts = B :=
  eq.mpr (id (propext exists_eq_left')) nth_denom_eq

@[simp] theorem zeroth_continuant_aux_eq_one_zero {K : Type u_1} {g : generalized_continued_fraction K} [division_ring K] : continuants_aux g 0 = pair.mk 1 0 :=
  rfl

@[simp] theorem first_continuant_aux_eq_h_one {K : Type u_1} {g : generalized_continued_fraction K} [division_ring K] : continuants_aux g 1 = pair.mk (h g) 1 :=
  rfl

@[simp] theorem zeroth_continuant_eq_h_one {K : Type u_1} {g : generalized_continued_fraction K} [division_ring K] : continuants g 0 = pair.mk (h g) 1 :=
  rfl

@[simp] theorem zeroth_numerator_eq_h {K : Type u_1} {g : generalized_continued_fraction K} [division_ring K] : numerators g 0 = h g :=
  rfl

@[simp] theorem zeroth_denominator_eq_one {K : Type u_1} {g : generalized_continued_fraction K} [division_ring K] : denominators g 0 = 1 :=
  rfl

@[simp] theorem zeroth_convergent_eq_h {K : Type u_1} {g : generalized_continued_fraction K} [division_ring K] : convergents g 0 = h g := sorry

theorem second_continuant_aux_eq {K : Type u_1} {g : generalized_continued_fraction K} [division_ring K] {gp : pair K} (zeroth_s_eq : seq.nth (s g) 0 = some gp) : continuants_aux g (bit0 1) = pair.mk (pair.b gp * h g + pair.a gp) (pair.b gp) := sorry

theorem first_continuant_eq {K : Type u_1} {g : generalized_continued_fraction K} [division_ring K] {gp : pair K} (zeroth_s_eq : seq.nth (s g) 0 = some gp) : continuants g 1 = pair.mk (pair.b gp * h g + pair.a gp) (pair.b gp) := sorry

theorem first_numerator_eq {K : Type u_1} {g : generalized_continued_fraction K} [division_ring K] {gp : pair K} (zeroth_s_eq : seq.nth (s g) 0 = some gp) : numerators g 1 = pair.b gp * h g + pair.a gp := sorry

theorem first_denominator_eq {K : Type u_1} {g : generalized_continued_fraction K} [division_ring K] {gp : pair K} (zeroth_s_eq : seq.nth (s g) 0 = some gp) : denominators g 1 = pair.b gp := sorry

@[simp] theorem zeroth_convergent'_aux_eq_zero {K : Type u_1} [division_ring K] {s : seq (pair K)} : convergents'_aux s 0 = 0 :=
  rfl

@[simp] theorem zeroth_convergent'_eq_h {K : Type u_1} {g : generalized_continued_fraction K} [division_ring K] : convergents' g 0 = h g := sorry

