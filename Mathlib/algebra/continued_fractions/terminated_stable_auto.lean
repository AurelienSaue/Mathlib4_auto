/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.continued_fractions.translations
import PostPort

universes u_1 

namespace Mathlib

/-!
# Stabilisation of gcf Computations Under Termination

## Summary

We show that the continuants and convergents of a gcf stabilise once the gcf terminates.
-/

namespace generalized_continued_fraction


/-- If a gcf terminated at position `n`, it also terminated at `m ≥ n`.-/
theorem terminated_stable {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} {m : ℕ} (n_le_m : n ≤ m) (terminated_at_n : terminated_at g n) : terminated_at g m :=
  seq.terminated_stable (s g) n_le_m terminated_at_n

theorem continuants_aux_stable_step_of_terminated {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} [division_ring K] (terminated_at_n : terminated_at g n) : continuants_aux g (n + bit0 1) = continuants_aux g (n + 1) := sorry

theorem continuants_aux_stable_of_terminated {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} {m : ℕ} [division_ring K] (succ_n_le_m : n + 1 ≤ m) (terminated_at_n : terminated_at g n) : continuants_aux g m = continuants_aux g (n + 1) := sorry

theorem convergents'_aux_stable_step_of_terminated {K : Type u_1} {n : ℕ} [division_ring K] {s : seq (pair K)} (terminated_at_n : seq.terminated_at s n) : convergents'_aux s (n + 1) = convergents'_aux s n := sorry

theorem convergents'_aux_stable_of_terminated {K : Type u_1} {n : ℕ} {m : ℕ} [division_ring K] {s : seq (pair K)} (n_le_m : n ≤ m) (terminated_at_n : seq.terminated_at s n) : convergents'_aux s m = convergents'_aux s n := sorry

theorem continuants_stable_of_terminated {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} {m : ℕ} [division_ring K] (n_le_m : n ≤ m) (terminated_at_n : terminated_at g n) : continuants g m = continuants g n := sorry

theorem numerators_stable_of_terminated {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} {m : ℕ} [division_ring K] (n_le_m : n ≤ m) (terminated_at_n : terminated_at g n) : numerators g m = numerators g n := sorry

theorem denominators_stable_of_terminated {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} {m : ℕ} [division_ring K] (n_le_m : n ≤ m) (terminated_at_n : terminated_at g n) : denominators g m = denominators g n := sorry

theorem convergents_stable_of_terminated {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} {m : ℕ} [division_ring K] (n_le_m : n ≤ m) (terminated_at_n : terminated_at g n) : convergents g m = convergents g n := sorry

theorem convergents'_stable_of_terminated {K : Type u_1} {g : generalized_continued_fraction K} {n : ℕ} {m : ℕ} [division_ring K] (n_le_m : n ≤ m) (terminated_at_n : terminated_at g n) : convergents' g m = convergents' g n := sorry

