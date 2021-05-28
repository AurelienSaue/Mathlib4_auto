/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.choose.basic
import Mathlib.tactic.linarith.default
import Mathlib.tactic.omega.default
import Mathlib.algebra.big_operators.ring
import Mathlib.algebra.big_operators.intervals
import Mathlib.algebra.big_operators.order
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Sums of binomial coefficients

This file includes variants of the binomial theorem and other results on sums of binomial
coefficients. Theorems whose proofs depend on such sums may also go in this file for import
reasons.

-/

/-- A version of the binomial theorem for noncommutative semirings. -/
theorem commute.add_pow {α : Type u_1} [semiring α] {x : α} {y : α} (h : commute x y) (n : ℕ) : (x + y) ^ n = finset.sum (finset.range (n + 1)) fun (m : ℕ) => x ^ m * y ^ (n - m) * ↑(nat.choose n m) := sorry

/-- The binomial theorem -/
theorem add_pow {α : Type u_1} [comm_semiring α] (x : α) (y : α) (n : ℕ) : (x + y) ^ n = finset.sum (finset.range (n + 1)) fun (m : ℕ) => x ^ m * y ^ (n - m) * ↑(nat.choose n m) :=
  commute.add_pow (commute.all x y) n

namespace nat


/-- The sum of entries in a row of Pascal's triangle -/
theorem sum_range_choose (n : ℕ) : (finset.sum (finset.range (n + 1)) fun (m : ℕ) => choose n m) = bit0 1 ^ n := sorry

theorem sum_range_choose_halfway (m : ℕ) : (finset.sum (finset.range (m + 1)) fun (i : ℕ) => choose (bit0 1 * m + 1) i) = bit0 (bit0 1) ^ m := sorry

theorem choose_middle_le_pow (n : ℕ) : choose (bit0 1 * n + 1) n ≤ bit0 (bit0 1) ^ n := sorry

end nat


theorem int.alternating_sum_range_choose {n : ℕ} : (finset.sum (finset.range (n + 1)) fun (m : ℕ) => (-1) ^ m * ↑(nat.choose n m)) = ite (n = 0) 1 0 := sorry

theorem int.alternating_sum_range_choose_of_ne {n : ℕ} (h0 : n ≠ 0) : (finset.sum (finset.range (n + 1)) fun (m : ℕ) => (-1) ^ m * ↑(nat.choose n m)) = 0 := sorry

namespace finset


theorem sum_powerset_apply_card {α : Type u_1} {β : Type u_2} [add_comm_monoid α] (f : ℕ → α) {x : finset β} : (finset.sum (powerset x) fun (m : finset β) => f (card m)) =
  finset.sum (range (card x + 1)) fun (m : ℕ) => nat.choose (card x) m •ℕ f m := sorry

theorem sum_powerset_neg_one_pow_card {α : Type u_1} [DecidableEq α] {x : finset α} : (finset.sum (powerset x) fun (m : finset α) => (-1) ^ card m) = ite (x = ∅) 1 0 := sorry

theorem sum_powerset_neg_one_pow_card_of_nonempty {α : Type u_1} {x : finset α} (h0 : finset.nonempty x) : (finset.sum (powerset x) fun (m : finset α) => (-1) ^ card m) = 0 := sorry

