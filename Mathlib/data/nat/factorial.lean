/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# The factorial function

-/

namespace nat


/-- `nat.factorial n` is the factorial of `n`. -/
@[simp] def factorial : ℕ → ℕ :=
  sorry

@[simp] theorem factorial_zero : factorial 0 = factorial 1 :=
  rfl

@[simp] theorem factorial_succ (n : ℕ) : factorial (Nat.succ n) = Nat.succ n * factorial n :=
  rfl

@[simp] theorem factorial_one : factorial 1 = 1 :=
  rfl

theorem mul_factorial_pred {n : ℕ} (hn : 0 < n) : n * factorial (n - 1) = factorial n :=
  nat.sub_add_cancel hn ▸ rfl

theorem factorial_pos (n : ℕ) : 0 < factorial n := sorry

theorem factorial_ne_zero (n : ℕ) : factorial n ≠ 0 :=
  ne_of_gt (factorial_pos n)

theorem factorial_dvd_factorial {m : ℕ} {n : ℕ} (h : m ≤ n) : factorial m ∣ factorial n := sorry

theorem dvd_factorial {m : ℕ} {n : ℕ} : 0 < m → m ≤ n → m ∣ factorial n := sorry

theorem factorial_le {m : ℕ} {n : ℕ} (h : m ≤ n) : factorial m ≤ factorial n :=
  le_of_dvd (factorial_pos n) (factorial_dvd_factorial h)

theorem factorial_mul_pow_le_factorial {m : ℕ} {n : ℕ} : factorial m * Nat.succ m ^ n ≤ factorial (m + n) := sorry

theorem monotone_factorial : monotone factorial :=
  fun (n m : ℕ) => factorial_le

theorem factorial_lt {m : ℕ} {n : ℕ} (h0 : 0 < n) : factorial n < factorial m ↔ n < m := sorry

theorem one_lt_factorial {n : ℕ} : 1 < factorial n ↔ 1 < n := sorry

theorem factorial_eq_one {n : ℕ} : factorial n = 1 ↔ n ≤ 1 := sorry

theorem factorial_inj {m : ℕ} {n : ℕ} (h0 : 1 < factorial n) : factorial n = factorial m ↔ n = m := sorry

theorem self_le_factorial (n : ℕ) : n ≤ factorial n := sorry

