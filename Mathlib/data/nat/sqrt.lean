/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.int.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# Square root of natural numbers

An efficient binary implementation of a (`sqrt n`) function that
returns `s` such that
```
s*s ≤ n ≤ s*s + s + s
```
-/

namespace nat


theorem sqrt_aux_dec {b : ℕ} (h : b ≠ 0) : shiftr b (bit0 1) < b := sorry

/-- Auxiliary function for `nat.sqrt`. See e.g.
<https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)> -/
def sqrt_aux : ℕ → ℕ → ℕ → ℕ :=
  sorry

/-- `sqrt n` is the square root of a natural number `n`. If `n` is not a
  perfect square, it returns the largest `k:ℕ` such that `k*k ≤ n`. -/
def sqrt (n : ℕ) : ℕ :=
  sorry

theorem sqrt_aux_0 (r : ℕ) (n : ℕ) : sqrt_aux 0 r n = r := sorry

theorem sqrt_aux_1 {r : ℕ} {n : ℕ} {b : ℕ} (h : b ≠ 0) {n' : ℕ} (h₂ : r + b + n' = n) : sqrt_aux b r n = sqrt_aux (shiftr b (bit0 1)) (div2 r + b) n' := sorry

theorem sqrt_aux_2 {r : ℕ} {n : ℕ} {b : ℕ} (h : b ≠ 0) (h₂ : n < r + b) : sqrt_aux b r n = sqrt_aux (shiftr b (bit0 1)) (div2 r) n := sorry

theorem sqrt_le (n : ℕ) : sqrt n * sqrt n ≤ n :=
  and.left (sqrt_is_sqrt n)

theorem lt_succ_sqrt (n : ℕ) : n < Nat.succ (sqrt n) * Nat.succ (sqrt n) :=
  and.right (sqrt_is_sqrt n)

theorem sqrt_le_add (n : ℕ) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n ≤ sqrt n * sqrt n + sqrt n + sqrt n)) (Eq.symm (succ_mul (sqrt n) (sqrt n)))))
    (le_of_lt_succ (lt_succ_sqrt n))

theorem le_sqrt {m : ℕ} {n : ℕ} : m ≤ sqrt n ↔ m * m ≤ n :=
  { mp := fun (h : m ≤ sqrt n) => le_trans (mul_self_le_mul_self h) (sqrt_le n),
    mpr := fun (h : m * m ≤ n) => le_of_lt_succ (iff.mpr mul_self_lt_mul_self_iff (lt_of_le_of_lt h (lt_succ_sqrt n))) }

theorem sqrt_lt {m : ℕ} {n : ℕ} : sqrt m < n ↔ m < n * n :=
  lt_iff_lt_of_le_iff_le le_sqrt

theorem sqrt_le_self (n : ℕ) : sqrt n ≤ n :=
  le_trans (le_mul_self (sqrt n)) (sqrt_le n)

theorem sqrt_le_sqrt {m : ℕ} {n : ℕ} (h : m ≤ n) : sqrt m ≤ sqrt n :=
  iff.mpr le_sqrt (le_trans (sqrt_le m) h)

theorem sqrt_eq_zero {n : ℕ} : sqrt n = 0 ↔ n = 0 := sorry

theorem eq_sqrt {n : ℕ} {q : ℕ} : q = sqrt n ↔ q * q ≤ n ∧ n < (q + 1) * (q + 1) := sorry

theorem le_three_of_sqrt_eq_one {n : ℕ} (h : sqrt n = 1) : n ≤ bit1 1 :=
  le_of_lt_succ (iff.mp sqrt_lt (eq.mpr (id (Eq._oldrec (Eq.refl (sqrt n < bit0 1)) h)) (of_as_true trivial)))

theorem sqrt_lt_self {n : ℕ} (h : 1 < n) : sqrt n < n :=
  iff.mpr sqrt_lt
    (eq.mp (Eq._oldrec (Eq.refl (n * 1 < n * n)) (mul_one n)) (nat.mul_lt_mul_of_pos_left h (lt_of_succ_lt h)))

theorem sqrt_pos {n : ℕ} : 0 < sqrt n ↔ 0 < n :=
  le_sqrt

theorem sqrt_add_eq (n : ℕ) {a : ℕ} (h : a ≤ n + n) : sqrt (n * n + a) = n := sorry

theorem sqrt_eq (n : ℕ) : sqrt (n * n) = n :=
  sqrt_add_eq n (zero_le (n + n))

theorem sqrt_succ_le_succ_sqrt (n : ℕ) : sqrt (Nat.succ n) ≤ Nat.succ (sqrt n) := sorry

theorem exists_mul_self (x : ℕ) : (∃ (n : ℕ), n * n = x) ↔ sqrt x * sqrt x = x := sorry

theorem sqrt_mul_sqrt_lt_succ (n : ℕ) : sqrt n * sqrt n < n + 1 :=
  iff.mpr lt_succ_iff (sqrt_le n)

theorem succ_le_succ_sqrt (n : ℕ) : n + 1 ≤ (sqrt n + 1) * (sqrt n + 1) :=
  le_of_pred_lt (lt_succ_sqrt (Nat.pred (n + 1)))

/-- There are no perfect squares strictly between m² and (m+1)² -/
theorem not_exists_sq {n : ℕ} {m : ℕ} (hl : m * m < n) (hr : n < (m + 1) * (m + 1)) : ¬∃ (t : ℕ), t * t = n := sorry

