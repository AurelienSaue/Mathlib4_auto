/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.factorial
import Mathlib.PostPort

namespace Mathlib

/-!
# Binomial coefficients

This file contains a definition of binomial coefficients and simple lemmas (i.e. those not
requiring more imports).

## Main definition and results

- `nat.choose`: binomial coefficients, defined inductively
- `nat.choose_eq_factorial_div_factorial`: a proof that `choose n k = n! / (k! * (n - k)!)`
- `nat.choose_symm`: symmetry of binomial coefficients
- `nat.choose_le_succ_of_lt_half_left`: `choose n k` is increasing for small values of `k`
- `nat.choose_le_middle`: `choose n r` is maximised when `r` is `n/2`

-/

namespace nat


/-- `choose n k` is the number of `k`-element subsets in an `n`-element set. Also known as binomial
coefficients. -/
def choose : ℕ → ℕ → ℕ := sorry

@[simp] theorem choose_zero_right (n : ℕ) : choose n 0 = 1 :=
  nat.cases_on n (Eq.refl (choose 0 0)) fun (n : ℕ) => Eq.refl (choose (Nat.succ n) 0)

@[simp] theorem choose_zero_succ (k : ℕ) : choose 0 (Nat.succ k) = 0 := rfl

theorem choose_succ_succ (n : ℕ) (k : ℕ) :
    choose (Nat.succ n) (Nat.succ k) = choose n k + choose n (Nat.succ k) :=
  rfl

theorem choose_eq_zero_of_lt {n : ℕ} {k : ℕ} : n < k → choose n k = 0 := sorry

@[simp] theorem choose_self (n : ℕ) : choose n n = 1 := sorry

@[simp] theorem choose_succ_self (n : ℕ) : choose n (Nat.succ n) = 0 :=
  choose_eq_zero_of_lt (lt_succ_self n)

@[simp] theorem choose_one_right (n : ℕ) : choose n 1 = n := sorry

/- The `n+1`-st triangle number is `n` more than the `n`-th triangle number -/

theorem triangle_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / bit0 1 = n * (n - 1) / bit0 1 + n := sorry

/-- `choose n 2` is the `n`-th triangle number. -/
theorem choose_two_right (n : ℕ) : choose n (bit0 1) = n * (n - 1) / bit0 1 := sorry

theorem choose_pos {n : ℕ} {k : ℕ} : k ≤ n → 0 < choose n k := sorry

theorem succ_mul_choose_eq (n : ℕ) (k : ℕ) :
    Nat.succ n * choose n k = choose (Nat.succ n) (Nat.succ k) * Nat.succ k :=
  sorry

theorem choose_mul_factorial_mul_factorial {n : ℕ} {k : ℕ} :
    k ≤ n → choose n k * factorial k * factorial (n - k) = factorial n :=
  sorry

theorem choose_eq_factorial_div_factorial {n : ℕ} {k : ℕ} (hk : k ≤ n) :
    choose n k = factorial n / (factorial k * factorial (n - k)) :=
  sorry

theorem factorial_mul_factorial_dvd_factorial {n : ℕ} {k : ℕ} (hk : k ≤ n) :
    factorial k * factorial (n - k) ∣ factorial n :=
  sorry

@[simp] theorem choose_symm {n : ℕ} {k : ℕ} (hk : k ≤ n) : choose n (n - k) = choose n k := sorry

theorem choose_symm_of_eq_add {n : ℕ} {a : ℕ} {b : ℕ} (h : n = a + b) : choose n a = choose n b :=
  sorry

theorem choose_symm_add {a : ℕ} {b : ℕ} : choose (a + b) a = choose (a + b) b :=
  choose_symm_of_eq_add rfl

theorem choose_symm_half (m : ℕ) : choose (bit0 1 * m + 1) (m + 1) = choose (bit0 1 * m + 1) m :=
  sorry

theorem choose_succ_right_eq (n : ℕ) (k : ℕ) : choose n (k + 1) * (k + 1) = choose n k * (n - k) :=
  sorry

@[simp] theorem choose_succ_self_right (n : ℕ) : choose (n + 1) n = n + 1 := sorry

theorem choose_mul_succ_eq (n : ℕ) (k : ℕ) :
    choose n k * (n + 1) = choose (n + 1) k * (n + 1 - k) :=
  sorry

/-! ### Inequalities -/

/-- Show that `nat.choose` is increasing for small values of the right argument. -/
theorem choose_le_succ_of_lt_half_left {r : ℕ} {n : ℕ} (h : r < n / bit0 1) :
    choose n r ≤ choose n (r + 1) :=
  sorry

/-- Show that for small values of the right argument, the middle value is largest. -/
/-- `choose n r` is maximised when `r` is `n/2`. -/
theorem choose_le_middle (r : ℕ) (n : ℕ) : choose n r ≤ choose n (n / bit0 1) := sorry

end Mathlib