/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The `even` and `odd` predicates on the natural numbers.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.modeq
import PostPort

universes u_1 

namespace Mathlib

namespace nat


@[simp] theorem mod_two_ne_one {n : ℕ} : ¬n % bit0 1 = 1 ↔ n % bit0 1 = 0 := sorry

@[simp] theorem mod_two_ne_zero {n : ℕ} : ¬n % bit0 1 = 0 ↔ n % bit0 1 = 1 := sorry

theorem even_iff {n : ℕ} : even n ↔ n % bit0 1 = 0 := sorry

theorem odd_iff {n : ℕ} : odd n ↔ n % bit0 1 = 1 := sorry

theorem not_even_iff {n : ℕ} : ¬even n ↔ n % bit0 1 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬even n ↔ n % bit0 1 = 1)) (propext even_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬n % bit0 1 = 0 ↔ n % bit0 1 = 1)) (propext mod_two_ne_zero)))
      (iff.refl (n % bit0 1 = 1)))

theorem not_odd_iff {n : ℕ} : ¬odd n ↔ n % bit0 1 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬odd n ↔ n % bit0 1 = 0)) (propext odd_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬n % bit0 1 = 1 ↔ n % bit0 1 = 0)) (propext mod_two_ne_one)))
      (iff.refl (n % bit0 1 = 0)))

theorem even_iff_not_odd {n : ℕ} : even n ↔ ¬odd n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (even n ↔ ¬odd n)) (propext not_odd_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (even n ↔ n % bit0 1 = 0)) (propext even_iff))) (iff.refl (n % bit0 1 = 0)))

@[simp] theorem odd_iff_not_even {n : ℕ} : odd n ↔ ¬even n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (odd n ↔ ¬even n)) (propext not_even_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (odd n ↔ n % bit0 1 = 1)) (propext odd_iff))) (iff.refl (n % bit0 1 = 1)))

theorem even_or_odd (n : ℕ) : even n ∨ odd n :=
  or.imp_right (iff.mpr odd_iff_not_even) (em (even n))

theorem even_or_odd' (n : ℕ) : ∃ (k : ℕ), n = bit0 1 * k ∨ n = bit0 1 * k + 1 := sorry

theorem even_xor_odd (n : ℕ) : xor (even n) (odd n) :=
  or.dcases_on (even_or_odd n) (fun (h : even n) => Or.inl { left := h, right := iff.mp even_iff_not_odd h })
    fun (h : odd n) => Or.inr { left := h, right := iff.mp odd_iff_not_even h }

theorem even_xor_odd' (n : ℕ) : ∃ (k : ℕ), xor (n = bit0 1 * k) (n = bit0 1 * k + 1) := sorry

theorem odd_gt_zero {n : ℕ} (h : odd n) : 0 < n :=
  Exists.dcases_on h fun (k : ℕ) (hk : n = bit0 1 * k + 1) => eq.mpr (id (Eq._oldrec (Eq.refl (0 < n)) hk)) succ_pos'

protected instance even.decidable_pred : decidable_pred even :=
  fun (n : ℕ) => decidable_of_decidable_of_iff (nat.decidable_eq (n % bit0 1) 0) sorry

protected instance decidable_pred_odd : decidable_pred odd :=
  fun (n : ℕ) => decidable_of_decidable_of_iff not.decidable sorry

@[simp] theorem even_zero : even 0 :=
  Exists.intro 0 (of_as_true trivial)

@[simp] theorem not_even_one : ¬even 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬even 1)) (propext even_iff))) one_ne_zero

@[simp] theorem even_bit0 (n : ℕ) : even (bit0 n) :=
  Exists.intro n
    (eq.mpr (id (Eq._oldrec (Eq.refl (bit0 n = bit0 1 * n)) (bit0.equations._eqn_1 n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (n + n = bit0 1 * n)) (two_mul n))) (Eq.refl (n + n))))

theorem even_add {m : ℕ} {n : ℕ} : even (m + n) ↔ (even m ↔ even n) := sorry

theorem even.add {m : ℕ} {n : ℕ} (hm : even m) (hn : even n) : even (m + n) := sorry

@[simp] theorem not_even_bit1 (n : ℕ) : ¬even (bit1 n) := sorry

theorem two_not_dvd_two_mul_add_one (a : ℕ) : ¬bit0 1 ∣ bit0 1 * a + 1 := sorry

theorem two_not_dvd_two_mul_sub_one {a : ℕ} (w : 0 < a) : ¬bit0 1 ∣ bit0 1 * a - 1 := sorry

theorem even_sub {m : ℕ} {n : ℕ} (h : n ≤ m) : even (m - n) ↔ (even m ↔ even n) := sorry

theorem even.sub {m : ℕ} {n : ℕ} (hm : even m) (hn : even n) : even (m - n) := sorry

theorem even_succ {n : ℕ} : even (Nat.succ n) ↔ ¬even n := sorry

theorem even_mul {m : ℕ} {n : ℕ} : even (m * n) ↔ even m ∨ even n := sorry

/-- If `m` and `n` are natural numbers, then the natural number `m^n` is even
if and only if `m` is even and `n` is positive. -/
theorem even_pow {m : ℕ} {n : ℕ} : even (m ^ n) ↔ even m ∧ n ≠ 0 := sorry

theorem even_div {a : ℕ} {b : ℕ} : even (a / b) ↔ a % (bit0 1 * b) / b = 0 := sorry

theorem neg_one_pow_eq_one_iff_even {α : Type u_1} [ring α] {n : ℕ} (h1 : -1 ≠ 1) : (-1) ^ n = 1 ↔ even n := sorry

@[simp] theorem neg_one_pow_two {α : Type u_1} [ring α] : (-1) ^ bit0 1 = 1 := sorry

theorem neg_one_pow_of_even {α : Type u_1} [ring α] {n : ℕ} : even n → (-1) ^ n = 1 := sorry

theorem neg_one_pow_of_odd {α : Type u_1} [ring α] {n : ℕ} : odd n → (-1) ^ n = -1 := sorry

