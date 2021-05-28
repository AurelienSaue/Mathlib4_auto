/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Benjamin Davidson

The `even` and `odd` predicates on the integers.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.int.modeq
import Mathlib.data.nat.parity
import Mathlib.PostPort

namespace Mathlib

namespace int


@[simp] theorem mod_two_ne_one {n : ℤ} : ¬n % bit0 1 = 1 ↔ n % bit0 1 = 0 := sorry

theorem mod_two_ne_zero {n : ℤ} : ¬n % bit0 1 = 0 ↔ n % bit0 1 = 1 := sorry

@[simp] theorem even_coe_nat (n : ℕ) : even ↑n ↔ even n := sorry

theorem even_iff {n : ℤ} : even n ↔ n % bit0 1 = 0 := sorry

theorem odd_iff {n : ℤ} : odd n ↔ n % bit0 1 = 1 := sorry

theorem not_even_iff {n : ℤ} : ¬even n ↔ n % bit0 1 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬even n ↔ n % bit0 1 = 1)) (propext even_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬n % bit0 1 = 0 ↔ n % bit0 1 = 1)) (propext mod_two_ne_zero)))
      (iff.refl (n % bit0 1 = 1)))

theorem not_odd_iff {n : ℤ} : ¬odd n ↔ n % bit0 1 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬odd n ↔ n % bit0 1 = 0)) (propext odd_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬n % bit0 1 = 1 ↔ n % bit0 1 = 0)) (propext mod_two_ne_one)))
      (iff.refl (n % bit0 1 = 0)))

theorem even_iff_not_odd {n : ℤ} : even n ↔ ¬odd n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (even n ↔ ¬odd n)) (propext not_odd_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (even n ↔ n % bit0 1 = 0)) (propext even_iff))) (iff.refl (n % bit0 1 = 0)))

@[simp] theorem odd_iff_not_even {n : ℤ} : odd n ↔ ¬even n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (odd n ↔ ¬even n)) (propext not_even_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (odd n ↔ n % bit0 1 = 1)) (propext odd_iff))) (iff.refl (n % bit0 1 = 1)))

theorem even_or_odd (n : ℤ) : even n ∨ odd n :=
  or.imp_right (iff.mpr odd_iff_not_even) (em (even n))

theorem even_or_odd' (n : ℤ) : ∃ (k : ℤ), n = bit0 1 * k ∨ n = bit0 1 * k + 1 := sorry

theorem even_xor_odd (n : ℤ) : xor (even n) (odd n) :=
  or.dcases_on (even_or_odd n) (fun (h : even n) => Or.inl { left := h, right := iff.mp even_iff_not_odd h })
    fun (h : odd n) => Or.inr { left := h, right := iff.mp odd_iff_not_even h }

theorem even_xor_odd' (n : ℤ) : ∃ (k : ℤ), xor (n = bit0 1 * k) (n = bit0 1 * k + 1) := sorry

theorem ne_of_odd_sum {x : ℤ} {y : ℤ} (h : odd (x + y)) : x ≠ y := sorry

@[simp] theorem two_dvd_ne_zero {n : ℤ} : ¬bit0 1 ∣ n ↔ n % bit0 1 = 1 :=
  not_even_iff

protected instance even.decidable_pred : decidable_pred even :=
  fun (n : ℤ) => decidable_of_decidable_of_iff (int.decidable_eq (n % bit0 1) 0) sorry

protected instance decidable_pred_odd : decidable_pred odd :=
  fun (n : ℤ) => decidable_of_decidable_of_iff not.decidable sorry

@[simp] theorem even_zero : even 0 :=
  Exists.intro 0 (of_as_true trivial)

@[simp] theorem not_even_one : ¬even 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬even 1)) (propext even_iff))) one_ne_zero

@[simp] theorem even_bit0 (n : ℤ) : even (bit0 n) :=
  Exists.intro n
    (eq.mpr (id (Eq._oldrec (Eq.refl (bit0 n = bit0 1 * n)) (bit0.equations._eqn_1 n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (n + n = bit0 1 * n)) (two_mul n))) (Eq.refl (n + n))))

theorem even_add {m : ℤ} {n : ℤ} : even (m + n) ↔ (even m ↔ even n) := sorry

theorem even_neg {n : ℤ} : even (-n) ↔ even n := sorry

@[simp] theorem not_even_bit1 (n : ℤ) : ¬even (bit1 n) := sorry

theorem even_sub {m : ℤ} {n : ℤ} : even (m - n) ↔ (even m ↔ even n) := sorry

theorem even_mul {m : ℤ} {n : ℤ} : even (m * n) ↔ even m ∨ even n := sorry

theorem even_pow {m : ℤ} {n : ℕ} : even (m ^ n) ↔ even m ∧ n ≠ 0 := sorry

