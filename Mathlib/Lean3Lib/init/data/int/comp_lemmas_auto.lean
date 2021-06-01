/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Auxiliary lemmas used to compare int numerals.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.int.order

namespace Mathlib

namespace int


/- Auxiliary lemmas for proving that to int numerals are different -/

/- 1. Lemmas for reducing the problem to the case where the numerals are positive -/

protected theorem ne_neg_of_ne {a : ℤ} {b : ℤ} : a ≠ b → -a ≠ -b :=
  fun (h₁ : a ≠ b) (h₂ : -a = -b) => absurd (int.neg_inj h₂) h₁

protected theorem neg_ne_zero_of_ne {a : ℤ} : a ≠ 0 → -a ≠ 0 :=
  fun (h₁ : a ≠ 0) (h₂ : -a = 0) =>
    (fun (this : -a = -0) => (fun (this : a = 0) => absurd this h₁) (int.neg_inj this))
      (eq.mpr (id (Eq._oldrec (Eq.refl (-a = -0)) int.neg_zero)) h₂)

protected theorem zero_ne_neg_of_ne {a : ℤ} (h : 0 ≠ a) : 0 ≠ -a :=
  ne.symm (int.neg_ne_zero_of_ne (ne.symm h))

protected theorem neg_ne_of_pos {a : ℤ} {b : ℤ} : a > 0 → b > 0 → -a ≠ b := sorry

protected theorem ne_neg_of_pos {a : ℤ} {b : ℤ} : a > 0 → b > 0 → a ≠ -b :=
  fun (h₁ : a > 0) (h₂ : b > 0) => ne.symm (int.neg_ne_of_pos h₂ h₁)

/- 2. Lemmas for proving that positive int numerals are nonneg and positive -/

protected theorem one_pos : 1 > 0 := int.zero_lt_one

protected theorem bit0_pos {a : ℤ} : a > 0 → bit0 a > 0 := fun (h : a > 0) => int.add_pos h h

protected theorem bit1_pos {a : ℤ} : a ≥ 0 → bit1 a > 0 :=
  fun (h : a ≥ 0) => int.lt_add_of_le_of_pos (int.add_nonneg h h) int.zero_lt_one

protected theorem zero_nonneg : 0 ≥ 0 := le_refl 0

protected theorem one_nonneg : 1 ≥ 0 := le_of_lt int.zero_lt_one

protected theorem bit0_nonneg {a : ℤ} : a ≥ 0 → bit0 a ≥ 0 := fun (h : a ≥ 0) => int.add_nonneg h h

protected theorem bit1_nonneg {a : ℤ} : a ≥ 0 → bit1 a ≥ 0 :=
  fun (h : a ≥ 0) => le_of_lt (int.bit1_pos h)

protected theorem nonneg_of_pos {a : ℤ} : a > 0 → a ≥ 0 := le_of_lt

/- 3. nat_abs auxiliary lemmas -/

theorem neg_succ_of_nat_lt_zero (n : ℕ) : Int.negSucc n < 0 := sorry

theorem of_nat_ge_zero (n : ℕ) : Int.ofNat n ≥ 0 :=
  le.intro
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 + ↑n = Int.ofNat n)) (int.zero_add ↑n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑n = Int.ofNat n)) (int.coe_nat_eq n)))
        (Eq.refl (Int.ofNat n))))

theorem of_nat_nat_abs_eq_of_nonneg {a : ℤ} : a ≥ 0 → Int.ofNat (nat_abs a) = a := sorry

theorem ne_of_nat_abs_ne_nat_abs_of_nonneg {a : ℤ} {b : ℤ} (ha : a ≥ 0) (hb : b ≥ 0)
    (h : nat_abs a ≠ nat_abs b) : a ≠ b :=
  sorry

protected theorem ne_of_nat_ne_nonneg_case {a : ℤ} {b : ℤ} {n : ℕ} {m : ℕ} (ha : a ≥ 0) (hb : b ≥ 0)
    (e1 : nat_abs a = n) (e2 : nat_abs b = m) (h : n ≠ m) : a ≠ b :=
  (fun (this : nat_abs a ≠ nat_abs b) => ne_of_nat_abs_ne_nat_abs_of_nonneg ha hb this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs a ≠ nat_abs b)) e1))
      (eq.mpr (id (Eq._oldrec (Eq.refl (n ≠ nat_abs b)) e2)) h))

/- 4. Aux lemmas for pushing nat_abs inside numerals
   nat_abs_zero and nat_abs_one are defined at init/data/int/basic.lean -/

theorem nat_abs_of_nat_core (n : ℕ) : nat_abs (Int.ofNat n) = n := rfl

theorem nat_abs_of_neg_succ_of_nat (n : ℕ) : nat_abs (Int.negSucc n) = Nat.succ n := rfl

protected theorem nat_abs_add_nonneg {a : ℤ} {b : ℤ} :
    a ≥ 0 → b ≥ 0 → nat_abs (a + b) = nat_abs a + nat_abs b :=
  sorry

protected theorem nat_abs_add_neg {a : ℤ} {b : ℤ} :
    a < 0 → b < 0 → nat_abs (a + b) = nat_abs a + nat_abs b :=
  sorry

protected theorem nat_abs_bit0 (a : ℤ) : nat_abs (bit0 a) = bit0 (nat_abs a) := sorry

protected theorem nat_abs_bit0_step {a : ℤ} {n : ℕ} (h : nat_abs a = n) :
    nat_abs (bit0 a) = bit0 n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs (bit0 a) = bit0 n)) (Eq.symm h))) (int.nat_abs_bit0 a)

protected theorem nat_abs_bit1_nonneg {a : ℤ} (h : a ≥ 0) : nat_abs (bit1 a) = bit1 (nat_abs a) :=
  sorry

protected theorem nat_abs_bit1_nonneg_step {a : ℤ} {n : ℕ} (h₁ : a ≥ 0) (h₂ : nat_abs a = n) :
    nat_abs (bit1 a) = bit1 n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs (bit1 a) = bit1 n)) (Eq.symm h₂)))
    (int.nat_abs_bit1_nonneg h₁)

end Mathlib