/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.modeq
import Mathlib.tactic.ring
import PostPort

namespace Mathlib

namespace int


/-- `a ≡ b [ZMOD n]` when `a % n = b % n`. -/
def modeq (n : ℤ) (a : ℤ) (b : ℤ)  :=
  a % n = b % n

namespace modeq


protected theorem refl {n : ℤ} (a : ℤ) : modeq n a a :=
  rfl

protected theorem symm {n : ℤ} {a : ℤ} {b : ℤ} : modeq n a b → modeq n b a :=
  Eq.symm

protected theorem trans {n : ℤ} {a : ℤ} {b : ℤ} {c : ℤ} : modeq n a b → modeq n b c → modeq n a c :=
  Eq.trans

theorem coe_nat_modeq_iff {a : ℕ} {b : ℕ} {n : ℕ} : modeq ↑n ↑a ↑b ↔ nat.modeq n a b := sorry

protected instance decidable {n : ℤ} {a : ℤ} {b : ℤ} : Decidable (modeq n a b) :=
  eq.mpr sorry (int.decidable_eq (a % n) (b % n))

theorem modeq_zero_iff {n : ℤ} {a : ℤ} : modeq n a 0 ↔ n ∣ a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (modeq n a 0 ↔ n ∣ a)) (equations._eqn_1 n a 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a % n = 0 % n ↔ n ∣ a)) (zero_mod n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a % n = 0 ↔ n ∣ a)) (propext (dvd_iff_mod_eq_zero n a)))) (iff.refl (a % n = 0))))

theorem modeq_iff_dvd {n : ℤ} {a : ℤ} {b : ℤ} : modeq n a b ↔ n ∣ b - a := sorry

theorem modeq_of_dvd_of_modeq {n : ℤ} {m : ℤ} {a : ℤ} {b : ℤ} (d : m ∣ n) (h : modeq n a b) : modeq m a b :=
  iff.mpr modeq_iff_dvd (dvd_trans d (iff.mp modeq_iff_dvd h))

theorem modeq_mul_left' {n : ℤ} {a : ℤ} {b : ℤ} {c : ℤ} (hc : 0 ≤ c) (h : modeq n a b) : modeq (c * n) (c * a) (c * b) := sorry

theorem modeq_mul_right' {n : ℤ} {a : ℤ} {b : ℤ} {c : ℤ} (hc : 0 ≤ c) (h : modeq n a b) : modeq (n * c) (a * c) (b * c) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (modeq (n * c) (a * c) (b * c))) (mul_comm a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (modeq (n * c) (c * a) (b * c))) (mul_comm b c)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (modeq (n * c) (c * a) (c * b))) (mul_comm n c))) (modeq_mul_left' hc h)))

theorem modeq_add {n : ℤ} {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (h₁ : modeq n a b) (h₂ : modeq n c d) : modeq n (a + c) (b + d) := sorry

theorem modeq_add_cancel_left {n : ℤ} {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (h₁ : modeq n a b) (h₂ : modeq n (a + c) (b + d)) : modeq n c d := sorry

theorem modeq_add_cancel_right {n : ℤ} {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (h₁ : modeq n c d) (h₂ : modeq n (a + c) (b + d)) : modeq n a b :=
  modeq_add_cancel_left h₁
    (eq.mp (Eq._oldrec (Eq.refl (modeq n (c + a) (b + d))) (add_comm b d))
      (eq.mp (Eq._oldrec (Eq.refl (modeq n (a + c) (b + d))) (add_comm a c)) h₂))

theorem mod_modeq (a : ℤ) (n : ℤ) : modeq n (a % n) a :=
  mod_mod a n

theorem modeq_neg {n : ℤ} {a : ℤ} {b : ℤ} (h : modeq n a b) : modeq n (-a) (-b) := sorry

theorem modeq_sub {n : ℤ} {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (h₁ : modeq n a b) (h₂ : modeq n c d) : modeq n (a - c) (b - d) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (modeq n (a - c) (b - d))) (sub_eq_add_neg a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (modeq n (a + -c) (b - d))) (sub_eq_add_neg b d))) (modeq_add h₁ (modeq_neg h₂)))

theorem modeq_mul_left {n : ℤ} {a : ℤ} {b : ℤ} (c : ℤ) (h : modeq n a b) : modeq n (c * a) (c * b) := sorry

theorem modeq_mul_right {n : ℤ} {a : ℤ} {b : ℤ} (c : ℤ) (h : modeq n a b) : modeq n (a * c) (b * c) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (modeq n (a * c) (b * c))) (mul_comm a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (modeq n (c * a) (b * c))) (mul_comm b c))) (modeq_mul_left c h))

theorem modeq_mul {n : ℤ} {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (h₁ : modeq n a b) (h₂ : modeq n c d) : modeq n (a * c) (b * d) :=
  modeq.trans (modeq_mul_left a h₂) (modeq_mul_right d h₁)

theorem modeq_of_modeq_mul_left {n : ℤ} {a : ℤ} {b : ℤ} (m : ℤ) (h : modeq (m * n) a b) : modeq n a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (modeq n a b)) (propext modeq_iff_dvd)))
    (dvd.trans (dvd_mul_left n m) (eq.mp (Eq._oldrec (Eq.refl (modeq (m * n) a b)) (propext modeq_iff_dvd)) h))

theorem modeq_of_modeq_mul_right {n : ℤ} {a : ℤ} {b : ℤ} (m : ℤ) : modeq (n * m) a b → modeq n a b :=
  mul_comm m n ▸ modeq_of_modeq_mul_left m

theorem modeq_and_modeq_iff_modeq_mul {a : ℤ} {b : ℤ} {m : ℤ} {n : ℤ} (hmn : nat.coprime (nat_abs m) (nat_abs n)) : modeq m a b ∧ modeq n a b ↔ modeq (m * n) a b := sorry

theorem gcd_a_modeq (a : ℕ) (b : ℕ) : modeq (↑b) (↑a * nat.gcd_a a b) ↑(nat.gcd a b) := sorry

theorem modeq_add_fac {a : ℤ} {b : ℤ} {n : ℤ} (c : ℤ) (ha : modeq n a b) : modeq n (a + n * c) b := sorry

theorem mod_coprime {a : ℕ} {b : ℕ} (hab : nat.coprime a b) : ∃ (y : ℤ), modeq (↑b) (↑a * y) 1 := sorry

theorem exists_unique_equiv (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ (z : ℤ), 0 ≤ z ∧ z < b ∧ modeq b z a := sorry

theorem exists_unique_equiv_nat (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ (z : ℕ), ↑z < b ∧ modeq b (↑z) a := sorry

end modeq


@[simp] theorem mod_mul_right_mod (a : ℤ) (b : ℤ) (c : ℤ) : a % (b * c) % b = a % b :=
  modeq.modeq_of_modeq_mul_right c (modeq.mod_modeq a (b * c))

@[simp] theorem mod_mul_left_mod (a : ℤ) (b : ℤ) (c : ℤ) : a % (b * c) % c = a % c :=
  modeq.modeq_of_modeq_mul_left b (modeq.mod_modeq a (b * c))

