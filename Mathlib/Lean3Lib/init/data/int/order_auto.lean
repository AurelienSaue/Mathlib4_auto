/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The order relation on the integers.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.int.basic
import Mathlib.Lean3Lib.init.data.ordering.basic

namespace Mathlib

namespace int


def nonneg (a : ℤ) := int.cases_on a (fun (n : ℕ) => True) fun (n : ℕ) => False

protected def le (a : ℤ) (b : ℤ) := nonneg (b - a)

protected instance has_le : HasLessEq ℤ := { LessEq := int.le }

protected def lt (a : ℤ) (b : ℤ) := a + 1 ≤ b

protected instance has_lt : HasLess ℤ := { Less := int.lt }

def decidable_nonneg (a : ℤ) : Decidable (nonneg a) :=
  int.cases_on a (fun (a : ℕ) => decidable.true) fun (a : ℕ) => decidable.false

protected instance decidable_le (a : ℤ) (b : ℤ) : Decidable (a ≤ b) := decidable_nonneg (b - a)

protected instance decidable_lt (a : ℤ) (b : ℤ) : Decidable (a < b) :=
  decidable_nonneg (b - (a + 1))

theorem lt_iff_add_one_le (a : ℤ) (b : ℤ) : a < b ↔ a + 1 ≤ b := iff.refl (a < b)

theorem nonneg.elim {a : ℤ} : nonneg a → ∃ (n : ℕ), a = ↑n :=
  int.cases_on a (fun (n : ℕ) (H : nonneg (Int.ofNat n)) => exists.intro n rfl)
    fun (n' : ℕ) => false.elim

theorem nonneg_or_nonneg_neg (a : ℤ) : nonneg a ∨ nonneg (-a) :=
  int.cases_on a (fun (n : ℕ) => Or.inl trivial) fun (n : ℕ) => Or.inr trivial

theorem le.intro_sub {a : ℤ} {b : ℤ} {n : ℕ} (h : b - a = ↑n) : a ≤ b :=
  (fun (this : nonneg (b - a)) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (nonneg (b - a))) h)) trivial)

theorem le.intro {a : ℤ} {b : ℤ} {n : ℕ} (h : a + ↑n = b) : a ≤ b := sorry

theorem le.dest_sub {a : ℤ} {b : ℤ} (h : a ≤ b) : ∃ (n : ℕ), b - a = ↑n := nonneg.elim h

theorem le.dest {a : ℤ} {b : ℤ} (h : a ≤ b) : ∃ (n : ℕ), a + ↑n = b := sorry

theorem le.elim {a : ℤ} {b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ (n : ℕ), a + ↑n = b → P) : P :=
  exists.elim (le.dest h) h'

protected theorem le_total (a : ℤ) (b : ℤ) : a ≤ b ∨ b ≤ a := sorry

theorem coe_nat_le_coe_nat_of_le {m : ℕ} {n : ℕ} (h : m ≤ n) : ↑m ≤ ↑n := sorry

theorem le_of_coe_nat_le_coe_nat {m : ℕ} {n : ℕ} (h : ↑m ≤ ↑n) : m ≤ n :=
  le.elim h
    fun (k : ℕ) (hk : ↑m + ↑k = ↑n) =>
      (fun (this : m + k = n) => nat.le.intro this)
        (int.coe_nat_inj (Eq.trans (int.coe_nat_add m k) hk))

theorem coe_nat_le_coe_nat_iff (m : ℕ) (n : ℕ) : ↑m ≤ ↑n ↔ m ≤ n :=
  { mp := le_of_coe_nat_le_coe_nat, mpr := coe_nat_le_coe_nat_of_le }

theorem coe_zero_le (n : ℕ) : 0 ≤ ↑n := coe_nat_le_coe_nat_of_le (nat.zero_le n)

theorem eq_coe_of_zero_le {a : ℤ} (h : 0 ≤ a) : ∃ (n : ℕ), a = ↑n := sorry

theorem eq_succ_of_zero_lt {a : ℤ} (h : 0 < a) : ∃ (n : ℕ), a = ↑(Nat.succ n) := sorry

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + ↑(Nat.succ n) := sorry

theorem lt.intro {a : ℤ} {b : ℤ} {n : ℕ} (h : a + ↑(Nat.succ n) = b) : a < b := h ▸ lt_add_succ a n

theorem lt.dest {a : ℤ} {b : ℤ} (h : a < b) : ∃ (n : ℕ), a + ↑(Nat.succ n) = b := sorry

theorem lt.elim {a : ℤ} {b : ℤ} (h : a < b) {P : Prop} (h' : ∀ (n : ℕ), a + ↑(Nat.succ n) = b → P) :
    P :=
  exists.elim (lt.dest h) h'

theorem coe_nat_lt_coe_nat_iff (n : ℕ) (m : ℕ) : ↑n < ↑m ↔ n < m := sorry

theorem lt_of_coe_nat_lt_coe_nat {m : ℕ} {n : ℕ} (h : ↑m < ↑n) : m < n :=
  iff.mp (coe_nat_lt_coe_nat_iff m n) h

theorem coe_nat_lt_coe_nat_of_lt {m : ℕ} {n : ℕ} (h : m < n) : ↑m < ↑n :=
  iff.mpr (coe_nat_lt_coe_nat_iff m n) h

/- show that the integers form an ordered additive group -/

protected theorem le_refl (a : ℤ) : a ≤ a := le.intro (int.add_zero a)

protected theorem le_trans {a : ℤ} {b : ℤ} {c : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := sorry

protected theorem le_antisymm {a : ℤ} {b : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := sorry

protected theorem lt_irrefl (a : ℤ) : ¬a < a := sorry

protected theorem ne_of_lt {a : ℤ} {b : ℤ} (h : a < b) : a ≠ b :=
  fun (this : a = b) => absurd (eq.mp (Eq._oldrec (Eq.refl (a < b)) this) h) (int.lt_irrefl b)

theorem le_of_lt {a : ℤ} {b : ℤ} (h : a < b) : a ≤ b :=
  lt.elim h fun (n : ℕ) (hn : a + ↑(Nat.succ n) = b) => le.intro hn

protected theorem lt_iff_le_and_ne (a : ℤ) (b : ℤ) : a < b ↔ a ≤ b ∧ a ≠ b := sorry

theorem lt_succ (a : ℤ) : a < a + 1 := int.le_refl (a + 1)

protected theorem add_le_add_left {a : ℤ} {b : ℤ} (h : a ≤ b) (c : ℤ) : c + a ≤ c + b := sorry

protected theorem add_lt_add_left {a : ℤ} {b : ℤ} (h : a < b) (c : ℤ) : c + a < c + b := sorry

protected theorem mul_nonneg {a : ℤ} {b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := sorry

protected theorem mul_pos {a : ℤ} {b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := sorry

protected theorem zero_lt_one : 0 < 1 := trivial

protected theorem lt_iff_le_not_le {a : ℤ} {b : ℤ} : a < b ↔ a ≤ b ∧ ¬b ≤ a := sorry

protected instance linear_order : linear_order ℤ :=
  linear_order.mk int.le int.lt int.le_refl int.le_trans int.le_antisymm int.le_total
    int.decidable_le int.decidable_eq int.decidable_lt

theorem eq_nat_abs_of_zero_le {a : ℤ} (h : 0 ≤ a) : a = ↑(nat_abs a) := sorry

theorem le_nat_abs {a : ℤ} : a ≤ ↑(nat_abs a) := sorry

theorem neg_succ_lt_zero (n : ℕ) : Int.negSucc n < 0 := sorry

theorem eq_neg_succ_of_lt_zero {a : ℤ} : a < 0 → ∃ (n : ℕ), a = Int.negSucc n := sorry

/- int is an ordered add comm group -/

protected theorem eq_neg_of_eq_neg {a : ℤ} {b : ℤ} (h : a = -b) : b = -a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b = -a)) h))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b = --b)) (int.neg_neg b))) (Eq.refl b))

protected theorem neg_add_cancel_left (a : ℤ) (b : ℤ) : -a + (a + b) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-a + (a + b) = b)) (Eq.symm (int.add_assoc (-a) a b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-a + a + b = b)) (int.add_left_neg a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 + b = b)) (int.zero_add b))) (Eq.refl b)))

protected theorem add_neg_cancel_left (a : ℤ) (b : ℤ) : a + (-a + b) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + (-a + b) = b)) (Eq.symm (int.add_assoc a (-a) b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -a + b = b)) (int.add_right_neg a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 + b = b)) (int.zero_add b))) (Eq.refl b)))

protected theorem add_neg_cancel_right (a : ℤ) (b : ℤ) : a + b + -b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + b + -b = a)) (int.add_assoc a b (-b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + (b + -b) = a)) (int.add_right_neg b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a + 0 = a)) (int.add_zero a))) (Eq.refl a)))

protected theorem neg_add_cancel_right (a : ℤ) (b : ℤ) : a + -b + b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + -b + b = a)) (int.add_assoc a (-b) b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + (-b + b) = a)) (int.add_left_neg b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a + 0 = a)) (int.add_zero a))) (Eq.refl a)))

protected theorem sub_self (a : ℤ) : a - a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - a = 0)) int.sub_eq_add_neg))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -a = 0)) (int.add_right_neg a))) (Eq.refl 0))

protected theorem sub_eq_zero_of_eq {a : ℤ} {b : ℤ} (h : a = b) : a - b = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b = 0)) h))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b - b = 0)) (int.sub_self b))) (Eq.refl 0))

protected theorem eq_of_sub_eq_zero {a : ℤ} {b : ℤ} (h : a - b = 0) : a = b := sorry

protected theorem sub_eq_zero_iff_eq {a : ℤ} {b : ℤ} : a - b = 0 ↔ a = b :=
  { mp := int.eq_of_sub_eq_zero, mpr := int.sub_eq_zero_of_eq }

@[simp] protected theorem neg_eq_of_add_eq_zero {a : ℤ} {b : ℤ} (h : a + b = 0) : -a = b := sorry

protected theorem neg_mul_eq_neg_mul (a : ℤ) (b : ℤ) : -(a * b) = -a * b := sorry

protected theorem neg_mul_eq_mul_neg (a : ℤ) (b : ℤ) : -(a * b) = a * -b := sorry

@[simp] theorem neg_mul_eq_neg_mul_symm (a : ℤ) (b : ℤ) : -a * b = -(a * b) :=
  Eq.symm (int.neg_mul_eq_neg_mul a b)

@[simp] theorem mul_neg_eq_neg_mul_symm (a : ℤ) (b : ℤ) : a * -b = -(a * b) :=
  Eq.symm (int.neg_mul_eq_mul_neg a b)

protected theorem neg_mul_neg (a : ℤ) (b : ℤ) : -a * -b = a * b := sorry

protected theorem neg_mul_comm (a : ℤ) (b : ℤ) : -a * b = a * -b := sorry

protected theorem mul_sub (a : ℤ) (b : ℤ) (c : ℤ) : a * (b - c) = a * b - a * c := sorry

protected theorem sub_mul (a : ℤ) (b : ℤ) (c : ℤ) : (a - b) * c = a * c - b * c := sorry

protected theorem le_of_add_le_add_left {a : ℤ} {b : ℤ} {c : ℤ} (h : a + b ≤ a + c) : b ≤ c := sorry

protected theorem lt_of_add_lt_add_left {a : ℤ} {b : ℤ} {c : ℤ} (h : a + b < a + c) : b < c := sorry

protected theorem add_le_add_right {a : ℤ} {b : ℤ} (h : a ≤ b) (c : ℤ) : a + c ≤ b + c :=
  int.add_comm c a ▸ int.add_comm c b ▸ int.add_le_add_left h c

protected theorem add_lt_add_right {a : ℤ} {b : ℤ} (h : a < b) (c : ℤ) : a + c < b + c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + c < b + c)) (int.add_comm a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (c + a < b + c)) (int.add_comm b c)))
      (int.add_lt_add_left h c))

protected theorem add_le_add {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a + c ≤ b + d :=
  le_trans (int.add_le_add_right h₁ c) (int.add_le_add_left h₂ b)

protected theorem le_add_of_nonneg_right {a : ℤ} {b : ℤ} (h : b ≥ 0) : a ≤ a + b :=
  (fun (this : a + b ≥ a + 0) => eq.mp (Eq._oldrec (Eq.refl (a + b ≥ a + 0)) (int.add_zero a)) this)
    (int.add_le_add_left h a)

protected theorem le_add_of_nonneg_left {a : ℤ} {b : ℤ} (h : b ≥ 0) : a ≤ b + a :=
  (fun (this : 0 + a ≤ b + a) => eq.mp (Eq._oldrec (Eq.refl (0 + a ≤ b + a)) (int.zero_add a)) this)
    (int.add_le_add_right h a)

protected theorem add_lt_add {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (h₁ : a < b) (h₂ : c < d) :
    a + c < b + d :=
  lt_trans (int.add_lt_add_right h₁ c) (int.add_lt_add_left h₂ b)

protected theorem add_lt_add_of_le_of_lt {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (h₁ : a ≤ b) (h₂ : c < d) :
    a + c < b + d :=
  lt_of_le_of_lt (int.add_le_add_right h₁ c) (int.add_lt_add_left h₂ b)

protected theorem add_lt_add_of_lt_of_le {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (h₁ : a < b) (h₂ : c ≤ d) :
    a + c < b + d :=
  lt_of_lt_of_le (int.add_lt_add_right h₁ c) (int.add_le_add_left h₂ b)

protected theorem lt_add_of_pos_right (a : ℤ) {b : ℤ} (h : b > 0) : a < a + b :=
  (fun (this : a + 0 < a + b) => eq.mp (Eq._oldrec (Eq.refl (a + 0 < a + b)) (int.add_zero a)) this)
    (int.add_lt_add_left h a)

protected theorem lt_add_of_pos_left (a : ℤ) {b : ℤ} (h : b > 0) : a < b + a :=
  (fun (this : 0 + a < b + a) => eq.mp (Eq._oldrec (Eq.refl (0 + a < b + a)) (int.zero_add a)) this)
    (int.add_lt_add_right h a)

protected theorem le_of_add_le_add_right {a : ℤ} {b : ℤ} {c : ℤ} (h : a + b ≤ c + b) : a ≤ c :=
  sorry

protected theorem lt_of_add_lt_add_right {a : ℤ} {b : ℤ} {c : ℤ} (h : a + b < c + b) : a < c :=
  sorry

-- here we start using properties of zero.

protected theorem add_nonneg {a : ℤ} {b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  int.zero_add 0 ▸ int.add_le_add ha hb

protected theorem add_pos {a : ℤ} {b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  int.zero_add 0 ▸ int.add_lt_add ha hb

protected theorem add_pos_of_pos_of_nonneg {a : ℤ} {b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  int.zero_add 0 ▸ int.add_lt_add_of_lt_of_le ha hb

protected theorem add_pos_of_nonneg_of_pos {a : ℤ} {b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
  int.zero_add 0 ▸ int.add_lt_add_of_le_of_lt ha hb

protected theorem add_nonpos {a : ℤ} {b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
  int.zero_add 0 ▸ int.add_le_add ha hb

protected theorem add_neg {a : ℤ} {b : ℤ} (ha : a < 0) (hb : b < 0) : a + b < 0 :=
  int.zero_add 0 ▸ int.add_lt_add ha hb

protected theorem add_neg_of_neg_of_nonpos {a : ℤ} {b : ℤ} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
  int.zero_add 0 ▸ int.add_lt_add_of_lt_of_le ha hb

protected theorem add_neg_of_nonpos_of_neg {a : ℤ} {b : ℤ} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
  int.zero_add 0 ▸ int.add_lt_add_of_le_of_lt ha hb

protected theorem lt_add_of_le_of_pos {a : ℤ} {b : ℤ} {c : ℤ} (hbc : b ≤ c) (ha : 0 < a) :
    b < c + a :=
  int.add_zero b ▸ int.add_lt_add_of_le_of_lt hbc ha

protected theorem sub_add_cancel (a : ℤ) (b : ℤ) : a - b + b = a := int.neg_add_cancel_right a b

protected theorem add_sub_cancel (a : ℤ) (b : ℤ) : a + b - b = a := int.add_neg_cancel_right a b

protected theorem add_sub_assoc (a : ℤ) (b : ℤ) (c : ℤ) : a + b - c = a + (b - c) := sorry

protected theorem neg_le_neg {a : ℤ} {b : ℤ} (h : a ≤ b) : -b ≤ -a := sorry

protected theorem le_of_neg_le_neg {a : ℤ} {b : ℤ} (h : -b ≤ -a) : a ≤ b := sorry

protected theorem nonneg_of_neg_nonpos {a : ℤ} (h : -a ≤ 0) : 0 ≤ a :=
  (fun (this : -a ≤ -0) => int.le_of_neg_le_neg this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (-a ≤ -0)) int.neg_zero)) h)

protected theorem neg_nonpos_of_nonneg {a : ℤ} (h : 0 ≤ a) : -a ≤ 0 :=
  (fun (this : -a ≤ -0) => eq.mp (Eq._oldrec (Eq.refl (-a ≤ -0)) int.neg_zero) this)
    (int.neg_le_neg h)

protected theorem nonpos_of_neg_nonneg {a : ℤ} (h : 0 ≤ -a) : a ≤ 0 :=
  (fun (this : -0 ≤ -a) => int.le_of_neg_le_neg this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (-0 ≤ -a)) int.neg_zero)) h)

protected theorem neg_nonneg_of_nonpos {a : ℤ} (h : a ≤ 0) : 0 ≤ -a :=
  (fun (this : -0 ≤ -a) => eq.mp (Eq._oldrec (Eq.refl (-0 ≤ -a)) int.neg_zero) this)
    (int.neg_le_neg h)

protected theorem neg_lt_neg {a : ℤ} {b : ℤ} (h : a < b) : -b < -a := sorry

protected theorem lt_of_neg_lt_neg {a : ℤ} {b : ℤ} (h : -b < -a) : a < b :=
  int.neg_neg a ▸ int.neg_neg b ▸ int.neg_lt_neg h

protected theorem pos_of_neg_neg {a : ℤ} (h : -a < 0) : 0 < a :=
  (fun (this : -a < -0) => int.lt_of_neg_lt_neg this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (-a < -0)) int.neg_zero)) h)

protected theorem neg_neg_of_pos {a : ℤ} (h : 0 < a) : -a < 0 :=
  (fun (this : -a < -0) => eq.mp (Eq._oldrec (Eq.refl (-a < -0)) int.neg_zero) this)
    (int.neg_lt_neg h)

protected theorem neg_of_neg_pos {a : ℤ} (h : 0 < -a) : a < 0 :=
  (fun (this : -0 < -a) => int.lt_of_neg_lt_neg this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (-0 < -a)) int.neg_zero)) h)

protected theorem neg_pos_of_neg {a : ℤ} (h : a < 0) : 0 < -a :=
  (fun (this : -0 < -a) => eq.mp (Eq._oldrec (Eq.refl (-0 < -a)) int.neg_zero) this)
    (int.neg_lt_neg h)

protected theorem le_neg_of_le_neg {a : ℤ} {b : ℤ} (h : a ≤ -b) : b ≤ -a :=
  eq.mp (Eq._oldrec (Eq.refl ( --b ≤ -a)) (int.neg_neg b)) (int.neg_le_neg h)

protected theorem neg_le_of_neg_le {a : ℤ} {b : ℤ} (h : -a ≤ b) : -b ≤ a :=
  eq.mp (Eq._oldrec (Eq.refl (-b ≤ --a)) (int.neg_neg a)) (int.neg_le_neg h)

protected theorem lt_neg_of_lt_neg {a : ℤ} {b : ℤ} (h : a < -b) : b < -a :=
  eq.mp (Eq._oldrec (Eq.refl ( --b < -a)) (int.neg_neg b)) (int.neg_lt_neg h)

protected theorem neg_lt_of_neg_lt {a : ℤ} {b : ℤ} (h : -a < b) : -b < a :=
  eq.mp (Eq._oldrec (Eq.refl (-b < --a)) (int.neg_neg a)) (int.neg_lt_neg h)

protected theorem sub_nonneg_of_le {a : ℤ} {b : ℤ} (h : b ≤ a) : 0 ≤ a - b :=
  eq.mp (Eq._oldrec (Eq.refl (b + -b ≤ a + -b)) (int.add_right_neg b)) (int.add_le_add_right h (-b))

protected theorem le_of_sub_nonneg {a : ℤ} {b : ℤ} (h : 0 ≤ a - b) : b ≤ a :=
  eq.mp (Eq._oldrec (Eq.refl (0 + b ≤ a)) (int.zero_add b))
    (eq.mp (Eq._oldrec (Eq.refl (0 + b ≤ a - b + b)) (int.sub_add_cancel a b))
      (int.add_le_add_right h b))

protected theorem sub_nonpos_of_le {a : ℤ} {b : ℤ} (h : a ≤ b) : a - b ≤ 0 :=
  eq.mp (Eq._oldrec (Eq.refl (a + -b ≤ b + -b)) (int.add_right_neg b)) (int.add_le_add_right h (-b))

protected theorem le_of_sub_nonpos {a : ℤ} {b : ℤ} (h : a - b ≤ 0) : a ≤ b :=
  eq.mp (Eq._oldrec (Eq.refl (a ≤ 0 + b)) (int.zero_add b))
    (eq.mp (Eq._oldrec (Eq.refl (a - b + b ≤ 0 + b)) (int.sub_add_cancel a b))
      (int.add_le_add_right h b))

protected theorem sub_pos_of_lt {a : ℤ} {b : ℤ} (h : b < a) : 0 < a - b :=
  eq.mp (Eq._oldrec (Eq.refl (b + -b < a + -b)) (int.add_right_neg b)) (int.add_lt_add_right h (-b))

protected theorem lt_of_sub_pos {a : ℤ} {b : ℤ} (h : 0 < a - b) : b < a :=
  eq.mp (Eq._oldrec (Eq.refl (0 + b < a)) (int.zero_add b))
    (eq.mp (Eq._oldrec (Eq.refl (0 + b < a - b + b)) (int.sub_add_cancel a b))
      (int.add_lt_add_right h b))

protected theorem sub_neg_of_lt {a : ℤ} {b : ℤ} (h : a < b) : a - b < 0 :=
  eq.mp (Eq._oldrec (Eq.refl (a + -b < b + -b)) (int.add_right_neg b)) (int.add_lt_add_right h (-b))

protected theorem lt_of_sub_neg {a : ℤ} {b : ℤ} (h : a - b < 0) : a < b :=
  eq.mp (Eq._oldrec (Eq.refl (a < 0 + b)) (int.zero_add b))
    (eq.mp (Eq._oldrec (Eq.refl (a - b + b < 0 + b)) (int.sub_add_cancel a b))
      (int.add_lt_add_right h b))

protected theorem add_le_of_le_neg_add {a : ℤ} {b : ℤ} {c : ℤ} (h : b ≤ -a + c) : a + b ≤ c :=
  eq.mp (Eq._oldrec (Eq.refl (a + b ≤ a + (-a + c))) (int.add_neg_cancel_left a c))
    (int.add_le_add_left h a)

protected theorem le_neg_add_of_add_le {a : ℤ} {b : ℤ} {c : ℤ} (h : a + b ≤ c) : b ≤ -a + c :=
  eq.mp (Eq._oldrec (Eq.refl (-a + (a + b) ≤ -a + c)) (int.neg_add_cancel_left a b))
    (int.add_le_add_left h (-a))

protected theorem add_le_of_le_sub_left {a : ℤ} {b : ℤ} {c : ℤ} (h : b ≤ c - a) : a + b ≤ c :=
  eq.mp (Eq._oldrec (Eq.refl (a + b ≤ c + a - a)) (int.add_sub_cancel c a))
    (eq.mp (Eq._oldrec (Eq.refl (a + b ≤ a + c - a)) (int.add_comm a c))
      (eq.mp (Eq._oldrec (Eq.refl (a + b ≤ a + (c - a))) (Eq.symm (int.add_sub_assoc a c a)))
        (int.add_le_add_left h a)))

protected theorem le_sub_left_of_add_le {a : ℤ} {b : ℤ} {c : ℤ} (h : a + b ≤ c) : b ≤ c - a :=
  eq.mp (Eq._oldrec (Eq.refl (b + a + -a ≤ c + -a)) (int.add_neg_cancel_right b a))
    (eq.mp (Eq._oldrec (Eq.refl (a + b + -a ≤ c + -a)) (int.add_comm a b))
      (int.add_le_add_right h (-a)))

protected theorem add_le_of_le_sub_right {a : ℤ} {b : ℤ} {c : ℤ} (h : a ≤ c - b) : a + b ≤ c :=
  eq.mp (Eq._oldrec (Eq.refl (a + b ≤ c - b + b)) (int.sub_add_cancel c b))
    (int.add_le_add_right h b)

protected theorem le_sub_right_of_add_le {a : ℤ} {b : ℤ} {c : ℤ} (h : a + b ≤ c) : a ≤ c - b :=
  eq.mp (Eq._oldrec (Eq.refl (a + b + -b ≤ c + -b)) (int.add_neg_cancel_right a b))
    (int.add_le_add_right h (-b))

protected theorem le_add_of_neg_add_le {a : ℤ} {b : ℤ} {c : ℤ} (h : -b + a ≤ c) : a ≤ b + c :=
  eq.mp (Eq._oldrec (Eq.refl (b + (-b + a) ≤ b + c)) (int.add_neg_cancel_left b a))
    (int.add_le_add_left h b)

protected theorem neg_add_le_of_le_add {a : ℤ} {b : ℤ} {c : ℤ} (h : a ≤ b + c) : -b + a ≤ c :=
  eq.mp (Eq._oldrec (Eq.refl (-b + a ≤ -b + (b + c))) (int.neg_add_cancel_left b c))
    (int.add_le_add_left h (-b))

protected theorem le_add_of_sub_left_le {a : ℤ} {b : ℤ} {c : ℤ} (h : a - b ≤ c) : a ≤ b + c :=
  eq.mp (Eq._oldrec (Eq.refl (a ≤ c + b)) (int.add_comm c b))
    (eq.mp (Eq._oldrec (Eq.refl (a - b + b ≤ c + b)) (int.sub_add_cancel a b))
      (int.add_le_add_right h b))

protected theorem sub_left_le_of_le_add {a : ℤ} {b : ℤ} {c : ℤ} (h : a ≤ b + c) : a - b ≤ c :=
  eq.mp (Eq._oldrec (Eq.refl (a + -b ≤ c + b + -b)) (int.add_neg_cancel_right c b))
    (eq.mp (Eq._oldrec (Eq.refl (a + -b ≤ b + c + -b)) (int.add_comm b c))
      (int.add_le_add_right h (-b)))

protected theorem le_add_of_sub_right_le {a : ℤ} {b : ℤ} {c : ℤ} (h : a - c ≤ b) : a ≤ b + c :=
  eq.mp (Eq._oldrec (Eq.refl (a - c + c ≤ b + c)) (int.sub_add_cancel a c))
    (int.add_le_add_right h c)

protected theorem sub_right_le_of_le_add {a : ℤ} {b : ℤ} {c : ℤ} (h : a ≤ b + c) : a - c ≤ b :=
  eq.mp (Eq._oldrec (Eq.refl (a + -c ≤ b + c + -c)) (int.add_neg_cancel_right b c))
    (int.add_le_add_right h (-c))

protected theorem le_add_of_neg_add_le_left {a : ℤ} {b : ℤ} {c : ℤ} (h : -b + a ≤ c) : a ≤ b + c :=
  int.le_add_of_sub_left_le (eq.mp (Eq._oldrec (Eq.refl (-b + a ≤ c)) (int.add_comm (-b) a)) h)

protected theorem neg_add_le_left_of_le_add {a : ℤ} {b : ℤ} {c : ℤ} (h : a ≤ b + c) : -b + a ≤ c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-b + a ≤ c)) (int.add_comm (-b) a)))
    (int.sub_left_le_of_le_add h)

protected theorem le_add_of_neg_add_le_right {a : ℤ} {b : ℤ} {c : ℤ} (h : -c + a ≤ b) : a ≤ b + c :=
  int.le_add_of_sub_right_le (eq.mp (Eq._oldrec (Eq.refl (-c + a ≤ b)) (int.add_comm (-c) a)) h)

protected theorem neg_add_le_right_of_le_add {a : ℤ} {b : ℤ} {c : ℤ} (h : a ≤ b + c) : -c + a ≤ b :=
  int.neg_add_le_left_of_le_add (eq.mp (Eq._oldrec (Eq.refl (a ≤ b + c)) (int.add_comm b c)) h)

protected theorem le_add_of_neg_le_sub_left {a : ℤ} {b : ℤ} {c : ℤ} (h : -a ≤ b - c) : c ≤ a + b :=
  int.le_add_of_neg_add_le_left (int.add_le_of_le_sub_right h)

protected theorem neg_le_sub_left_of_le_add {a : ℤ} {b : ℤ} {c : ℤ} (h : c ≤ a + b) : -a ≤ b - c :=
  eq.mp (Eq._oldrec (Eq.refl (-a ≤ -c + b)) (int.add_comm (-c) b))
    (int.le_neg_add_of_add_le (int.sub_left_le_of_le_add h))

protected theorem le_add_of_neg_le_sub_right {a : ℤ} {b : ℤ} {c : ℤ} (h : -b ≤ a - c) : c ≤ a + b :=
  int.le_add_of_sub_right_le (int.add_le_of_le_sub_left h)

protected theorem neg_le_sub_right_of_le_add {a : ℤ} {b : ℤ} {c : ℤ} (h : c ≤ a + b) : -b ≤ a - c :=
  int.le_sub_left_of_add_le (int.sub_right_le_of_le_add h)

protected theorem sub_le_of_sub_le {a : ℤ} {b : ℤ} {c : ℤ} (h : a - b ≤ c) : a - c ≤ b :=
  int.sub_left_le_of_le_add (int.le_add_of_sub_right_le h)

protected theorem sub_le_sub_left {a : ℤ} {b : ℤ} (h : a ≤ b) (c : ℤ) : c - b ≤ c - a :=
  int.add_le_add_left (int.neg_le_neg h) c

protected theorem sub_le_sub_right {a : ℤ} {b : ℤ} (h : a ≤ b) (c : ℤ) : a - c ≤ b - c :=
  int.add_le_add_right h (-c)

protected theorem sub_le_sub {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (hab : a ≤ b) (hcd : c ≤ d) :
    a - d ≤ b - c :=
  int.add_le_add hab (int.neg_le_neg hcd)

protected theorem add_lt_of_lt_neg_add {a : ℤ} {b : ℤ} {c : ℤ} (h : b < -a + c) : a + b < c :=
  eq.mp (Eq._oldrec (Eq.refl (a + b < a + (-a + c))) (int.add_neg_cancel_left a c))
    (int.add_lt_add_left h a)

protected theorem lt_neg_add_of_add_lt {a : ℤ} {b : ℤ} {c : ℤ} (h : a + b < c) : b < -a + c :=
  eq.mp (Eq._oldrec (Eq.refl (-a + (a + b) < -a + c)) (int.neg_add_cancel_left a b))
    (int.add_lt_add_left h (-a))

protected theorem add_lt_of_lt_sub_left {a : ℤ} {b : ℤ} {c : ℤ} (h : b < c - a) : a + b < c :=
  eq.mp (Eq._oldrec (Eq.refl (a + b < c + a - a)) (int.add_sub_cancel c a))
    (eq.mp (Eq._oldrec (Eq.refl (a + b < a + c - a)) (int.add_comm a c))
      (eq.mp (Eq._oldrec (Eq.refl (a + b < a + (c - a))) (Eq.symm (int.add_sub_assoc a c a)))
        (int.add_lt_add_left h a)))

protected theorem lt_sub_left_of_add_lt {a : ℤ} {b : ℤ} {c : ℤ} (h : a + b < c) : b < c - a :=
  eq.mp (Eq._oldrec (Eq.refl (b + a + -a < c + -a)) (int.add_neg_cancel_right b a))
    (eq.mp (Eq._oldrec (Eq.refl (a + b + -a < c + -a)) (int.add_comm a b))
      (int.add_lt_add_right h (-a)))

protected theorem add_lt_of_lt_sub_right {a : ℤ} {b : ℤ} {c : ℤ} (h : a < c - b) : a + b < c :=
  eq.mp (Eq._oldrec (Eq.refl (a + b < c - b + b)) (int.sub_add_cancel c b))
    (int.add_lt_add_right h b)

protected theorem lt_sub_right_of_add_lt {a : ℤ} {b : ℤ} {c : ℤ} (h : a + b < c) : a < c - b :=
  eq.mp (Eq._oldrec (Eq.refl (a + b + -b < c + -b)) (int.add_neg_cancel_right a b))
    (int.add_lt_add_right h (-b))

protected theorem lt_add_of_neg_add_lt {a : ℤ} {b : ℤ} {c : ℤ} (h : -b + a < c) : a < b + c :=
  eq.mp (Eq._oldrec (Eq.refl (b + (-b + a) < b + c)) (int.add_neg_cancel_left b a))
    (int.add_lt_add_left h b)

protected theorem neg_add_lt_of_lt_add {a : ℤ} {b : ℤ} {c : ℤ} (h : a < b + c) : -b + a < c :=
  eq.mp (Eq._oldrec (Eq.refl (-b + a < -b + (b + c))) (int.neg_add_cancel_left b c))
    (int.add_lt_add_left h (-b))

protected theorem lt_add_of_sub_left_lt {a : ℤ} {b : ℤ} {c : ℤ} (h : a - b < c) : a < b + c :=
  eq.mp (Eq._oldrec (Eq.refl (a < c + b)) (int.add_comm c b))
    (eq.mp (Eq._oldrec (Eq.refl (a - b + b < c + b)) (int.sub_add_cancel a b))
      (int.add_lt_add_right h b))

protected theorem sub_left_lt_of_lt_add {a : ℤ} {b : ℤ} {c : ℤ} (h : a < b + c) : a - b < c :=
  eq.mp (Eq._oldrec (Eq.refl (a + -b < c + b + -b)) (int.add_neg_cancel_right c b))
    (eq.mp (Eq._oldrec (Eq.refl (a + -b < b + c + -b)) (int.add_comm b c))
      (int.add_lt_add_right h (-b)))

protected theorem lt_add_of_sub_right_lt {a : ℤ} {b : ℤ} {c : ℤ} (h : a - c < b) : a < b + c :=
  eq.mp (Eq._oldrec (Eq.refl (a - c + c < b + c)) (int.sub_add_cancel a c))
    (int.add_lt_add_right h c)

protected theorem sub_right_lt_of_lt_add {a : ℤ} {b : ℤ} {c : ℤ} (h : a < b + c) : a - c < b :=
  eq.mp (Eq._oldrec (Eq.refl (a + -c < b + c + -c)) (int.add_neg_cancel_right b c))
    (int.add_lt_add_right h (-c))

protected theorem lt_add_of_neg_add_lt_left {a : ℤ} {b : ℤ} {c : ℤ} (h : -b + a < c) : a < b + c :=
  int.lt_add_of_sub_left_lt (eq.mp (Eq._oldrec (Eq.refl (-b + a < c)) (int.add_comm (-b) a)) h)

protected theorem neg_add_lt_left_of_lt_add {a : ℤ} {b : ℤ} {c : ℤ} (h : a < b + c) : -b + a < c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-b + a < c)) (int.add_comm (-b) a)))
    (int.sub_left_lt_of_lt_add h)

protected theorem lt_add_of_neg_add_lt_right {a : ℤ} {b : ℤ} {c : ℤ} (h : -c + a < b) : a < b + c :=
  int.lt_add_of_sub_right_lt (eq.mp (Eq._oldrec (Eq.refl (-c + a < b)) (int.add_comm (-c) a)) h)

protected theorem neg_add_lt_right_of_lt_add {a : ℤ} {b : ℤ} {c : ℤ} (h : a < b + c) : -c + a < b :=
  int.neg_add_lt_left_of_lt_add (eq.mp (Eq._oldrec (Eq.refl (a < b + c)) (int.add_comm b c)) h)

protected theorem lt_add_of_neg_lt_sub_left {a : ℤ} {b : ℤ} {c : ℤ} (h : -a < b - c) : c < a + b :=
  int.lt_add_of_neg_add_lt_left (int.add_lt_of_lt_sub_right h)

protected theorem neg_lt_sub_left_of_lt_add {a : ℤ} {b : ℤ} {c : ℤ} (h : c < a + b) : -a < b - c :=
  eq.mp (Eq._oldrec (Eq.refl (-a < -c + b)) (int.add_comm (-c) b))
    (int.lt_neg_add_of_add_lt (int.sub_left_lt_of_lt_add h))

protected theorem lt_add_of_neg_lt_sub_right {a : ℤ} {b : ℤ} {c : ℤ} (h : -b < a - c) : c < a + b :=
  int.lt_add_of_sub_right_lt (int.add_lt_of_lt_sub_left h)

protected theorem neg_lt_sub_right_of_lt_add {a : ℤ} {b : ℤ} {c : ℤ} (h : c < a + b) : -b < a - c :=
  int.lt_sub_left_of_add_lt (int.sub_right_lt_of_lt_add h)

protected theorem sub_lt_of_sub_lt {a : ℤ} {b : ℤ} {c : ℤ} (h : a - b < c) : a - c < b :=
  int.sub_left_lt_of_lt_add (int.lt_add_of_sub_right_lt h)

protected theorem sub_lt_sub_left {a : ℤ} {b : ℤ} (h : a < b) (c : ℤ) : c - b < c - a :=
  int.add_lt_add_left (int.neg_lt_neg h) c

protected theorem sub_lt_sub_right {a : ℤ} {b : ℤ} (h : a < b) (c : ℤ) : a - c < b - c :=
  int.add_lt_add_right h (-c)

protected theorem sub_lt_sub {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (hab : a < b) (hcd : c < d) :
    a - d < b - c :=
  int.add_lt_add hab (int.neg_lt_neg hcd)

protected theorem sub_lt_sub_of_le_of_lt {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (hab : a ≤ b)
    (hcd : c < d) : a - d < b - c :=
  int.add_lt_add_of_le_of_lt hab (int.neg_lt_neg hcd)

protected theorem sub_lt_sub_of_lt_of_le {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (hab : a < b)
    (hcd : c ≤ d) : a - d < b - c :=
  int.add_lt_add_of_lt_of_le hab (int.neg_le_neg hcd)

protected theorem sub_le_self (a : ℤ) {b : ℤ} (h : b ≥ 0) : a - b ≤ a :=
  trans_rel_left LessEq
    (trans_rel_right LessEq rfl (int.add_le_add_left (int.neg_nonpos_of_nonneg h) a))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + 0 = a)) (int.add_zero a))) (Eq.refl a))

protected theorem sub_lt_self (a : ℤ) {b : ℤ} (h : b > 0) : a - b < a :=
  trans_rel_left Less (trans_rel_right Less rfl (int.add_lt_add_left (int.neg_neg_of_pos h) a))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + 0 = a)) (int.add_zero a))) (Eq.refl a))

protected theorem add_le_add_three {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} {e : ℤ} {f : ℤ} (h₁ : a ≤ d)
    (h₂ : b ≤ e) (h₃ : c ≤ f) : a + b + c ≤ d + e + f :=
  le_trans (int.add_le_add (int.add_le_add h₁ h₂) h₃) (le_refl (d + e + f))

/- missing facts -/

protected theorem mul_lt_mul_of_pos_left {a : ℤ} {b : ℤ} {c : ℤ} (h₁ : a < b) (h₂ : 0 < c) :
    c * a < c * b :=
  sorry

protected theorem mul_lt_mul_of_pos_right {a : ℤ} {b : ℤ} {c : ℤ} (h₁ : a < b) (h₂ : 0 < c) :
    a * c < b * c :=
  sorry

protected theorem mul_le_mul_of_nonneg_left {a : ℤ} {b : ℤ} {c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) :
    c * a ≤ c * b :=
  sorry

protected theorem mul_le_mul_of_nonneg_right {a : ℤ} {b : ℤ} {c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) :
    a * c ≤ b * c :=
  sorry

-- TODO: there are four variations, depending on which variables we assume to be nonneg

protected theorem mul_le_mul {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (hac : a ≤ c) (hbd : b ≤ d)
    (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) : a * b ≤ c * d :=
  le_trans (int.mul_le_mul_of_nonneg_right hac nn_b) (int.mul_le_mul_of_nonneg_left hbd nn_c)

protected theorem mul_nonpos_of_nonneg_of_nonpos {a : ℤ} {b : ℤ} (ha : a ≥ 0) (hb : b ≤ 0) :
    a * b ≤ 0 :=
  (fun (h : a * b ≤ a * 0) => eq.mp (Eq._oldrec (Eq.refl (a * b ≤ a * 0)) (int.mul_zero a)) h)
    (int.mul_le_mul_of_nonneg_left hb ha)

protected theorem mul_nonpos_of_nonpos_of_nonneg {a : ℤ} {b : ℤ} (ha : a ≤ 0) (hb : b ≥ 0) :
    a * b ≤ 0 :=
  (fun (h : a * b ≤ 0 * b) => eq.mp (Eq._oldrec (Eq.refl (a * b ≤ 0 * b)) (int.zero_mul b)) h)
    (int.mul_le_mul_of_nonneg_right ha hb)

protected theorem mul_lt_mul {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (hac : a < c) (hbd : b ≤ d)
    (pos_b : 0 < b) (nn_c : 0 ≤ c) : a * b < c * d :=
  lt_of_lt_of_le (int.mul_lt_mul_of_pos_right hac pos_b) (int.mul_le_mul_of_nonneg_left hbd nn_c)

protected theorem mul_lt_mul' {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (h1 : a ≤ c) (h2 : b < d) (h3 : b ≥ 0)
    (h4 : c > 0) : a * b < c * d :=
  lt_of_le_of_lt (int.mul_le_mul_of_nonneg_right h1 h3) (int.mul_lt_mul_of_pos_left h2 h4)

protected theorem mul_neg_of_pos_of_neg {a : ℤ} {b : ℤ} (ha : a > 0) (hb : b < 0) : a * b < 0 :=
  (fun (h : a * b < a * 0) => eq.mp (Eq._oldrec (Eq.refl (a * b < a * 0)) (int.mul_zero a)) h)
    (int.mul_lt_mul_of_pos_left hb ha)

protected theorem mul_neg_of_neg_of_pos {a : ℤ} {b : ℤ} (ha : a < 0) (hb : b > 0) : a * b < 0 :=
  (fun (h : a * b < 0 * b) => eq.mp (Eq._oldrec (Eq.refl (a * b < 0 * b)) (int.zero_mul b)) h)
    (int.mul_lt_mul_of_pos_right ha hb)

protected theorem mul_le_mul_of_nonpos_right {a : ℤ} {b : ℤ} {c : ℤ} (h : b ≤ a) (hc : c ≤ 0) :
    a * c ≤ b * c :=
  sorry

protected theorem mul_nonneg_of_nonpos_of_nonpos {a : ℤ} {b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) :
    0 ≤ a * b :=
  (fun (this : 0 * b ≤ a * b) => eq.mp (Eq._oldrec (Eq.refl (0 * b ≤ a * b)) (int.zero_mul b)) this)
    (int.mul_le_mul_of_nonpos_right ha hb)

protected theorem mul_lt_mul_of_neg_left {a : ℤ} {b : ℤ} {c : ℤ} (h : b < a) (hc : c < 0) :
    c * a < c * b :=
  sorry

protected theorem mul_lt_mul_of_neg_right {a : ℤ} {b : ℤ} {c : ℤ} (h : b < a) (hc : c < 0) :
    a * c < b * c :=
  sorry

protected theorem mul_pos_of_neg_of_neg {a : ℤ} {b : ℤ} (ha : a < 0) (hb : b < 0) : 0 < a * b :=
  (fun (this : 0 * b < a * b) => eq.mp (Eq._oldrec (Eq.refl (0 * b < a * b)) (int.zero_mul b)) this)
    (int.mul_lt_mul_of_neg_right ha hb)

protected theorem mul_self_le_mul_self {a : ℤ} {b : ℤ} (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
  int.mul_le_mul h2 h2 h1 (le_trans h1 h2)

protected theorem mul_self_lt_mul_self {a : ℤ} {b : ℤ} (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
  int.mul_lt_mul' (le_of_lt h2) h2 h1 (lt_of_le_of_lt h1 h2)

/- more facts specific to int -/

theorem of_nat_nonneg (n : ℕ) : 0 ≤ Int.ofNat n := trivial

theorem coe_succ_pos (n : ℕ) : ↑(Nat.succ n) > 0 := coe_nat_lt_coe_nat_of_lt (nat.succ_pos n)

theorem exists_eq_neg_of_nat {a : ℤ} (H : a ≤ 0) : ∃ (n : ℕ), a = -↑n := sorry

theorem nat_abs_of_nonneg {a : ℤ} (H : a ≥ 0) : ↑(nat_abs a) = a := sorry

theorem of_nat_nat_abs_of_nonpos {a : ℤ} (H : a ≤ 0) : ↑(nat_abs a) = -a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(nat_abs a) = -a)) (Eq.symm (nat_abs_neg a))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (↑(nat_abs (-a)) = -a))
          (nat_abs_of_nonneg (int.neg_nonneg_of_nonpos H))))
      (Eq.refl (-a)))

theorem lt_of_add_one_le {a : ℤ} {b : ℤ} (H : a + 1 ≤ b) : a < b := H

theorem add_one_le_of_lt {a : ℤ} {b : ℤ} (H : a < b) : a + 1 ≤ b := H

theorem lt_add_one_of_le {a : ℤ} {b : ℤ} (H : a ≤ b) : a < b + 1 := int.add_le_add_right H 1

theorem le_of_lt_add_one {a : ℤ} {b : ℤ} (H : a < b + 1) : a ≤ b := int.le_of_add_le_add_right H

theorem sub_one_le_of_lt {a : ℤ} {b : ℤ} (H : a ≤ b) : a - 1 < b :=
  int.sub_right_lt_of_lt_add (lt_add_one_of_le H)

theorem lt_of_sub_one_le {a : ℤ} {b : ℤ} (H : a - 1 < b) : a ≤ b :=
  le_of_lt_add_one (int.lt_add_of_sub_right_lt H)

theorem le_sub_one_of_lt {a : ℤ} {b : ℤ} (H : a < b) : a ≤ b - 1 := int.le_sub_right_of_add_le H

theorem lt_of_le_sub_one {a : ℤ} {b : ℤ} (H : a ≤ b - 1) : a < b := int.add_le_of_le_sub_right H

theorem sign_of_succ (n : ℕ) : sign ↑(Nat.succ n) = 1 := rfl

theorem sign_eq_one_of_pos {a : ℤ} (h : 0 < a) : sign a = 1 := sorry

theorem sign_eq_neg_one_of_neg {a : ℤ} (h : a < 0) : sign a = -1 := sorry

theorem eq_zero_of_sign_eq_zero {a : ℤ} : sign a = 0 → a = 0 := sorry

theorem pos_of_sign_eq_one {a : ℤ} : sign a = 1 → 0 < a := sorry

theorem neg_of_sign_eq_neg_one {a : ℤ} : sign a = -1 → a < 0 := sorry

theorem sign_eq_one_iff_pos (a : ℤ) : sign a = 1 ↔ 0 < a :=
  { mp := pos_of_sign_eq_one, mpr := sign_eq_one_of_pos }

theorem sign_eq_neg_one_iff_neg (a : ℤ) : sign a = -1 ↔ a < 0 :=
  { mp := neg_of_sign_eq_neg_one, mpr := sign_eq_neg_one_of_neg }

theorem sign_eq_zero_iff_zero (a : ℤ) : sign a = 0 ↔ a = 0 := sorry

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {a : ℤ} {b : ℤ} (h : a * b = 0) :
    a = 0 ∨ b = 0 :=
  sorry

protected theorem eq_of_mul_eq_mul_right {a : ℤ} {b : ℤ} {c : ℤ} (ha : a ≠ 0) (h : b * a = c * a) :
    b = c :=
  sorry

protected theorem eq_of_mul_eq_mul_left {a : ℤ} {b : ℤ} {c : ℤ} (ha : a ≠ 0) (h : a * b = a * c) :
    b = c :=
  sorry

theorem eq_one_of_mul_eq_self_left {a : ℤ} {b : ℤ} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
  int.eq_of_mul_eq_mul_right Hpos
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a = 1 * a)) (int.one_mul a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b * a = a)) H)) (Eq.refl a)))

theorem eq_one_of_mul_eq_self_right {a : ℤ} {b : ℤ} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
  int.eq_of_mul_eq_mul_left Hpos
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a = b * 1)) (int.mul_one b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b * a = b)) H)) (Eq.refl b)))

end Mathlib