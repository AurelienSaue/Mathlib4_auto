/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.nat.basic
import Mathlib.Lean3Lib.init.data.nat.div
import Mathlib.Lean3Lib.init.meta.default
import Mathlib.Lean3Lib.init.algebra.functions

universes u 

namespace Mathlib

namespace nat


protected theorem add_comm (n : ℕ) (m : ℕ) : n + m = m + n := sorry

protected theorem add_assoc (n : ℕ) (m : ℕ) (k : ℕ) : n + m + k = n + (m + k) := sorry

protected theorem add_left_comm (n : ℕ) (m : ℕ) (k : ℕ) : n + (m + k) = m + (n + k) :=
  left_comm Nat.add nat.add_comm nat.add_assoc

protected theorem add_left_cancel {n : ℕ} {m : ℕ} {k : ℕ} : n + m = n + k → m = k := sorry

protected theorem add_right_cancel {n : ℕ} {m : ℕ} {k : ℕ} (h : n + m = k + m) : n = k :=
  (fun (this : m + n = m + k) => nat.add_left_cancel this)
    (eq.mp (Eq._oldrec (Eq.refl (m + n = k + m)) (nat.add_comm k m))
      (eq.mp (Eq._oldrec (Eq.refl (n + m = k + m)) (nat.add_comm n m)) h))

theorem succ_ne_zero (n : ℕ) : Nat.succ n ≠ 0 := fun (h : Nat.succ n = 0) => nat.no_confusion h

theorem succ_ne_self (n : ℕ) : Nat.succ n ≠ n := sorry

protected theorem one_ne_zero : 1 ≠ 0 := fun (h : 1 = 0) => nat.no_confusion h

protected theorem zero_ne_one : 0 ≠ 1 := fun (h : 0 = 1) => nat.no_confusion h

theorem eq_zero_of_add_eq_zero_right {n : ℕ} {m : ℕ} : n + m = 0 → n = 0 := sorry

theorem eq_zero_of_add_eq_zero_left {n : ℕ} {m : ℕ} (h : n + m = 0) : m = 0 :=
  eq_zero_of_add_eq_zero_right (nat.add_comm n m ▸ h)

@[simp] theorem pred_zero : Nat.pred 0 = 0 := rfl

@[simp] theorem pred_succ (n : ℕ) : Nat.pred (Nat.succ n) = n := rfl

protected theorem mul_zero (n : ℕ) : n * 0 = 0 := rfl

theorem mul_succ (n : ℕ) (m : ℕ) : n * Nat.succ m = n * m + n := rfl

protected theorem zero_mul (n : ℕ) : 0 * n = 0 := sorry

theorem succ_mul (n : ℕ) (m : ℕ) : Nat.succ n * m = n * m + m := sorry

protected theorem right_distrib (n : ℕ) (m : ℕ) (k : ℕ) : (n + m) * k = n * k + m * k := sorry

protected theorem left_distrib (n : ℕ) (m : ℕ) (k : ℕ) : n * (m + k) = n * m + n * k := sorry

protected theorem mul_comm (n : ℕ) (m : ℕ) : n * m = m * n := sorry

protected theorem mul_assoc (n : ℕ) (m : ℕ) (k : ℕ) : n * m * k = n * (m * k) := sorry

protected theorem mul_one (n : ℕ) : n * 1 = n := nat.zero_add

protected theorem one_mul (n : ℕ) : 1 * n = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 * n = n)) (nat.mul_comm 1 n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n * 1 = n)) (nat.mul_one n))) (Eq.refl n))

/- properties of inequality -/

protected theorem le_of_eq {n : ℕ} {m : ℕ} (p : n = m) : n ≤ m := p ▸ less_than_or_equal.refl

theorem le_succ_of_le {n : ℕ} {m : ℕ} (h : n ≤ m) : n ≤ Nat.succ m := nat.le_trans h (le_succ m)

theorem le_of_succ_le {n : ℕ} {m : ℕ} (h : Nat.succ n ≤ m) : n ≤ m := nat.le_trans (le_succ n) h

protected theorem le_of_lt {n : ℕ} {m : ℕ} (h : n < m) : n ≤ m := le_of_succ_le h

def lt.step {n : ℕ} {m : ℕ} : n < m → n < Nat.succ m := less_than_or_equal.step

theorem eq_zero_or_pos (n : ℕ) : n = 0 ∨ n > 0 :=
  nat.cases_on n (Or.inl rfl) fun (n : ℕ) => Or.inr (succ_pos n)

protected theorem pos_of_ne_zero {n : ℕ} : n ≠ 0 → n > 0 := or.resolve_left (eq_zero_or_pos n)

protected theorem lt_trans {n : ℕ} {m : ℕ} {k : ℕ} (h₁ : n < m) : m < k → n < k :=
  nat.le_trans (less_than_or_equal.step h₁)

protected theorem lt_of_le_of_lt {n : ℕ} {m : ℕ} {k : ℕ} (h₁ : n ≤ m) : m < k → n < k :=
  nat.le_trans (succ_le_succ h₁)

def lt.base (n : ℕ) : n < Nat.succ n := nat.le_refl (Nat.succ n)

theorem lt_succ_self (n : ℕ) : n < Nat.succ n := lt.base n

protected theorem le_antisymm {n : ℕ} {m : ℕ} (h₁ : n ≤ m) : m ≤ n → n = m :=
  less_than_or_equal.cases_on h₁ (fun (a : n ≤ n) => rfl)
    fun (a : ℕ) (b : less_than_or_equal n a) (c : Nat.succ a ≤ n) =>
      absurd (nat.lt_of_le_of_lt b c) (nat.lt_irrefl n)

protected theorem lt_or_ge (a : ℕ) (b : ℕ) : a < b ∨ a ≥ b := sorry

protected theorem le_total {m : ℕ} {n : ℕ} : m ≤ n ∨ n ≤ m :=
  or.imp_left nat.le_of_lt (nat.lt_or_ge m n)

protected theorem lt_of_le_and_ne {m : ℕ} {n : ℕ} (h1 : m ≤ n) : m ≠ n → m < n :=
  or.resolve_right (or.swap (nat.eq_or_lt_of_le h1))

protected theorem lt_iff_le_not_le {m : ℕ} {n : ℕ} : m < n ↔ m ≤ n ∧ ¬n ≤ m := sorry

protected instance linear_order : linear_order ℕ :=
  linear_order.mk less_than_or_equal nat.lt nat.le_refl nat.le_trans nat.le_antisymm nat.le_total
    nat.decidable_le nat.decidable_eq nat.decidable_lt

theorem eq_zero_of_le_zero {n : ℕ} (h : n ≤ 0) : n = 0 := le_antisymm h (zero_le n)

theorem succ_lt_succ {a : ℕ} {b : ℕ} : a < b → Nat.succ a < Nat.succ b := succ_le_succ

theorem lt_of_succ_lt {a : ℕ} {b : ℕ} : Nat.succ a < b → a < b := le_of_succ_le

theorem lt_of_succ_lt_succ {a : ℕ} {b : ℕ} : Nat.succ a < Nat.succ b → a < b := le_of_succ_le_succ

theorem pred_lt_pred {n : ℕ} {m : ℕ} : n ≠ 0 → n < m → Nat.pred n < Nat.pred m := sorry

theorem lt_of_succ_le {a : ℕ} {b : ℕ} (h : Nat.succ a ≤ b) : a < b := h

theorem succ_le_of_lt {a : ℕ} {b : ℕ} (h : a < b) : Nat.succ a ≤ b := h

theorem le_add_right (n : ℕ) (k : ℕ) : n ≤ n + k := sorry

theorem le_add_left (n : ℕ) (m : ℕ) : n ≤ m + n := nat.add_comm n m ▸ le_add_right n m

theorem le.dest {n : ℕ} {m : ℕ} : n ≤ m → ∃ (k : ℕ), n + k = m := sorry

theorem le.intro {n : ℕ} {m : ℕ} {k : ℕ} (h : n + k = m) : n ≤ m := h ▸ le_add_right n k

protected theorem add_le_add_left {n : ℕ} {m : ℕ} (h : n ≤ m) (k : ℕ) : k + n ≤ k + m := sorry

protected theorem add_le_add_right {n : ℕ} {m : ℕ} (h : n ≤ m) (k : ℕ) : n + k ≤ m + k :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n + k ≤ m + k)) (nat.add_comm n k)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (k + n ≤ m + k)) (nat.add_comm m k)))
      (nat.add_le_add_left h k))

protected theorem le_of_add_le_add_left {k : ℕ} {n : ℕ} {m : ℕ} (h : k + n ≤ k + m) : n ≤ m := sorry

protected theorem le_of_add_le_add_right {k : ℕ} {n : ℕ} {m : ℕ} : n + k ≤ m + k → n ≤ m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n + k ≤ m + k → n ≤ m)) (nat.add_comm n k)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (k + n ≤ m + k → n ≤ m)) (nat.add_comm m k)))
      nat.le_of_add_le_add_left)

protected theorem add_le_add_iff_le_right (k : ℕ) (n : ℕ) (m : ℕ) : n + k ≤ m + k ↔ n ≤ m :=
  { mp := nat.le_of_add_le_add_right, mpr := fun (h : n ≤ m) => nat.add_le_add_right h k }

protected theorem lt_of_add_lt_add_left {k : ℕ} {n : ℕ} {m : ℕ} (h : k + n < k + m) : n < m :=
  let h' : k + n ≤ k + m := nat.le_of_lt h;
  nat.lt_of_le_and_ne (nat.le_of_add_le_add_left h')
    fun (heq : n = m) => nat.lt_irrefl (k + m) (eq.mp (Eq._oldrec (Eq.refl (k + n < k + m)) heq) h)

protected theorem lt_of_add_lt_add_right {a : ℕ} {b : ℕ} {c : ℕ} (h : a + b < c + b) : a < c :=
  sorry

protected theorem add_lt_add_left {n : ℕ} {m : ℕ} (h : n < m) (k : ℕ) : k + n < k + m :=
  lt_of_succ_le (add_succ k n ▸ nat.add_le_add_left (succ_le_of_lt h) k)

protected theorem add_lt_add_right {n : ℕ} {m : ℕ} (h : n < m) (k : ℕ) : n + k < m + k :=
  nat.add_comm k m ▸ nat.add_comm k n ▸ nat.add_lt_add_left h k

protected theorem lt_add_of_pos_right {n : ℕ} {k : ℕ} (h : k > 0) : n < n + k :=
  nat.add_lt_add_left h n

protected theorem lt_add_of_pos_left {n : ℕ} {k : ℕ} (h : k > 0) : n < k + n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n < k + n)) (nat.add_comm k n))) (nat.lt_add_of_pos_right h)

protected theorem add_lt_add {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (h₁ : a < b) (h₂ : c < d) :
    a + c < b + d :=
  lt_trans (nat.add_lt_add_right h₁ c) (nat.add_lt_add_left h₂ b)

protected theorem add_le_add {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a + c ≤ b + d :=
  le_trans (nat.add_le_add_right h₁ c) (nat.add_le_add_left h₂ b)

protected theorem zero_lt_one : 0 < 1 := zero_lt_succ 0

theorem mul_le_mul_left {n : ℕ} {m : ℕ} (k : ℕ) (h : n ≤ m) : k * n ≤ k * m := sorry

theorem mul_le_mul_right {n : ℕ} {m : ℕ} (k : ℕ) (h : n ≤ m) : n * k ≤ m * k :=
  nat.mul_comm k m ▸ nat.mul_comm k n ▸ mul_le_mul_left k h

protected theorem mul_lt_mul_of_pos_left {n : ℕ} {m : ℕ} {k : ℕ} (h : n < m) (hk : k > 0) :
    k * n < k * m :=
  nat.lt_of_lt_of_le (nat.lt_add_of_pos_right hk)
    (mul_succ k n ▸ mul_le_mul_left k (succ_le_of_lt h))

protected theorem mul_lt_mul_of_pos_right {n : ℕ} {m : ℕ} {k : ℕ} (h : n < m) (hk : k > 0) :
    n * k < m * k :=
  nat.mul_comm k m ▸ nat.mul_comm k n ▸ nat.mul_lt_mul_of_pos_left h hk

protected theorem le_of_mul_le_mul_left {a : ℕ} {b : ℕ} {c : ℕ} (h : c * a ≤ c * b) (hc : c > 0) :
    a ≤ b :=
  iff.mp decidable.not_lt
    fun (h1 : b < a) =>
      (fun (h2 : c * b < c * a) => not_le_of_gt h2 h) (nat.mul_lt_mul_of_pos_left h1 hc)

theorem le_of_lt_succ {m : ℕ} {n : ℕ} : m < Nat.succ n → m ≤ n := le_of_succ_le_succ

theorem eq_of_mul_eq_mul_left {m : ℕ} {k : ℕ} {n : ℕ} (Hn : n > 0) (H : n * m = n * k) : m = k :=
  le_antisymm (nat.le_of_mul_le_mul_left (le_of_eq H) Hn)
    (nat.le_of_mul_le_mul_left (le_of_eq (Eq.symm H)) Hn)

/- sub properties -/

@[simp] protected theorem zero_sub (a : ℕ) : 0 - a = 0 := sorry

theorem sub_lt_succ (a : ℕ) (b : ℕ) : a - b < Nat.succ a := lt_succ_of_le (sub_le a b)

protected theorem sub_le_sub_right {n : ℕ} {m : ℕ} (h : n ≤ m) (k : ℕ) : n - k ≤ m - k := sorry

/- bit0/bit1 properties -/

protected theorem bit1_eq_succ_bit0 (n : ℕ) : bit1 n = Nat.succ (bit0 n) := rfl

protected theorem bit1_succ_eq (n : ℕ) : bit1 (Nat.succ n) = Nat.succ (Nat.succ (bit1 n)) :=
  Eq.trans (nat.bit1_eq_succ_bit0 (Nat.succ n)) (congr_arg Nat.succ (nat.bit0_succ_eq n))

protected theorem bit1_ne_one {n : ℕ} : n ≠ 0 → bit1 n ≠ 1 := sorry

protected theorem bit0_ne_one (n : ℕ) : bit0 n ≠ 1 := sorry

protected theorem add_self_ne_one (n : ℕ) : n + n ≠ 1 := sorry

protected theorem bit1_ne_bit0 (n : ℕ) (m : ℕ) : bit1 n ≠ bit0 m := sorry

protected theorem bit0_ne_bit1 (n : ℕ) (m : ℕ) : bit0 n ≠ bit1 m := ne.symm (nat.bit1_ne_bit0 m n)

protected theorem bit0_inj {n : ℕ} {m : ℕ} : bit0 n = bit0 m → n = m := sorry

protected theorem bit1_inj {n : ℕ} {m : ℕ} : bit1 n = bit1 m → n = m := sorry

protected theorem bit0_ne {n : ℕ} {m : ℕ} : n ≠ m → bit0 n ≠ bit0 m :=
  fun (h₁ : n ≠ m) (h₂ : bit0 n = bit0 m) => absurd (nat.bit0_inj h₂) h₁

protected theorem bit1_ne {n : ℕ} {m : ℕ} : n ≠ m → bit1 n ≠ bit1 m :=
  fun (h₁ : n ≠ m) (h₂ : bit1 n = bit1 m) => absurd (nat.bit1_inj h₂) h₁

protected theorem zero_ne_bit0 {n : ℕ} : n ≠ 0 → 0 ≠ bit0 n :=
  fun (h : n ≠ 0) => ne.symm (nat.bit0_ne_zero h)

protected theorem zero_ne_bit1 (n : ℕ) : 0 ≠ bit1 n := ne.symm (nat.bit1_ne_zero n)

protected theorem one_ne_bit0 (n : ℕ) : 1 ≠ bit0 n := ne.symm (nat.bit0_ne_one n)

protected theorem one_ne_bit1 {n : ℕ} : n ≠ 0 → 1 ≠ bit1 n :=
  fun (h : n ≠ 0) => ne.symm (nat.bit1_ne_one h)

protected theorem one_lt_bit1 {n : ℕ} : n ≠ 0 → 1 < bit1 n := sorry

protected theorem one_lt_bit0 {n : ℕ} : n ≠ 0 → 1 < bit0 n := sorry

protected theorem bit0_lt {n : ℕ} {m : ℕ} (h : n < m) : bit0 n < bit0 m := nat.add_lt_add h h

protected theorem bit1_lt {n : ℕ} {m : ℕ} (h : n < m) : bit1 n < bit1 m :=
  succ_lt_succ (nat.add_lt_add h h)

protected theorem bit0_lt_bit1 {n : ℕ} {m : ℕ} (h : n ≤ m) : bit0 n < bit1 m :=
  lt_succ_of_le (nat.add_le_add h h)

protected theorem bit1_lt_bit0 {n : ℕ} {m : ℕ} : n < m → bit1 n < bit0 m := sorry

protected theorem one_le_bit1 (n : ℕ) : 1 ≤ bit1 n :=
  (fun (this : 1 ≤ Nat.succ (bit0 n)) => this) (succ_le_succ (zero_le (bit0 n)))

protected theorem one_le_bit0 (n : ℕ) : n ≠ 0 → 1 ≤ bit0 n := sorry

/- subtraction -/

@[simp] protected theorem sub_zero (n : ℕ) : n - 0 = n := rfl

theorem sub_succ (n : ℕ) (m : ℕ) : n - Nat.succ m = Nat.pred (n - m) := rfl

theorem succ_sub_succ (n : ℕ) (m : ℕ) : Nat.succ n - Nat.succ m = n - m := succ_sub_succ_eq_sub n m

protected theorem sub_self (n : ℕ) : n - n = 0 := sorry

/- TODO(Leo): remove the following ematch annotations as soon as we have
   arithmetic theory in the smt_stactic -/

protected theorem add_sub_add_right (n : ℕ) (k : ℕ) (m : ℕ) : n + k - (m + k) = n - m := sorry

protected theorem add_sub_add_left (k : ℕ) (n : ℕ) (m : ℕ) : k + n - (k + m) = n - m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (k + n - (k + m) = n - m)) (nat.add_comm k n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n + k - (k + m) = n - m)) (nat.add_comm k m)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (n + k - (m + k) = n - m)) (nat.add_sub_add_right n k m)))
        (Eq.refl (n - m))))

protected theorem add_sub_cancel (n : ℕ) (m : ℕ) : n + m - m = n :=
  (fun (this : n + m - (0 + m) = n) =>
      eq.mp (Eq._oldrec (Eq.refl (n + m - (0 + m) = n)) (nat.zero_add m)) this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (n + m - (0 + m) = n)) (nat.add_sub_add_right n m 0)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (n - 0 = n)) (nat.sub_zero n))) (Eq.refl n)))

protected theorem add_sub_cancel_left (n : ℕ) (m : ℕ) : n + m - n = m :=
  (fun (this : n + m - (n + 0) = m) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (n + m - (n + 0) = m)) (nat.add_sub_add_left n m 0)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (m - 0 = m)) (nat.sub_zero m))) (Eq.refl m)))

protected theorem sub_sub (n : ℕ) (m : ℕ) (k : ℕ) : n - m - k = n - (m + k) := sorry

theorem le_of_le_of_sub_le_sub_right {n : ℕ} {m : ℕ} {k : ℕ} (h₀ : k ≤ m) (h₁ : n - k ≤ m - k) :
    n ≤ m :=
  sorry

protected theorem sub_le_sub_right_iff (n : ℕ) (m : ℕ) (k : ℕ) (h : k ≤ m) :
    n - k ≤ m - k ↔ n ≤ m :=
  { mp := le_of_le_of_sub_le_sub_right h, mpr := fun (h : n ≤ m) => nat.sub_le_sub_right h k }

theorem sub_self_add (n : ℕ) (m : ℕ) : n - (n + m) = 0 :=
  (fun (this : n + 0 - (n + m) = 0) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (n + 0 - (n + m) = 0)) (nat.add_sub_add_left n 0 m)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 - m = 0)) (nat.zero_sub m))) (Eq.refl 0)))

theorem add_le_to_le_sub (x : ℕ) {y : ℕ} {k : ℕ} (h : k ≤ y) : x + k ≤ y ↔ x ≤ y - k := sorry

theorem sub_lt_of_pos_le (a : ℕ) (b : ℕ) (h₀ : 0 < a) (h₁ : a ≤ b) : b - a < b :=
  sub_lt (lt_of_lt_of_le h₀ h₁) h₀

theorem sub_one (n : ℕ) : n - 1 = Nat.pred n := rfl

theorem succ_sub_one (n : ℕ) : Nat.succ n - 1 = n := rfl

theorem succ_pred_eq_of_pos {n : ℕ} : n > 0 → Nat.succ (Nat.pred n) = n := sorry

theorem sub_eq_zero_of_le {n : ℕ} {m : ℕ} (h : n ≤ m) : n - m = 0 := sorry

protected theorem le_of_sub_eq_zero {n : ℕ} {m : ℕ} : n - m = 0 → n ≤ m := sorry

protected theorem sub_eq_zero_iff_le {n : ℕ} {m : ℕ} : n - m = 0 ↔ n ≤ m :=
  { mp := nat.le_of_sub_eq_zero, mpr := sub_eq_zero_of_le }

theorem add_sub_of_le {n : ℕ} {m : ℕ} (h : n ≤ m) : n + (m - n) = m := sorry

protected theorem sub_add_cancel {n : ℕ} {m : ℕ} (h : n ≥ m) : n - m + m = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n - m + m = n)) (nat.add_comm (n - m) m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (m + (n - m) = n)) (add_sub_of_le h))) (Eq.refl n))

protected theorem add_sub_assoc {m : ℕ} {k : ℕ} (h : k ≤ m) (n : ℕ) : n + m - k = n + (m - k) :=
  sorry

protected theorem sub_eq_iff_eq_add {a : ℕ} {b : ℕ} {c : ℕ} (ab : b ≤ a) : a - b = c ↔ a = c + b :=
  sorry

protected theorem lt_of_sub_eq_succ {m : ℕ} {n : ℕ} {l : ℕ} (H : m - n = Nat.succ l) : n < m :=
  sorry

@[simp] theorem zero_min (a : ℕ) : min 0 a = 0 := min_eq_left (zero_le a)

@[simp] theorem min_zero (a : ℕ) : min a 0 = 0 := min_eq_right (zero_le a)

-- Distribute succ over min

theorem min_succ_succ (x : ℕ) (y : ℕ) : min (Nat.succ x) (Nat.succ y) = Nat.succ (min x y) := sorry

theorem sub_eq_sub_min (n : ℕ) (m : ℕ) : n - m = n - min n m := sorry

@[simp] theorem sub_add_min_cancel (n : ℕ) (m : ℕ) : n - m + min n m = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n - m + min n m = n)) (sub_eq_sub_min n m)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (n - min n m + min n m = n)) (nat.sub_add_cancel (min_le_left n m))))
      (Eq.refl n))

/- TODO(Leo): sub + inequalities -/

protected def strong_rec_on {p : ℕ → Sort u} (n : ℕ) (h : (n : ℕ) → ((m : ℕ) → m < n → p m) → p n) :
    p n :=
  (fun (this : (n m : ℕ) → m < n → p m) => this (Nat.succ n) n (lt_succ_self n))
    fun (n : ℕ) =>
      Nat.rec (fun (m : ℕ) (h₁ : m < 0) => absurd h₁ (not_lt_zero m))
        (fun (n : ℕ) (ih : (m : ℕ) → m < n → p m) (m : ℕ) (h₁ : m < Nat.succ n) =>
          or.by_cases sorry (fun (ᾰ : m < n) => ih m ᾰ)
            fun (ᾰ : m = n) => Eq._oldrec (fun (h₁ : n < Nat.succ n) => h n ih) (Eq.symm ᾰ) h₁)
        n

protected theorem strong_induction_on {p : ℕ → Prop} (n : ℕ)
    (h : ∀ (n : ℕ), (∀ (m : ℕ), m < n → p m) → p n) : p n :=
  nat.strong_rec_on n h

protected theorem case_strong_induction_on {p : ℕ → Prop} (a : ℕ) (hz : p 0)
    (hi : ∀ (n : ℕ), (∀ (m : ℕ), m ≤ n → p m) → p (Nat.succ n)) : p a :=
  sorry

/- mod -/

theorem mod_def (x : ℕ) (y : ℕ) : x % y = ite (0 < y ∧ y ≤ x) ((x - y) % y) x := sorry

@[simp] theorem mod_zero (a : ℕ) : a % 0 = a := sorry

theorem mod_eq_of_lt {a : ℕ} {b : ℕ} (h : a < b) : a % b = a := sorry

@[simp] theorem zero_mod (b : ℕ) : 0 % b = 0 := sorry

theorem mod_eq_sub_mod {a : ℕ} {b : ℕ} (h : a ≥ b) : a % b = (a - b) % b := sorry

theorem mod_lt (x : ℕ) {y : ℕ} (h : y > 0) : x % y < y := sorry

@[simp] theorem mod_self (n : ℕ) : n % n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n % n = 0)) (mod_eq_sub_mod (le_refl n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((n - n) % n = 0)) (nat.sub_self n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 % n = 0)) (zero_mod n))) (Eq.refl 0)))

@[simp] theorem mod_one (n : ℕ) : n % 1 = 0 :=
  (fun (this : n % 1 < 1) => eq_zero_of_le_zero (le_of_lt_succ this)) (mod_lt n (succ_pos 0))

theorem mod_two_eq_zero_or_one (n : ℕ) : n % bit0 1 = 0 ∨ n % bit0 1 = 1 := sorry

/- div & mod -/

theorem div_def (x : ℕ) (y : ℕ) : x / y = ite (0 < y ∧ y ≤ x) ((x - y) / y + 1) 0 := sorry

theorem mod_add_div (m : ℕ) (k : ℕ) : m % k + k * (m / k) = m := sorry

/- div -/

@[simp] protected theorem div_one (n : ℕ) : n / 1 = n := sorry

@[simp] protected theorem div_zero (n : ℕ) : n / 0 = 0 := sorry

@[simp] protected theorem zero_div (b : ℕ) : 0 / b = 0 :=
  Eq.trans (div_def 0 b) (if_neg (And._oldrec not_le_of_gt))

protected theorem div_le_of_le_mul {m : ℕ} {n : ℕ} {k : ℕ} : m ≤ k * n → m / k ≤ n := sorry

protected theorem div_le_self (m : ℕ) (n : ℕ) : m / n ≤ m := sorry

theorem div_eq_sub_div {a : ℕ} {b : ℕ} (h₁ : b > 0) (h₂ : a ≥ b) : a / b = (a - b) / b + 1 := sorry

theorem div_eq_of_lt {a : ℕ} {b : ℕ} (h₀ : a < b) : a / b = 0 := sorry

-- this is a Galois connection

--   f x ≤ y ↔ x ≤ g y

-- with

--   f x = x * k

--   g y = y / k

theorem le_div_iff_mul_le (x : ℕ) (y : ℕ) {k : ℕ} (Hk : k > 0) : x ≤ y / k ↔ x * k ≤ y := sorry

theorem div_lt_iff_lt_mul (x : ℕ) (y : ℕ) {k : ℕ} (Hk : k > 0) : x / k < y ↔ x < y * k := sorry

def iterate {α : Sort u} (op : α → α) : ℕ → α → α := sorry

/- successor and predecessor -/

theorem add_one_ne_zero (n : ℕ) : n + 1 ≠ 0 := succ_ne_zero n

theorem eq_zero_or_eq_succ_pred (n : ℕ) : n = 0 ∨ n = Nat.succ (Nat.pred n) := sorry

theorem exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : ∃ (k : ℕ), n = Nat.succ k :=
  Exists.intro (Nat.pred n) (or.resolve_left (eq_zero_or_eq_succ_pred n) H)

theorem discriminate {B : Sort u} {n : ℕ} (H1 : n = 0 → B) (H2 : (m : ℕ) → n = Nat.succ m → B) :
    B :=
  (fun (_x : ℕ) (h : n = _x) =>
      Nat.rec (fun (h : n = 0) => H1 h)
        (fun (n_1 : ℕ) (ih : n = n_1 → B) (h : n = Nat.succ n_1) => H2 n_1 h) _x h)
    n rfl

theorem one_succ_zero : 1 = Nat.succ 0 := rfl

theorem two_step_induction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
    (H3 : (n : ℕ) → P n → P (Nat.succ n) → P (Nat.succ (Nat.succ n))) (a : ℕ) : P a :=
  sorry

theorem sub_induction {P : ℕ → ℕ → Sort u} (H1 : (m : ℕ) → P 0 m) (H2 : (n : ℕ) → P (Nat.succ n) 0)
    (H3 : (n m : ℕ) → P n m → P (Nat.succ n) (Nat.succ m)) (n : ℕ) (m : ℕ) : P n m :=
  sorry

/- addition -/

theorem succ_add_eq_succ_add (n : ℕ) (m : ℕ) : Nat.succ n + m = n + Nat.succ m := sorry

-- theorem one_add (n : ℕ) : 1 + n = succ n := by simp [add_comm]

protected theorem add_right_comm (n : ℕ) (m : ℕ) (k : ℕ) : n + m + k = n + k + m :=
  right_comm Nat.add nat.add_comm nat.add_assoc

theorem eq_zero_of_add_eq_zero {n : ℕ} {m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0 :=
  { left := eq_zero_of_add_eq_zero_right H, right := eq_zero_of_add_eq_zero_left H }

theorem eq_zero_of_mul_eq_zero {n : ℕ} {m : ℕ} : n * m = 0 → n = 0 ∨ m = 0 := sorry

/- properties of inequality -/

theorem le_succ_of_pred_le {n : ℕ} {m : ℕ} : Nat.pred n ≤ m → n ≤ Nat.succ m :=
  nat.cases_on n less_than_or_equal.step fun (a : ℕ) => succ_le_succ

theorem le_lt_antisymm {n : ℕ} {m : ℕ} (h₁ : n ≤ m) (h₂ : m < n) : False :=
  nat.lt_irrefl n (nat.lt_of_le_of_lt h₁ h₂)

theorem lt_le_antisymm {n : ℕ} {m : ℕ} (h₁ : n < m) (h₂ : m ≤ n) : False := le_lt_antisymm h₂ h₁

protected theorem lt_asymm {n : ℕ} {m : ℕ} (h₁ : n < m) : ¬m < n := le_lt_antisymm (nat.le_of_lt h₁)

protected def lt_ge_by_cases {a : ℕ} {b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a ≥ b → C) : C :=
  decidable.by_cases h₁ fun (h : ¬a < b) => h₂ sorry

protected def lt_by_cases {a : ℕ} {b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a = b → C)
    (h₃ : b < a → C) : C :=
  nat.lt_ge_by_cases h₁
    fun (h₁ : a ≥ b) => nat.lt_ge_by_cases h₃ fun (h : b ≥ a) => h₂ (nat.le_antisymm h h₁)

protected theorem lt_trichotomy (a : ℕ) (b : ℕ) : a < b ∨ a = b ∨ b < a :=
  nat.lt_by_cases (fun (h : a < b) => Or.inl h) (fun (h : a = b) => Or.inr (Or.inl h))
    fun (h : b < a) => Or.inr (Or.inr h)

protected theorem eq_or_lt_of_not_lt {a : ℕ} {b : ℕ} (hnlt : ¬a < b) : a = b ∨ b < a :=
  or.resolve_left (nat.lt_trichotomy a b) hnlt

theorem lt_succ_of_lt {a : ℕ} {b : ℕ} (h : a < b) : a < Nat.succ b := le_succ_of_le h

def one_pos : 0 < 1 := nat.zero_lt_one

/- subtraction -/

protected theorem sub_le_sub_left {n : ℕ} {m : ℕ} (k : ℕ) (h : n ≤ m) : k - m ≤ k - n :=
  less_than_or_equal.drec (le_refl (k - n))
    (fun {h_b : ℕ} (h_ᾰ : less_than_or_equal n h_b) (h_ih : k - h_b ≤ k - n) =>
      le_trans (pred_le (Nat.sub k h_b)) h_ih)
    h

theorem succ_sub_sub_succ (n : ℕ) (m : ℕ) (k : ℕ) : Nat.succ n - m - Nat.succ k = n - m - k := sorry

protected theorem sub.right_comm (m : ℕ) (n : ℕ) (k : ℕ) : m - n - k = m - k - n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m - n - k = m - k - n)) (nat.sub_sub m n k)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (m - (n + k) = m - k - n)) (nat.sub_sub m k n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (m - (n + k) = m - (k + n))) (nat.add_comm n k)))
        (Eq.refl (m - (k + n)))))

theorem mul_pred_left (n : ℕ) (m : ℕ) : Nat.pred n * m = n * m - m := sorry

theorem mul_pred_right (n : ℕ) (m : ℕ) : n * Nat.pred m = n * m - n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n * Nat.pred m = n * m - n)) (nat.mul_comm n (Nat.pred m))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Nat.pred m * n = n * m - n)) (mul_pred_left m n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (m * n - n = n * m - n)) (nat.mul_comm m n)))
        (Eq.refl (n * m - n))))

protected theorem mul_sub_right_distrib (n : ℕ) (m : ℕ) (k : ℕ) : (n - m) * k = n * k - m * k :=
  sorry

protected theorem mul_sub_left_distrib (n : ℕ) (m : ℕ) (k : ℕ) : n * (m - k) = n * m - n * k :=
  sorry

protected theorem mul_self_sub_mul_self_eq (a : ℕ) (b : ℕ) : a * a - b * b = (a + b) * (a - b) :=
  sorry

theorem succ_mul_succ_eq (a : ℕ) (b : ℕ) : Nat.succ a * Nat.succ b = a * b + a + b + 1 := sorry

theorem succ_sub {m : ℕ} {n : ℕ} (h : m ≥ n) : Nat.succ m - n = Nat.succ (m - n) := sorry

protected theorem sub_pos_of_lt {m : ℕ} {n : ℕ} (h : m < n) : n - m > 0 :=
  (fun (this : 0 + m < n - m + m) => nat.lt_of_add_lt_add_right this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 + m < n - m + m)) (nat.zero_add m)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (m < n - m + m)) (nat.sub_add_cancel (le_of_lt h)))) h))

protected theorem sub_sub_self {n : ℕ} {m : ℕ} (h : m ≤ n) : n - (n - m) = m :=
  iff.mpr (nat.sub_eq_iff_eq_add (sub_le n m)) (Eq.symm (add_sub_of_le h))

protected theorem sub_add_comm {n : ℕ} {m : ℕ} {k : ℕ} (h : k ≤ n) : n + m - k = n - k + m :=
  iff.mpr (nat.sub_eq_iff_eq_add (nat.le_trans h (le_add_right n m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n + m = n - k + m + k)) (nat.add_right_comm (n - k) m k)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (n + m = n - k + k + m)) (nat.sub_add_cancel h)))
        (Eq.refl (n + m))))

theorem sub_one_sub_lt {n : ℕ} {i : ℕ} (h : i < n) : n - 1 - i < n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n - 1 - i < n)) (nat.sub_sub n 1 i)))
    (sub_lt (lt_of_lt_of_le (zero_lt_succ i) h)
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 < 1 + i)) (nat.add_comm 1 i))) (zero_lt_succ i)))

theorem pred_inj {a : ℕ} {b : ℕ} : a > 0 → b > 0 → Nat.pred a = Nat.pred b → a = b := sorry

/- find -/

protected def find_x {p : ℕ → Prop} [decidable_pred p] (H : ∃ (n : ℕ), p n) :
    Subtype fun (n : ℕ) => p n ∧ ∀ (m : ℕ), m < n → ¬p m :=
  well_founded.fix (wf_lbp H)
    (fun (m : ℕ)
      (IH :
      (y : ℕ) →
        lbp y m →
          (fun (k : ℕ) =>
              (∀ (n : ℕ), n < k → ¬p n) → Subtype fun (n : ℕ) => p n ∧ ∀ (m : ℕ), m < n → ¬p m)
            y)
      (al : ∀ (n : ℕ), n < m → ¬p n) =>
      dite (p m) (fun (pm : p m) => { val := m, property := sorry })
        fun (pm : ¬p m) => (fun (this : ∀ (n : ℕ), n ≤ m → ¬p n) => IH (m + 1) sorry sorry) sorry)
    0 sorry

protected def find {p : ℕ → Prop} [decidable_pred p] (H : ∃ (n : ℕ), p n) : ℕ :=
  subtype.val (nat.find_x H)

protected theorem find_spec {p : ℕ → Prop} [decidable_pred p] (H : ∃ (n : ℕ), p n) :
    p (nat.find H) :=
  and.left (subtype.property (nat.find_x H))

protected theorem find_min {p : ℕ → Prop} [decidable_pred p] (H : ∃ (n : ℕ), p n) {m : ℕ} :
    m < nat.find H → ¬p m :=
  and.right (subtype.property (nat.find_x H))

protected theorem find_min' {p : ℕ → Prop} [decidable_pred p] (H : ∃ (n : ℕ), p n) {m : ℕ}
    (h : p m) : nat.find H ≤ m :=
  decidable.le_of_not_lt fun (l : m < nat.find H) => nat.find_min H l h

/- mod -/

theorem mod_le (x : ℕ) (y : ℕ) : x % y ≤ x := sorry

@[simp] theorem add_mod_right (x : ℕ) (z : ℕ) : (x + z) % z = x % z :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((x + z) % z = x % z)) (mod_eq_sub_mod (le_add_left z x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((x + z - z) % z = x % z)) (nat.add_sub_cancel x z)))
      (Eq.refl (x % z)))

@[simp] theorem add_mod_left (x : ℕ) (z : ℕ) : (x + z) % x = z % x :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((x + z) % x = z % x)) (nat.add_comm x z)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((z + x) % x = z % x)) (add_mod_right z x))) (Eq.refl (z % x)))

@[simp] theorem add_mul_mod_self_left (x : ℕ) (y : ℕ) (z : ℕ) : (x + y * z) % y = x % y := sorry

@[simp] theorem add_mul_mod_self_right (x : ℕ) (y : ℕ) (z : ℕ) : (x + y * z) % z = x % z :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((x + y * z) % z = x % z)) (nat.mul_comm y z)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((x + z * y) % z = x % z)) (add_mul_mod_self_left x z y)))
      (Eq.refl (x % z)))

@[simp] theorem mul_mod_right (m : ℕ) (n : ℕ) : m * n % m = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m * n % m = 0)) (Eq.symm (nat.zero_add (m * n)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((0 + m * n) % m = 0)) (add_mul_mod_self_left 0 m n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 % m = 0)) (zero_mod m))) (Eq.refl 0)))

@[simp] theorem mul_mod_left (m : ℕ) (n : ℕ) : m * n % n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m * n % n = 0)) (nat.mul_comm m n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n * m % n = 0)) (mul_mod_right n m))) (Eq.refl 0))

theorem mul_mod_mul_left (z : ℕ) (x : ℕ) (y : ℕ) : z * x % (z * y) = z * (x % y) := sorry

theorem mul_mod_mul_right (z : ℕ) (x : ℕ) (y : ℕ) : x * z % (y * z) = x % y * z := sorry

theorem cond_to_bool_mod_two (x : ℕ) [d : Decidable (x % bit0 1 = 1)] :
    cond (to_bool (x % bit0 1 = 1)) 1 0 = x % bit0 1 :=
  sorry

theorem sub_mul_mod (x : ℕ) (k : ℕ) (n : ℕ) (h₁ : n * k ≤ x) : (x - n * k) % n = x % n := sorry

/- div -/

theorem sub_mul_div (x : ℕ) (n : ℕ) (p : ℕ) (h₁ : n * p ≤ x) : (x - n * p) / n = x / n - p := sorry

theorem div_mul_le_self (m : ℕ) (n : ℕ) : m / n * n ≤ m := sorry

@[simp] theorem add_div_right (x : ℕ) {z : ℕ} (H : z > 0) : (x + z) / z = Nat.succ (x / z) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl ((x + z) / z = Nat.succ (x / z))) (div_eq_sub_div H (le_add_left z x))))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl ((x + z - z) / z + 1 = Nat.succ (x / z))) (nat.add_sub_cancel x z)))
      (Eq.refl (x / z + 1)))

@[simp] theorem add_div_left (x : ℕ) {z : ℕ} (H : z > 0) : (z + x) / z = Nat.succ (x / z) :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((z + x) / z = Nat.succ (x / z))) (nat.add_comm z x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((x + z) / z = Nat.succ (x / z))) (add_div_right x H)))
      (Eq.refl (Nat.succ (x / z))))

@[simp] theorem mul_div_right (n : ℕ) {m : ℕ} (H : m > 0) : m * n / m = n := sorry

@[simp] theorem mul_div_left (m : ℕ) {n : ℕ} (H : n > 0) : m * n / n = m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m * n / n = m)) (nat.mul_comm m n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n * m / n = m)) (mul_div_right m H))) (Eq.refl m))

protected theorem div_self {n : ℕ} (H : n > 0) : n / n = 1 :=
  let t : (0 + n) / n = Nat.succ (0 / n) := add_div_right 0 H;
  eq.mp (Eq._oldrec (Eq.refl (n / n = Nat.succ (0 / n))) (nat.zero_div n))
    (eq.mp (Eq._oldrec (Eq.refl ((0 + n) / n = Nat.succ (0 / n))) (nat.zero_add n)) t)

theorem add_mul_div_left (x : ℕ) (z : ℕ) {y : ℕ} (H : y > 0) : (x + y * z) / y = x / y + z := sorry

theorem add_mul_div_right (x : ℕ) (y : ℕ) {z : ℕ} (H : z > 0) : (x + y * z) / z = x / z + y :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((x + y * z) / z = x / z + y)) (nat.mul_comm y z)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((x + z * y) / z = x / z + y)) (add_mul_div_left x y H)))
      (Eq.refl (x / z + y)))

protected theorem mul_div_cancel (m : ℕ) {n : ℕ} (H : n > 0) : m * n / n = m := sorry

protected theorem mul_div_cancel_left (m : ℕ) {n : ℕ} (H : n > 0) : n * m / n = m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n * m / n = m)) (nat.mul_comm n m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (m * n / n = m)) (nat.mul_div_cancel m H))) (Eq.refl m))

protected theorem div_eq_of_eq_mul_left {m : ℕ} {n : ℕ} {k : ℕ} (H1 : n > 0) (H2 : m = k * n) :
    m / n = k :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m / n = k)) H2))
    (eq.mpr (id (Eq._oldrec (Eq.refl (k * n / n = k)) (nat.mul_div_cancel k H1))) (Eq.refl k))

protected theorem div_eq_of_eq_mul_right {m : ℕ} {n : ℕ} {k : ℕ} (H1 : n > 0) (H2 : m = n * k) :
    m / n = k :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m / n = k)) H2))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n * k / n = k)) (nat.mul_div_cancel_left k H1))) (Eq.refl k))

protected theorem div_eq_of_lt_le {m : ℕ} {n : ℕ} {k : ℕ} (lo : k * n ≤ m)
    (hi : m < Nat.succ k * n) : m / n = k :=
  sorry

theorem mul_sub_div (x : ℕ) (n : ℕ) (p : ℕ) (h₁ : x < n * p) :
    (n * p - Nat.succ x) / n = p - Nat.succ (x / n) :=
  sorry

protected theorem mul_pos {a : ℕ} {b : ℕ} (ha : a > 0) (hb : b > 0) : a * b > 0 :=
  (fun (h : 0 * b < a * b) => eq.mp (Eq._oldrec (Eq.refl (0 * b < a * b)) (nat.zero_mul b)) h)
    (nat.mul_lt_mul_of_pos_right ha hb)

protected theorem div_div_eq_div_mul (m : ℕ) (n : ℕ) (k : ℕ) : m / n / k = m / (n * k) := sorry

protected theorem mul_div_mul {m : ℕ} (n : ℕ) (k : ℕ) (H : m > 0) : m * n / (m * k) = n / k :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (m * n / (m * k) = n / k))
        (Eq.symm (nat.div_div_eq_div_mul (m * n) m k))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (m * n / m / k = n / k)) (nat.mul_div_cancel_left n H)))
      (Eq.refl (n / k)))

/- dvd -/

@[simp] protected theorem dvd_mul_right (a : ℕ) (b : ℕ) : a ∣ a * b := Exists.intro b rfl

protected theorem dvd_trans {a : ℕ} {b : ℕ} {c : ℕ} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := sorry

protected theorem eq_zero_of_zero_dvd {a : ℕ} (h : 0 ∣ a) : a = 0 :=
  exists.elim h fun (c : ℕ) (H' : a = 0 * c) => Eq.trans H' (nat.zero_mul c)

protected theorem dvd_add {a : ℕ} {b : ℕ} {c : ℕ} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c := sorry

protected theorem dvd_add_iff_right {k : ℕ} {m : ℕ} {n : ℕ} (h : k ∣ m) : k ∣ n ↔ k ∣ m + n := sorry

protected theorem dvd_add_iff_left {k : ℕ} {m : ℕ} {n : ℕ} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (k ∣ m ↔ k ∣ m + n)) (nat.add_comm m n)))
    (nat.dvd_add_iff_right h)

theorem dvd_sub {k : ℕ} {m : ℕ} {n : ℕ} (H : n ≤ m) (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
  iff.mpr (nat.dvd_add_iff_left h₂)
    (eq.mpr (id (Eq._oldrec (Eq.refl (k ∣ m - n + n)) (nat.sub_add_cancel H))) h₁)

theorem dvd_mod_iff {k : ℕ} {m : ℕ} {n : ℕ} (h : k ∣ n) : k ∣ m % n ↔ k ∣ m :=
  let t : k ∣ m % n ↔ k ∣ m % n + n * (m / n) :=
    nat.dvd_add_iff_left (nat.dvd_trans h (nat.dvd_mul_right n (m / n)));
  eq.mp (Eq._oldrec (Eq.refl (k ∣ m % n ↔ k ∣ m % n + n * (m / n))) (mod_add_div m n)) t

theorem le_of_dvd {m : ℕ} {n : ℕ} (h : n > 0) : m ∣ n → m ≤ n := sorry

theorem dvd_antisymm {m : ℕ} {n : ℕ} : m ∣ n → n ∣ m → m = n := sorry

theorem pos_of_dvd_of_pos {m : ℕ} {n : ℕ} (H1 : m ∣ n) (H2 : n > 0) : m > 0 := sorry

theorem eq_one_of_dvd_one {n : ℕ} (H : n ∣ 1) : n = 1 :=
  le_antisymm (le_of_dvd (of_as_true trivial) H) (pos_of_dvd_of_pos H (of_as_true trivial))

theorem dvd_of_mod_eq_zero {m : ℕ} {n : ℕ} (H : n % m = 0) : m ∣ n :=
  Exists.intro (n / m)
    (eq.mp (Eq._oldrec (Eq.refl (n = 0 + m * (n / m))) (nat.zero_add (m * (n / m))))
      (eq.mp (Eq._oldrec (Eq.refl (n = n % m + m * (n / m))) H) (Eq.symm (mod_add_div n m))))

theorem mod_eq_zero_of_dvd {m : ℕ} {n : ℕ} (H : m ∣ n) : n % m = 0 := sorry

theorem dvd_iff_mod_eq_zero (m : ℕ) (n : ℕ) : m ∣ n ↔ n % m = 0 :=
  { mp := mod_eq_zero_of_dvd, mpr := dvd_of_mod_eq_zero }

protected instance decidable_dvd : DecidableRel has_dvd.dvd :=
  fun (m n : ℕ) => decidable_of_decidable_of_iff (nat.decidable_eq (n % m) 0) sorry

protected theorem mul_div_cancel' {m : ℕ} {n : ℕ} (H : n ∣ m) : n * (m / n) = m :=
  let t : m % n + n * (m / n) = m := mod_add_div m n;
  eq.mp (Eq._oldrec (Eq.refl (0 + n * (m / n) = m)) (nat.zero_add (n * (m / n))))
    (eq.mp (Eq._oldrec (Eq.refl (m % n + n * (m / n) = m)) (mod_eq_zero_of_dvd H)) t)

protected theorem div_mul_cancel {m : ℕ} {n : ℕ} (H : n ∣ m) : m / n * n = m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m / n * n = m)) (nat.mul_comm (m / n) n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n * (m / n) = m)) (nat.mul_div_cancel' H))) (Eq.refl m))

protected theorem mul_div_assoc (m : ℕ) {n : ℕ} {k : ℕ} (H : k ∣ n) : m * n / k = m * (n / k) :=
  sorry

theorem dvd_of_mul_dvd_mul_left {m : ℕ} {n : ℕ} {k : ℕ} (kpos : k > 0) (H : k * m ∣ k * n) :
    m ∣ n :=
  sorry

theorem dvd_of_mul_dvd_mul_right {m : ℕ} {n : ℕ} {k : ℕ} (kpos : k > 0) (H : m * k ∣ n * k) :
    m ∣ n :=
  dvd_of_mul_dvd_mul_left kpos
    (eq.mp (Eq._oldrec (Eq.refl (k * m ∣ n * k)) (nat.mul_comm n k))
      (eq.mp (Eq._oldrec (Eq.refl (m * k ∣ n * k)) (nat.mul_comm m k)) H))

/- --- -/

protected theorem mul_le_mul_of_nonneg_left {a : ℕ} {b : ℕ} {c : ℕ} (h₁ : a ≤ b) : c * a ≤ c * b :=
  sorry

protected theorem mul_le_mul_of_nonneg_right {a : ℕ} {b : ℕ} {c : ℕ} (h₁ : a ≤ b) : a * c ≤ b * c :=
  sorry

protected theorem mul_lt_mul {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (hac : a < c) (hbd : b ≤ d)
    (pos_b : 0 < b) : a * b < c * d :=
  lt_of_lt_of_le (nat.mul_lt_mul_of_pos_right hac pos_b) (nat.mul_le_mul_of_nonneg_left hbd)

protected theorem mul_lt_mul' {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (h1 : a ≤ c) (h2 : b < d)
    (h3 : 0 < c) : a * b < c * d :=
  lt_of_le_of_lt (nat.mul_le_mul_of_nonneg_right h1) (nat.mul_lt_mul_of_pos_left h2 h3)

-- TODO: there are four variations, depending on which variables we assume to be nonneg

protected theorem mul_le_mul {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    a * b ≤ c * d :=
  le_trans (nat.mul_le_mul_of_nonneg_right hac) (nat.mul_le_mul_of_nonneg_left hbd)

theorem div_lt_self {n : ℕ} {m : ℕ} : n > 0 → m > 1 → n / m < n := sorry

end Mathlib