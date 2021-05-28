/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.logic
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace nat


notation:1024 "ℕ" => Mathlib.nat

inductive less_than_or_equal (a : ℕ) : ℕ → Prop
where
| refl : less_than_or_equal a a
| step : ∀ {b : ℕ}, less_than_or_equal a b → less_than_or_equal a (Nat.succ b)

protected instance has_le : HasLessEq ℕ :=
  { LessEq := less_than_or_equal }

protected def le (n : ℕ) (m : ℕ)  :=
  less_than_or_equal n m

protected def lt (n : ℕ) (m : ℕ)  :=
  less_than_or_equal (Nat.succ n) m

protected instance has_lt : HasLess ℕ :=
  { Less := nat.lt }

def pred : ℕ → ℕ :=
  Nat.pred

protected def sub : ℕ → ℕ → ℕ :=
  Nat.sub

protected def mul : ℕ → ℕ → ℕ :=
  Nat.mul

protected instance has_sub : Sub ℕ :=
  { sub := Nat.sub }

protected instance has_mul : Mul ℕ :=
  { mul := Nat.mul }

-- defeq to the instance provided by comm_semiring

protected instance has_dvd : has_dvd ℕ :=
  has_dvd.mk fun (a b : ℕ) => ∃ (c : ℕ), b = a * c

protected instance decidable_eq : DecidableEq ℕ :=
  sorry

def repeat {α : Type u} (f : ℕ → α → α) : ℕ → α → α :=
  sorry

protected instance inhabited : Inhabited ℕ :=
  { default := 0 }

@[simp] theorem nat_zero_eq_zero : 0 = 0 :=
  rfl

/- properties of inequality -/

protected def le_refl (a : ℕ) : a ≤ a :=
  less_than_or_equal.refl

theorem le_succ (n : ℕ) : n ≤ Nat.succ n :=
  less_than_or_equal.step (nat.le_refl n)

theorem succ_le_succ {n : ℕ} {m : ℕ} : n ≤ m → Nat.succ n ≤ Nat.succ m :=
  fun (h : n ≤ m) =>
    less_than_or_equal._oldrec (nat.le_refl (Nat.succ n))
      (fun (a : ℕ) (b : less_than_or_equal n a) => less_than_or_equal.step) h

theorem zero_le (n : ℕ) : 0 ≤ n := sorry

theorem zero_lt_succ (n : ℕ) : 0 < Nat.succ n :=
  succ_le_succ (zero_le n)

def succ_pos (n : ℕ) : 0 < Nat.succ n :=
  zero_lt_succ

theorem not_succ_le_zero (n : ℕ) : Nat.succ n ≤ 0 → False := sorry

theorem not_lt_zero (a : ℕ) : ¬a < 0 :=
  not_succ_le_zero a

theorem pred_le_pred {n : ℕ} {m : ℕ} : n ≤ m → Nat.pred n ≤ Nat.pred m := sorry

theorem le_of_succ_le_succ {n : ℕ} {m : ℕ} : Nat.succ n ≤ Nat.succ m → n ≤ m :=
  pred_le_pred

protected instance decidable_le (a : ℕ) (b : ℕ) : Decidable (a ≤ b) :=
  sorry

protected instance decidable_lt (a : ℕ) (b : ℕ) : Decidable (a < b) :=
  nat.decidable_le (Nat.succ a) b

protected theorem eq_or_lt_of_le {a : ℕ} {b : ℕ} (h : a ≤ b) : a = b ∨ a < b :=
  less_than_or_equal.cases_on h (Or.inl rfl) fun (n : ℕ) (h : less_than_or_equal a n) => Or.inr (succ_le_succ h)

theorem lt_succ_of_le {a : ℕ} {b : ℕ} : a ≤ b → a < Nat.succ b :=
  succ_le_succ

@[simp] theorem succ_sub_succ_eq_sub (a : ℕ) (b : ℕ) : Nat.succ a - Nat.succ b = a - b :=
  nat.rec_on b ((fun (this : Nat.succ a - 1 = a - 0) => this) (Eq.refl (Nat.succ a - 1)))
    fun (b : ℕ) => congr_arg Nat.pred

theorem not_succ_le_self (n : ℕ) : ¬Nat.succ n ≤ n :=
  Nat.rec (not_succ_le_zero 0)
    (fun (a : ℕ) (b : ¬Nat.succ a ≤ a) (c : Nat.succ (Nat.succ a) ≤ Nat.succ a) => b (le_of_succ_le_succ c)) n

protected theorem lt_irrefl (n : ℕ) : ¬n < n :=
  not_succ_le_self n

protected theorem le_trans {n : ℕ} {m : ℕ} {k : ℕ} (h1 : n ≤ m) : m ≤ k → n ≤ k :=
  less_than_or_equal._oldrec h1 fun (p : ℕ) (h2 : less_than_or_equal m p) => less_than_or_equal.step

theorem pred_le (n : ℕ) : Nat.pred n ≤ n :=
  nat.cases_on n (idRhs (less_than_or_equal (Nat.pred 0) (Nat.pred 0)) less_than_or_equal.refl)
    fun (n : ℕ) =>
      idRhs (less_than_or_equal (Nat.pred (Nat.succ n)) (Nat.succ n)) (less_than_or_equal.step less_than_or_equal.refl)

theorem pred_lt {n : ℕ} : n ≠ 0 → Nat.pred n < n := sorry

theorem sub_le (a : ℕ) (b : ℕ) : a - b ≤ a :=
  nat.rec_on b (nat.le_refl (a - 0)) fun (b₁ : ℕ) => nat.le_trans (pred_le (a - b₁))

theorem sub_lt {a : ℕ} {b : ℕ} : 0 < a → 0 < b → a - b < a := sorry

protected theorem lt_of_lt_of_le {n : ℕ} {m : ℕ} {k : ℕ} : n < m → m ≤ k → n < k :=
  nat.le_trans

/- Basic nat.add lemmas -/

protected theorem zero_add (n : ℕ) : 0 + n = n := sorry

theorem succ_add (n : ℕ) (m : ℕ) : Nat.succ n + m = Nat.succ (n + m) := sorry

theorem add_succ (n : ℕ) (m : ℕ) : n + Nat.succ m = Nat.succ (n + m) :=
  rfl

protected theorem add_zero (n : ℕ) : n + 0 = n :=
  rfl

theorem add_one (n : ℕ) : n + 1 = Nat.succ n :=
  rfl

theorem succ_eq_add_one (n : ℕ) : Nat.succ n = n + 1 :=
  rfl

/- Basic lemmas for comparing numerals -/

protected theorem bit0_succ_eq (n : ℕ) : bit0 (Nat.succ n) = Nat.succ (Nat.succ (bit0 n)) :=
  (fun (this : Nat.succ (Nat.succ n + n) = Nat.succ (Nat.succ (n + n))) => this) (congr_arg Nat.succ (succ_add n n))

protected theorem zero_lt_bit0 {n : ℕ} : n ≠ 0 → 0 < bit0 n := sorry

protected theorem zero_lt_bit1 (n : ℕ) : 0 < bit1 n :=
  zero_lt_succ (bit0 n)

protected theorem bit0_ne_zero {n : ℕ} : n ≠ 0 → bit0 n ≠ 0 := sorry

protected theorem bit1_ne_zero (n : ℕ) : bit1 n ≠ 0 :=
  (fun (this : Nat.succ (n + n) ≠ 0) => this) fun (h : Nat.succ (n + n) = 0) => nat.no_confusion h

