/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.nat.default
import Mathlib.Lean3Lib.init.data.fin.basic
import Mathlib.PostPort

namespace Mathlib

namespace fin


protected def succ {n : ℕ} : fin n → fin (Nat.succ n) :=
  sorry

def of_nat {n : ℕ} (a : ℕ) : fin (Nat.succ n) :=
  { val := a % Nat.succ n, property := sorry }

protected def add {n : ℕ} : fin n → fin n → fin n :=
  sorry

protected def mul {n : ℕ} : fin n → fin n → fin n :=
  sorry

protected def sub {n : ℕ} : fin n → fin n → fin n :=
  sorry

protected def mod {n : ℕ} : fin n → fin n → fin n :=
  sorry

protected def div {n : ℕ} : fin n → fin n → fin n :=
  sorry

protected instance has_zero {n : ℕ} : HasZero (fin (Nat.succ n)) :=
  { zero := { val := 0, property := nat.succ_pos n } }

protected instance has_one {n : ℕ} : HasOne (fin (Nat.succ n)) :=
  { one := of_nat 1 }

protected instance has_add {n : ℕ} : Add (fin n) :=
  { add := fin.add }

protected instance has_sub {n : ℕ} : Sub (fin n) :=
  { sub := fin.sub }

protected instance has_mul {n : ℕ} : Mul (fin n) :=
  { mul := fin.mul }

protected instance has_mod {n : ℕ} : Mod (fin n) :=
  { mod := fin.mod }

protected instance has_div {n : ℕ} : Div (fin n) :=
  { div := fin.div }

theorem of_nat_zero {n : ℕ} : of_nat 0 = 0 :=
  rfl

theorem add_def {n : ℕ} (a : fin n) (b : fin n) : subtype.val (a + b) = (subtype.val a + subtype.val b) % n := sorry

theorem mul_def {n : ℕ} (a : fin n) (b : fin n) : subtype.val (a * b) = subtype.val a * subtype.val b % n := sorry

theorem sub_def {n : ℕ} (a : fin n) (b : fin n) : subtype.val (a - b) = subtype.val a - subtype.val b := sorry

theorem mod_def {n : ℕ} (a : fin n) (b : fin n) : subtype.val (a % b) = subtype.val a % subtype.val b := sorry

theorem div_def {n : ℕ} (a : fin n) (b : fin n) : subtype.val (a / b) = subtype.val a / subtype.val b := sorry

theorem lt_def {n : ℕ} (a : fin n) (b : fin n) : a < b = (subtype.val a < subtype.val b) := sorry

theorem le_def {n : ℕ} (a : fin n) (b : fin n) : a ≤ b = (subtype.val a ≤ subtype.val b) := sorry

theorem val_zero {n : ℕ} : subtype.val 0 = 0 :=
  rfl

def pred {n : ℕ} (i : fin (Nat.succ n)) : i ≠ 0 → fin n :=
  sorry

