/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fin
import Mathlib.data.equiv.basic
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Equivalences for `fin n`
-/

/-- Equivalence between `fin 0` and `empty`. -/
def fin_zero_equiv : fin 0 ≃ empty :=
  equiv.mk fin_zero_elim empty.elim sorry sorry

/-- Equivalence between `fin 0` and `pempty`. -/
def fin_zero_equiv' : fin 0 ≃ pempty :=
  equiv.equiv_pempty sorry

/-- Equivalence between `fin 1` and `punit`. -/
def fin_one_equiv : fin 1 ≃ PUnit :=
  equiv.mk (fun (_x : fin 1) => Unit.unit) (fun (_x : PUnit) => 0) sorry sorry

/-- Equivalence between `fin 2` and `bool`. -/
def fin_two_equiv : fin (bit0 1) ≃ Bool :=
  equiv.mk (fin.cases false fun (_x : fin 1) => tt) (fun (b : Bool) => cond b 1 0) sorry sorry

/-- Equivalence between `fin n.succ` and `option (fin n)` -/
def fin_succ_equiv (n : ℕ) : fin (Nat.succ n) ≃ Option (fin n) :=
  equiv.mk (fun (x : fin (Nat.succ n)) => fin.cases none some x) (fun (x : Option (fin n)) => option.rec_on x 0 fin.succ)
    sorry sorry

@[simp] theorem fin_succ_equiv_zero {n : ℕ} : coe_fn (fin_succ_equiv n) 0 = none :=
  rfl

@[simp] theorem fin_succ_equiv_succ {n : ℕ} (m : fin n) : coe_fn (fin_succ_equiv n) (fin.succ m) = some m := sorry

@[simp] theorem fin_succ_equiv_symm_none {n : ℕ} : coe_fn (equiv.symm (fin_succ_equiv n)) none = 0 :=
  rfl

@[simp] theorem fin_succ_equiv_symm_some {n : ℕ} (m : fin n) : coe_fn (equiv.symm (fin_succ_equiv n)) (some m) = fin.succ m :=
  rfl

/-- Equivalence between `fin m ⊕ fin n` and `fin (m + n)` -/
def sum_fin_sum_equiv {m : ℕ} {n : ℕ} : fin m ⊕ fin n ≃ fin (m + n) :=
  equiv.mk
    (fun (x : fin m ⊕ fin n) =>
      sum.rec_on x (fun (y : fin m) => { val := subtype.val y, property := sorry })
        fun (y : fin n) => { val := m + subtype.val y, property := sorry })
    (fun (x : fin (m + n)) =>
      dite (subtype.val x < m) (fun (H : subtype.val x < m) => sum.inl { val := subtype.val x, property := H })
        fun (H : ¬subtype.val x < m) => sum.inr { val := subtype.val x - m, property := sorry })
    sorry sorry

/-- Equivalence between `fin m × fin n` and `fin (m * n)` -/
def fin_prod_fin_equiv {m : ℕ} {n : ℕ} : fin m × fin n ≃ fin (m * n) :=
  equiv.mk
    (fun (x : fin m × fin n) => { val := subtype.val (prod.snd x) + n * subtype.val (prod.fst x), property := sorry })
    (fun (x : fin (m * n)) =>
      (fun (H : 0 < n) =>
          ({ val := subtype.val x / n, property := sorry }, { val := subtype.val x % n, property := sorry }))
        sorry)
    sorry sorry

/-- `fin 0` is a subsingleton. -/
protected instance subsingleton_fin_zero : subsingleton (fin 0) :=
  equiv.subsingleton fin_zero_equiv

/-- `fin 1` is a subsingleton. -/
protected instance subsingleton_fin_one : subsingleton (fin 1) :=
  equiv.subsingleton fin_one_equiv

