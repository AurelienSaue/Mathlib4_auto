/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.nat.basic
 

universes u 

namespace Mathlib

/-- `fin n` is the subtype of `ℕ` consisting of natural numbers strictly smaller than `n`. -/
def fin (n : ℕ)  :=
  Subtype fun (i : ℕ) => i < n

namespace fin


/-- Backwards-compatible constructor for `fin n`. -/
def mk {n : ℕ} (i : ℕ) (h : i < n) : fin n :=
  { val := i, property := h }

protected def lt {n : ℕ} (a : fin n) (b : fin n)  :=
  subtype.val a < subtype.val b

protected def le {n : ℕ} (a : fin n) (b : fin n)  :=
  subtype.val a ≤ subtype.val b

protected instance has_lt {n : ℕ} : HasLess (fin n) :=
  { Less := fin.lt }

protected instance has_le {n : ℕ} : HasLessEq (fin n) :=
  { LessEq := fin.le }

protected instance decidable_lt {n : ℕ} (a : fin n) (b : fin n) : Decidable (a < b) :=
  nat.decidable_lt (subtype.val a) (subtype.val b)

protected instance decidable_le {n : ℕ} (a : fin n) (b : fin n) : Decidable (a ≤ b) :=
  nat.decidable_le (subtype.val a) (subtype.val b)

def elim0 {α : fin 0 → Sort u} (x : fin 0) : α x :=
  sorry

theorem eq_of_veq {n : ℕ} {i : fin n} {j : fin n} : subtype.val i = subtype.val j → i = j := sorry

theorem veq_of_eq {n : ℕ} {i : fin n} {j : fin n} : i = j → subtype.val i = subtype.val j := sorry

theorem ne_of_vne {n : ℕ} {i : fin n} {j : fin n} (h : subtype.val i ≠ subtype.val j) : i ≠ j :=
  fun (h' : i = j) => absurd (veq_of_eq h') h

theorem vne_of_ne {n : ℕ} {i : fin n} {j : fin n} (h : i ≠ j) : subtype.val i ≠ subtype.val j :=
  fun (h' : subtype.val i = subtype.val j) => absurd (eq_of_veq h') h

end fin


protected instance fin.decidable_eq (n : ℕ) : DecidableEq (fin n) :=
  fun (i j : fin n) => decidable_of_decidable_of_iff (nat.decidable_eq (subtype.val i) (subtype.val j)) sorry

