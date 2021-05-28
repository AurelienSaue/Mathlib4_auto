/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.basic
import PostPort

namespace Mathlib

/-!
# Partial predecessor and partial subtraction on the natural numbers

The usual definition of natural number subtraction (`nat.sub`) returns 0 as a "garbage value" for
`a - b` when `a < b`. Similarly, `nat.pred 0` is defined to be `0`. The functions in this file
wrap the result in an `option` type instead:

## Main definitions

- `nat.ppred`: a partial predecessor operation
- `nat.psub`: a partial subtraction operation

-/

namespace nat


/-- Partial predecessor operation. Returns `ppred n = some m`
  if `n = m + 1`, otherwise `none`. -/
@[simp] def ppred : ℕ → Option ℕ :=
  sorry

/-- Partial subtraction operation. Returns `psub m n = some k`
  if `m = n + k`, otherwise `none`. -/
@[simp] def psub (m : ℕ) : ℕ → Option ℕ :=
  sorry

theorem pred_eq_ppred (n : ℕ) : Nat.pred n = option.get_or_else (ppred n) 0 :=
  nat.cases_on n (Eq.refl (Nat.pred 0)) fun (n : ℕ) => Eq.refl (Nat.pred (Nat.succ n))

theorem sub_eq_psub (m : ℕ) (n : ℕ) : m - n = option.get_or_else (psub m n) 0 := sorry

@[simp] theorem ppred_eq_some {m : ℕ} {n : ℕ} : ppred n = some m ↔ Nat.succ m = n := sorry

@[simp] theorem ppred_eq_none {n : ℕ} : ppred n = none ↔ n = 0 := sorry

theorem psub_eq_some {m : ℕ} {n : ℕ} {k : ℕ} : psub m n = some k ↔ k + n = m := sorry

theorem psub_eq_none {m : ℕ} {n : ℕ} : psub m n = none ↔ m < n := sorry

theorem ppred_eq_pred {n : ℕ} (h : 0 < n) : ppred n = some (Nat.pred n) :=
  iff.mpr ppred_eq_some (succ_pred_eq_of_pos h)

theorem psub_eq_sub {m : ℕ} {n : ℕ} (h : n ≤ m) : psub m n = some (m - n) :=
  iff.mpr psub_eq_some (nat.sub_add_cancel h)

theorem psub_add (m : ℕ) (n : ℕ) (k : ℕ) : psub m (n + k) =
  do 
    let x ← psub m n 
    psub x k := sorry

/-- Same as `psub`, but with a more efficient implementation. -/
def psub' (m : ℕ) (n : ℕ) : Option ℕ :=
  ite (n ≤ m) (some (m - n)) none

theorem psub'_eq_psub (m : ℕ) (n : ℕ) : psub' m n = psub m n := sorry

