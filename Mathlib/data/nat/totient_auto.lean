/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.big_operators.basic
import Mathlib.PostPort

namespace Mathlib

namespace nat


/-- Euler's totient function. This counts the number of positive integers less than `n` which are
coprime with `n`. -/
def totient (n : ℕ) : ℕ := finset.card (finset.filter (coprime n) (finset.range n))

@[simp] theorem totient_zero : totient 0 = 0 := rfl

theorem totient_le (n : ℕ) : totient n ≤ n :=
  trans_rel_left LessEq
    (finset.card_le_of_subset (finset.filter_subset (coprime n) (finset.range n)))
    (finset.card_range n)

theorem totient_pos {n : ℕ} : 0 < n → 0 < totient n := sorry

theorem sum_totient (n : ℕ) :
    (finset.sum (finset.filter (fun (_x : ℕ) => _x ∣ n) (finset.range (Nat.succ n)))
          fun (m : ℕ) => totient m) =
        n :=
  sorry

end Mathlib