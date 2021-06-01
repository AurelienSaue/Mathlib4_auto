/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.monotonicity.basic
import Mathlib.data.set.lattice
import Mathlib.order.bounds
import Mathlib.PostPort

universes u_1 

namespace Mathlib

theorem mul_mono_nonneg {α : Type u_1} {x : α} {y : α} {z : α} [ordered_semiring α] (h' : 0 ≤ z)
    (h : x ≤ y) : x * z ≤ y * z :=
  mul_le_mul_of_nonneg_right h h'

theorem lt_of_mul_lt_mul_neg_right {α : Type u_1} {a : α} {b : α} {c : α} [linear_ordered_ring α]
    (h : a * c < b * c) (hc : c ≤ 0) : b < a :=
  sorry

theorem mul_mono_nonpos {α : Type u_1} {x : α} {y : α} {z : α} [linear_ordered_ring α] (h' : z ≤ 0)
    (h : y ≤ x) : x * z ≤ y * z :=
  decidable.by_contradiction
    fun (h'' : ¬x * z ≤ y * z) => not_le_of_lt (lt_of_mul_lt_mul_neg_right (lt_of_not_ge h'') h') h

theorem nat.sub_mono_left_strict {x : ℕ} {y : ℕ} {z : ℕ} (h' : z ≤ x) (h : x < y) : x - z < y - z :=
  nat.lt_of_add_lt_add_left
    (eq.mpr (id (Eq._oldrec (Eq.refl (z + (x - z) < z + (y - z))) (nat.add_sub_of_le h')))
      (eq.mpr
        (id (Eq._oldrec (Eq.refl (x < z + (y - z))) (nat.add_sub_of_le (le_trans h' (le_of_lt h)))))
        h))

theorem nat.sub_mono_right_strict {x : ℕ} {y : ℕ} {z : ℕ} (h' : x ≤ z) (h : y < x) :
    z - x < z - y :=
  sorry

end Mathlib