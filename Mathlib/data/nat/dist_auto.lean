/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn, Jeremy Avigad
Distance function on the natural numbers.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.basic
import PostPort

namespace Mathlib

namespace nat


/- distance -/

/-- Distance (absolute value of difference) between natural numbers. -/
def dist (n : ℕ) (m : ℕ) : ℕ :=
  n - m + (m - n)

theorem dist.def (n : ℕ) (m : ℕ) : dist n m = n - m + (m - n) :=
  rfl

theorem dist_comm (n : ℕ) (m : ℕ) : dist n m = dist m n := sorry

@[simp] theorem dist_self (n : ℕ) : dist n n = 0 := sorry

theorem eq_of_dist_eq_zero {n : ℕ} {m : ℕ} (h : dist n m = 0) : n = m := sorry

theorem dist_eq_zero {n : ℕ} {m : ℕ} (h : n = m) : dist n m = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dist n m = 0)) h))
    (eq.mpr (id (Eq._oldrec (Eq.refl (dist m m = 0)) (dist_self m))) (Eq.refl 0))

theorem dist_eq_sub_of_le {n : ℕ} {m : ℕ} (h : n ≤ m) : dist n m = m - n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dist n m = m - n)) (dist.def n m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n - m + (m - n) = m - n)) (sub_eq_zero_of_le h)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 + (m - n) = m - n)) (zero_add (m - n)))) (Eq.refl (m - n))))

theorem dist_eq_sub_of_le_right {n : ℕ} {m : ℕ} (h : m ≤ n) : dist n m = n - m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dist n m = n - m)) (dist_comm n m))) (dist_eq_sub_of_le h)

theorem dist_tri_left (n : ℕ) (m : ℕ) : m ≤ dist n m + n :=
  le_trans (nat.le_sub_add m n) (add_le_add_right (le_add_left (m - n) (n - m)) n)

theorem dist_tri_right (n : ℕ) (m : ℕ) : m ≤ n + dist n m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m ≤ n + dist n m)) (add_comm n (dist n m)))) (dist_tri_left n m)

theorem dist_tri_left' (n : ℕ) (m : ℕ) : n ≤ dist n m + m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n ≤ dist n m + m)) (dist_comm n m))) (dist_tri_left m n)

theorem dist_tri_right' (n : ℕ) (m : ℕ) : n ≤ m + dist n m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n ≤ m + dist n m)) (dist_comm n m))) (dist_tri_right m n)

theorem dist_zero_right (n : ℕ) : dist n 0 = n :=
  Eq.trans (dist_eq_sub_of_le_right (zero_le n)) (nat.sub_zero n)

theorem dist_zero_left (n : ℕ) : dist 0 n = n :=
  Eq.trans (dist_eq_sub_of_le (zero_le n)) (nat.sub_zero n)

theorem dist_add_add_right (n : ℕ) (k : ℕ) (m : ℕ) : dist (n + k) (m + k) = dist n m := sorry

theorem dist_add_add_left (k : ℕ) (n : ℕ) (m : ℕ) : dist (k + n) (k + m) = dist n m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dist (k + n) (k + m) = dist n m)) (add_comm k n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (dist (n + k) (k + m) = dist n m)) (add_comm k m))) (dist_add_add_right n k m))

theorem dist_eq_intro {n : ℕ} {m : ℕ} {k : ℕ} {l : ℕ} (h : n + m = k + l) : dist n k = dist l m := sorry

protected theorem sub_lt_sub_add_sub (n : ℕ) (m : ℕ) (k : ℕ) : n - k ≤ n - m + (m - k) := sorry

theorem dist.triangle_inequality (n : ℕ) (m : ℕ) (k : ℕ) : dist n k ≤ dist n m + dist m k := sorry

theorem dist_mul_right (n : ℕ) (k : ℕ) (m : ℕ) : dist (n * k) (m * k) = dist n m * k := sorry

theorem dist_mul_left (k : ℕ) (n : ℕ) (m : ℕ) : dist (k * n) (k * m) = k * dist n m := sorry

-- TODO(Jeremy): do when we have max and minx

--theorem dist_eq_max_sub_min {i j : nat} : dist i j = (max i j) - min i j :=

--sorry

/-
or.elim (lt_or_ge i j)
  (assume : i < j,
    by rw [max_eq_right_of_lt this, min_eq_left_of_lt this, dist_eq_sub_of_lt this])
  (assume : i ≥ j,
    by rw [max_eq_left this , min_eq_right this, dist_eq_sub_of_le_right this])
-/

theorem dist_succ_succ {i : ℕ} {j : ℕ} : dist (Nat.succ i) (Nat.succ j) = dist i j := sorry

theorem dist_pos_of_ne {i : ℕ} {j : ℕ} : i ≠ j → 0 < dist i j := sorry

