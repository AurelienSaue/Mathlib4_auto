/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.big_operators.basic
import Mathlib.data.finset.intervals
import Mathlib.PostPort

universes u_1 v 

namespace Mathlib

/-!
# Results about big operators over intervals

We prove results about big operators over intervals (mostly the `ℕ`-valued `Ico m n`).
-/

namespace finset


theorem sum_Ico_add {δ : Type u_1} [add_comm_monoid δ] (f : ℕ → δ) (m : ℕ) (n : ℕ) (k : ℕ) : (finset.sum (Ico m n) fun (l : ℕ) => f (k + l)) = finset.sum (Ico (m + k) (n + k)) fun (l : ℕ) => f l :=
  Eq.subst (Ico.image_add m n k) Eq.symm
    (sum_image fun (x : ℕ) (hx : x ∈ Ico m n) (y : ℕ) (hy : y ∈ Ico m n) (h : k + x = k + y) => nat.add_left_cancel h)

theorem prod_Ico_add {β : Type v} [comm_monoid β] (f : ℕ → β) (m : ℕ) (n : ℕ) (k : ℕ) : (finset.prod (Ico m n) fun (l : ℕ) => f (k + l)) = finset.prod (Ico (m + k) (n + k)) fun (l : ℕ) => f l :=
  sum_Ico_add f m n k

theorem sum_Ico_succ_top {δ : Type u_1} [add_comm_monoid δ] {a : ℕ} {b : ℕ} (hab : a ≤ b) (f : ℕ → δ) : (finset.sum (Ico a (b + 1)) fun (k : ℕ) => f k) = (finset.sum (Ico a b) fun (k : ℕ) => f k) + f b := sorry

theorem prod_Ico_succ_top {β : Type v} [comm_monoid β] {a : ℕ} {b : ℕ} (hab : a ≤ b) (f : ℕ → β) : (finset.prod (Ico a (b + 1)) fun (k : ℕ) => f k) = (finset.prod (Ico a b) fun (k : ℕ) => f k) * f b :=
  sum_Ico_succ_top hab fun (k : ℕ) => f k

theorem sum_eq_sum_Ico_succ_bot {δ : Type u_1} [add_comm_monoid δ] {a : ℕ} {b : ℕ} (hab : a < b) (f : ℕ → δ) : (finset.sum (Ico a b) fun (k : ℕ) => f k) = f a + finset.sum (Ico (a + 1) b) fun (k : ℕ) => f k := sorry

theorem prod_eq_prod_Ico_succ_bot {β : Type v} [comm_monoid β] {a : ℕ} {b : ℕ} (hab : a < b) (f : ℕ → β) : (finset.prod (Ico a b) fun (k : ℕ) => f k) = f a * finset.prod (Ico (a + 1) b) fun (k : ℕ) => f k :=
  sum_eq_sum_Ico_succ_bot hab fun (k : ℕ) => f k

theorem prod_Ico_consecutive {β : Type v} [comm_monoid β] (f : ℕ → β) {m : ℕ} {n : ℕ} {k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) : ((finset.prod (Ico m n) fun (i : ℕ) => f i) * finset.prod (Ico n k) fun (i : ℕ) => f i) =
  finset.prod (Ico m k) fun (i : ℕ) => f i :=
  Eq.subst (Ico.union_consecutive hmn hnk) Eq.symm (prod_union (Ico.disjoint_consecutive m n k))

theorem sum_range_add_sum_Ico {β : Type v} [add_comm_monoid β] (f : ℕ → β) {m : ℕ} {n : ℕ} (h : m ≤ n) : ((finset.sum (range m) fun (k : ℕ) => f k) + finset.sum (Ico m n) fun (k : ℕ) => f k) =
  finset.sum (range n) fun (k : ℕ) => f k :=
  Ico.zero_bot m ▸ Ico.zero_bot n ▸ sum_Ico_consecutive f (nat.zero_le m) h

theorem sum_Ico_eq_add_neg {δ : Type u_1} [add_comm_group δ] (f : ℕ → δ) {m : ℕ} {n : ℕ} (h : m ≤ n) : (finset.sum (Ico m n) fun (k : ℕ) => f k) =
  (finset.sum (range n) fun (k : ℕ) => f k) + -finset.sum (range m) fun (k : ℕ) => f k := sorry

theorem sum_Ico_eq_sub {δ : Type u_1} [add_comm_group δ] (f : ℕ → δ) {m : ℕ} {n : ℕ} (h : m ≤ n) : (finset.sum (Ico m n) fun (k : ℕ) => f k) =
  (finset.sum (range n) fun (k : ℕ) => f k) - finset.sum (range m) fun (k : ℕ) => f k := sorry

theorem sum_Ico_eq_sum_range {β : Type v} [add_comm_monoid β] (f : ℕ → β) (m : ℕ) (n : ℕ) : (finset.sum (Ico m n) fun (k : ℕ) => f k) = finset.sum (range (n - m)) fun (k : ℕ) => f (m + k) := sorry

theorem prod_Ico_reflect {β : Type v} [comm_monoid β] (f : ℕ → β) (k : ℕ) {m : ℕ} {n : ℕ} (h : m ≤ n + 1) : (finset.prod (Ico k m) fun (j : ℕ) => f (n - j)) = finset.prod (Ico (n + 1 - m) (n + 1 - k)) fun (j : ℕ) => f j := sorry

theorem sum_Ico_reflect {δ : Type u_1} [add_comm_monoid δ] (f : ℕ → δ) (k : ℕ) {m : ℕ} {n : ℕ} (h : m ≤ n + 1) : (finset.sum (Ico k m) fun (j : ℕ) => f (n - j)) = finset.sum (Ico (n + 1 - m) (n + 1 - k)) fun (j : ℕ) => f j :=
  prod_Ico_reflect f k h

theorem prod_range_reflect {β : Type v} [comm_monoid β] (f : ℕ → β) (n : ℕ) : (finset.prod (range n) fun (j : ℕ) => f (n - 1 - j)) = finset.prod (range n) fun (j : ℕ) => f j := sorry

theorem sum_range_reflect {δ : Type u_1} [add_comm_monoid δ] (f : ℕ → δ) (n : ℕ) : (finset.sum (range n) fun (j : ℕ) => f (n - 1 - j)) = finset.sum (range n) fun (j : ℕ) => f j :=
  prod_range_reflect f n

@[simp] theorem prod_Ico_id_eq_factorial (n : ℕ) : (finset.prod (Ico 1 (n + 1)) fun (x : ℕ) => x) = nat.factorial n := sorry

@[simp] theorem prod_range_add_one_eq_factorial (n : ℕ) : (finset.prod (range n) fun (x : ℕ) => x + 1) = nat.factorial n := sorry

/-- Gauss' summation formula -/
theorem sum_range_id_mul_two (n : ℕ) : (finset.sum (range n) fun (i : ℕ) => i) * bit0 1 = n * (n - 1) := sorry

/-- Gauss' summation formula -/
theorem sum_range_id (n : ℕ) : (finset.sum (range n) fun (i : ℕ) => i) = n * (n - 1) / bit0 1 := sorry

