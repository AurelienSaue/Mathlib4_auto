/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.range
import Mathlib.data.list.bag_inter
import Mathlib.PostPort

namespace Mathlib

namespace list


/--
`Ico n m` is the list of natural numbers `n ≤ x < m`.
(Ico stands for "interval, closed-open".)

See also `data/set/intervals.lean` for `set.Ico`, modelling intervals in general preorders, and
`multiset.Ico` and `finset.Ico` for `n ≤ x < m` as a multiset or as a finset.

@TODO (anyone): Define `Ioo` and `Icc`, state basic lemmas about them.
@TODO (anyone): Also do the versions for integers?
@TODO (anyone): One could generalise even further, defining
'locally finite partial orders', for which `set.Ico a b` is `[finite]`, and
'locally finite total orders', for which there is a list model.
 -/
def Ico (n : ℕ) (m : ℕ) : List ℕ :=
  range' n (m - n)

namespace Ico


theorem zero_bot (n : ℕ) : Ico 0 n = range n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Ico 0 n = range n)) (equations._eqn_1 0 n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (range' 0 (n - 0) = range n)) (nat.sub_zero n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (range' 0 n = range n)) (range_eq_range' n))) (Eq.refl (range' 0 n))))

@[simp] theorem length (n : ℕ) (m : ℕ) : length (Ico n m) = m - n := sorry

theorem pairwise_lt (n : ℕ) (m : ℕ) : pairwise Less (Ico n m) :=
  id (eq.mpr (id (propext ((fun (s n : ℕ) => iff_true_intro (pairwise_lt_range' s n)) n (m - n)))) trivial)

theorem nodup (n : ℕ) (m : ℕ) : nodup (Ico n m) :=
  id (eq.mpr (id (propext ((fun (s n : ℕ) => iff_true_intro (nodup_range' s n)) n (m - n)))) trivial)

@[simp] theorem mem {n : ℕ} {m : ℕ} {l : ℕ} : l ∈ Ico n m ↔ n ≤ l ∧ l < m := sorry

theorem eq_nil_of_le {n : ℕ} {m : ℕ} (h : m ≤ n) : Ico n m = [] := sorry

theorem map_add (n : ℕ) (m : ℕ) (k : ℕ) : map (Add.add k) (Ico n m) = Ico (n + k) (m + k) := sorry

theorem map_sub (n : ℕ) (m : ℕ) (k : ℕ) (h₁ : k ≤ n) : map (fun (x : ℕ) => x - k) (Ico n m) = Ico (n - k) (m - k) := sorry

@[simp] theorem self_empty {n : ℕ} : Ico n n = [] :=
  eq_nil_of_le (le_refl n)

@[simp] theorem eq_empty_iff {n : ℕ} {m : ℕ} : Ico n m = [] ↔ m ≤ n := sorry

theorem append_consecutive {n : ℕ} {m : ℕ} {l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) : Ico n m ++ Ico m l = Ico n l := sorry

@[simp] theorem inter_consecutive (n : ℕ) (m : ℕ) (l : ℕ) : Ico n m ∩ Ico m l = [] := sorry

@[simp] theorem bag_inter_consecutive (n : ℕ) (m : ℕ) (l : ℕ) : list.bag_inter (Ico n m) (Ico m l) = [] :=
  iff.mpr (bag_inter_nil_iff_inter_nil (Ico n m) (Ico m l)) (inter_consecutive n m l)

@[simp] theorem succ_singleton {n : ℕ} : Ico n (n + 1) = [n] := sorry

theorem succ_top {n : ℕ} {m : ℕ} (h : n ≤ m) : Ico n (m + 1) = Ico n m ++ [m] :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Ico n (m + 1) = Ico n m ++ [m])) (Eq.symm succ_singleton)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Ico n (m + 1) = Ico n m ++ Ico m (m + 1))) (append_consecutive h (nat.le_succ m))))
      (Eq.refl (Ico n (m + 1))))

theorem eq_cons {n : ℕ} {m : ℕ} (h : n < m) : Ico n m = n :: Ico (n + 1) m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Ico n m = n :: Ico (n + 1) m)) (Eq.symm (append_consecutive (nat.le_succ n) h))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Ico n (Nat.succ n) ++ Ico (Nat.succ n) m = n :: Ico (n + 1) m)) succ_singleton))
      (Eq.refl ([n] ++ Ico (Nat.succ n) m)))

@[simp] theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = [m - 1] := sorry

theorem chain'_succ (n : ℕ) (m : ℕ) : chain' (fun (a b : ℕ) => b = Nat.succ a) (Ico n m) := sorry

@[simp] theorem not_mem_top {n : ℕ} {m : ℕ} : ¬m ∈ Ico n m := sorry

theorem filter_lt_of_top_le {n : ℕ} {m : ℕ} {l : ℕ} (hml : m ≤ l) : filter (fun (x : ℕ) => x < l) (Ico n m) = Ico n m :=
  iff.mpr filter_eq_self fun (k : ℕ) (hk : k ∈ Ico n m) => lt_of_lt_of_le (and.right (iff.mp mem hk)) hml

theorem filter_lt_of_le_bot {n : ℕ} {m : ℕ} {l : ℕ} (hln : l ≤ n) : filter (fun (x : ℕ) => x < l) (Ico n m) = [] :=
  iff.mpr filter_eq_nil fun (k : ℕ) (hk : k ∈ Ico n m) => not_lt_of_le (le_trans hln (and.left (iff.mp mem hk)))

theorem filter_lt_of_ge {n : ℕ} {m : ℕ} {l : ℕ} (hlm : l ≤ m) : filter (fun (x : ℕ) => x < l) (Ico n m) = Ico n l := sorry

@[simp] theorem filter_lt (n : ℕ) (m : ℕ) (l : ℕ) : filter (fun (x : ℕ) => x < l) (Ico n m) = Ico n (min m l) := sorry

theorem filter_le_of_le_bot {n : ℕ} {m : ℕ} {l : ℕ} (hln : l ≤ n) : filter (fun (x : ℕ) => l ≤ x) (Ico n m) = Ico n m :=
  iff.mpr filter_eq_self fun (k : ℕ) (hk : k ∈ Ico n m) => le_trans hln (and.left (iff.mp mem hk))

theorem filter_le_of_top_le {n : ℕ} {m : ℕ} {l : ℕ} (hml : m ≤ l) : filter (fun (x : ℕ) => l ≤ x) (Ico n m) = [] :=
  iff.mpr filter_eq_nil fun (k : ℕ) (hk : k ∈ Ico n m) => not_le_of_gt (lt_of_lt_of_le (and.right (iff.mp mem hk)) hml)

theorem filter_le_of_le {n : ℕ} {m : ℕ} {l : ℕ} (hnl : n ≤ l) : filter (fun (x : ℕ) => l ≤ x) (Ico n m) = Ico l m := sorry

@[simp] theorem filter_le (n : ℕ) (m : ℕ) (l : ℕ) : filter (fun (x : ℕ) => l ≤ x) (Ico n m) = Ico (max n l) m := sorry

theorem filter_lt_of_succ_bot {n : ℕ} {m : ℕ} (hnm : n < m) : filter (fun (x : ℕ) => x < n + 1) (Ico n m) = [n] := sorry

@[simp] theorem filter_le_of_bot {n : ℕ} {m : ℕ} (hnm : n < m) : filter (fun (x : ℕ) => x ≤ n) (Ico n m) = [n] :=
  eq.mpr (id (Eq._oldrec (Eq.refl (filter (fun (x : ℕ) => x ≤ n) (Ico n m) = [n])) (Eq.symm (filter_lt_of_succ_bot hnm))))
    (filter_congr fun (_x : ℕ) (_x_1 : _x ∈ Ico n m) => iff.symm nat.lt_succ_iff)

/--
For any natural numbers n, a, and b, one of the following holds:
1. n < a
2. n ≥ b
3. n ∈ Ico a b
-/
theorem trichotomy (n : ℕ) (a : ℕ) (b : ℕ) : n < a ∨ b ≤ n ∨ n ∈ Ico a b := sorry

