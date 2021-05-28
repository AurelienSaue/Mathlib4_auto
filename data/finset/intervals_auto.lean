/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.finset.basic
import Mathlib.data.multiset.intervals
import PostPort

namespace Mathlib

/-!
# Intervals in ℕ as finsets

For now this only covers `Ico n m`, the "closed-open" interval containing `[n, ..., m-1]`.
-/

namespace finset


/-! ### intervals -/

/- Ico (a closed open interval) -/

/-- `Ico n m` is the set of natural numbers `n ≤ k < m`. -/
def Ico (n : ℕ) (m : ℕ) : finset ℕ :=
  mk (multiset.Ico n m) (multiset.Ico.nodup n m)

namespace Ico


@[simp] theorem val (n : ℕ) (m : ℕ) : val (Ico n m) = multiset.Ico n m :=
  rfl

@[simp] theorem to_finset (n : ℕ) (m : ℕ) : multiset.to_finset (multiset.Ico n m) = Ico n m :=
  Eq.symm (multiset.to_finset_eq (multiset.Ico.nodup n m))

theorem image_add (n : ℕ) (m : ℕ) (k : ℕ) : image (Add.add k) (Ico n m) = Ico (n + k) (m + k) := sorry

theorem image_sub (n : ℕ) (m : ℕ) (k : ℕ) (h : k ≤ n) : image (fun (x : ℕ) => x - k) (Ico n m) = Ico (n - k) (m - k) := sorry

theorem zero_bot (n : ℕ) : Ico 0 n = range n :=
  eq_of_veq (multiset.Ico.zero_bot n)

@[simp] theorem card (n : ℕ) (m : ℕ) : card (Ico n m) = m - n :=
  multiset.Ico.card n m

@[simp] theorem mem {n : ℕ} {m : ℕ} {l : ℕ} : l ∈ Ico n m ↔ n ≤ l ∧ l < m :=
  multiset.Ico.mem

@[simp] theorem coe_eq_Ico {n : ℕ} {m : ℕ} : ↑(Ico n m) = set.Ico n m := sorry

theorem eq_empty_of_le {n : ℕ} {m : ℕ} (h : m ≤ n) : Ico n m = ∅ :=
  eq_of_veq (multiset.Ico.eq_zero_of_le h)

@[simp] theorem self_eq_empty (n : ℕ) : Ico n n = ∅ :=
  eq_empty_of_le (le_refl n)

@[simp] theorem eq_empty_iff {n : ℕ} {m : ℕ} : Ico n m = ∅ ↔ m ≤ n :=
  iff.trans (iff.symm val_eq_zero) multiset.Ico.eq_zero_iff

theorem subset_iff {m₁ : ℕ} {n₁ : ℕ} {m₂ : ℕ} {n₂ : ℕ} (hmn : m₁ < n₁) : Ico m₁ n₁ ⊆ Ico m₂ n₂ ↔ m₂ ≤ m₁ ∧ n₁ ≤ n₂ := sorry

protected theorem subset {m₁ : ℕ} {n₁ : ℕ} {m₂ : ℕ} {n₂ : ℕ} (hmm : m₂ ≤ m₁) (hnn : n₁ ≤ n₂) : Ico m₁ n₁ ⊆ Ico m₂ n₂ :=
  eq.mpr (id (Eq.trans (propext subset_iff) (forall_congr_eq fun (x : ℕ) => imp_congr_eq (propext mem) (propext mem))))
    fun (x : ℕ) (hx : m₁ ≤ x ∧ x < n₁) =>
      { left := le_trans hmm (and.left hx), right := lt_of_lt_of_le (and.right hx) hnn }

theorem union_consecutive {n : ℕ} {m : ℕ} {l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) : Ico n m ∪ Ico m l = Ico n l := sorry

theorem union' {n : ℕ} {m : ℕ} {l : ℕ} {k : ℕ} (hlm : l ≤ m) (hnk : n ≤ k) : Ico n m ∪ Ico l k = Ico (min n l) (max m k) := sorry

theorem union {n : ℕ} {m : ℕ} {l : ℕ} {k : ℕ} (h₁ : min n m ≤ max l k) (h₂ : min l k ≤ max n m) : Ico n m ∪ Ico l k = Ico (min n l) (max m k) := sorry

@[simp] theorem inter_consecutive (n : ℕ) (m : ℕ) (l : ℕ) : Ico n m ∩ Ico m l = ∅ := sorry

theorem inter {n : ℕ} {m : ℕ} {l : ℕ} {k : ℕ} : Ico n m ∩ Ico l k = Ico (max n l) (min m k) := sorry

theorem disjoint_consecutive (n : ℕ) (m : ℕ) (l : ℕ) : disjoint (Ico n m) (Ico m l) :=
  le_of_eq (inter_consecutive n m l)

@[simp] theorem succ_singleton (n : ℕ) : Ico n (n + 1) = singleton n :=
  eq_of_veq multiset.Ico.succ_singleton

theorem succ_top {n : ℕ} {m : ℕ} (h : n ≤ m) : Ico n (m + 1) = insert m (Ico n m) := sorry

theorem succ_top' {n : ℕ} {m : ℕ} (h : n < m) : Ico n m = insert (m - 1) (Ico n (m - 1)) := sorry

theorem insert_succ_bot {n : ℕ} {m : ℕ} (h : n < m) : insert n (Ico (n + 1) m) = Ico n m := sorry

@[simp] theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = singleton (m - 1) :=
  eq_of_veq (multiset.Ico.pred_singleton h)

@[simp] theorem not_mem_top {n : ℕ} {m : ℕ} : ¬m ∈ Ico n m :=
  multiset.Ico.not_mem_top

theorem filter_lt_of_top_le {n : ℕ} {m : ℕ} {l : ℕ} (hml : m ≤ l) : filter (fun (x : ℕ) => x < l) (Ico n m) = Ico n m :=
  eq_of_veq (multiset.Ico.filter_lt_of_top_le hml)

theorem filter_lt_of_le_bot {n : ℕ} {m : ℕ} {l : ℕ} (hln : l ≤ n) : filter (fun (x : ℕ) => x < l) (Ico n m) = ∅ :=
  eq_of_veq (multiset.Ico.filter_lt_of_le_bot hln)

theorem filter_Ico_bot {n : ℕ} {m : ℕ} (hnm : n < m) : filter (fun (x : ℕ) => x ≤ n) (Ico n m) = singleton n :=
  eq_of_veq (multiset.Ico.filter_le_of_bot hnm)

theorem filter_lt_of_ge {n : ℕ} {m : ℕ} {l : ℕ} (hlm : l ≤ m) : filter (fun (x : ℕ) => x < l) (Ico n m) = Ico n l :=
  eq_of_veq (multiset.Ico.filter_lt_of_ge hlm)

@[simp] theorem filter_lt (n : ℕ) (m : ℕ) (l : ℕ) : filter (fun (x : ℕ) => x < l) (Ico n m) = Ico n (min m l) :=
  eq_of_veq (multiset.Ico.filter_lt n m l)

theorem filter_le_of_le_bot {n : ℕ} {m : ℕ} {l : ℕ} (hln : l ≤ n) : filter (fun (x : ℕ) => l ≤ x) (Ico n m) = Ico n m :=
  eq_of_veq (multiset.Ico.filter_le_of_le_bot hln)

theorem filter_le_of_top_le {n : ℕ} {m : ℕ} {l : ℕ} (hml : m ≤ l) : filter (fun (x : ℕ) => l ≤ x) (Ico n m) = ∅ :=
  eq_of_veq (multiset.Ico.filter_le_of_top_le hml)

theorem filter_le_of_le {n : ℕ} {m : ℕ} {l : ℕ} (hnl : n ≤ l) : filter (fun (x : ℕ) => l ≤ x) (Ico n m) = Ico l m :=
  eq_of_veq (multiset.Ico.filter_le_of_le hnl)

@[simp] theorem filter_le (n : ℕ) (m : ℕ) (l : ℕ) : filter (fun (x : ℕ) => l ≤ x) (Ico n m) = Ico (max n l) m :=
  eq_of_veq (multiset.Ico.filter_le n m l)

@[simp] theorem diff_left (l : ℕ) (n : ℕ) (m : ℕ) : Ico n m \ Ico n l = Ico (max n l) m := sorry

@[simp] theorem diff_right (l : ℕ) (n : ℕ) (m : ℕ) : Ico n m \ Ico l m = Ico n (min m l) := sorry

theorem image_const_sub {k : ℕ} {m : ℕ} {n : ℕ} (hkn : k ≤ n) : image (fun (j : ℕ) => n - j) (Ico k m) = Ico (n + 1 - m) (n + 1 - k) := sorry

end Ico


theorem range_eq_Ico (n : ℕ) : range n = Ico 0 n := sorry

theorem range_image_pred_top_sub (n : ℕ) : image (fun (j : ℕ) => n - 1 - j) (range n) = range n := sorry

-- TODO We don't yet attempt to reproduce the entire interface for `Ico` for `Ico_ℤ`.

/-- `Ico_ℤ l u` is the set of integers `l ≤ k < u`. -/
def Ico_ℤ (l : ℤ) (u : ℤ) : finset ℤ :=
  map (function.embedding.mk (fun (n : ℕ) => ↑n + l) sorry) (range (int.to_nat (u - l)))

@[simp] theorem Ico_ℤ.mem {n : ℤ} {m : ℤ} {l : ℤ} : l ∈ Ico_ℤ n m ↔ n ≤ l ∧ l < m := sorry

@[simp] theorem Ico_ℤ.card (l : ℤ) (u : ℤ) : card (Ico_ℤ l u) = int.to_nat (u - l) := sorry

