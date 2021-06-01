/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.nodup
import Mathlib.data.list.intervals
import Mathlib.PostPort

namespace Mathlib

/-!
# Intervals in ℕ as multisets

For now this only covers `Ico n m`, the "closed-open" interval containing `[n, ..., m-1]`.
-/

namespace multiset


/-! ### Ico -/

/-- `Ico n m` is the multiset lifted from the list `Ico n m`, e.g. the set `{n, n+1, ..., m-1}`. -/
def Ico (n : ℕ) (m : ℕ) : multiset ℕ := ↑(list.Ico n m)

namespace Ico


theorem map_add (n : ℕ) (m : ℕ) (k : ℕ) : map (Add.add k) (Ico n m) = Ico (n + k) (m + k) :=
  congr_arg coe (list.Ico.map_add n m k)

theorem map_sub (n : ℕ) (m : ℕ) (k : ℕ) (h : k ≤ n) :
    map (fun (x : ℕ) => x - k) (Ico n m) = Ico (n - k) (m - k) :=
  congr_arg coe (list.Ico.map_sub n m k h)

theorem zero_bot (n : ℕ) : Ico 0 n = range n := congr_arg coe (list.Ico.zero_bot n)

@[simp] theorem card (n : ℕ) (m : ℕ) : coe_fn card (Ico n m) = m - n := list.Ico.length n m

theorem nodup (n : ℕ) (m : ℕ) : nodup (Ico n m) := list.Ico.nodup n m

@[simp] theorem mem {n : ℕ} {m : ℕ} {l : ℕ} : l ∈ Ico n m ↔ n ≤ l ∧ l < m := list.Ico.mem

theorem eq_zero_of_le {n : ℕ} {m : ℕ} (h : m ≤ n) : Ico n m = 0 :=
  congr_arg coe (list.Ico.eq_nil_of_le h)

@[simp] theorem self_eq_zero {n : ℕ} : Ico n n = 0 := eq_zero_of_le (le_refl n)

@[simp] theorem eq_zero_iff {n : ℕ} {m : ℕ} : Ico n m = 0 ↔ m ≤ n :=
  iff.trans (coe_eq_zero (list.Ico n m)) list.Ico.eq_empty_iff

theorem add_consecutive {n : ℕ} {m : ℕ} {l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
    Ico n m + Ico m l = Ico n l :=
  congr_arg coe (list.Ico.append_consecutive hnm hml)

@[simp] theorem inter_consecutive (n : ℕ) (m : ℕ) (l : ℕ) : Ico n m ∩ Ico m l = 0 :=
  congr_arg coe (list.Ico.bag_inter_consecutive n m l)

@[simp] theorem succ_singleton {n : ℕ} : Ico n (n + 1) = singleton n :=
  congr_arg coe list.Ico.succ_singleton

theorem succ_top {n : ℕ} {m : ℕ} (h : n ≤ m) : Ico n (m + 1) = m ::ₘ Ico n m := sorry

theorem eq_cons {n : ℕ} {m : ℕ} (h : n < m) : Ico n m = n ::ₘ Ico (n + 1) m :=
  congr_arg coe (list.Ico.eq_cons h)

@[simp] theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = singleton (m - 1) :=
  congr_arg coe (list.Ico.pred_singleton h)

@[simp] theorem not_mem_top {n : ℕ} {m : ℕ} : ¬m ∈ Ico n m := list.Ico.not_mem_top

theorem filter_lt_of_top_le {n : ℕ} {m : ℕ} {l : ℕ} (hml : m ≤ l) :
    filter (fun (x : ℕ) => x < l) (Ico n m) = Ico n m :=
  congr_arg coe (list.Ico.filter_lt_of_top_le hml)

theorem filter_lt_of_le_bot {n : ℕ} {m : ℕ} {l : ℕ} (hln : l ≤ n) :
    filter (fun (x : ℕ) => x < l) (Ico n m) = ∅ :=
  congr_arg coe (list.Ico.filter_lt_of_le_bot hln)

theorem filter_le_of_bot {n : ℕ} {m : ℕ} (hnm : n < m) :
    filter (fun (x : ℕ) => x ≤ n) (Ico n m) = singleton n :=
  congr_arg coe (list.Ico.filter_le_of_bot hnm)

theorem filter_lt_of_ge {n : ℕ} {m : ℕ} {l : ℕ} (hlm : l ≤ m) :
    filter (fun (x : ℕ) => x < l) (Ico n m) = Ico n l :=
  congr_arg coe (list.Ico.filter_lt_of_ge hlm)

@[simp] theorem filter_lt (n : ℕ) (m : ℕ) (l : ℕ) :
    filter (fun (x : ℕ) => x < l) (Ico n m) = Ico n (min m l) :=
  congr_arg coe (list.Ico.filter_lt n m l)

theorem filter_le_of_le_bot {n : ℕ} {m : ℕ} {l : ℕ} (hln : l ≤ n) :
    filter (fun (x : ℕ) => l ≤ x) (Ico n m) = Ico n m :=
  congr_arg coe (list.Ico.filter_le_of_le_bot hln)

theorem filter_le_of_top_le {n : ℕ} {m : ℕ} {l : ℕ} (hml : m ≤ l) :
    filter (fun (x : ℕ) => l ≤ x) (Ico n m) = ∅ :=
  congr_arg coe (list.Ico.filter_le_of_top_le hml)

theorem filter_le_of_le {n : ℕ} {m : ℕ} {l : ℕ} (hnl : n ≤ l) :
    filter (fun (x : ℕ) => l ≤ x) (Ico n m) = Ico l m :=
  congr_arg coe (list.Ico.filter_le_of_le hnl)

@[simp] theorem filter_le (n : ℕ) (m : ℕ) (l : ℕ) :
    filter (fun (x : ℕ) => l ≤ x) (Ico n m) = Ico (max n l) m :=
  congr_arg coe (list.Ico.filter_le n m l)

end Mathlib