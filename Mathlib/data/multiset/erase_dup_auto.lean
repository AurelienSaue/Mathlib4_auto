/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.nodup
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Erasing duplicates in a multiset.
-/

namespace multiset


/-! ### erase_dup -/

/-- `erase_dup s` removes duplicates from `s`, yielding a `nodup` multiset. -/
def erase_dup {α : Type u_1} [DecidableEq α] (s : multiset α) : multiset α :=
  quot.lift_on s (fun (l : List α) => ↑(list.erase_dup l)) sorry

@[simp] theorem coe_erase_dup {α : Type u_1} [DecidableEq α] (l : List α) :
    erase_dup ↑l = ↑(list.erase_dup l) :=
  rfl

@[simp] theorem erase_dup_zero {α : Type u_1} [DecidableEq α] : erase_dup 0 = 0 := rfl

@[simp] theorem mem_erase_dup {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} :
    a ∈ erase_dup s ↔ a ∈ s :=
  quot.induction_on s fun (l : List α) => list.mem_erase_dup

@[simp] theorem erase_dup_cons_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} :
    a ∈ s → erase_dup (a ::ₘ s) = erase_dup s :=
  quot.induction_on s
    fun (l : List α) (m : a ∈ Quot.mk setoid.r l) => congr_arg coe (list.erase_dup_cons_of_mem m)

@[simp] theorem erase_dup_cons_of_not_mem {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} :
    ¬a ∈ s → erase_dup (a ::ₘ s) = a ::ₘ erase_dup s :=
  quot.induction_on s
    fun (l : List α) (m : ¬a ∈ Quot.mk setoid.r l) =>
      congr_arg coe (list.erase_dup_cons_of_not_mem m)

theorem erase_dup_le {α : Type u_1} [DecidableEq α] (s : multiset α) : erase_dup s ≤ s :=
  quot.induction_on s fun (l : List α) => list.sublist.subperm (list.erase_dup_sublist l)

theorem erase_dup_subset {α : Type u_1} [DecidableEq α] (s : multiset α) : erase_dup s ⊆ s :=
  subset_of_le (erase_dup_le s)

theorem subset_erase_dup {α : Type u_1} [DecidableEq α] (s : multiset α) : s ⊆ erase_dup s :=
  fun (a : α) => iff.mpr mem_erase_dup

@[simp] theorem erase_dup_subset' {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} :
    erase_dup s ⊆ t ↔ s ⊆ t :=
  { mp := subset.trans (subset_erase_dup s), mpr := subset.trans (erase_dup_subset s) }

@[simp] theorem subset_erase_dup' {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} :
    s ⊆ erase_dup t ↔ s ⊆ t :=
  { mp := fun (h : s ⊆ erase_dup t) => subset.trans h (erase_dup_subset t),
    mpr := fun (h : s ⊆ t) => subset.trans h (subset_erase_dup t) }

@[simp] theorem nodup_erase_dup {α : Type u_1} [DecidableEq α] (s : multiset α) :
    nodup (erase_dup s) :=
  quot.induction_on s list.nodup_erase_dup

theorem erase_dup_eq_self {α : Type u_1} [DecidableEq α] {s : multiset α} :
    erase_dup s = s ↔ nodup s :=
  sorry

theorem erase_dup_eq_zero {α : Type u_1} [DecidableEq α] {s : multiset α} :
    erase_dup s = 0 ↔ s = 0 :=
  { mp := fun (h : erase_dup s = 0) => eq_zero_of_subset_zero (h ▸ subset_erase_dup s),
    mpr := fun (h : s = 0) => Eq.symm h ▸ erase_dup_zero }

@[simp] theorem erase_dup_singleton {α : Type u_1} [DecidableEq α] {a : α} :
    erase_dup (a ::ₘ 0) = a ::ₘ 0 :=
  iff.mpr erase_dup_eq_self (nodup_singleton a)

theorem le_erase_dup {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} :
    s ≤ erase_dup t ↔ s ≤ t ∧ nodup s :=
  sorry

theorem erase_dup_ext {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} :
    erase_dup s = erase_dup t ↔ ∀ (a : α), a ∈ s ↔ a ∈ t :=
  sorry

theorem erase_dup_map_erase_dup_eq {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β]
    (f : α → β) (s : multiset α) : erase_dup (map f (erase_dup s)) = erase_dup (map f s) :=
  sorry

@[simp] theorem erase_dup_nsmul {α : Type u_1} [DecidableEq α] {s : multiset α} {n : ℕ}
    (h0 : n ≠ 0) : erase_dup (n •ℕ s) = erase_dup s :=
  sorry

theorem nodup.le_erase_dup_iff_le {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α}
    (hno : nodup s) : s ≤ erase_dup t ↔ s ≤ t :=
  sorry

end multiset


theorem multiset.nodup.le_nsmul_iff_le {α : Type u_1} {s : multiset α} {t : multiset α} {n : ℕ}
    (h : multiset.nodup s) (hn : n ≠ 0) : s ≤ n •ℕ t ↔ s ≤ t :=
  sorry

end Mathlib