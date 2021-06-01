/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.erase_dup
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Preparations for defining operations on `finset`.

The operations here ignore multiplicities,
and preparatory for defining the corresponding operations on `finset`.
-/

namespace multiset


/-! ### finset insert -/

/-- `ndinsert a s` is the lift of the list `insert` operation. This operation
  does not respect multiplicities, unlike `cons`, but it is suitable as
  an insert operation on `finset`. -/
def ndinsert {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) : multiset α :=
  quot.lift_on s (fun (l : List α) => ↑(list.insert a l)) sorry

@[simp] theorem coe_ndinsert {α : Type u_1} [DecidableEq α] (a : α) (l : List α) :
    ndinsert a ↑l = ↑(insert a l) :=
  rfl

@[simp] theorem ndinsert_zero {α : Type u_1} [DecidableEq α] (a : α) : ndinsert a 0 = a ::ₘ 0 := rfl

@[simp] theorem ndinsert_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} :
    a ∈ s → ndinsert a s = s :=
  quot.induction_on s
    fun (l : List α) (h : a ∈ Quot.mk setoid.r l) => congr_arg coe (list.insert_of_mem h)

@[simp] theorem ndinsert_of_not_mem {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} :
    ¬a ∈ s → ndinsert a s = a ::ₘ s :=
  quot.induction_on s
    fun (l : List α) (h : ¬a ∈ Quot.mk setoid.r l) => congr_arg coe (list.insert_of_not_mem h)

@[simp] theorem mem_ndinsert {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : multiset α} :
    a ∈ ndinsert b s ↔ a = b ∨ a ∈ s :=
  quot.induction_on s fun (l : List α) => list.mem_insert_iff

@[simp] theorem le_ndinsert_self {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) :
    s ≤ ndinsert a s :=
  quot.induction_on s
    fun (l : List α) => list.sublist.subperm (list.sublist_of_suffix (list.suffix_insert a l))

@[simp] theorem mem_ndinsert_self {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) :
    a ∈ ndinsert a s :=
  iff.mpr mem_ndinsert (Or.inl rfl)

theorem mem_ndinsert_of_mem {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : multiset α}
    (h : a ∈ s) : a ∈ ndinsert b s :=
  iff.mpr mem_ndinsert (Or.inr h)

@[simp] theorem length_ndinsert_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α}
    (h : a ∈ s) : coe_fn card (ndinsert a s) = coe_fn card s :=
  sorry

@[simp] theorem length_ndinsert_of_not_mem {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α}
    (h : ¬a ∈ s) : coe_fn card (ndinsert a s) = coe_fn card s + 1 :=
  sorry

theorem erase_dup_cons {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} :
    erase_dup (a ::ₘ s) = ndinsert a (erase_dup s) :=
  sorry

theorem nodup_ndinsert {α : Type u_1} [DecidableEq α] (a : α) {s : multiset α} :
    nodup s → nodup (ndinsert a s) :=
  quot.induction_on s fun (l : List α) => list.nodup_insert

theorem ndinsert_le {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} {t : multiset α} :
    ndinsert a s ≤ t ↔ s ≤ t ∧ a ∈ t :=
  sorry

theorem attach_ndinsert {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) :
    attach (ndinsert a s) =
        ndinsert { val := a, property := mem_ndinsert_self a s }
          (map
            (fun (p : Subtype fun (x : α) => x ∈ s) =>
              { val := subtype.val p, property := mem_ndinsert_of_mem (subtype.property p) })
            (attach s)) :=
  sorry

@[simp] theorem disjoint_ndinsert_left {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α}
    {t : multiset α} : disjoint (ndinsert a s) t ↔ ¬a ∈ t ∧ disjoint s t :=
  sorry

@[simp] theorem disjoint_ndinsert_right {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α}
    {t : multiset α} : disjoint s (ndinsert a t) ↔ ¬a ∈ s ∧ disjoint s t :=
  sorry

/-! ### finset union -/

/-- `ndunion s t` is the lift of the list `union` operation. This operation
  does not respect multiplicities, unlike `s ∪ t`, but it is suitable as
  a union operation on `finset`. (`s ∪ t` would also work as a union operation
  on finset, but this is more efficient.) -/
def ndunion {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : multiset α :=
  quotient.lift_on₂ s t (fun (l₁ l₂ : List α) => ↑(list.union l₁ l₂)) sorry

@[simp] theorem coe_ndunion {α : Type u_1} [DecidableEq α] (l₁ : List α) (l₂ : List α) :
    ndunion ↑l₁ ↑l₂ = ↑(l₁ ∪ l₂) :=
  rfl

@[simp] theorem zero_ndunion {α : Type u_1} [DecidableEq α] (s : multiset α) : ndunion 0 s = s :=
  quot.induction_on s fun (l : List α) => rfl

@[simp] theorem cons_ndunion {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α)
    (a : α) : ndunion (a ::ₘ s) t = ndinsert a (ndunion s t) :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => rfl

@[simp] theorem mem_ndunion {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α}
    {a : α} : a ∈ ndunion s t ↔ a ∈ s ∨ a ∈ t :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => list.mem_union

theorem le_ndunion_right {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    t ≤ ndunion s t :=
  quotient.induction_on₂ s t
    fun (l₁ l₂ : List α) =>
      list.sublist.subperm (list.sublist_of_suffix (list.suffix_union_right l₁ l₂))

theorem subset_ndunion_right {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    t ⊆ ndunion s t :=
  subset_of_le (le_ndunion_right s t)

theorem ndunion_le_add {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    ndunion s t ≤ s + t :=
  quotient.induction_on₂ s t
    fun (l₁ l₂ : List α) => list.sublist.subperm (list.union_sublist_append l₁ l₂)

theorem ndunion_le {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α}
    {u : multiset α} : ndunion s t ≤ u ↔ s ⊆ u ∧ t ≤ u :=
  sorry

theorem subset_ndunion_left {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    s ⊆ ndunion s t :=
  fun (a : α) (h : a ∈ s) => iff.mpr mem_ndunion (Or.inl h)

theorem le_ndunion_left {α : Type u_1} [DecidableEq α] {s : multiset α} (t : multiset α)
    (d : nodup s) : s ≤ ndunion s t :=
  iff.mpr (le_iff_subset d) (subset_ndunion_left s t)

theorem ndunion_le_union {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    ndunion s t ≤ s ∪ t :=
  iff.mpr ndunion_le { left := subset_of_le (le_union_left s t), right := le_union_right s t }

theorem nodup_ndunion {α : Type u_1} [DecidableEq α] (s : multiset α) {t : multiset α} :
    nodup t → nodup (ndunion s t) :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => list.nodup_union l₁

@[simp] theorem ndunion_eq_union {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α}
    (d : nodup s) : ndunion s t = s ∪ t :=
  le_antisymm (ndunion_le_union s t) (union_le (le_ndunion_left t d) (le_ndunion_right s t))

theorem erase_dup_add {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    erase_dup (s + t) = ndunion s (erase_dup t) :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => congr_arg coe (list.erase_dup_append l₁ l₂)

/-! ### finset inter -/

/-- `ndinter s t` is the lift of the list `∩` operation. This operation
  does not respect multiplicities, unlike `s ∩ t`, but it is suitable as
  an intersection operation on `finset`. (`s ∩ t` would also work as a union operation
  on finset, but this is more efficient.) -/
def ndinter {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : multiset α :=
  filter (fun (_x : α) => _x ∈ t) s

@[simp] theorem coe_ndinter {α : Type u_1} [DecidableEq α] (l₁ : List α) (l₂ : List α) :
    ndinter ↑l₁ ↑l₂ = ↑(l₁ ∩ l₂) :=
  rfl

@[simp] theorem zero_ndinter {α : Type u_1} [DecidableEq α] (s : multiset α) : ndinter 0 s = 0 :=
  rfl

@[simp] theorem cons_ndinter_of_mem {α : Type u_1} [DecidableEq α] {a : α} (s : multiset α)
    {t : multiset α} (h : a ∈ t) : ndinter (a ::ₘ s) t = a ::ₘ ndinter s t :=
  sorry

@[simp] theorem ndinter_cons_of_not_mem {α : Type u_1} [DecidableEq α] {a : α} (s : multiset α)
    {t : multiset α} (h : ¬a ∈ t) : ndinter (a ::ₘ s) t = ndinter s t :=
  sorry

@[simp] theorem mem_ndinter {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α}
    {a : α} : a ∈ ndinter s t ↔ a ∈ s ∧ a ∈ t :=
  mem_filter

@[simp] theorem nodup_ndinter {α : Type u_1} [DecidableEq α] {s : multiset α} (t : multiset α) :
    nodup s → nodup (ndinter s t) :=
  nodup_filter fun (_x : α) => _x ∈ t

theorem le_ndinter {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α}
    {u : multiset α} : s ≤ ndinter t u ↔ s ≤ t ∧ s ⊆ u :=
  sorry

theorem ndinter_le_left {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    ndinter s t ≤ s :=
  and.left (iff.mp le_ndinter (le_refl (ndinter s t)))

theorem ndinter_subset_left {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    ndinter s t ⊆ s :=
  subset_of_le (ndinter_le_left s t)

theorem ndinter_subset_right {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    ndinter s t ⊆ t :=
  and.right (iff.mp le_ndinter (le_refl (ndinter s t)))

theorem ndinter_le_right {α : Type u_1} [DecidableEq α] {s : multiset α} (t : multiset α)
    (d : nodup s) : ndinter s t ≤ t :=
  iff.mpr (le_iff_subset (nodup_ndinter t d)) (ndinter_subset_right s t)

theorem inter_le_ndinter {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    s ∩ t ≤ ndinter s t :=
  iff.mpr le_ndinter { left := inter_le_left s t, right := subset_of_le (inter_le_right s t) }

@[simp] theorem ndinter_eq_inter {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α}
    (d : nodup s) : ndinter s t = s ∩ t :=
  le_antisymm (le_inter (ndinter_le_left s t) (ndinter_le_right t d)) (inter_le_ndinter s t)

theorem ndinter_eq_zero_iff_disjoint {α : Type u_1} [DecidableEq α] {s : multiset α}
    {t : multiset α} : ndinter s t = 0 ↔ disjoint s t :=
  sorry

end Mathlib