/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.powerset
import Mathlib.data.multiset.range
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# The `nodup` predicate for multisets without duplicate elements.
-/

namespace multiset


/- nodup -/

/-- `nodup s` means that `s` has no duplicates, i.e. the multiplicity of
  any element is at most 1. -/
def nodup {α : Type u_1} (s : multiset α) := quot.lift_on s list.nodup sorry

@[simp] theorem coe_nodup {α : Type u_1} {l : List α} : nodup ↑l ↔ list.nodup l := iff.rfl

@[simp] theorem nodup_zero {α : Type u_1} : nodup 0 := list.pairwise.nil

@[simp] theorem nodup_cons {α : Type u_1} {a : α} {s : multiset α} :
    nodup (a ::ₘ s) ↔ ¬a ∈ s ∧ nodup s :=
  quot.induction_on s fun (l : List α) => list.nodup_cons

theorem nodup_cons_of_nodup {α : Type u_1} {a : α} {s : multiset α} (m : ¬a ∈ s) (n : nodup s) :
    nodup (a ::ₘ s) :=
  iff.mpr nodup_cons { left := m, right := n }

theorem nodup_singleton {α : Type u_1} (a : α) : nodup (a ::ₘ 0) := list.nodup_singleton

theorem nodup_of_nodup_cons {α : Type u_1} {a : α} {s : multiset α} (h : nodup (a ::ₘ s)) :
    nodup s :=
  and.right (iff.mp nodup_cons h)

theorem not_mem_of_nodup_cons {α : Type u_1} {a : α} {s : multiset α} (h : nodup (a ::ₘ s)) :
    ¬a ∈ s :=
  and.left (iff.mp nodup_cons h)

theorem nodup_of_le {α : Type u_1} {s : multiset α} {t : multiset α} (h : s ≤ t) :
    nodup t → nodup s :=
  le_induction_on h fun (l₁ l₂ : List α) => list.nodup_of_sublist

theorem not_nodup_pair {α : Type u_1} (a : α) : ¬nodup (a ::ₘ a ::ₘ 0) := list.not_nodup_pair

theorem nodup_iff_le {α : Type u_1} {s : multiset α} : nodup s ↔ ∀ (a : α), ¬a ::ₘ a ::ₘ 0 ≤ s :=
  quot.induction_on s
    fun (l : List α) =>
      iff.trans list.nodup_iff_sublist
        (forall_congr fun (a : α) => not_congr (iff.symm repeat_le_coe))

theorem nodup_iff_ne_cons_cons {α : Type u_1} {s : multiset α} :
    nodup s ↔ ∀ (a : α) (t : multiset α), s ≠ a ::ₘ a ::ₘ t :=
  sorry

theorem nodup_iff_count_le_one {α : Type u_1} [DecidableEq α] {s : multiset α} :
    nodup s ↔ ∀ (a : α), count a s ≤ 1 :=
  quot.induction_on s fun (l : List α) => list.nodup_iff_count_le_one

@[simp] theorem count_eq_one_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α}
    (d : nodup s) (h : a ∈ s) : count a s = 1 :=
  le_antisymm (iff.mp nodup_iff_count_le_one d a) (iff.mpr count_pos h)

theorem nodup_iff_pairwise {α : Type u_1} {s : multiset α} : nodup s ↔ pairwise ne s :=
  quotient.induction_on s
    fun (l : List α) => iff.symm (pairwise_coe_iff_pairwise fun (a b : α) => ne.symm)

theorem pairwise_of_nodup {α : Type u_1} {r : α → α → Prop} {s : multiset α} :
    (∀ (a : α), a ∈ s → ∀ (b : α), b ∈ s → a ≠ b → r a b) → nodup s → pairwise r s :=
  sorry

theorem forall_of_pairwise {α : Type u_1} {r : α → α → Prop} (H : symmetric r) {s : multiset α}
    (hs : pairwise r s) (a : α) : a ∈ s → ∀ (b : α), b ∈ s → a ≠ b → r a b :=
  sorry

theorem nodup_add {α : Type u_1} {s : multiset α} {t : multiset α} :
    nodup (s + t) ↔ nodup s ∧ nodup t ∧ disjoint s t :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => list.nodup_append

theorem disjoint_of_nodup_add {α : Type u_1} {s : multiset α} {t : multiset α} (d : nodup (s + t)) :
    disjoint s t :=
  and.right (and.right (iff.mp nodup_add d))

theorem nodup_add_of_nodup {α : Type u_1} {s : multiset α} {t : multiset α} (d₁ : nodup s)
    (d₂ : nodup t) : nodup (s + t) ↔ disjoint s t :=
  sorry

theorem nodup_of_nodup_map {α : Type u_1} {β : Type u_2} (f : α → β) {s : multiset α} :
    nodup (map f s) → nodup s :=
  quot.induction_on s fun (l : List α) => list.nodup_of_nodup_map f

theorem nodup_map_on {α : Type u_1} {β : Type u_2} {f : α → β} {s : multiset α} :
    (∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → f x = f y → x = y) → nodup s → nodup (map f s) :=
  quot.induction_on s fun (l : List α) => list.nodup_map_on

theorem nodup_map {α : Type u_1} {β : Type u_2} {f : α → β} {s : multiset α}
    (hf : function.injective f) : nodup s → nodup (map f s) :=
  nodup_map_on fun (x : α) (_x : x ∈ s) (y : α) (_x : y ∈ s) (h : f x = f y) => hf h

theorem nodup_filter {α : Type u_1} (p : α → Prop) [decidable_pred p] {s : multiset α} :
    nodup s → nodup (filter p s) :=
  quot.induction_on s fun (l : List α) => list.nodup_filter p

@[simp] theorem nodup_attach {α : Type u_1} {s : multiset α} : nodup (attach s) ↔ nodup s :=
  quot.induction_on s fun (l : List α) => list.nodup_attach

theorem nodup_pmap {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a : α) → p a → β}
    {s : multiset α} {H : ∀ (a : α), a ∈ s → p a}
    (hf : ∀ (a : α) (ha : p a) (b : α) (hb : p b), f a ha = f b hb → a = b) :
    nodup s → nodup (pmap f s H) :=
  quot.induction_on s
    (fun (l : List α) (H : ∀ (a : α), a ∈ Quot.mk setoid.r l → p a) => list.nodup_pmap hf) H

protected instance nodup_decidable {α : Type u_1} [DecidableEq α] (s : multiset α) :
    Decidable (nodup s) :=
  quotient.rec_on_subsingleton s fun (l : List α) => list.nodup_decidable l

theorem nodup_erase_eq_filter {α : Type u_1} [DecidableEq α] (a : α) {s : multiset α} :
    nodup s → erase s a = filter (fun (_x : α) => _x ≠ a) s :=
  quot.induction_on s
    fun (l : List α) (d : nodup (Quot.mk setoid.r l)) =>
      congr_arg coe (list.nodup_erase_eq_filter a d)

theorem nodup_erase_of_nodup {α : Type u_1} [DecidableEq α] (a : α) {l : multiset α} :
    nodup l → nodup (erase l a) :=
  nodup_of_le (erase_le a l)

theorem mem_erase_iff_of_nodup {α : Type u_1} [DecidableEq α] {a : α} {b : α} {l : multiset α}
    (d : nodup l) : a ∈ erase l b ↔ a ≠ b ∧ a ∈ l :=
  sorry

theorem mem_erase_of_nodup {α : Type u_1} [DecidableEq α] {a : α} {l : multiset α} (h : nodup l) :
    ¬a ∈ erase l a :=
  sorry

theorem nodup_product {α : Type u_1} {β : Type u_2} {s : multiset α} {t : multiset β} :
    nodup s → nodup t → nodup (product s t) :=
  sorry

theorem nodup_sigma {α : Type u_1} {σ : α → Type u_2} {s : multiset α}
    {t : (a : α) → multiset (σ a)} :
    nodup s → (∀ (a : α), nodup (t a)) → nodup (multiset.sigma s t) :=
  sorry

theorem nodup_filter_map {α : Type u_1} {β : Type u_2} (f : α → Option β) {s : multiset α}
    (H : ∀ (a a' : α) (b : β), b ∈ f a → b ∈ f a' → a = a') : nodup s → nodup (filter_map f s) :=
  quot.induction_on s fun (l : List α) => list.nodup_filter_map H

theorem nodup_range (n : ℕ) : nodup (range n) := list.nodup_range n

theorem nodup_inter_left {α : Type u_1} [DecidableEq α] {s : multiset α} (t : multiset α) :
    nodup s → nodup (s ∩ t) :=
  nodup_of_le (inter_le_left s t)

theorem nodup_inter_right {α : Type u_1} [DecidableEq α] (s : multiset α) {t : multiset α} :
    nodup t → nodup (s ∩ t) :=
  nodup_of_le (inter_le_right s t)

@[simp] theorem nodup_union {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} :
    nodup (s ∪ t) ↔ nodup s ∧ nodup t :=
  sorry

@[simp] theorem nodup_powerset {α : Type u_1} {s : multiset α} : nodup (powerset s) ↔ nodup s :=
  sorry

theorem nodup_powerset_len {α : Type u_1} {n : ℕ} {s : multiset α} (h : nodup s) :
    nodup (powerset_len n s) :=
  nodup_of_le (powerset_len_le_powerset n s) (iff.mpr nodup_powerset h)

@[simp] theorem nodup_bind {α : Type u_1} {β : Type u_2} {s : multiset α} {t : α → multiset β} :
    nodup (bind s t) ↔
        (∀ (a : α), a ∈ s → nodup (t a)) ∧ pairwise (fun (a b : α) => disjoint (t a) (t b)) s :=
  sorry

theorem nodup_ext {α : Type u_1} {s : multiset α} {t : multiset α} :
    nodup s → nodup t → (s = t ↔ ∀ (a : α), a ∈ s ↔ a ∈ t) :=
  quotient.induction_on₂ s t
    fun (l₁ l₂ : List α) (d₁ : nodup (quotient.mk l₁)) (d₂ : nodup (quotient.mk l₂)) =>
      iff.trans quotient.eq (list.perm_ext d₁ d₂)

theorem le_iff_subset {α : Type u_1} {s : multiset α} {t : multiset α} :
    nodup s → (s ≤ t ↔ s ⊆ t) :=
  quotient.induction_on₂ s t
    fun (l₁ l₂ : List α) (d : nodup (quotient.mk l₁)) =>
      { mp := subset_of_le, mpr := list.subperm_of_subset_nodup d }

theorem range_le {m : ℕ} {n : ℕ} : range m ≤ range n ↔ m ≤ n :=
  iff.trans (le_iff_subset (nodup_range m)) range_subset

theorem mem_sub_of_nodup {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} {t : multiset α}
    (d : nodup s) : a ∈ s - t ↔ a ∈ s ∧ ¬a ∈ t :=
  sorry

theorem map_eq_map_of_bij_of_nodup {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → γ)
    (g : β → γ) {s : multiset α} {t : multiset β} (hs : nodup s) (ht : nodup t)
    (i : (a : α) → a ∈ s → β) (hi : ∀ (a : α) (ha : a ∈ s), i a ha ∈ t)
    (h : ∀ (a : α) (ha : a ∈ s), f a = g (i a ha))
    (i_inj : ∀ (a₁ a₂ : α) (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ (b : β), b ∈ t → ∃ (a : α), ∃ (ha : a ∈ s), b = i a ha) : map f s = map g t :=
  sorry

end Mathlib