/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.list.pairwise
import Mathlib.data.list.forall2
import PostPort

universes u v u_1 

namespace Mathlib

/-!
# Lists with no duplicates

`list.nodup` is defined in `data/list/defs`. In this file we prove various properties of this
predicate.
-/

namespace list


@[simp] theorem forall_mem_ne {α : Type u} {a : α} {l : List α} : (∀ (a' : α), a' ∈ l → ¬a = a') ↔ ¬a ∈ l :=
  { mp := fun (h : ∀ (a' : α), a' ∈ l → ¬a = a') (m : a ∈ l) => h a m rfl,
    mpr := fun (h : ¬a ∈ l) (a' : α) (m : a' ∈ l) (e : a = a') => h (Eq.symm e ▸ m) }

@[simp] theorem nodup_nil {α : Type u} : nodup [] :=
  pairwise.nil

@[simp] theorem nodup_cons {α : Type u} {a : α} {l : List α} : nodup (a :: l) ↔ ¬a ∈ l ∧ nodup l := sorry

protected theorem pairwise.nodup {α : Type u} {l : List α} {r : α → α → Prop} [is_irrefl α r] (h : pairwise r l) : nodup l :=
  pairwise.imp (fun (a b : α) => ne_of_irrefl) h

theorem rel_nodup {α : Type u} {β : Type v} {r : α → β → Prop} (hr : relator.bi_unique r) : relator.lift_fun (forall₂ r) Iff nodup nodup := sorry

theorem nodup_cons_of_nodup {α : Type u} {a : α} {l : List α} (m : ¬a ∈ l) (n : nodup l) : nodup (a :: l) :=
  iff.mpr nodup_cons { left := m, right := n }

theorem nodup_singleton {α : Type u} (a : α) : nodup [a] :=
  nodup_cons_of_nodup (not_mem_nil a) nodup_nil

theorem nodup_of_nodup_cons {α : Type u} {a : α} {l : List α} (h : nodup (a :: l)) : nodup l :=
  and.right (iff.mp nodup_cons h)

theorem not_mem_of_nodup_cons {α : Type u} {a : α} {l : List α} (h : nodup (a :: l)) : ¬a ∈ l :=
  and.left (iff.mp nodup_cons h)

theorem not_nodup_cons_of_mem {α : Type u} {a : α} {l : List α} : a ∈ l → ¬nodup (a :: l) :=
  iff.mp imp_not_comm not_mem_of_nodup_cons

theorem nodup_of_sublist {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <+ l₂ → nodup l₂ → nodup l₁ :=
  pairwise_of_sublist

theorem not_nodup_pair {α : Type u} (a : α) : ¬nodup [a, a] :=
  not_nodup_cons_of_mem (mem_singleton_self a)

theorem nodup_iff_sublist {α : Type u} {l : List α} : nodup l ↔ ∀ (a : α), ¬[a, a] <+ l := sorry

theorem nodup_iff_nth_le_inj {α : Type u} {l : List α} : nodup l ↔ ∀ (i j : ℕ) (h₁ : i < length l) (h₂ : j < length l), nth_le l i h₁ = nth_le l j h₂ → i = j := sorry

@[simp] theorem nth_le_index_of {α : Type u} [DecidableEq α] {l : List α} (H : nodup l) (n : ℕ) (h : n < length l) : index_of (nth_le l n h) l = n :=
  iff.mp nodup_iff_nth_le_inj H (index_of (nth_le l n h) l) n (iff.mpr index_of_lt_length (nth_le_mem l n h)) h
    (index_of_nth_le (iff.mpr index_of_lt_length (nth_le_mem l n h)))

theorem nodup_iff_count_le_one {α : Type u} [DecidableEq α] {l : List α} : nodup l ↔ ∀ (a : α), count a l ≤ 1 := sorry

theorem nodup_repeat {α : Type u} (a : α) {n : ℕ} : nodup (repeat a n) ↔ n ≤ 1 := sorry

@[simp] theorem count_eq_one_of_mem {α : Type u} [DecidableEq α] {a : α} {l : List α} (d : nodup l) (h : a ∈ l) : count a l = 1 :=
  le_antisymm (iff.mp nodup_iff_count_le_one d a) (iff.mpr count_pos h)

theorem nodup_of_nodup_append_left {α : Type u} {l₁ : List α} {l₂ : List α} : nodup (l₁ ++ l₂) → nodup l₁ :=
  nodup_of_sublist (sublist_append_left l₁ l₂)

theorem nodup_of_nodup_append_right {α : Type u} {l₁ : List α} {l₂ : List α} : nodup (l₁ ++ l₂) → nodup l₂ :=
  nodup_of_sublist (sublist_append_right l₁ l₂)

theorem nodup_append {α : Type u} {l₁ : List α} {l₂ : List α} : nodup (l₁ ++ l₂) ↔ nodup l₁ ∧ nodup l₂ ∧ disjoint l₁ l₂ := sorry

theorem disjoint_of_nodup_append {α : Type u} {l₁ : List α} {l₂ : List α} (d : nodup (l₁ ++ l₂)) : disjoint l₁ l₂ :=
  and.right (and.right (iff.mp nodup_append d))

theorem nodup_append_of_nodup {α : Type u} {l₁ : List α} {l₂ : List α} (d₁ : nodup l₁) (d₂ : nodup l₂) (dj : disjoint l₁ l₂) : nodup (l₁ ++ l₂) :=
  iff.mpr nodup_append { left := d₁, right := { left := d₂, right := dj } }

theorem nodup_append_comm {α : Type u} {l₁ : List α} {l₂ : List α} : nodup (l₁ ++ l₂) ↔ nodup (l₂ ++ l₁) := sorry

theorem nodup_middle {α : Type u} {a : α} {l₁ : List α} {l₂ : List α} : nodup (l₁ ++ a :: l₂) ↔ nodup (a :: (l₁ ++ l₂)) := sorry

theorem nodup_of_nodup_map {α : Type u} {β : Type v} (f : α → β) {l : List α} : nodup (map f l) → nodup l :=
  pairwise_of_pairwise_map f fun (a b : α) => mt (congr_arg f)

theorem nodup_map_on {α : Type u} {β : Type v} {f : α → β} {l : List α} (H : ∀ (x : α), x ∈ l → ∀ (y : α), y ∈ l → f x = f y → x = y) (d : nodup l) : nodup (map f l) := sorry

theorem nodup_map {α : Type u} {β : Type v} {f : α → β} {l : List α} (hf : function.injective f) : nodup l → nodup (map f l) :=
  nodup_map_on fun (x : α) (_x : x ∈ l) (y : α) (_x : y ∈ l) (h : f x = f y) => hf h

theorem nodup_map_iff {α : Type u} {β : Type v} {f : α → β} {l : List α} (hf : function.injective f) : nodup (map f l) ↔ nodup l :=
  { mp := nodup_of_nodup_map f, mpr := nodup_map hf }

@[simp] theorem nodup_attach {α : Type u} {l : List α} : nodup (attach l) ↔ nodup l := sorry

theorem nodup_pmap {α : Type u} {β : Type v} {p : α → Prop} {f : (a : α) → p a → β} {l : List α} {H : ∀ (a : α), a ∈ l → p a} (hf : ∀ (a : α) (ha : p a) (b : α) (hb : p b), f a ha = f b hb → a = b) (h : nodup l) : nodup (pmap f l H) := sorry

theorem nodup_filter {α : Type u} (p : α → Prop) [decidable_pred p] {l : List α} : nodup l → nodup (filter p l) :=
  pairwise_filter_of_pairwise p

@[simp] theorem nodup_reverse {α : Type u} {l : List α} : nodup (reverse l) ↔ nodup l := sorry

theorem nodup_erase_eq_filter {α : Type u} [DecidableEq α] (a : α) {l : List α} (d : nodup l) : list.erase l a = filter (fun (_x : α) => _x ≠ a) l := sorry

theorem nodup_erase_of_nodup {α : Type u} [DecidableEq α] (a : α) {l : List α} : nodup l → nodup (list.erase l a) :=
  nodup_of_sublist (erase_sublist a l)

theorem nodup_diff {α : Type u} [DecidableEq α] {l₁ : List α} {l₂ : List α} (h : nodup l₁) : nodup (list.diff l₁ l₂) := sorry

theorem mem_erase_iff_of_nodup {α : Type u} [DecidableEq α] {a : α} {b : α} {l : List α} (d : nodup l) : a ∈ list.erase l b ↔ a ≠ b ∧ a ∈ l := sorry

theorem mem_erase_of_nodup {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : nodup l) : ¬a ∈ list.erase l a :=
  fun (H : a ∈ list.erase l a) => and.left (iff.mp (mem_erase_iff_of_nodup h) H) rfl

theorem nodup_join {α : Type u} {L : List (List α)} : nodup (join L) ↔ (∀ (l : List α), l ∈ L → nodup l) ∧ pairwise disjoint L := sorry

theorem nodup_bind {α : Type u} {β : Type v} {l₁ : List α} {f : α → List β} : nodup (list.bind l₁ f) ↔ (∀ (x : α), x ∈ l₁ → nodup (f x)) ∧ pairwise (fun (a b : α) => disjoint (f a) (f b)) l₁ := sorry

theorem nodup_product {α : Type u} {β : Type v} {l₁ : List α} {l₂ : List β} (d₁ : nodup l₁) (d₂ : nodup l₂) : nodup (product l₁ l₂) := sorry

theorem nodup_sigma {α : Type u} {σ : α → Type u_1} {l₁ : List α} {l₂ : (a : α) → List (σ a)} (d₁ : nodup l₁) (d₂ : ∀ (a : α), nodup (l₂ a)) : nodup (list.sigma l₁ l₂) := sorry

theorem nodup_filter_map {α : Type u} {β : Type v} {f : α → Option β} {l : List α} (H : ∀ (a a' : α) (b : β), b ∈ f a → b ∈ f a' → a = a') : nodup l → nodup (filter_map f l) :=
  pairwise_filter_map_of_pairwise f
    fun (a a' : α) (n : a ≠ a') (b : β) (bm : b ∈ f a) (b' : β) (bm' : b' ∈ f a') (e : b = b') =>
      n (H a a' b' (e ▸ bm) bm')

theorem nodup_concat {α : Type u} {a : α} {l : List α} (h : ¬a ∈ l) (h' : nodup l) : nodup (concat l a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nodup (concat l a))) (concat_eq_append a l)))
    (nodup_append_of_nodup h' (nodup_singleton a) (iff.mpr disjoint_singleton h))

theorem nodup_insert {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : nodup l) : nodup (insert a l) := sorry

theorem nodup_union {α : Type u} [DecidableEq α] (l₁ : List α) {l₂ : List α} (h : nodup l₂) : nodup (l₁ ∪ l₂) := sorry

theorem nodup_inter_of_nodup {α : Type u} [DecidableEq α] {l₁ : List α} (l₂ : List α) : nodup l₁ → nodup (l₁ ∩ l₂) :=
  nodup_filter fun (_x : α) => _x ∈ l₂

@[simp] theorem nodup_sublists {α : Type u} {l : List α} : nodup (sublists l) ↔ nodup l := sorry

@[simp] theorem nodup_sublists' {α : Type u} {l : List α} : nodup (sublists' l) ↔ nodup l := sorry

theorem nodup_sublists_len {α : Type u_1} (n : ℕ) {l : List α} (nd : nodup l) : nodup (sublists_len n l) :=
  nodup_of_sublist (sublists_len_sublist_sublists' n l) (iff.mpr nodup_sublists' nd)

theorem diff_eq_filter_of_nodup {α : Type u} [DecidableEq α] {l₁ : List α} {l₂ : List α} (hl₁ : nodup l₁) : list.diff l₁ l₂ = filter (fun (_x : α) => ¬_x ∈ l₂) l₁ := sorry

theorem mem_diff_iff_of_nodup {α : Type u} [DecidableEq α] {l₁ : List α} {l₂ : List α} (hl₁ : nodup l₁) {a : α} : a ∈ list.diff l₁ l₂ ↔ a ∈ l₁ ∧ ¬a ∈ l₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ list.diff l₁ l₂ ↔ a ∈ l₁ ∧ ¬a ∈ l₂)) (diff_eq_filter_of_nodup hl₁)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ filter (fun (_x : α) => ¬_x ∈ l₂) l₁ ↔ a ∈ l₁ ∧ ¬a ∈ l₂)) (propext mem_filter)))
      (iff.refl (a ∈ l₁ ∧ ¬a ∈ l₂)))

theorem nodup_update_nth {α : Type u} {l : List α} {n : ℕ} {a : α} (hl : nodup l) (ha : ¬a ∈ l) : nodup (update_nth l n a) := sorry

theorem nodup.map_update {α : Type u} {β : Type v} [DecidableEq α] {l : List α} (hl : nodup l) (f : α → β) (x : α) (y : β) : map (function.update f x y) l = ite (x ∈ l) (update_nth (map f l) (index_of x l) y) (map f l) := sorry

end list


theorem option.to_list_nodup {α : Type u_1} (o : Option α) : list.nodup (option.to_list o) :=
  option.cases_on o (idRhs (list.nodup []) list.nodup_nil) fun (o : α) => idRhs (list.nodup [o]) (list.nodup_singleton o)

