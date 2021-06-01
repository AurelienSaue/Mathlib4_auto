/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.nodup
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace list


/- erase duplicates function -/

@[simp] theorem erase_dup_nil {α : Type u} [DecidableEq α] : erase_dup [] = [] := rfl

theorem erase_dup_cons_of_mem' {α : Type u} [DecidableEq α] {a : α} {l : List α}
    (h : a ∈ erase_dup l) : erase_dup (a :: l) = erase_dup l :=
  sorry

theorem erase_dup_cons_of_not_mem' {α : Type u} [DecidableEq α] {a : α} {l : List α}
    (h : ¬a ∈ erase_dup l) : erase_dup (a :: l) = a :: erase_dup l :=
  pw_filter_cons_of_pos (eq.mpr (id (propext forall_mem_ne)) (eq.mp (Eq.refl (¬a ∈ erase_dup l)) h))

@[simp] theorem mem_erase_dup {α : Type u} [DecidableEq α] {a : α} {l : List α} :
    a ∈ erase_dup l ↔ a ∈ l :=
  sorry

@[simp] theorem erase_dup_cons_of_mem {α : Type u} [DecidableEq α] {a : α} {l : List α}
    (h : a ∈ l) : erase_dup (a :: l) = erase_dup l :=
  erase_dup_cons_of_mem' (iff.mpr mem_erase_dup h)

@[simp] theorem erase_dup_cons_of_not_mem {α : Type u} [DecidableEq α] {a : α} {l : List α}
    (h : ¬a ∈ l) : erase_dup (a :: l) = a :: erase_dup l :=
  erase_dup_cons_of_not_mem' (mt (iff.mp mem_erase_dup) h)

theorem erase_dup_sublist {α : Type u} [DecidableEq α] (l : List α) : erase_dup l <+ l :=
  pw_filter_sublist

theorem erase_dup_subset {α : Type u} [DecidableEq α] (l : List α) : erase_dup l ⊆ l :=
  pw_filter_subset

theorem subset_erase_dup {α : Type u} [DecidableEq α] (l : List α) : l ⊆ erase_dup l :=
  fun (a : α) => iff.mpr mem_erase_dup

theorem nodup_erase_dup {α : Type u} [DecidableEq α] (l : List α) : nodup (erase_dup l) :=
  pairwise_pw_filter

theorem erase_dup_eq_self {α : Type u} [DecidableEq α] {l : List α} : erase_dup l = l ↔ nodup l :=
  pw_filter_eq_self

@[simp] theorem erase_dup_idempotent {α : Type u} [DecidableEq α] {l : List α} :
    erase_dup (erase_dup l) = erase_dup l :=
  pw_filter_idempotent

theorem erase_dup_append {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) :
    erase_dup (l₁ ++ l₂) = l₁ ∪ erase_dup l₂ :=
  sorry

end Mathlib