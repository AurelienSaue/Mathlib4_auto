/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.default
import Lean3Lib.data.rbtree.default
import PostPort

universes u v 

namespace Mathlib

namespace rbmap


/- Auxiliary instances -/

/- Helper lemmas for reusing rbtree results. -/

theorem eq_some_of_to_value_eq_some {α : Type u} {β : Type v} {e : Option (α × β)} {v : β} : to_value e = some v → ∃ (k : α), e = some (k, v) := sorry

theorem eq_none_of_to_value_eq_none {α : Type u} {β : Type v} {e : Option (α × β)} : to_value e = none → e = none := sorry

/- Lemmas -/

theorem not_mem_mk_rbmap {α : Type u} {β : Type v} {lt : α → α → Prop} (k : α) : ¬k ∈ mk_rbmap α β := sorry

theorem not_mem_of_empty {α : Type u} {β : Type v} {lt : α → α → Prop} {m : rbmap α β} (k : α) : empty m = tt → ¬k ∈ m := sorry

theorem not_mem_of_find_entry_none {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k : α} {m : rbmap α β} : find_entry m k = none → ¬k ∈ m := sorry

theorem not_mem_of_find_none {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k : α} {m : rbmap α β} : find m k = none → ¬k ∈ m := sorry

theorem mem_of_find_entry_some {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {e : α × β} {m : rbmap α β} : find_entry m k₁ = some e → k₁ ∈ m := sorry

theorem mem_of_find_some {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k : α} {v : β} {m : rbmap α β} : find m k = some v → k ∈ m := sorry

theorem find_entry_eq_find_entry_of_eqv {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {m : rbmap α β} {k₁ : α} {k₂ : α} : strict_weak_order.equiv k₁ k₂ → find_entry m k₁ = find_entry m k₂ := sorry

theorem find_eq_find_of_eqv {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {k₂ : α} (m : rbmap α β) : strict_weak_order.equiv k₁ k₂ → find m k₁ = find m k₂ := sorry

theorem find_entry_correct {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (k : α) (m : rbmap α β) : k ∈ m ↔ ∃ (e : α × β), find_entry m k = some e ∧ strict_weak_order.equiv k (prod.fst e) := sorry

theorem eqv_of_find_entry_some {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {k₂ : α} {v : β} {m : rbmap α β} : find_entry m k₁ = some (k₂, v) → strict_weak_order.equiv k₁ k₂ := sorry

theorem eq_of_find_entry_some {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] {k₁ : α} {k₂ : α} {v : β} {m : rbmap α β} : find_entry m k₁ = some (k₂, v) → k₁ = k₂ :=
  fun (h : find_entry m k₁ = some (k₂, v)) =>
    (fun (this : strict_weak_order.equiv k₁ k₂) => eq_of_eqv_lt this) (eqv_of_find_entry_some h)

theorem find_correct {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (k : α) (m : rbmap α β) : k ∈ m ↔ ∃ (v : β), find m k = some v := sorry

theorem constains_correct {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (k : α) (m : rbmap α β) : k ∈ m ↔ contains m k = tt := sorry

theorem mem_of_mem_of_eqv {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {m : rbmap α β} {k₁ : α} {k₂ : α} : k₁ ∈ m → strict_weak_order.equiv k₁ k₂ → k₂ ∈ m := sorry

theorem mem_insert_of_incomp {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {k₂ : α} (m : rbmap α β) (v : β) : ¬lt k₁ k₂ ∧ ¬lt k₂ k₁ → k₁ ∈ insert m k₂ v :=
  fun (h : ¬lt k₁ k₂ ∧ ¬lt k₂ k₁) => to_rbmap_mem (rbtree.mem_insert_of_incomp m (eqv_entries_of_eqv_keys v v h))

theorem mem_insert {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (k : α) (m : rbmap α β) (v : β) : k ∈ insert m k v :=
  to_rbmap_mem (rbtree.mem_insert (k, v) m)

theorem mem_insert_of_equiv {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {k₂ : α} (m : rbmap α β) (v : β) : strict_weak_order.equiv k₁ k₂ → k₁ ∈ insert m k₂ v :=
  mem_insert_of_incomp m v

theorem mem_insert_of_mem {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {m : rbmap α β} (k₂ : α) (v : β) : k₁ ∈ m → k₁ ∈ insert m k₂ v :=
  fun (h : k₁ ∈ m) => to_rbmap_mem (rbtree.mem_insert_of_mem (k₂, v) (to_rbtree_mem' v h))

theorem equiv_or_mem_of_mem_insert {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {k₂ : α} {v : β} {m : rbmap α β} : k₁ ∈ insert m k₂ v → strict_weak_order.equiv k₁ k₂ ∨ k₁ ∈ m := sorry

theorem incomp_or_mem_of_mem_ins {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {k₂ : α} {v : β} {m : rbmap α β} : k₁ ∈ insert m k₂ v → ¬lt k₁ k₂ ∧ ¬lt k₂ k₁ ∨ k₁ ∈ m :=
  equiv_or_mem_of_mem_insert

theorem eq_or_mem_of_mem_ins {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] {k₁ : α} {k₂ : α} {v : β} {m : rbmap α β} : k₁ ∈ insert m k₂ v → k₁ = k₂ ∨ k₁ ∈ m := sorry

theorem find_entry_insert_of_eqv {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (m : rbmap α β) {k₁ : α} {k₂ : α} (v : β) : strict_weak_order.equiv k₁ k₂ → find_entry (insert m k₁ v) k₂ = some (k₁, v) := sorry

theorem find_entry_insert {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (m : rbmap α β) (k : α) (v : β) : find_entry (insert m k v) k = some (k, v) :=
  find_entry_insert_of_eqv m v (refl k)

theorem find_insert_of_eqv {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (m : rbmap α β) {k₁ : α} {k₂ : α} (v : β) : strict_weak_order.equiv k₁ k₂ → find (insert m k₁ v) k₂ = some v := sorry

theorem find_insert {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (m : rbmap α β) (k : α) (v : β) : find (insert m k v) k = some v :=
  find_insert_of_eqv m v (refl k)

theorem find_entry_insert_of_disj {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {k₂ : α} (m : rbmap α β) (v : β) : lt k₁ k₂ ∨ lt k₂ k₁ → find_entry (insert m k₁ v) k₂ = find_entry m k₂ := sorry

theorem find_entry_insert_of_not_eqv {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {k₂ : α} (m : rbmap α β) (v : β) : ¬strict_weak_order.equiv k₁ k₂ → find_entry (insert m k₁ v) k₂ = find_entry m k₂ := sorry

theorem find_entry_insert_of_ne {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] {k₁ : α} {k₂ : α} (m : rbmap α β) (v : β) : k₁ ≠ k₂ → find_entry (insert m k₁ v) k₂ = find_entry m k₂ :=
  fun (h : k₁ ≠ k₂) => find_entry_insert_of_not_eqv m v fun (h' : strict_weak_order.equiv k₁ k₂) => h (eq_of_eqv_lt h')

theorem find_insert_of_disj {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {k₂ : α} (m : rbmap α β) (v : β) : lt k₁ k₂ ∨ lt k₂ k₁ → find (insert m k₁ v) k₂ = find m k₂ := sorry

theorem find_insert_of_not_eqv {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k₁ : α} {k₂ : α} (m : rbmap α β) (v : β) : ¬strict_weak_order.equiv k₁ k₂ → find (insert m k₁ v) k₂ = find m k₂ := sorry

theorem find_insert_of_ne {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] {k₁ : α} {k₂ : α} (m : rbmap α β) (v : β) : k₁ ≠ k₂ → find (insert m k₁ v) k₂ = find m k₂ := sorry

theorem mem_of_min_eq {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] {k : α} {v : β} {m : rbmap α β} : min m = some (k, v) → k ∈ m :=
  fun (h : min m = some (k, v)) => to_rbmap_mem (rbtree.mem_of_min_eq h)

theorem mem_of_max_eq {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] {k : α} {v : β} {m : rbmap α β} : max m = some (k, v) → k ∈ m :=
  fun (h : max m = some (k, v)) => to_rbmap_mem (rbtree.mem_of_max_eq h)

theorem eq_leaf_of_min_eq_none {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {m : rbmap α β} : min m = none → m = mk_rbmap α β :=
  rbtree.eq_leaf_of_min_eq_none

theorem eq_leaf_of_max_eq_none {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {m : rbmap α β} : max m = none → m = mk_rbmap α β :=
  rbtree.eq_leaf_of_max_eq_none

theorem min_is_minimal {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k : α} {v : β} {m : rbmap α β} : min m = some (k, v) → ∀ {k' : α}, k' ∈ m → strict_weak_order.equiv k k' ∨ lt k k' := sorry

theorem max_is_maximal {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {k : α} {v : β} {m : rbmap α β} : max m = some (k, v) → ∀ {k' : α}, k' ∈ m → strict_weak_order.equiv k k' ∨ lt k' k := sorry

theorem min_is_minimal_of_total {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] {k : α} {v : β} {m : rbmap α β} : min m = some (k, v) → ∀ {k' : α}, k' ∈ m → k = k' ∨ lt k k' := sorry

theorem max_is_maximal_of_total {α : Type u} {β : Type v} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] {k : α} {v : β} {m : rbmap α β} : max m = some (k, v) → ∀ {k' : α}, k' ∈ m → k = k' ∨ lt k' k := sorry

