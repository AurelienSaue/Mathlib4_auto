/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.Lean3Lib.data.rbtree.find
import Mathlib.Lean3Lib.data.rbtree.insert
import Mathlib.Lean3Lib.data.rbtree.min_max
 

universes u 

namespace Mathlib

namespace rbnode


theorem is_searchable_of_well_formed {α : Type u} {lt : α → α → Prop} {t : rbnode α} [is_strict_weak_order α lt] : well_formed lt t → is_searchable lt t none none := sorry

theorem is_red_black_of_well_formed {α : Type u} {lt : α → α → Prop} {t : rbnode α} : well_formed lt t → ∃ (c : color), ∃ (n : ℕ), is_red_black t c n := sorry

end rbnode


namespace rbtree


theorem balanced {α : Type u} {lt : α → α → Prop} (t : rbtree α) : bit0 1 * depth min t + 1 ≥ depth max t := sorry

theorem not_mem_mk_rbtree {α : Type u} {lt : α → α → Prop} (a : α) : ¬a ∈ mk_rbtree α := sorry

theorem not_mem_of_empty {α : Type u} {lt : α → α → Prop} {t : rbtree α} (a : α) : empty t = tt → ¬a ∈ t := sorry

theorem mem_of_mem_of_eqv {α : Type u} {lt : α → α → Prop} [is_strict_weak_order α lt] {t : rbtree α} {a : α} {b : α} : a ∈ t → strict_weak_order.equiv a b → b ∈ t := sorry

theorem insert_ne_mk_rbtree {α : Type u} {lt : α → α → Prop} [DecidableRel lt] (t : rbtree α) (a : α) : insert t a ≠ mk_rbtree α := sorry

theorem find_correct {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (a : α) (t : rbtree α) : a ∈ t ↔ ∃ (b : α), find t a = some b ∧ strict_weak_order.equiv a b :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) =>
      rbnode.find_correct (rbnode.is_searchable_of_well_formed t_property)

theorem find_correct_of_total {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] (a : α) (t : rbtree α) : a ∈ t ↔ find t a = some a := sorry

theorem find_correct_exact {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] (a : α) (t : rbtree α) : mem_exact a t ↔ find t a = some a :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) =>
      rbnode.find_correct_exact (rbnode.is_searchable_of_well_formed t_property)

theorem find_insert_of_eqv {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (t : rbtree α) {x : α} {y : α} : strict_weak_order.equiv x y → find (insert t x) y = some x :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) (h : strict_weak_order.equiv x y) =>
      rbnode.find_insert_of_eqv lt h (rbnode.is_searchable_of_well_formed t_property)

theorem find_insert {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (t : rbtree α) (x : α) : find (insert t x) x = some x :=
  find_insert_of_eqv t (refl x)

theorem find_insert_of_disj {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {x : α} {y : α} (t : rbtree α) : lt x y ∨ lt y x → find (insert t x) y = find t y :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) (h : lt x y ∨ lt y x) =>
      rbnode.find_insert_of_disj lt h (rbnode.is_searchable_of_well_formed t_property)

theorem find_insert_of_not_eqv {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {x : α} {y : α} (t : rbtree α) : ¬strict_weak_order.equiv x y → find (insert t x) y = find t y :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) (h : ¬strict_weak_order.equiv x y) =>
      rbnode.find_insert_of_not_eqv lt h (rbnode.is_searchable_of_well_formed t_property)

theorem find_insert_of_ne {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] {x : α} {y : α} (t : rbtree α) : x ≠ y → find (insert t x) y = find t y := sorry

theorem not_mem_of_find_none {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {a : α} {t : rbtree α} : find t a = none → ¬a ∈ t := sorry

theorem eqv_of_find_some {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {a : α} {b : α} {t : rbtree α} : find t a = some b → strict_weak_order.equiv a b :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) =>
      rbnode.eqv_of_find_some (rbnode.is_searchable_of_well_formed t_property)

theorem eq_of_find_some {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] {a : α} {b : α} {t : rbtree α} : find t a = some b → a = b :=
  fun (h : find t a = some b) => (fun (this : strict_weak_order.equiv a b) => eq_of_eqv_lt this) (eqv_of_find_some h)

theorem mem_of_find_some {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {a : α} {b : α} {t : rbtree α} : find t a = some b → a ∈ t :=
  fun (h : find t a = some b) => iff.mpr (find_correct a t) (Exists.intro b { left := h, right := eqv_of_find_some h })

theorem find_eq_find_of_eqv {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {a : α} {b : α} (t : rbtree α) : strict_weak_order.equiv a b → find t a = find t b :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) =>
      rbnode.find_eq_find_of_eqv (rbnode.is_searchable_of_well_formed t_property)

theorem contains_correct {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] (a : α) (t : rbtree α) : a ∈ t ↔ contains t a = tt := sorry

theorem mem_insert_of_incomp {α : Type u} {lt : α → α → Prop} [DecidableRel lt] {a : α} {b : α} (t : rbtree α) : ¬lt a b ∧ ¬lt b a → a ∈ insert t b :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) => rbnode.mem_insert_of_incomp lt t_val

theorem mem_insert {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_irrefl α lt] (a : α) (t : rbtree α) : a ∈ insert t a :=
  mem_insert_of_incomp t { left := irrefl_of lt a, right := irrefl_of lt a }

theorem mem_insert_of_equiv {α : Type u} {lt : α → α → Prop} [DecidableRel lt] {a : α} {b : α} (t : rbtree α) : strict_weak_order.equiv a b → a ∈ insert t b :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) => rbnode.mem_insert_of_incomp lt t_val

theorem mem_insert_of_mem {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {a : α} {t : rbtree α} (b : α) : a ∈ t → a ∈ insert t b :=
  subtype.cases_on t fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) => rbnode.mem_insert_of_mem lt b

theorem equiv_or_mem_of_mem_insert {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {a : α} {b : α} {t : rbtree α} : a ∈ insert t b → strict_weak_order.equiv a b ∨ a ∈ t :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) => rbnode.equiv_or_mem_of_mem_insert lt

theorem incomp_or_mem_of_mem_ins {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {a : α} {b : α} {t : rbtree α} : a ∈ insert t b → ¬lt a b ∧ ¬lt b a ∨ a ∈ t :=
  equiv_or_mem_of_mem_insert

theorem eq_or_mem_of_mem_ins {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_total_order α lt] {a : α} {b : α} {t : rbtree α} : a ∈ insert t b → a = b ∨ a ∈ t := sorry

theorem mem_of_min_eq {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_irrefl α lt] {a : α} {t : rbtree α} : rbtree.min t = some a → a ∈ t :=
  subtype.cases_on t fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) => rbnode.mem_of_min_eq lt

theorem mem_of_max_eq {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_irrefl α lt] {a : α} {t : rbtree α} : rbtree.max t = some a → a ∈ t :=
  subtype.cases_on t fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) => rbnode.mem_of_max_eq lt

theorem eq_leaf_of_min_eq_none {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {t : rbtree α} : rbtree.min t = none → t = mk_rbtree α := sorry

theorem eq_leaf_of_max_eq_none {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {t : rbtree α} : rbtree.max t = none → t = mk_rbtree α := sorry

theorem min_is_minimal {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {a : α} {t : rbtree α} : rbtree.min t = some a → ∀ {b : α}, b ∈ t → strict_weak_order.equiv a b ∨ lt a b :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) =>
      rbnode.min_is_minimal (rbnode.is_searchable_of_well_formed t_property)

theorem max_is_maximal {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {a : α} {t : rbtree α} : rbtree.max t = some a → ∀ {b : α}, b ∈ t → strict_weak_order.equiv a b ∨ lt b a :=
  subtype.cases_on t
    fun (t_val : rbnode α) (t_property : rbnode.well_formed lt t_val) =>
      rbnode.max_is_maximal (rbnode.is_searchable_of_well_formed t_property)

