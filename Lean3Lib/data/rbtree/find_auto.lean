/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.default
import Lean3Lib.data.rbtree.basic
import PostPort

universes u 

namespace Mathlib

namespace rbnode


theorem find.induction {α : Type u} {p : rbnode α → Prop} (lt : α → α → Prop) [DecidableRel lt] (t : rbnode α) (x : α) (h₁ : p leaf) (h₂ : ∀ (l : rbnode α) (y : α) (r : rbnode α), cmp_using lt x y = ordering.lt → p l → p (red_node l y r)) (h₃ : ∀ (l : rbnode α) (y : α) (r : rbnode α), cmp_using lt x y = ordering.eq → p (red_node l y r)) (h₄ : ∀ (l : rbnode α) (y : α) (r : rbnode α), cmp_using lt x y = ordering.gt → p r → p (red_node l y r)) (h₅ : ∀ (l : rbnode α) (y : α) (r : rbnode α), cmp_using lt x y = ordering.lt → p l → p (black_node l y r)) (h₆ : ∀ (l : rbnode α) (y : α) (r : rbnode α), cmp_using lt x y = ordering.eq → p (black_node l y r)) (h₇ : ∀ (l : rbnode α) (y : α) (r : rbnode α), cmp_using lt x y = ordering.gt → p r → p (black_node l y r)) : p t := sorry

theorem find_correct {α : Type u} {t : rbnode α} {lt : α → α → Prop} {x : α} [DecidableRel lt] [is_strict_weak_order α lt] {lo : Option α} {hi : Option α} (hs : is_searchable lt t lo hi) : mem lt x t ↔ ∃ (y : α), find lt t x = some y ∧ strict_weak_order.equiv x y := sorry

theorem mem_of_mem_exact {α : Type u} {lt : α → α → Prop} [is_irrefl α lt] {x : α} {t : rbnode α} : mem_exact x t → mem lt x t := sorry

theorem find_correct_exact {α : Type u} {t : rbnode α} {lt : α → α → Prop} {x : α} [DecidableRel lt] [is_strict_weak_order α lt] {lo : Option α} {hi : Option α} (hs : is_searchable lt t lo hi) : mem_exact x t ↔ find lt t x = some x := sorry

theorem eqv_of_find_some {α : Type u} {t : rbnode α} {lt : α → α → Prop} {x : α} {y : α} [DecidableRel lt] [is_strict_weak_order α lt] {lo : Option α} {hi : Option α} (hs : is_searchable lt t lo hi) (he : find lt t x = some y) : strict_weak_order.equiv x y := sorry

theorem find_eq_find_of_eqv {α : Type u} {lt : α → α → Prop} {a : α} {b : α} [DecidableRel lt] [is_strict_weak_order α lt] {t : rbnode α} {lo : Option α} {hi : Option α} (hs : is_searchable lt t lo hi) (heqv : strict_weak_order.equiv a b) : find lt t a = find lt t b := sorry

