/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.Lean3Lib.data.rbtree.basic
 

universes u 

namespace Mathlib

namespace rbnode


theorem mem_of_min_eq {α : Type u} (lt : α → α → Prop) [is_irrefl α lt] {a : α} {t : rbnode α} : rbnode.min t = some a → mem lt a t := sorry

theorem mem_of_max_eq {α : Type u} (lt : α → α → Prop) [is_irrefl α lt] {a : α} {t : rbnode α} : rbnode.max t = some a → mem lt a t := sorry

theorem eq_leaf_of_min_eq_none {α : Type u} {t : rbnode α} : rbnode.min t = none → t = leaf := sorry

theorem eq_leaf_of_max_eq_none {α : Type u} {t : rbnode α} : rbnode.max t = none → t = leaf := sorry

theorem min_is_minimal {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {a : α} {t : rbnode α} {lo : Option α} {hi : Option α} : is_searchable lt t lo hi → rbnode.min t = some a → ∀ {b : α}, mem lt b t → strict_weak_order.equiv a b ∨ lt a b := sorry

theorem max_is_maximal {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {a : α} {t : rbnode α} {lo : Option α} {hi : Option α} : is_searchable lt t lo hi → rbnode.max t = some a → ∀ {b : α}, mem lt b t → strict_weak_order.equiv a b ∨ lt b a := sorry

