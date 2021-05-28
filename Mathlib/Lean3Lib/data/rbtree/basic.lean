/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace rbnode


inductive is_node_of {α : Type u} : rbnode α → rbnode α → α → rbnode α → Prop
where
| of_red : ∀ (l : rbnode α) (v : α) (r : rbnode α), is_node_of (red_node l v r) l v r
| of_black : ∀ (l : rbnode α) (v : α) (r : rbnode α), is_node_of (black_node l v r) l v r

def lift {α : Type u} (lt : α → α → Prop) : Option α → Option α → Prop :=
  sorry

inductive is_searchable {α : Type u} (lt : α → α → Prop) : rbnode α → Option α → Option α → Prop
where
| leaf_s : ∀ {lo hi : Option α}, lift lt lo hi → is_searchable lt leaf lo hi
| red_s : ∀ {l r : rbnode α} {v : α} {lo hi : Option α},
  is_searchable lt l lo (some v) → is_searchable lt r (some v) hi → is_searchable lt (red_node l v r) lo hi
| black_s : ∀ {l r : rbnode α} {v : α} {lo hi : Option α},
  is_searchable lt l lo (some v) → is_searchable lt r (some v) hi → is_searchable lt (black_node l v r) lo hi

theorem lo_lt_hi {α : Type u} {t : rbnode α} {lt : α → α → Prop} [is_trans α lt] {lo : Option α} {hi : Option α} : is_searchable lt t lo hi → lift lt lo hi := sorry

theorem is_searchable_of_is_searchable_of_incomp {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {t : rbnode α} {lo : Option α} {hi : α} {hi' : α} (hc : ¬lt hi' hi ∧ ¬lt hi hi') (hs : is_searchable lt t lo (some hi)) : is_searchable lt t lo (some hi') := sorry

theorem is_searchable_of_incomp_of_is_searchable {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {t : rbnode α} {lo : α} {lo' : α} {hi : Option α} (hc : ¬lt lo' lo ∧ ¬lt lo lo') (hs : is_searchable lt t (some lo) hi) : is_searchable lt t (some lo') hi := sorry

theorem is_searchable_some_low_of_is_searchable_of_lt {α : Type u} {lt : α → α → Prop} [DecidableRel lt] {t : rbnode α} [is_trans α lt] {lo : α} {hi : Option α} {lo' : α} (hlt : lt lo' lo) (hs : is_searchable lt t (some lo) hi) : is_searchable lt t (some lo') hi := sorry

theorem is_searchable_none_low_of_is_searchable_some_low {α : Type u} {lt : α → α → Prop} [DecidableRel lt] {t : rbnode α} {y : α} {hi : Option α} (hlt : is_searchable lt t (some y) hi) : is_searchable lt t none hi := sorry

theorem is_searchable_some_high_of_is_searchable_of_lt {α : Type u} {lt : α → α → Prop} [DecidableRel lt] {t : rbnode α} [is_trans α lt] {lo : Option α} {hi : α} {hi' : α} (hlt : lt hi hi') (hs : is_searchable lt t lo (some hi)) : is_searchable lt t lo (some hi') := sorry

theorem is_searchable_none_high_of_is_searchable_some_high {α : Type u} {lt : α → α → Prop} [DecidableRel lt] {t : rbnode α} {lo : Option α} {y : α} (hlt : is_searchable lt t lo (some y)) : is_searchable lt t lo none := sorry

theorem range {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {t : rbnode α} {x : α} {lo : Option α} {hi : Option α} : is_searchable lt t lo hi → mem lt x t → lift lt lo (some x) ∧ lift lt (some x) hi := sorry

theorem lt_of_mem_left {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {y : α} {t : rbnode α} {l : rbnode α} {r : rbnode α} {lo : Option α} {hi : Option α} : is_searchable lt t lo hi → is_node_of t l y r → ∀ {x : α}, mem lt x l → lt x y := sorry

theorem lt_of_mem_right {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {y : α} {t : rbnode α} {l : rbnode α} {r : rbnode α} {lo : Option α} {hi : Option α} : is_searchable lt t lo hi → is_node_of t l y r → ∀ {z : α}, mem lt z r → lt y z := sorry

theorem lt_of_mem_left_right {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_weak_order α lt] {y : α} {t : rbnode α} {l : rbnode α} {r : rbnode α} {lo : Option α} {hi : Option α} : is_searchable lt t lo hi → is_node_of t l y r → ∀ {x z : α}, mem lt x l → mem lt z r → lt x z := sorry

inductive is_red_black {α : Type u} : rbnode α → color → ℕ → Prop
where
| leaf_rb : is_red_black leaf color.black 0
| red_rb : ∀ {v : α} {l r : rbnode α} {n : ℕ},
  is_red_black l color.black n → is_red_black r color.black n → is_red_black (red_node l v r) color.red n
| black_rb : ∀ {v : α} {l r : rbnode α} {n : ℕ} {c₁ c₂ : color},
  is_red_black l c₁ n → is_red_black r c₂ n → is_red_black (black_node l v r) color.black (Nat.succ n)

theorem depth_min {α : Type u} {c : color} {n : ℕ} {t : rbnode α} : is_red_black t c n → depth min t ≥ n := sorry

theorem depth_max' {α : Type u} {c : color} {n : ℕ} {t : rbnode α} : is_red_black t c n → depth max t ≤ upper c n := sorry

theorem depth_max {α : Type u} {c : color} {n : ℕ} {t : rbnode α} (h : is_red_black t c n) : depth max t ≤ bit0 1 * n + 1 :=
  le_trans (depth_max' h) (upper_le c n)

theorem balanced {α : Type u} {c : color} {n : ℕ} {t : rbnode α} (h : is_red_black t c n) : bit0 1 * depth min t + 1 ≥ depth max t :=
  le_trans (depth_max h) (nat.succ_le_succ (nat.mul_le_mul_left (bit0 1) (depth_min h)))

