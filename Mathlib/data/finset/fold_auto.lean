/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finset.basic
import Mathlib.data.multiset.fold
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# The fold operation for a commutative associative operation over a finset.
-/

namespace finset


/-! ### fold -/

/-- `fold op b f s` folds the commutative associative operation `op` over the
  `f`-image of `s`, i.e. `fold (+) b f {1,2,3} = `f 1 + f 2 + f 3 + b`. -/
def fold {α : Type u_1} {β : Type u_2} (op : β → β → β) [hc : is_commutative β op]
    [ha : is_associative β op] (b : β) (f : α → β) (s : finset α) : β :=
  multiset.fold op b (multiset.map f (val s))

@[simp] theorem fold_empty {α : Type u_1} {β : Type u_2} {op : β → β → β} [hc : is_commutative β op]
    [ha : is_associative β op] {f : α → β} {b : β} : fold op b f ∅ = b :=
  rfl

@[simp] theorem fold_insert {α : Type u_1} {β : Type u_2} {op : β → β → β}
    [hc : is_commutative β op] [ha : is_associative β op] {f : α → β} {b : β} {s : finset α} {a : α}
    [DecidableEq α] (h : ¬a ∈ s) : fold op b f (insert a s) = op (f a) (fold op b f s) :=
  sorry

@[simp] theorem fold_singleton {α : Type u_1} {β : Type u_2} {op : β → β → β}
    [hc : is_commutative β op] [ha : is_associative β op] {f : α → β} {b : β} {a : α} :
    fold op b f (singleton a) = op (f a) b :=
  rfl

@[simp] theorem fold_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {op : β → β → β}
    [hc : is_commutative β op] [ha : is_associative β op] {f : α → β} {b : β} {g : γ ↪ α}
    {s : finset γ} : fold op b f (map g s) = fold op b (f ∘ ⇑g) s :=
  sorry

@[simp] theorem fold_image {α : Type u_1} {β : Type u_2} {γ : Type u_3} {op : β → β → β}
    [hc : is_commutative β op] [ha : is_associative β op] {f : α → β} {b : β} [DecidableEq α]
    {g : γ → α} {s : finset γ} (H : ∀ (x : γ), x ∈ s → ∀ (y : γ), y ∈ s → g x = g y → x = y) :
    fold op b f (image g s) = fold op b (f ∘ g) s :=
  sorry

theorem fold_congr {α : Type u_1} {β : Type u_2} {op : β → β → β} [hc : is_commutative β op]
    [ha : is_associative β op] {f : α → β} {b : β} {s : finset α} {g : α → β}
    (H : ∀ (x : α), x ∈ s → f x = g x) : fold op b f s = fold op b g s :=
  sorry

theorem fold_op_distrib {α : Type u_1} {β : Type u_2} {op : β → β → β} [hc : is_commutative β op]
    [ha : is_associative β op] {s : finset α} {f : α → β} {g : α → β} {b₁ : β} {b₂ : β} :
    fold op (op b₁ b₂) (fun (x : α) => op (f x) (g x)) s = op (fold op b₁ f s) (fold op b₂ g s) :=
  sorry

theorem fold_hom {α : Type u_1} {β : Type u_2} {γ : Type u_3} {op : β → β → β}
    [hc : is_commutative β op] [ha : is_associative β op] {f : α → β} {b : β} {s : finset α}
    {op' : γ → γ → γ} [is_commutative γ op'] [is_associative γ op'] {m : β → γ}
    (hm : ∀ (x y : β), m (op x y) = op' (m x) (m y)) :
    fold op' (m b) (fun (x : α) => m (f x)) s = m (fold op b f s) :=
  sorry

theorem fold_union_inter {α : Type u_1} {β : Type u_2} {op : β → β → β} [hc : is_commutative β op]
    [ha : is_associative β op] {f : α → β} [DecidableEq α] {s₁ : finset α} {s₂ : finset α} {b₁ : β}
    {b₂ : β} :
    op (fold op b₁ f (s₁ ∪ s₂)) (fold op b₂ f (s₁ ∩ s₂)) = op (fold op b₂ f s₁) (fold op b₁ f s₂) :=
  sorry

@[simp] theorem fold_insert_idem {α : Type u_1} {β : Type u_2} {op : β → β → β}
    [hc : is_commutative β op] [ha : is_associative β op] {f : α → β} {b : β} {s : finset α} {a : α}
    [DecidableEq α] [hi : is_idempotent β op] :
    fold op b f (insert a s) = op (f a) (fold op b f s) :=
  sorry

theorem fold_op_rel_iff_and {α : Type u_1} {β : Type u_2} {op : β → β → β}
    [hc : is_commutative β op] [ha : is_associative β op] {f : α → β} {b : β} {s : finset α}
    {r : β → β → Prop} (hr : ∀ {x y z : β}, r x (op y z) ↔ r x y ∧ r x z) {c : β} :
    r c (fold op b f s) ↔ r c b ∧ ∀ (x : α), x ∈ s → r c (f x) :=
  sorry

theorem fold_op_rel_iff_or {α : Type u_1} {β : Type u_2} {op : β → β → β} [hc : is_commutative β op]
    [ha : is_associative β op] {f : α → β} {b : β} {s : finset α} {r : β → β → Prop}
    (hr : ∀ {x y z : β}, r x (op y z) ↔ r x y ∨ r x z) {c : β} :
    r c (fold op b f s) ↔ r c b ∨ ∃ (x : α), ∃ (H : x ∈ s), r c (f x) :=
  sorry

@[simp] theorem fold_union_empty_singleton {α : Type u_1} [DecidableEq α] (s : finset α) :
    fold has_union.union ∅ singleton s = s :=
  sorry

@[simp] theorem fold_sup_bot_singleton {α : Type u_1} [DecidableEq α] (s : finset α) :
    fold has_sup.sup ⊥ singleton s = s :=
  fold_union_empty_singleton s

theorem le_fold_min {α : Type u_1} {β : Type u_2} {f : α → β} {b : β} {s : finset α}
    [linear_order β] (c : β) : c ≤ fold min b f s ↔ c ≤ b ∧ ∀ (x : α), x ∈ s → c ≤ f x :=
  fold_op_rel_iff_and fun (x y z : β) => le_min_iff

theorem fold_min_le {α : Type u_1} {β : Type u_2} {f : α → β} {b : β} {s : finset α}
    [linear_order β] (c : β) : fold min b f s ≤ c ↔ b ≤ c ∨ ∃ (x : α), ∃ (H : x ∈ s), f x ≤ c :=
  id (fold_op_rel_iff_or fun (x y z : β) => id min_le_iff)

theorem lt_fold_min {α : Type u_1} {β : Type u_2} {f : α → β} {b : β} {s : finset α}
    [linear_order β] (c : β) : c < fold min b f s ↔ c < b ∧ ∀ (x : α), x ∈ s → c < f x :=
  fold_op_rel_iff_and fun (x y z : β) => lt_min_iff

theorem fold_min_lt {α : Type u_1} {β : Type u_2} {f : α → β} {b : β} {s : finset α}
    [linear_order β] (c : β) : fold min b f s < c ↔ b < c ∨ ∃ (x : α), ∃ (H : x ∈ s), f x < c :=
  id (fold_op_rel_iff_or fun (x y z : β) => id min_lt_iff)

theorem fold_max_le {α : Type u_1} {β : Type u_2} {f : α → β} {b : β} {s : finset α}
    [linear_order β] (c : β) : fold max b f s ≤ c ↔ b ≤ c ∧ ∀ (x : α), x ∈ s → f x ≤ c :=
  id (fold_op_rel_iff_and fun (x y z : β) => id max_le_iff)

theorem le_fold_max {α : Type u_1} {β : Type u_2} {f : α → β} {b : β} {s : finset α}
    [linear_order β] (c : β) : c ≤ fold max b f s ↔ c ≤ b ∨ ∃ (x : α), ∃ (H : x ∈ s), c ≤ f x :=
  fold_op_rel_iff_or fun (x y z : β) => le_max_iff

theorem fold_max_lt {α : Type u_1} {β : Type u_2} {f : α → β} {b : β} {s : finset α}
    [linear_order β] (c : β) : fold max b f s < c ↔ b < c ∧ ∀ (x : α), x ∈ s → f x < c :=
  id (fold_op_rel_iff_and fun (x y z : β) => id max_lt_iff)

theorem lt_fold_max {α : Type u_1} {β : Type u_2} {f : α → β} {b : β} {s : finset α}
    [linear_order β] (c : β) : c < fold max b f s ↔ c < b ∨ ∃ (x : α), ∃ (H : x ∈ s), c < f x :=
  fold_op_rel_iff_or fun (x y z : β) => lt_max_iff

end Mathlib