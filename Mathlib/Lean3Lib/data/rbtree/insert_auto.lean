/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.Lean3Lib.data.rbtree.find

universes u v 

namespace Mathlib

namespace rbnode


@[simp] theorem balance1_eq₁ {α : Type u} (l : rbnode α) (x : α) (r₁ : rbnode α) (y : α)
    (r₂ : rbnode α) (v : α) (t : rbnode α) :
    balance1 (red_node l x r₁) y r₂ v t = red_node (black_node l x r₁) y (black_node r₂ v t) :=
  sorry

@[simp] theorem balance1_eq₂ {α : Type u} (l₁ : rbnode α) (y : α) (l₂ : rbnode α) (x : α)
    (r : rbnode α) (v : α) (t : rbnode α) :
    get_color l₁ ≠ color.red →
        balance1 l₁ y (red_node l₂ x r) v t = red_node (black_node l₁ y l₂) x (black_node r v t) :=
  sorry

@[simp] theorem balance1_eq₃ {α : Type u} (l : rbnode α) (y : α) (r : rbnode α) (v : α)
    (t : rbnode α) :
    get_color l ≠ color.red →
        get_color r ≠ color.red → balance1 l y r v t = black_node (red_node l y r) v t :=
  sorry

@[simp] theorem balance2_eq₁ {α : Type u} (l : rbnode α) (x₁ : α) (r₁ : rbnode α) (y : α)
    (r₂ : rbnode α) (v : α) (t : rbnode α) :
    balance2 (red_node l x₁ r₁) y r₂ v t = red_node (black_node t v l) x₁ (black_node r₁ y r₂) :=
  sorry

@[simp] theorem balance2_eq₂ {α : Type u} (l₁ : rbnode α) (y : α) (l₂ : rbnode α) (x₂ : α)
    (r₂ : rbnode α) (v : α) (t : rbnode α) :
    get_color l₁ ≠ color.red →
        balance2 l₁ y (red_node l₂ x₂ r₂) v t =
          red_node (black_node t v l₁) y (black_node l₂ x₂ r₂) :=
  sorry

@[simp] theorem balance2_eq₃ {α : Type u} (l : rbnode α) (y : α) (r : rbnode α) (v : α)
    (t : rbnode α) :
    get_color l ≠ color.red →
        get_color r ≠ color.red → balance2 l y r v t = black_node t v (red_node l y r) :=
  sorry

/- We can use the same induction principle for balance1 and balance2 -/

theorem balance.cases {α : Type u} {p : rbnode α → α → rbnode α → Prop} (l : rbnode α) (y : α)
    (r : rbnode α)
    (red_left :
      ∀ (l : rbnode α) (x : α) (r₁ : rbnode α) (y : α) (r₂ : rbnode α), p (red_node l x r₁) y r₂)
    (red_right :
      ∀ (l₁ : rbnode α) (y : α) (l₂ : rbnode α) (x : α) (r : rbnode α),
        get_color l₁ ≠ color.red → p l₁ y (red_node l₂ x r))
    (other :
      ∀ (l : rbnode α) (y : α) (r : rbnode α),
        get_color l ≠ color.red → get_color r ≠ color.red → p l y r) :
    p l y r :=
  sorry

theorem balance1_ne_leaf {α : Type u} (l : rbnode α) (x : α) (r : rbnode α) (v : α) (t : rbnode α) :
    balance1 l x r v t ≠ leaf :=
  sorry

theorem balance1_node_ne_leaf {α : Type u} {s : rbnode α} (a : α) (t : rbnode α) :
    s ≠ leaf → balance1_node s a t ≠ leaf :=
  sorry

theorem balance2_ne_leaf {α : Type u} (l : rbnode α) (x : α) (r : rbnode α) (v : α) (t : rbnode α) :
    balance2 l x r v t ≠ leaf :=
  sorry

theorem balance2_node_ne_leaf {α : Type u} {s : rbnode α} (a : α) (t : rbnode α) :
    s ≠ leaf → balance2_node s a t ≠ leaf :=
  sorry

theorem ins.induction {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {p : rbnode α → Prop}
    (t : rbnode α) (x : α) (is_leaf : p leaf)
    (is_red_lt :
      ∀ (a : rbnode α) (y : α) (b : rbnode α),
        cmp_using lt x y = ordering.lt → p a → p (red_node a y b))
    (is_red_eq :
      ∀ (a : rbnode α) (y : α) (b : rbnode α), cmp_using lt x y = ordering.eq → p (red_node a y b))
    (is_red_gt :
      ∀ (a : rbnode α) (y : α) (b : rbnode α),
        cmp_using lt x y = ordering.gt → p b → p (red_node a y b))
    (is_black_lt_red :
      ∀ (a : rbnode α) (y : α) (b : rbnode α),
        cmp_using lt x y = ordering.lt → get_color a = color.red → p a → p (black_node a y b))
    (is_black_lt_not_red :
      ∀ (a : rbnode α) (y : α) (b : rbnode α),
        cmp_using lt x y = ordering.lt → get_color a ≠ color.red → p a → p (black_node a y b))
    (is_black_eq :
      ∀ (a : rbnode α) (y : α) (b : rbnode α),
        cmp_using lt x y = ordering.eq → p (black_node a y b))
    (is_black_gt_red :
      ∀ (a : rbnode α) (y : α) (b : rbnode α),
        cmp_using lt x y = ordering.gt → get_color b = color.red → p b → p (black_node a y b))
    (is_black_gt_not_red :
      ∀ (a : rbnode α) (y : α) (b : rbnode α),
        cmp_using lt x y = ordering.gt → get_color b ≠ color.red → p b → p (black_node a y b)) :
    p t :=
  sorry

theorem is_searchable_balance1 {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {l : rbnode α}
    {y : α} {r : rbnode α} {v : α} {t : rbnode α} {lo : Option α} {hi : Option α} :
    is_searchable lt l lo (some y) →
        is_searchable lt r (some y) (some v) →
          is_searchable lt t (some v) hi → is_searchable lt (balance1 l y r v t) lo hi :=
  sorry

theorem is_searchable_balance1_node {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    {t : rbnode α} [is_trans α lt] {y : α} {s : rbnode α} {lo : Option α} {hi : Option α} :
    is_searchable lt t lo (some y) →
        is_searchable lt s (some y) hi → is_searchable lt (balance1_node t y s) lo hi :=
  sorry

theorem is_searchable_balance2 {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {l : rbnode α}
    {y : α} {r : rbnode α} {v : α} {t : rbnode α} {lo : Option α} {hi : Option α} :
    is_searchable lt t lo (some v) →
        is_searchable lt l (some v) (some y) →
          is_searchable lt r (some y) hi → is_searchable lt (balance2 l y r v t) lo hi :=
  sorry

theorem is_searchable_balance2_node {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    {t : rbnode α} [is_trans α lt] {y : α} {s : rbnode α} {lo : Option α} {hi : Option α} :
    is_searchable lt s lo (some y) →
        is_searchable lt t (some y) hi → is_searchable lt (balance2_node t y s) lo hi :=
  sorry

theorem is_searchable_ins {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {t : rbnode α} {x : α}
    [is_strict_weak_order α lt] {lo : Option α} {hi : Option α} (h : is_searchable lt t lo hi) :
    lift lt lo (some x) → lift lt (some x) hi → is_searchable lt (ins lt t x) lo hi :=
  sorry

theorem is_searchable_mk_insert_result {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    {c : color} {t : rbnode α} :
    is_searchable lt t none none → is_searchable lt (mk_insert_result c t) none none :=
  sorry

theorem is_searchable_insert {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {t : rbnode α}
    {x : α} [is_strict_weak_order α lt] :
    is_searchable lt t none none → is_searchable lt (insert lt t x) none none :=
  sorry

end rbnode


namespace rbnode


theorem mem_balance1_node_of_mem_left {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {x : α}
    {s : rbnode α} (v : α) (t : rbnode α) : mem lt x s → mem lt x (balance1_node s v t) :=
  sorry

theorem mem_balance2_node_of_mem_left {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {x : α}
    {s : rbnode α} (v : α) (t : rbnode α) : mem lt x s → mem lt x (balance2_node s v t) :=
  sorry

theorem mem_balance1_node_of_mem_right {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {x : α}
    {t : rbnode α} (v : α) (s : rbnode α) : mem lt x t → mem lt x (balance1_node s v t) :=
  sorry

theorem mem_balance2_node_of_mem_right {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {x : α}
    {t : rbnode α} (v : α) (s : rbnode α) : mem lt x t → mem lt x (balance2_node s v t) :=
  sorry

theorem mem_balance1_node_of_incomp {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {x : α}
    {v : α} (s : rbnode α) (t : rbnode α) :
    ¬lt x v ∧ ¬lt v x → s ≠ leaf → mem lt x (balance1_node s v t) :=
  sorry

theorem mem_balance2_node_of_incomp {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {x : α}
    {v : α} (s : rbnode α) (t : rbnode α) :
    ¬lt v x ∧ ¬lt x v → s ≠ leaf → mem lt x (balance2_node s v t) :=
  sorry

theorem ins_ne_leaf {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (t : rbnode α) (x : α) :
    ins lt t x ≠ leaf :=
  sorry

theorem insert_ne_leaf {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (t : rbnode α) (x : α) :
    insert lt t x ≠ leaf :=
  sorry

theorem mem_ins_of_incomp {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (t : rbnode α) {x : α}
    {y : α} (h : ¬lt x y ∧ ¬lt y x) : mem lt x (ins lt t y) :=
  sorry

theorem mem_ins_of_mem {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {t : rbnode α} (z : α) {x : α} (h : mem lt x t) :
    mem lt x (ins lt t z) :=
  sorry

theorem mem_mk_insert_result {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {a : α}
    {t : rbnode α} (c : color) : mem lt a t → mem lt a (mk_insert_result c t) :=
  sorry

theorem mem_of_mem_mk_insert_result {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {a : α}
    {t : rbnode α} {c : color} : mem lt a (mk_insert_result c t) → mem lt a t :=
  sorry

theorem mem_insert_of_incomp {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (t : rbnode α)
    {x : α} {y : α} (h : ¬lt x y ∧ ¬lt y x) : mem lt x (insert lt t y) :=
  sorry

theorem mem_insert_of_mem {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {t : rbnode α} {x : α} (z : α) :
    mem lt x t → mem lt x (insert lt t z) :=
  fun (ᾰ : mem lt x t) => mem_mk_insert_result lt (get_color t) (mem_ins_of_mem lt z ᾰ)

theorem of_mem_balance1_node {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {x : α} {s : rbnode α} {v : α} {t : rbnode α} :
    mem lt x (balance1_node s v t) → mem lt x s ∨ ¬lt x v ∧ ¬lt v x ∨ mem lt x t :=
  sorry

theorem of_mem_balance2_node {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {x : α} {s : rbnode α} {v : α} {t : rbnode α} :
    mem lt x (balance2_node s v t) → mem lt x s ∨ ¬lt x v ∧ ¬lt v x ∨ mem lt x t :=
  sorry

theorem equiv_or_mem_of_mem_ins {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {t : rbnode α} {x : α} {z : α} (h : mem lt x (ins lt t z)) :
    strict_weak_order.equiv x z ∨ mem lt x t :=
  sorry

theorem equiv_or_mem_of_mem_insert {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {t : rbnode α} {x : α} {z : α} (h : mem lt x (insert lt t z)) :
    strict_weak_order.equiv x z ∨ mem lt x t :=
  sorry

theorem mem_exact_balance1_node_of_mem_exact {α : Type u} {x : α} {s : rbnode α} (v : α)
    (t : rbnode α) : mem_exact x s → mem_exact x (balance1_node s v t) :=
  sorry

theorem mem_exact_balance2_node_of_mem_exact {α : Type u} {x : α} {s : rbnode α} (v : α)
    (t : rbnode α) : mem_exact x s → mem_exact x (balance2_node s v t) :=
  sorry

theorem find_balance1_node {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {x : α} {y : α} {z : α} {t : rbnode α} {s : rbnode α}
    {lo : Option α} {hi : Option α} :
    is_searchable lt t lo (some z) →
        is_searchable lt s (some z) hi →
          find lt t y = some x →
            strict_weak_order.equiv y x → find lt (balance1_node t z s) y = some x :=
  sorry

theorem find_balance2_node {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {x : α} {y : α} {z : α} {s : rbnode α} {t : rbnode α}
    [is_trans α lt] {lo : Option α} {hi : Option α} :
    is_searchable lt s lo (some z) →
        is_searchable lt t (some z) hi →
          find lt t y = some x →
            strict_weak_order.equiv y x → find lt (balance2_node t z s) y = some x :=
  sorry

/- Auxiliary lemma -/

theorem ite_eq_of_not_lt {α : Type u} (lt : α → α → Prop) [DecidableRel lt] [is_strict_order α lt]
    {a : α} {b : α} {β : Type v} (t : β) (s : β) (h : lt b a) : ite (lt a b) t s = s :=
  sorry

theorem find_ins_of_eqv {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {x : α} {y : α} {t : rbnode α} (he : strict_weak_order.equiv x y)
    {lo : Option α} {hi : Option α} (hs : is_searchable lt t lo hi) (hlt₁ : lift lt lo (some x))
    (hlt₂ : lift lt (some x) hi) : find lt (ins lt t x) y = some x :=
  sorry

theorem find_mk_insert_result {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (c : color)
    (t : rbnode α) (x : α) : find lt (mk_insert_result c t) x = find lt t x :=
  sorry

theorem find_insert_of_eqv {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {x : α} {y : α} {t : rbnode α} (he : strict_weak_order.equiv x y) :
    is_searchable lt t none none → find lt (insert lt t x) y = some x :=
  sorry

theorem weak_trichotomous {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (x : α) (y : α)
    {p : Prop} (is_lt : lt x y → p) (is_eqv : ¬lt x y ∧ ¬lt y x → p) (is_gt : lt y x → p) : p :=
  dite (lt x y)
    (fun (h : lt x y) =>
      dite (lt y x) (fun (h_1 : lt y x) => is_lt h) fun (h_1 : ¬lt y x) => is_lt h)
    fun (h : ¬lt x y) =>
      dite (lt y x) (fun (h : lt y x) => is_gt h)
        fun (h_1 : ¬lt y x) => is_eqv { left := h, right := h_1 }

theorem find_black_eq_find_red {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {l : rbnode α}
    {y : α} {r : rbnode α} {x : α} : find lt (black_node l y r) x = find lt (red_node l y r) x :=
  sorry

theorem find_red_of_lt {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {l : rbnode α} {y : α}
    {r : rbnode α} {x : α} (h : lt x y) : find lt (red_node l y r) x = find lt l x :=
  sorry

theorem find_red_of_gt {α : Type u} (lt : α → α → Prop) [DecidableRel lt] [is_strict_order α lt]
    {l : rbnode α} {y : α} {r : rbnode α} {x : α} (h : lt y x) :
    find lt (red_node l y r) x = find lt r x :=
  sorry

theorem find_red_of_incomp {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {l : rbnode α} {y : α}
    {r : rbnode α} {x : α} (h : ¬lt x y ∧ ¬lt y x) : find lt (red_node l y r) x = some y :=
  sorry

theorem find_balance1_lt {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {l : rbnode α} {r : rbnode α} {t : rbnode α} {v : α} {x : α} {y : α}
    {lo : Option α} {hi : Option α} (h : lt x y) (hl : is_searchable lt l lo (some v))
    (hr : is_searchable lt r (some v) (some y)) (ht : is_searchable lt t (some y) hi) :
    find lt (balance1 l v r y t) x = find lt (red_node l v r) x :=
  sorry

theorem find_balance1_node_lt {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {t : rbnode α} {s : rbnode α} {x : α} {y : α} {lo : Option α}
    {hi : Option α} (hlt : lt y x) (ht : is_searchable lt t lo (some x))
    (hs : is_searchable lt s (some x) hi)
    (hne :
      autoParam (t ≠ leaf)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.rbnode.ins_ne_leaf_tac")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbnode")
            "ins_ne_leaf_tac")
          [])) :
    find lt (balance1_node t x s) y = find lt t y :=
  sorry

theorem find_balance1_gt {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {l : rbnode α} {r : rbnode α} {t : rbnode α} {v : α} {x : α} {y : α}
    {lo : Option α} {hi : Option α} (h : lt y x) (hl : is_searchable lt l lo (some v))
    (hr : is_searchable lt r (some v) (some y)) (ht : is_searchable lt t (some y) hi) :
    find lt (balance1 l v r y t) x = find lt t x :=
  sorry

theorem find_balance1_node_gt {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {t : rbnode α} {s : rbnode α} {x : α} {y : α} {lo : Option α}
    {hi : Option α} (h : lt x y) (ht : is_searchable lt t lo (some x))
    (hs : is_searchable lt s (some x) hi)
    (hne :
      autoParam (t ≠ leaf)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.rbnode.ins_ne_leaf_tac")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbnode")
            "ins_ne_leaf_tac")
          [])) :
    find lt (balance1_node t x s) y = find lt s y :=
  sorry

theorem find_balance1_eqv {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {l : rbnode α} {r : rbnode α} {t : rbnode α} {v : α} {x : α} {y : α}
    {lo : Option α} {hi : Option α} (h : ¬lt x y ∧ ¬lt y x) (hl : is_searchable lt l lo (some v))
    (hr : is_searchable lt r (some v) (some y)) (ht : is_searchable lt t (some y) hi) :
    find lt (balance1 l v r y t) x = some y :=
  sorry

theorem find_balance1_node_eqv {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {t : rbnode α} {s : rbnode α} {x : α} {y : α} {lo : Option α}
    {hi : Option α} (h : ¬lt x y ∧ ¬lt y x) (ht : is_searchable lt t lo (some y))
    (hs : is_searchable lt s (some y) hi)
    (hne :
      autoParam (t ≠ leaf)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.rbnode.ins_ne_leaf_tac")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbnode")
            "ins_ne_leaf_tac")
          [])) :
    find lt (balance1_node t y s) x = some y :=
  sorry

theorem find_balance2_lt {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {l : rbnode α} {v : α} {r : rbnode α} {t : rbnode α} {x : α} {y : α}
    {lo : Option α} {hi : Option α} (h : lt x y) (hl : is_searchable lt l (some y) (some v))
    (hr : is_searchable lt r (some v) hi) (ht : is_searchable lt t lo (some y)) :
    find lt (balance2 l v r y t) x = find lt t x :=
  sorry

theorem find_balance2_node_lt {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {s : rbnode α} {t : rbnode α} {x : α} {y : α} {lo : Option α}
    {hi : Option α} (h : lt x y) (ht : is_searchable lt t (some y) hi)
    (hs : is_searchable lt s lo (some y))
    (hne :
      autoParam (t ≠ leaf)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.rbnode.ins_ne_leaf_tac")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbnode")
            "ins_ne_leaf_tac")
          [])) :
    find lt (balance2_node t y s) x = find lt s x :=
  sorry

theorem find_balance2_gt {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {l : rbnode α} {v : α} {r : rbnode α} {t : rbnode α} {x : α} {y : α}
    {lo : Option α} {hi : Option α} (h : lt y x) (hl : is_searchable lt l (some y) (some v))
    (hr : is_searchable lt r (some v) hi) (ht : is_searchable lt t lo (some y)) :
    find lt (balance2 l v r y t) x = find lt (red_node l v r) x :=
  sorry

theorem find_balance2_node_gt {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {s : rbnode α} {t : rbnode α} {x : α} {y : α} {lo : Option α}
    {hi : Option α} (h : lt y x) (ht : is_searchable lt t (some y) hi)
    (hs : is_searchable lt s lo (some y))
    (hne :
      autoParam (t ≠ leaf)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.rbnode.ins_ne_leaf_tac")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbnode")
            "ins_ne_leaf_tac")
          [])) :
    find lt (balance2_node t y s) x = find lt t x :=
  sorry

theorem find_balance2_eqv {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {l : rbnode α} {v : α} {r : rbnode α} {t : rbnode α} {x : α} {y : α}
    {lo : Option α} {hi : Option α} (h : ¬lt x y ∧ ¬lt y x)
    (hl : is_searchable lt l (some y) (some v)) (hr : is_searchable lt r (some v) hi)
    (ht : is_searchable lt t lo (some y)) : find lt (balance2 l v r y t) x = some y :=
  sorry

theorem find_balance2_node_eqv {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {t : rbnode α} {s : rbnode α} {x : α} {y : α} {lo : Option α}
    {hi : Option α} (h : ¬lt x y ∧ ¬lt y x) (ht : is_searchable lt t (some y) hi)
    (hs : is_searchable lt s lo (some y))
    (hne :
      autoParam (t ≠ leaf)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.rbnode.ins_ne_leaf_tac")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbnode")
            "ins_ne_leaf_tac")
          [])) :
    find lt (balance2_node t y s) x = some y :=
  sorry

theorem find_ins_of_disj {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {x : α} {y : α} {t : rbnode α} (hn : lt x y ∨ lt y x)
    {lo : Option α} {hi : Option α} (hs : is_searchable lt t lo hi) (hlt₁ : lift lt lo (some x))
    (hlt₂ : lift lt (some x) hi) : find lt (ins lt t x) y = find lt t y :=
  sorry

theorem find_insert_of_disj {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {x : α} {y : α} {t : rbnode α} (hd : lt x y ∨ lt y x) :
    is_searchable lt t none none → find lt (insert lt t x) y = find lt t y :=
  sorry

theorem find_insert_of_not_eqv {α : Type u} (lt : α → α → Prop) [DecidableRel lt]
    [is_strict_weak_order α lt] {x : α} {y : α} {t : rbnode α} (hn : ¬strict_weak_order.equiv x y) :
    is_searchable lt t none none → find lt (insert lt t x) y = find lt t y :=
  sorry

inductive is_bad_red_black {α : Type u} : rbnode α → ℕ → Prop where
| bad_red :
    ∀ {c₁ c₂ : color} {n : ℕ} {l r : rbnode α} {v : α},
      is_red_black l c₁ n → is_red_black r c₂ n → is_bad_red_black (red_node l v r) n

theorem balance1_rb {α : Type u} {l : rbnode α} {r : rbnode α} {t : rbnode α} {y : α} {v : α}
    {c_l : color} {c_r : color} {c_t : color} {n : ℕ} :
    is_red_black l c_l n →
        is_red_black r c_r n →
          is_red_black t c_t n → ∃ (c : color), is_red_black (balance1 l y r v t) c (Nat.succ n) :=
  sorry

theorem balance2_rb {α : Type u} {l : rbnode α} {r : rbnode α} {t : rbnode α} {y : α} {v : α}
    {c_l : color} {c_r : color} {c_t : color} {n : ℕ} :
    is_red_black l c_l n →
        is_red_black r c_r n →
          is_red_black t c_t n → ∃ (c : color), is_red_black (balance2 l y r v t) c (Nat.succ n) :=
  sorry

theorem balance1_node_rb {α : Type u} {t : rbnode α} {s : rbnode α} {y : α} {c : color} {n : ℕ} :
    is_bad_red_black t n →
        is_red_black s c n → ∃ (c : color), is_red_black (balance1_node t y s) c (Nat.succ n) :=
  sorry

theorem balance2_node_rb {α : Type u} {t : rbnode α} {s : rbnode α} {y : α} {c : color} {n : ℕ} :
    is_bad_red_black t n →
        is_red_black s c n → ∃ (c : color), is_red_black (balance2_node t y s) c (Nat.succ n) :=
  sorry

def ins_rb_result {α : Type u} : rbnode α → color → ℕ → Prop := sorry

theorem of_get_color_eq_red {α : Type u} {t : rbnode α} {c : color} {n : ℕ} :
    get_color t = color.red → is_red_black t c n → c = color.red :=
  sorry

theorem of_get_color_ne_red {α : Type u} {t : rbnode α} {c : color} {n : ℕ} :
    get_color t ≠ color.red → is_red_black t c n → c = color.black :=
  sorry

theorem ins_rb {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {t : rbnode α} (x : α) {c : color}
    {n : ℕ} (h : is_red_black t c n) : ins_rb_result (ins lt t x) c n :=
  sorry

def insert_rb_result {α : Type u} : rbnode α → color → ℕ → Prop := sorry

theorem insert_rb {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {t : rbnode α} (x : α)
    {c : color} {n : ℕ} (h : is_red_black t c n) : insert_rb_result (insert lt t x) c n :=
  sorry

theorem insert_is_red_black {α : Type u} (lt : α → α → Prop) [DecidableRel lt] {t : rbnode α}
    {c : color} {n : ℕ} (x : α) :
    is_red_black t c n → ∃ (c : color), ∃ (n : ℕ), is_red_black (insert lt t x) c n :=
  sorry

end Mathlib