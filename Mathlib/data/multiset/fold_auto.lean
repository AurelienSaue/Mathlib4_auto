/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.erase_dup
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# The fold operation for a commutative associative operation over a multiset.
-/

namespace multiset


/-! ### fold -/

/-- `fold op b s` folds a commutative associative operation `op` over
  the multiset `s`. -/
def fold {α : Type u_1} (op : α → α → α) [hc : is_commutative α op] [ha : is_associative α op] :
    α → multiset α → α :=
  foldr op sorry

theorem fold_eq_foldr {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] (b : α) (s : multiset α) :
    fold op b s = foldr op (left_comm op is_commutative.comm is_associative.assoc) b s :=
  rfl

@[simp] theorem coe_fold_r {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] (b : α) (l : List α) : fold op b ↑l = list.foldr op b l :=
  rfl

theorem coe_fold_l {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] (b : α) (l : List α) : fold op b ↑l = list.foldl op b l :=
  sorry

theorem fold_eq_foldl {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] (b : α) (s : multiset α) :
    fold op b s = foldl op (right_comm op is_commutative.comm is_associative.assoc) b s :=
  quot.induction_on s fun (l : List α) => coe_fold_l op b l

@[simp] theorem fold_zero {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] (b : α) : fold op b 0 = b :=
  rfl

@[simp] theorem fold_cons_left {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] (b : α) (a : α) (s : multiset α) :
    fold op b (a ::ₘ s) = op a (fold op b s) :=
  foldr_cons op (fold._proof_1 op)

theorem fold_cons_right {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] (b : α) (a : α) (s : multiset α) :
    fold op b (a ::ₘ s) = op (fold op b s) a :=
  sorry

theorem fold_cons'_right {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] (b : α) (a : α) (s : multiset α) :
    fold op b (a ::ₘ s) = fold op (op b a) s :=
  sorry

theorem fold_cons'_left {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] (b : α) (a : α) (s : multiset α) :
    fold op b (a ::ₘ s) = fold op (op a b) s :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (fold op b (a ::ₘ s) = fold op (op a b) s)) (fold_cons'_right op b a s)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (fold op (op b a) s = fold op (op a b) s)) (is_commutative.comm b a)))
      (Eq.refl (fold op (op a b) s)))

theorem fold_add {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] (b₁ : α) (b₂ : α) (s₁ : multiset α) (s₂ : multiset α) :
    fold op (op b₁ b₂) (s₁ + s₂) = op (fold op b₁ s₁) (fold op b₂ s₂) :=
  sorry

theorem fold_singleton {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] (b : α) (a : α) : fold op b (a ::ₘ 0) = op a b :=
  sorry

theorem fold_distrib {α : Type u_1} {β : Type u_2} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] {f : β → α} {g : β → α} (u₁ : α) (u₂ : α) (s : multiset β) :
    fold op (op u₁ u₂) (map (fun (x : β) => op (f x) (g x)) s) =
        op (fold op u₁ (map f s)) (fold op u₂ (map g s)) :=
  sorry

theorem fold_hom {α : Type u_1} {β : Type u_2} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] {op' : β → β → β} [is_commutative β op'] [is_associative β op']
    {m : α → β} (hm : ∀ (x y : α), m (op x y) = op' (m x) (m y)) (b : α) (s : multiset α) :
    fold op' (m b) (map m s) = m (fold op b s) :=
  sorry

theorem fold_union_inter {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] [DecidableEq α] (s₁ : multiset α) (s₂ : multiset α) (b₁ : α)
    (b₂ : α) :
    op (fold op b₁ (s₁ ∪ s₂)) (fold op b₂ (s₁ ∩ s₂)) = op (fold op b₁ s₁) (fold op b₂ s₂) :=
  sorry

@[simp] theorem fold_erase_dup_idem {α : Type u_1} (op : α → α → α) [hc : is_commutative α op]
    [ha : is_associative α op] [DecidableEq α] [hi : is_idempotent α op] (s : multiset α) (b : α) :
    fold op b (erase_dup s) = fold op b s :=
  sorry

theorem le_smul_erase_dup {α : Type u_1} [DecidableEq α] (s : multiset α) :
    ∃ (n : ℕ), s ≤ n •ℕ erase_dup s :=
  sorry

end Mathlib