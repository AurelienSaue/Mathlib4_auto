/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury G. Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.basic
import PostPort

universes u l u_1 v 

namespace Mathlib

/-!
# Unbundled relation classes

In this file we prove some properties of `is_*` classes defined in `init.algebra.classes`. The main
difference between these classes and the usual order classes (`preorder` etc) is that usual classes
extend `has_le` and/or `has_lt` while these classes take a relation as an explicit argument.

-/

theorem is_refl.swap {α : Type u} (r : α → α → Prop) [is_refl α r] : is_refl α (function.swap r) :=
  is_refl.mk (refl_of r)

theorem is_irrefl.swap {α : Type u} (r : α → α → Prop) [is_irrefl α r] : is_irrefl α (function.swap r) :=
  is_irrefl.mk (irrefl_of r)

theorem is_trans.swap {α : Type u} (r : α → α → Prop) [is_trans α r] : is_trans α (function.swap r) :=
  is_trans.mk fun (a b c : α) (h₁ : function.swap r a b) (h₂ : function.swap r b c) => trans_of r h₂ h₁

theorem is_antisymm.swap {α : Type u} (r : α → α → Prop) [is_antisymm α r] : is_antisymm α (function.swap r) :=
  is_antisymm.mk fun (a b : α) (h₁ : function.swap r a b) (h₂ : function.swap r b a) => antisymm h₂ h₁

theorem is_asymm.swap {α : Type u} (r : α → α → Prop) [is_asymm α r] : is_asymm α (function.swap r) :=
  is_asymm.mk fun (a b : α) (h₁ : function.swap r a b) (h₂ : function.swap r b a) => asymm_of r h₂ h₁

theorem is_total.swap {α : Type u} (r : α → α → Prop) [is_total α r] : is_total α (function.swap r) :=
  is_total.mk fun (a b : α) => or.swap (total_of r a b)

theorem is_trichotomous.swap {α : Type u} (r : α → α → Prop) [is_trichotomous α r] : is_trichotomous α (function.swap r) := sorry

theorem is_preorder.swap {α : Type u} (r : α → α → Prop) [is_preorder α r] : is_preorder α (function.swap r) :=
  is_preorder.mk

theorem is_strict_order.swap {α : Type u} (r : α → α → Prop) [is_strict_order α r] : is_strict_order α (function.swap r) :=
  is_strict_order.mk

theorem is_partial_order.swap {α : Type u} (r : α → α → Prop) [is_partial_order α r] : is_partial_order α (function.swap r) :=
  is_partial_order.mk

theorem is_total_preorder.swap {α : Type u} (r : α → α → Prop) [is_total_preorder α r] : is_total_preorder α (function.swap r) :=
  is_total_preorder.mk

theorem is_linear_order.swap {α : Type u} (r : α → α → Prop) [is_linear_order α r] : is_linear_order α (function.swap r) :=
  is_linear_order.mk

protected theorem is_asymm.is_antisymm {α : Type u} (r : α → α → Prop) [is_asymm α r] : is_antisymm α r :=
  is_antisymm.mk fun (x y : α) (h₁ : r x y) (h₂ : r y x) => false.elim (asymm h₁ h₂)

protected theorem is_asymm.is_irrefl {α : Type u} {r : α → α → Prop} [is_asymm α r] : is_irrefl α r :=
  is_irrefl.mk fun (a : α) (h : r a a) => asymm h h

/- Convert algebraic structure style to explicit relation style typeclasses -/

protected instance has_le.le.is_refl {α : Type u} [preorder α] : is_refl α LessEq :=
  is_refl.mk le_refl

protected instance ge.is_refl {α : Type u} [preorder α] : is_refl α ge :=
  is_refl.swap fun (b a : α) => b ≤ a

protected instance has_le.le.is_trans {α : Type u} [preorder α] : is_trans α LessEq :=
  is_trans.mk le_trans

protected instance ge.is_trans {α : Type u} [preorder α] : is_trans α ge :=
  is_trans.swap fun (b a : α) => b ≤ a

protected instance has_le.le.is_preorder {α : Type u} [preorder α] : is_preorder α LessEq :=
  is_preorder.mk

protected instance ge.is_preorder {α : Type u} [preorder α] : is_preorder α ge :=
  is_preorder.mk

protected instance has_lt.lt.is_irrefl {α : Type u} [preorder α] : is_irrefl α Less :=
  is_irrefl.mk lt_irrefl

protected instance gt.is_irrefl {α : Type u} [preorder α] : is_irrefl α gt :=
  is_irrefl.swap fun (b a : α) => b < a

protected instance has_lt.lt.is_trans {α : Type u} [preorder α] : is_trans α Less :=
  is_trans.mk lt_trans

protected instance gt.is_trans {α : Type u} [preorder α] : is_trans α gt :=
  is_trans.swap fun (b a : α) => b < a

protected instance has_lt.lt.is_asymm {α : Type u} [preorder α] : is_asymm α Less :=
  is_asymm.mk lt_asymm

protected instance gt.is_asymm {α : Type u} [preorder α] : is_asymm α gt :=
  is_asymm.swap fun (b a : α) => b < a

protected instance has_lt.lt.is_antisymm {α : Type u} [preorder α] : is_antisymm α Less :=
  is_asymm.is_antisymm Less

protected instance gt.is_antisymm {α : Type u} [preorder α] : is_antisymm α gt :=
  is_asymm.is_antisymm gt

protected instance has_lt.lt.is_strict_order {α : Type u} [preorder α] : is_strict_order α Less :=
  is_strict_order.mk

protected instance gt.is_strict_order {α : Type u} [preorder α] : is_strict_order α gt :=
  is_strict_order.mk

protected instance preorder.is_total_preorder {α : Type u} [preorder α] [is_total α LessEq] : is_total_preorder α LessEq :=
  is_total_preorder.mk

protected instance has_le.le.is_antisymm {α : Type u} [partial_order α] : is_antisymm α LessEq :=
  is_antisymm.mk le_antisymm

protected instance ge.is_antisymm {α : Type u} [partial_order α] : is_antisymm α ge :=
  is_antisymm.swap fun (b a : α) => b ≤ a

protected instance has_le.le.is_partial_order {α : Type u} [partial_order α] : is_partial_order α LessEq :=
  is_partial_order.mk

protected instance ge.is_partial_order {α : Type u} [partial_order α] : is_partial_order α ge :=
  is_partial_order.mk

protected instance has_le.le.is_total {α : Type u} [linear_order α] : is_total α LessEq :=
  is_total.mk le_total

protected instance ge.is_total {α : Type u} [linear_order α] : is_total α ge :=
  is_total.swap fun (b a : α) => b ≤ a

protected instance linear_order.is_total_preorder {α : Type u} [linear_order α] : is_total_preorder α LessEq :=
  preorder.is_total_preorder

protected instance ge.is_total_preorder {α : Type u} [linear_order α] : is_total_preorder α ge :=
  is_total_preorder.mk

protected instance has_le.le.is_linear_order {α : Type u} [linear_order α] : is_linear_order α LessEq :=
  is_linear_order.mk

protected instance ge.is_linear_order {α : Type u} [linear_order α] : is_linear_order α ge :=
  is_linear_order.mk

protected instance has_lt.lt.is_trichotomous {α : Type u} [linear_order α] : is_trichotomous α Less :=
  is_trichotomous.mk lt_trichotomy

protected instance gt.is_trichotomous {α : Type u} [linear_order α] : is_trichotomous α gt :=
  is_trichotomous.swap fun (b a : α) => b < a

protected instance order_dual.is_total_le {α : Type u} [HasLessEq α] [is_total α LessEq] : is_total (order_dual α) LessEq :=
  is_total.swap fun (x y : α) => x ≤ y

theorem ne_of_irrefl {α : Type u} {r : α → α → Prop} [is_irrefl α r] {x : α} {y : α} : r x y → x ≠ y := sorry

theorem trans_trichotomous_left {α : Type u} {r : α → α → Prop} [is_trans α r] [is_trichotomous α r] {a : α} {b : α} {c : α} : ¬r b a → r b c → r a c := sorry

theorem trans_trichotomous_right {α : Type u} {r : α → α → Prop} [is_trans α r] [is_trichotomous α r] {a : α} {b : α} {c : α} : r a b → ¬r c b → r a c := sorry

/-- Construct a partial order from a `is_strict_order` relation -/
def partial_order_of_SO {α : Type u} (r : α → α → Prop) [is_strict_order α r] : partial_order α :=
  partial_order.mk (fun (x y : α) => x = y ∨ r x y) r sorry sorry sorry

/-- This is basically the same as `is_strict_total_order`, but that definition is
  in Type (probably by mistake) and also has redundant assumptions. -/
class is_strict_total_order' (α : Type u) (lt : α → α → Prop) 
extends is_trichotomous α lt, is_strict_order α lt
where

/-- Construct a linear order from an `is_strict_total_order'` relation -/
def linear_order_of_STO' {α : Type u} (r : α → α → Prop) [is_strict_total_order' α r] [(x y : α) → Decidable (¬r x y)] : linear_order α :=
  linear_order.mk partial_order.le partial_order.lt sorry sorry sorry sorry
    (fun (x y : α) => decidable_of_iff (¬r y x) sorry) Mathlib.decidable_eq_of_decidable_le
    Mathlib.decidable_lt_of_decidable_le

theorem is_strict_total_order'.swap {α : Type u} (r : α → α → Prop) [is_strict_total_order' α r] : is_strict_total_order' α (function.swap r) :=
  is_strict_total_order'.mk

protected instance has_lt.lt.is_strict_total_order' {α : Type u} [linear_order α] : is_strict_total_order' α Less :=
  is_strict_total_order'.mk

/-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`.
  This is recognizable as an intuitionistic substitute for `a ≤ b ∨ b ≤ a` on
  the constructive reals, and is also known as negative transitivity,
  since the contrapositive asserts transitivity of the relation `¬ a < b`.  -/
class is_order_connected (α : Type u) (lt : α → α → Prop) 
where
  conn : ∀ (a b c : α), lt a c → lt a b ∨ lt b c

theorem is_order_connected.neg_trans {α : Type u} {r : α → α → Prop} [is_order_connected α r] {a : α} {b : α} {c : α} (h₁ : ¬r a b) (h₂ : ¬r b c) : ¬r a c := sorry

theorem is_strict_weak_order_of_is_order_connected {α : Type u} {r : α → α → Prop} [is_asymm α r] [is_order_connected α r] : is_strict_weak_order α r :=
  is_strict_weak_order.mk

protected instance is_order_connected_of_is_strict_total_order' {α : Type u} {r : α → α → Prop} [is_strict_total_order' α r] : is_order_connected α r :=
  is_order_connected.mk
    fun (a b c : α) (h : r a c) =>
      or.imp_right (fun (o : a = b ∨ r b a) => or.elim o (fun (e : a = b) => e ▸ h) fun (h' : r b a) => trans h' h)
        (trichotomous a b)

protected instance is_strict_total_order_of_is_strict_total_order' {α : Type u} {r : α → α → Prop} [is_strict_total_order' α r] : is_strict_total_order α r :=
  is_strict_total_order.mk

protected instance has_lt.lt.is_strict_total_order {α : Type u} [linear_order α] : is_strict_total_order α Less :=
  Mathlib.is_strict_total_order_of_is_strict_total_order'

protected instance has_lt.lt.is_order_connected {α : Type u} [linear_order α] : is_order_connected α Less :=
  Mathlib.is_order_connected_of_is_strict_total_order'

protected instance has_lt.lt.is_incomp_trans {α : Type u} [linear_order α] : is_incomp_trans α Less :=
  is_strict_weak_order.to_is_incomp_trans

protected instance has_lt.lt.is_strict_weak_order {α : Type u} [linear_order α] : is_strict_weak_order α Less :=
  Mathlib.is_strict_weak_order_of_linear_order

/-- An extensional relation is one in which an element is determined by its set
  of predecessors. It is named for the `x ∈ y` relation in set theory, whose
  extensionality is one of the first axioms of ZFC. -/
class is_extensional (α : Type u) (r : α → α → Prop) 
where
  ext : ∀ (a b : α), (∀ (x : α), r x a ↔ r x b) → a = b

protected instance is_extensional_of_is_strict_total_order' {α : Type u} {r : α → α → Prop} [is_strict_total_order' α r] : is_extensional α r :=
  is_extensional.mk
    fun (a b : α) (H : ∀ (x : α), r x a ↔ r x b) =>
      or.resolve_right (or.resolve_left (trichotomous a b) (mt (iff.mpr (H a)) (irrefl a))) (mt (iff.mp (H b)) (irrefl b))

/-- A well order is a well-founded linear order. -/
class is_well_order (α : Type u) (r : α → α → Prop) 
extends is_strict_total_order' α r
where
  wf : well_founded r

protected instance is_well_order.is_strict_total_order {α : Type u_1} (r : α → α → Prop) [is_well_order α r] : is_strict_total_order α r :=
  Mathlib.is_strict_total_order_of_is_strict_total_order'

protected instance is_well_order.is_extensional {α : Type u_1} (r : α → α → Prop) [is_well_order α r] : is_extensional α r :=
  Mathlib.is_extensional_of_is_strict_total_order'

protected instance is_well_order.is_trichotomous {α : Type u_1} (r : α → α → Prop) [is_well_order α r] : is_trichotomous α r :=
  is_strict_total_order'.to_is_trichotomous

protected instance is_well_order.is_trans {α : Type u_1} (r : α → α → Prop) [is_well_order α r] : is_trans α r :=
  is_strict_order.to_is_trans

protected instance is_well_order.is_irrefl {α : Type u_1} (r : α → α → Prop) [is_well_order α r] : is_irrefl α r :=
  is_strict_order.to_is_irrefl

protected instance is_well_order.is_asymm {α : Type u_1} (r : α → α → Prop) [is_well_order α r] : is_asymm α r :=
  Mathlib.is_asymm_of_is_trans_of_is_irrefl

/-- Construct a decidable linear order from a well-founded linear order. -/
def is_well_order.linear_order {α : Type u} (r : α → α → Prop) [is_well_order α r] : linear_order α :=
  let _inst : (x y : α) → Decidable (¬r x y) := fun (x y : α) => classical.dec (¬r x y);
  linear_order_of_STO' r

protected instance empty_relation.is_well_order {α : Type u} [subsingleton α] : is_well_order α empty_relation :=
  is_well_order.mk (well_founded.intro fun (a : α) => acc.intro a fun (y : α) => false.elim)

protected instance nat.lt.is_well_order : is_well_order ℕ Less :=
  is_well_order.mk nat.lt_wf

protected instance sum.lex.is_well_order {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop} [is_well_order α r] [is_well_order β s] : is_well_order (α ⊕ β) (sum.lex r s) :=
  is_well_order.mk (sum.lex_wf is_well_order.wf is_well_order.wf)

protected instance prod.lex.is_well_order {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop} [is_well_order α r] [is_well_order β s] : is_well_order (α × β) (prod.lex r s) :=
  is_well_order.mk (prod.lex_wf is_well_order.wf is_well_order.wf)

/-- An unbounded or cofinal set -/
/-- A bounded or final set -/
def unbounded {α : Type u} (r : α → α → Prop) (s : set α)  :=
  ∀ (a : α), ∃ (b : α), ∃ (H : b ∈ s), ¬r b a

def bounded {α : Type u} (r : α → α → Prop) (s : set α)  :=
  ∃ (a : α), ∀ (b : α), b ∈ s → r b a

@[simp] theorem not_bounded_iff {α : Type u} {r : α → α → Prop} (s : set α) : ¬bounded r s ↔ unbounded r s := sorry

@[simp] theorem not_unbounded_iff {α : Type u} {r : α → α → Prop} (s : set α) : ¬unbounded r s ↔ bounded r s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬unbounded r s ↔ bounded r s)) (propext not_iff_comm)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬bounded r s ↔ unbounded r s)) (propext (not_bounded_iff s))))
      (iff.refl (unbounded r s)))

