/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.logic
import Mathlib.Lean3Lib.init.classical
import Mathlib.Lean3Lib.init.meta.name
import Mathlib.Lean3Lib.init.algebra.classes
import PostPort

universes u l u_1 

namespace Mathlib

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/

/-!
### Definition of `preorder` and lemmas about types with a `preorder`
-/

/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class preorder (α : Type u) 
extends HasLess α, HasLessEq α
where
  le : α → α → Prop
  lt : α → α → Prop
  le_refl : ∀ (a : α), a ≤ a
  le_trans : ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c
  lt_iff_le_not_le : autoParam (∀ (a b : α), a < b ↔ a ≤ b ∧ ¬b ≤ a)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.order_laws_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "order_laws_tac") [])

/-- The relation `≤` on a preorder is reflexive. -/
theorem le_refl {α : Type u} [preorder α] (a : α) : a ≤ a :=
  preorder.le_refl

/-- The relation `≤` on a preorder is transitive. -/
theorem le_trans {α : Type u} [preorder α] {a : α} {b : α} {c : α} : a ≤ b → b ≤ c → a ≤ c :=
  preorder.le_trans

theorem lt_iff_le_not_le {α : Type u} [preorder α] {a : α} {b : α} : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  preorder.lt_iff_le_not_le

theorem lt_of_le_not_le {α : Type u} [preorder α] {a : α} {b : α} : a ≤ b → ¬b ≤ a → a < b :=
  fun (ᾰ : a ≤ b) (ᾰ_1 : ¬b ≤ a) => idRhs (a < b) (iff.mpr lt_iff_le_not_le { left := ᾰ, right := ᾰ_1 })

theorem le_not_le_of_lt {α : Type u} [preorder α] {a : α} {b : α} : a < b → a ≤ b ∧ ¬b ≤ a :=
  fun (ᾰ : a < b) => idRhs (a ≤ b ∧ ¬b ≤ a) (iff.mp lt_iff_le_not_le ᾰ)

theorem le_of_eq {α : Type u} [preorder α] {a : α} {b : α} : a = b → a ≤ b :=
  fun (h : a = b) => h ▸ le_refl a

theorem ge_trans {α : Type u} [preorder α] {a : α} {b : α} {c : α} : a ≥ b → b ≥ c → a ≥ c :=
  fun (h₁ : a ≥ b) (h₂ : b ≥ c) => le_trans h₂ h₁

theorem lt_irrefl {α : Type u} [preorder α] (a : α) : ¬a < a := sorry

theorem gt_irrefl {α : Type u} [preorder α] (a : α) : ¬a > a :=
  lt_irrefl

theorem lt_trans {α : Type u} [preorder α] {a : α} {b : α} {c : α} : a < b → b < c → a < c := sorry

theorem gt_trans {α : Type u} [preorder α] {a : α} {b : α} {c : α} : a > b → b > c → a > c :=
  fun (h₁ : a > b) (h₂ : b > c) => lt_trans h₂ h₁

theorem ne_of_lt {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) : a ≠ b :=
  fun (he : a = b) => absurd h (he ▸ lt_irrefl a)

theorem ne_of_gt {α : Type u} [preorder α] {a : α} {b : α} (h : a > b) : a ≠ b :=
  fun (he : a = b) => absurd h (he ▸ lt_irrefl a)

theorem lt_asymm {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) : ¬b < a :=
  fun (h1 : b < a) => lt_irrefl a (lt_trans h h1)

theorem le_of_lt {α : Type u} [preorder α] {a : α} {b : α} : a < b → a ≤ b :=
  fun (ᾰ : a < b) => idRhs (a ≤ b) (and.left (le_not_le_of_lt ᾰ))

theorem lt_of_lt_of_le {α : Type u} [preorder α] {a : α} {b : α} {c : α} : a < b → b ≤ c → a < c := sorry

theorem lt_of_le_of_lt {α : Type u} [preorder α] {a : α} {b : α} {c : α} : a ≤ b → b < c → a < c := sorry

theorem gt_of_gt_of_ge {α : Type u} [preorder α] {a : α} {b : α} {c : α} (h₁ : a > b) (h₂ : b ≥ c) : a > c :=
  lt_of_le_of_lt h₂ h₁

theorem gt_of_ge_of_gt {α : Type u} [preorder α] {a : α} {b : α} {c : α} (h₁ : a ≥ b) (h₂ : b > c) : a > c :=
  lt_of_lt_of_le h₂ h₁

theorem not_le_of_gt {α : Type u} [preorder α] {a : α} {b : α} (h : a > b) : ¬a ≤ b :=
  and.right (le_not_le_of_lt h)

theorem not_lt_of_ge {α : Type u} [preorder α] {a : α} {b : α} (h : a ≥ b) : ¬a < b :=
  fun (hab : a < b) => not_le_of_gt hab h

theorem le_of_lt_or_eq {α : Type u} [preorder α] {a : α} {b : α} : a < b ∨ a = b → a ≤ b :=
  fun (ᾰ : a < b ∨ a = b) =>
    or.dcases_on ᾰ (fun (ᾰ : a < b) => idRhs (a ≤ b) (le_of_lt ᾰ))
      fun (ᾰ : a = b) => idRhs ((fun (_x : α) => a ≤ _x) b) (ᾰ ▸ le_refl a)

theorem le_of_eq_or_lt {α : Type u} [preorder α] {a : α} {b : α} (h : a = b ∨ a < b) : a ≤ b :=
  or.elim h le_of_eq le_of_lt

protected instance decidable_lt_of_decidable_le {α : Type u} [preorder α] [DecidableRel LessEq] : DecidableRel Less :=
  sorry

/-!
### Definition of `partial_order` and lemmas about types with a partial order
-/

/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class partial_order (α : Type u) 
extends preorder α
where
  le_antisymm : ∀ (a b : α), a ≤ b → b ≤ a → a = b

theorem le_antisymm {α : Type u} [partial_order α] {a : α} {b : α} : a ≤ b → b ≤ a → a = b :=
  partial_order.le_antisymm

theorem le_antisymm_iff {α : Type u} [partial_order α] {a : α} {b : α} : a = b ↔ a ≤ b ∧ b ≤ a := sorry

theorem lt_or_eq_of_le {α : Type u} [partial_order α] {a : α} {b : α} : a ≤ b → a < b ∨ a = b := sorry

theorem le_iff_lt_or_eq {α : Type u} [partial_order α] {a : α} {b : α} : a ≤ b ↔ a < b ∨ a = b :=
  idRhs (a ≤ b ↔ a < b ∨ a = b) { mp := lt_or_eq_of_le, mpr := le_of_lt_or_eq }

theorem lt_of_le_of_ne {α : Type u} [partial_order α] {a : α} {b : α} : a ≤ b → a ≠ b → a < b :=
  fun (h₁ : a ≤ b) (h₂ : a ≠ b) => lt_of_le_not_le h₁ (mt (le_antisymm h₁) h₂)

protected instance decidable_eq_of_decidable_le {α : Type u} [partial_order α] [DecidableRel LessEq] : DecidableEq α :=
  sorry

/-!
### Definition of `linear_order` and lemmas about types with a linear order
-/

/-- A linear order is reflexive, transitive, antisymmetric and total relation `≤`.
We assume that every linear ordered type has decidable `(≤)`, `(<)`, and `(=)`. -/
class linear_order (α : Type u) 
extends partial_order α
where
  le_total : ∀ (a b : α), a ≤ b ∨ b ≤ a
  decidable_le : DecidableRel LessEq
  decidable_eq : DecidableEq α
  decidable_lt : DecidableRel Less

theorem le_total {α : Type u} [linear_order α] (a : α) (b : α) : a ≤ b ∨ b ≤ a :=
  linear_order.le_total

theorem le_of_not_ge {α : Type u} [linear_order α] {a : α} {b : α} : ¬a ≥ b → a ≤ b :=
  or.resolve_left (le_total b a)

theorem le_of_not_le {α : Type u} [linear_order α] {a : α} {b : α} : ¬a ≤ b → b ≤ a :=
  or.resolve_left (le_total a b)

theorem not_lt_of_gt {α : Type u} [linear_order α] {a : α} {b : α} (h : a > b) : ¬a < b :=
  lt_asymm h

theorem lt_trichotomy {α : Type u} [linear_order α] (a : α) (b : α) : a < b ∨ a = b ∨ b < a := sorry

theorem le_of_not_gt {α : Type u} [linear_order α] {a : α} {b : α} (h : ¬a > b) : a ≤ b := sorry

theorem lt_of_not_ge {α : Type u} [linear_order α] {a : α} {b : α} (h : ¬a ≥ b) : a < b :=
  lt_of_le_not_le (or.resolve_right (le_total a b) h) h

theorem lt_or_ge {α : Type u} [linear_order α] (a : α) (b : α) : a < b ∨ a ≥ b := sorry

theorem le_or_gt {α : Type u} [linear_order α] (a : α) (b : α) : a ≤ b ∨ a > b :=
  or.swap (lt_or_ge b a)

theorem lt_or_gt_of_ne {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≠ b) : a < b ∨ a > b := sorry

theorem ne_iff_lt_or_gt {α : Type u} [linear_order α] {a : α} {b : α} : a ≠ b ↔ a < b ∨ a > b :=
  { mp := lt_or_gt_of_ne, mpr := fun (o : a < b ∨ a > b) => or.elim o ne_of_lt ne_of_gt }

theorem lt_iff_not_ge {α : Type u} [linear_order α] (x : α) (y : α) : x < y ↔ ¬x ≥ y :=
  { mp := not_le_of_gt, mpr := lt_of_not_ge }

@[simp] theorem not_lt {α : Type u} [linear_order α] {a : α} {b : α} : ¬a < b ↔ b ≤ a :=
  { mp := le_of_not_gt, mpr := not_lt_of_ge }

@[simp] theorem not_le {α : Type u} [linear_order α] {a : α} {b : α} : ¬a ≤ b ↔ b < a :=
  iff.symm (lt_iff_not_ge b a)

protected instance has_lt.lt.decidable {α : Type u} [linear_order α] (a : α) (b : α) : Decidable (a < b) :=
  linear_order.decidable_lt a b

protected instance has_le.le.decidable {α : Type u} [linear_order α] (a : α) (b : α) : Decidable (a ≤ b) :=
  linear_order.decidable_le a b

protected instance eq.decidable {α : Type u} [linear_order α] (a : α) (b : α) : Decidable (a = b) :=
  linear_order.decidable_eq a b

theorem eq_or_lt_of_not_lt {α : Type u} [linear_order α] {a : α} {b : α} (h : ¬a < b) : a = b ∨ b < a :=
  dite (a = b) (fun (h₁ : a = b) => Or.inl h₁)
    fun (h₁ : ¬a = b) => Or.inr (lt_of_not_ge fun (hge : b ≥ a) => h (lt_of_le_of_ne hge h₁))

protected instance has_le.le.is_total_preorder {α : Type u} [linear_order α] : is_total_preorder α LessEq :=
  is_total_preorder.mk

/- TODO(Leo): decide whether we should keep this instance or not -/

protected instance is_strict_weak_order_of_linear_order {α : Type u} [linear_order α] : is_strict_weak_order α Less :=
  is_strict_weak_order_of_is_total_preorder lt_iff_not_ge

/- TODO(Leo): decide whether we should keep this instance or not -/

protected instance is_strict_total_order_of_linear_order {α : Type u} [linear_order α] : is_strict_total_order α Less :=
  is_strict_total_order.mk

namespace decidable


theorem lt_or_eq_of_le {α : Type u} [partial_order α] [DecidableRel LessEq] {a : α} {b : α} (hab : a ≤ b) : a < b ∨ a = b :=
  dite (b ≤ a) (fun (hba : b ≤ a) => Or.inr (le_antisymm hab hba)) fun (hba : ¬b ≤ a) => Or.inl (lt_of_le_not_le hab hba)

theorem eq_or_lt_of_le {α : Type u} [partial_order α] [DecidableRel LessEq] {a : α} {b : α} (hab : a ≤ b) : a = b ∨ a < b :=
  or.swap (lt_or_eq_of_le hab)

theorem le_iff_lt_or_eq {α : Type u} [partial_order α] [DecidableRel LessEq] {a : α} {b : α} : a ≤ b ↔ a < b ∨ a = b :=
  { mp := lt_or_eq_of_le, mpr := le_of_lt_or_eq }

theorem le_of_not_lt {α : Type u} [linear_order α] {a : α} {b : α} (h : ¬b < a) : a ≤ b :=
  by_contradiction fun (h' : ¬a ≤ b) => h (lt_of_le_not_le (or.resolve_right (le_total b a) h') h')

theorem not_lt {α : Type u} [linear_order α] {a : α} {b : α} : ¬a < b ↔ b ≤ a :=
  { mp := le_of_not_lt, mpr := not_lt_of_ge }

theorem lt_or_le {α : Type u} [linear_order α] (a : α) (b : α) : a < b ∨ b ≤ a :=
  dite (b ≤ a) (fun (hba : b ≤ a) => Or.inr hba) fun (hba : ¬b ≤ a) => Or.inl (lt_of_not_ge hba)

theorem le_or_lt {α : Type u} [linear_order α] (a : α) (b : α) : a ≤ b ∨ b < a :=
  or.swap (lt_or_le b a)

theorem lt_trichotomy {α : Type u} [linear_order α] (a : α) (b : α) : a < b ∨ a = b ∨ b < a :=
  or.imp_right (fun (h : b ≤ a) => or.imp_left Eq.symm (eq_or_lt_of_le h)) (lt_or_le a b)

theorem lt_or_gt_of_ne {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≠ b) : a < b ∨ b < a :=
  or.imp_right (fun (h' : a = b ∨ b < a) => or.resolve_left h' h) (lt_trichotomy a b)

/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order. -/
def lt_by_cases {α : Type u} [linear_order α] (x : α) (y : α) {P : Sort u_1} (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
  dite (x < y) (fun (h : x < y) => h₁ h)
    fun (h : ¬x < y) => dite (y < x) (fun (h' : y < x) => h₃ h') fun (h' : ¬y < x) => h₂ sorry

theorem ne_iff_lt_or_gt {α : Type u} [linear_order α] {a : α} {b : α} : a ≠ b ↔ a < b ∨ b < a :=
  { mp := lt_or_gt_of_ne, mpr := fun (o : a < b ∨ b < a) => or.elim o ne_of_lt ne_of_gt }

theorem le_imp_le_of_lt_imp_lt {α : Type u} {β : Type u_1} [preorder α] [linear_order β] {a : α} {b : α} {c : β} {d : β} (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
  le_of_not_lt fun (h' : d < c) => not_le_of_gt (H h') h

