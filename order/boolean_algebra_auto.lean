/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Type class hierarchy for Boolean algebras.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.bounded_lattice
import PostPort

universes u_1 l u v 

namespace Mathlib

/-- Set / lattice complement -/
class has_compl (α : Type u_1) 
where
  compl : α → α

postfix:0 "ᶜ" => Mathlib.has_compl.compl

/-- A boolean algebra is a bounded distributive lattice with a
  complementation operation `-` such that `x ⊓ - x = ⊥` and `x ⊔ - x = ⊤`.
  This is a generalization of (classical) logic of propositions, or
  the powerset lattice. -/
class boolean_algebra (α : Type u_1) 
extends has_sdiff α, has_compl α, bounded_distrib_lattice α
where
  inf_compl_le_bot : ∀ (x : α), x ⊓ (xᶜ) ≤ ⊥
  top_le_sup_compl : ∀ (x : α), ⊤ ≤ x ⊔ (xᶜ)
  sdiff_eq : ∀ (x y : α), x \ y = x ⊓ (yᶜ)

@[simp] theorem inf_compl_eq_bot {α : Type u} {x : α} [boolean_algebra α] : x ⊓ (xᶜ) = ⊥ :=
  bot_unique (boolean_algebra.inf_compl_le_bot x)

@[simp] theorem compl_inf_eq_bot {α : Type u} {x : α} [boolean_algebra α] : xᶜ ⊓ x = ⊥ :=
  Eq.trans inf_comm inf_compl_eq_bot

@[simp] theorem sup_compl_eq_top {α : Type u} {x : α} [boolean_algebra α] : x ⊔ (xᶜ) = ⊤ :=
  top_unique (boolean_algebra.top_le_sup_compl x)

@[simp] theorem compl_sup_eq_top {α : Type u} {x : α} [boolean_algebra α] : xᶜ ⊔ x = ⊤ :=
  Eq.trans sup_comm sup_compl_eq_top

theorem is_compl_compl {α : Type u} {x : α} [boolean_algebra α] : is_compl x (xᶜ) :=
  is_compl.of_eq inf_compl_eq_bot sup_compl_eq_top

theorem is_compl.compl_eq {α : Type u} {x : α} {y : α} [boolean_algebra α] (h : is_compl x y) : xᶜ = y :=
  Eq.symm (is_compl.right_unique h is_compl_compl)

theorem disjoint_compl_right {α : Type u} {x : α} [boolean_algebra α] : disjoint x (xᶜ) :=
  is_compl.disjoint is_compl_compl

theorem disjoint_compl_left {α : Type u} {x : α} [boolean_algebra α] : disjoint (xᶜ) x :=
  disjoint.symm disjoint_compl_right

theorem sdiff_eq {α : Type u} {x : α} {y : α} [boolean_algebra α] : x \ y = x ⊓ (yᶜ) :=
  boolean_algebra.sdiff_eq x y

theorem compl_unique {α : Type u} {x : α} {y : α} [boolean_algebra α] (i : x ⊓ y = ⊥) (s : x ⊔ y = ⊤) : xᶜ = y :=
  is_compl.compl_eq (is_compl.of_eq i s)

@[simp] theorem compl_top {α : Type u} [boolean_algebra α] : ⊤ᶜ = ⊥ :=
  is_compl.compl_eq is_compl_top_bot

@[simp] theorem compl_bot {α : Type u} [boolean_algebra α] : ⊥ᶜ = ⊤ :=
  is_compl.compl_eq is_compl_bot_top

@[simp] theorem compl_compl {α : Type u} [boolean_algebra α] (x : α) : xᶜᶜ = x :=
  is_compl.compl_eq (is_compl.symm is_compl_compl)

theorem compl_injective {α : Type u} [boolean_algebra α] : function.injective compl :=
  function.involutive.injective compl_compl

@[simp] theorem compl_inj_iff {α : Type u} {x : α} {y : α} [boolean_algebra α] : xᶜ = (yᶜ) ↔ x = y :=
  function.injective.eq_iff compl_injective

theorem is_compl.compl_eq_iff {α : Type u} {x : α} {y : α} {z : α} [boolean_algebra α] (h : is_compl x y) : zᶜ = y ↔ z = x :=
  is_compl.compl_eq h ▸ compl_inj_iff

@[simp] theorem compl_eq_top {α : Type u} {x : α} [boolean_algebra α] : xᶜ = ⊤ ↔ x = ⊥ :=
  is_compl.compl_eq_iff is_compl_bot_top

@[simp] theorem compl_eq_bot {α : Type u} {x : α} [boolean_algebra α] : xᶜ = ⊥ ↔ x = ⊤ :=
  is_compl.compl_eq_iff is_compl_top_bot

@[simp] theorem compl_inf {α : Type u} {x : α} {y : α} [boolean_algebra α] : x ⊓ yᶜ = xᶜ ⊔ (yᶜ) :=
  is_compl.compl_eq (is_compl.inf_sup is_compl_compl is_compl_compl)

@[simp] theorem compl_sup {α : Type u} {x : α} {y : α} [boolean_algebra α] : x ⊔ yᶜ = xᶜ ⊓ (yᶜ) :=
  is_compl.compl_eq (is_compl.sup_inf is_compl_compl is_compl_compl)

theorem compl_le_compl {α : Type u} {x : α} {y : α} [boolean_algebra α] (h : y ≤ x) : xᶜ ≤ (yᶜ) :=
  is_compl.antimono is_compl_compl is_compl_compl h

@[simp] theorem compl_le_compl_iff_le {α : Type u} {x : α} {y : α} [boolean_algebra α] : yᶜ ≤ (xᶜ) ↔ x ≤ y := sorry

theorem le_compl_of_le_compl {α : Type u} {x : α} {y : α} [boolean_algebra α] (h : y ≤ (xᶜ)) : x ≤ (yᶜ) := sorry

theorem compl_le_of_compl_le {α : Type u} {x : α} {y : α} [boolean_algebra α] (h : yᶜ ≤ x) : xᶜ ≤ y := sorry

theorem le_compl_iff_le_compl {α : Type u} {x : α} {y : α} [boolean_algebra α] : y ≤ (xᶜ) ↔ x ≤ (yᶜ) :=
  { mp := le_compl_of_le_compl, mpr := le_compl_of_le_compl }

theorem compl_le_iff_compl_le {α : Type u} {x : α} {y : α} [boolean_algebra α] : xᶜ ≤ y ↔ yᶜ ≤ x :=
  { mp := compl_le_of_compl_le, mpr := compl_le_of_compl_le }

theorem sup_sdiff_same {α : Type u} {x : α} {y : α} [boolean_algebra α] : x ⊔ y \ x = x ⊔ y := sorry

theorem sdiff_eq_left {α : Type u} {x : α} {y : α} [boolean_algebra α] (h : x ⊓ y = ⊥) : x \ y = x := sorry

theorem sdiff_le_sdiff {α : Type u} {w : α} {x : α} {y : α} {z : α} [boolean_algebra α] (h₁ : w ≤ y) (h₂ : z ≤ x) : w \ x ≤ y \ z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (w \ x ≤ y \ z)) sdiff_eq))
    (eq.mpr (id (Eq._oldrec (Eq.refl (w ⊓ (xᶜ) ≤ y \ z)) sdiff_eq)) (inf_le_inf h₁ (compl_le_compl h₂)))

@[simp] theorem sdiff_idem_right {α : Type u} {x : α} {y : α} [boolean_algebra α] : x \ y \ y = x \ y := sorry

protected instance boolean_algebra_Prop : boolean_algebra Prop :=
  boolean_algebra.mk bounded_distrib_lattice.sup bounded_distrib_lattice.le bounded_distrib_lattice.lt sorry sorry sorry
    sorry sorry sorry bounded_distrib_lattice.inf sorry sorry sorry sorry bounded_distrib_lattice.top sorry
    bounded_distrib_lattice.bot sorry Not (fun (p q : Prop) => p ∧ ¬q) sorry sorry sorry

protected instance pi.boolean_algebra {α : Type u} {β : Type v} [boolean_algebra β] : boolean_algebra (α → β) :=
  boolean_algebra.mk (fun (ᾰ ᾰ_1 : α → β) (i : α) => boolean_algebra.sup (ᾰ i) (ᾰ_1 i)) partial_order.le partial_order.lt
    sorry sorry sorry sorry sorry sorry (fun (ᾰ ᾰ_1 : α → β) (i : α) => boolean_algebra.inf (ᾰ i) (ᾰ_1 i)) sorry sorry
    sorry sorry (fun (i : α) => boolean_algebra.top) sorry (fun (i : α) => boolean_algebra.bot) sorry
    (fun (ᾰ : α → β) (i : α) => boolean_algebra.compl (ᾰ i))
    (fun (ᾰ ᾰ_1 : α → β) (i : α) => boolean_algebra.sdiff (ᾰ i) (ᾰ_1 i)) sorry sorry sorry

