/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

# Preorder homomorphisms

Bundled monotone functions, `x ≤ y → f x ≤ f y`.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.logic.function.iterate
import Mathlib.order.basic
import Mathlib.order.bounded_lattice
import Mathlib.order.complete_lattice
import Mathlib.tactic.monotonicity.default
import Mathlib.PostPort

universes u_1 u_2 l u_3 

namespace Mathlib

/-! # Category of preorders -/

/-- Bundled monotone (aka, increasing) function -/
structure preorder_hom (α : Type u_1) (β : Type u_2) [preorder α] [preorder β] 
where
  to_fun : α → β
  monotone' : monotone to_fun

infixr:25 " →ₘ " => Mathlib.preorder_hom

namespace preorder_hom


protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] : has_coe_to_fun (α →ₘ β) :=
  has_coe_to_fun.mk (fun (f : α →ₘ β) => α → β) to_fun

theorem monotone {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α →ₘ β) : monotone ⇑f :=
  monotone' f

@[simp] theorem coe_fun_mk {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] {f : α → β} (hf : monotone f) (x : α) : coe_fn (mk f hf) x = f x :=
  rfl

theorem ext {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α →ₘ β) (g : α →ₘ β) (h : ∀ (a : α), coe_fn f a = coe_fn g a) : f = g := sorry

theorem coe_inj {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α →ₘ β) (g : α →ₘ β) (h : ⇑f = ⇑g) : f = g :=
  ext f g fun (a : α) => eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f a = coe_fn g a)) h)) (Eq.refl (coe_fn g a))

/-- The identity function as bundled monotone function. -/
def id {α : Type u_1} [preorder α] : α →ₘ α :=
  mk id monotone_id

protected instance inhabited {α : Type u_1} [preorder α] : Inhabited (α →ₘ α) :=
  { default := id }

@[simp] theorem coe_id {α : Type u_1} [preorder α] : ⇑id = ⇑id :=
  rfl

/-- The composition of two bundled monotone functions. -/
def comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [preorder α] [preorder β] [preorder γ] (g : β →ₘ γ) (f : α →ₘ β) : α →ₘ γ :=
  mk (⇑g ∘ ⇑f) sorry

@[simp] theorem comp_id {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α →ₘ β) : comp f id = f :=
  ext (comp f id) f fun (a : α) => Eq.refl (coe_fn (comp f id) a)

@[simp] theorem id_comp {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α →ₘ β) : comp id f = f :=
  ext (comp id f) f fun (a : α) => Eq.refl (coe_fn (comp id f) a)

/-- `subtype.val` as a bundled monotone function.  -/
def subtype.val {α : Type u_1} [preorder α] (p : α → Prop) : Subtype p →ₘ α :=
  mk subtype.val sorry

/-- The preorder structure of `α →ₘ β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ g a`. -/
protected instance preorder {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] : preorder (α →ₘ β) :=
  preorder.lift to_fun

protected instance partial_order {α : Type u_1} [preorder α] {β : Type u_2} [partial_order β] : partial_order (α →ₘ β) :=
  partial_order.lift to_fun sorry

protected instance has_sup {α : Type u_1} [preorder α] {β : Type u_2} [semilattice_sup β] : has_sup (α →ₘ β) :=
  has_sup.mk fun (f g : α →ₘ β) => mk (fun (a : α) => coe_fn f a ⊔ coe_fn g a) sorry

protected instance semilattice_sup {α : Type u_1} [preorder α] {β : Type u_2} [semilattice_sup β] : semilattice_sup (α →ₘ β) :=
  semilattice_sup.mk has_sup.sup partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

@[simp] theorem has_inf_inf_to_fun {α : Type u_1} [preorder α] {β : Type u_2} [semilattice_inf β] (f : α →ₘ β) (g : α →ₘ β) (a : α) : coe_fn (f ⊓ g) a = coe_fn f a ⊓ coe_fn g a :=
  Eq.refl (coe_fn (f ⊓ g) a)

protected instance semilattice_inf {α : Type u_1} [preorder α] {β : Type u_2} [semilattice_inf β] : semilattice_inf (α →ₘ β) :=
  semilattice_inf.mk has_inf.inf partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

protected instance lattice {α : Type u_1} [preorder α] {β : Type u_2} [lattice β] : lattice (α →ₘ β) :=
  lattice.mk semilattice_sup.sup semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

protected instance has_bot {α : Type u_1} [preorder α] {β : Type u_2} [order_bot β] : has_bot (α →ₘ β) :=
  has_bot.mk (mk (fun (a : α) => ⊥) sorry)

protected instance order_bot {α : Type u_1} [preorder α] {β : Type u_2} [order_bot β] : order_bot (α →ₘ β) :=
  order_bot.mk ⊥ partial_order.le partial_order.lt sorry sorry sorry sorry

@[simp] theorem has_top_top_to_fun {α : Type u_1} [preorder α] {β : Type u_2} [order_top β] (a : α) : coe_fn ⊤ a = ⊤ :=
  Eq.refl (coe_fn ⊤ a)

protected instance order_top {α : Type u_1} [preorder α] {β : Type u_2} [order_top β] : order_top (α →ₘ β) :=
  order_top.mk ⊤ partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance has_Inf {α : Type u_1} [preorder α] {β : Type u_2} [complete_lattice β] : has_Inf (α →ₘ β) :=
  has_Inf.mk fun (s : set (α →ₘ β)) => mk (fun (x : α) => Inf ((fun (f : α →ₘ β) => coe_fn f x) '' s)) sorry

@[simp] theorem has_Sup_Sup_to_fun {α : Type u_1} [preorder α] {β : Type u_2} [complete_lattice β] (s : set (α →ₘ β)) (x : α) : coe_fn (Sup s) x = Sup ((fun (f : α →ₘ β) => coe_fn f x) '' s) :=
  Eq.refl (coe_fn (Sup s) x)

protected instance complete_lattice {α : Type u_1} [preorder α] {β : Type u_2} [complete_lattice β] : complete_lattice (α →ₘ β) :=
  complete_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    order_top.top sorry order_bot.bot sorry Sup Inf sorry sorry sorry sorry

theorem iterate_sup_le_sup_iff {α : Type u_1} [semilattice_sup α] (f : α →ₘ α) : (∀ (n₁ n₂ : ℕ) (a₁ a₂ : α), nat.iterate (⇑f) (n₁ + n₂) (a₁ ⊔ a₂) ≤ nat.iterate (⇑f) n₁ a₁ ⊔ nat.iterate (⇑f) n₂ a₂) ↔
  ∀ (a₁ a₂ : α), coe_fn f (a₁ ⊔ a₂) ≤ coe_fn f a₁ ⊔ a₂ := sorry

