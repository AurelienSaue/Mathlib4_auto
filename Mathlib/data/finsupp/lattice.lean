/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finsupp.basic
import Mathlib.algebra.ordered_group
import Mathlib.PostPort

universes u_1 u_3 u_2 u_4 

namespace Mathlib

/-!
# Lattice structure on finsupps

This file provides instances of ordered structures on finsupps.

-/

namespace finsupp


protected instance order_bot {α : Type u_1} {μ : Type u_3} [canonically_ordered_add_monoid μ] : order_bot (α →₀ μ) :=
  order_bot.mk 0 partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance semilattice_inf {α : Type u_1} {β : Type u_2} [HasZero β] [semilattice_inf β] : semilattice_inf (α →₀ β) :=
  semilattice_inf.mk (zip_with has_inf.inf sorry) partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

@[simp] theorem inf_apply {α : Type u_1} {β : Type u_2} [HasZero β] [semilattice_inf β] {a : α} {f : α →₀ β} {g : α →₀ β} : coe_fn (f ⊓ g) a = coe_fn f a ⊓ coe_fn g a :=
  rfl

@[simp] theorem support_inf {α : Type u_1} {γ : Type u_4} [canonically_linear_ordered_add_monoid γ] {f : α →₀ γ} {g : α →₀ γ} : support (f ⊓ g) = support f ∩ support g := sorry

protected instance semilattice_sup {α : Type u_1} {β : Type u_2} [HasZero β] [semilattice_sup β] : semilattice_sup (α →₀ β) :=
  semilattice_sup.mk (zip_with has_sup.sup sorry) partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

@[simp] theorem sup_apply {α : Type u_1} {β : Type u_2} [HasZero β] [semilattice_sup β] {a : α} {f : α →₀ β} {g : α →₀ β} : coe_fn (f ⊔ g) a = coe_fn f a ⊔ coe_fn g a :=
  rfl

@[simp] theorem support_sup {α : Type u_1} {γ : Type u_4} [canonically_linear_ordered_add_monoid γ] {f : α →₀ γ} {g : α →₀ γ} : support (f ⊔ g) = support f ∪ support g := sorry

protected instance lattice {α : Type u_1} {β : Type u_2} [HasZero β] [lattice β] : lattice (α →₀ β) :=
  lattice.mk semilattice_sup.sup semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

protected instance semilattice_inf_bot {α : Type u_1} {γ : Type u_4} [canonically_linear_ordered_add_monoid γ] : semilattice_inf_bot (α →₀ γ) :=
  semilattice_inf_bot.mk order_bot.bot order_bot.le order_bot.lt sorry sorry sorry sorry lattice.inf sorry sorry sorry

theorem bot_eq_zero {α : Type u_1} {γ : Type u_4} [canonically_linear_ordered_add_monoid γ] : ⊥ = 0 :=
  rfl

theorem disjoint_iff {α : Type u_1} {γ : Type u_4} [canonically_linear_ordered_add_monoid γ] {x : α →₀ γ} {y : α →₀ γ} : disjoint x y ↔ disjoint (support x) (support y) := sorry

/-- The order on `finsupp`s over a partial order embeds into the order on functions -/
def order_embedding_to_fun {α : Type u_1} {β : Type u_2} [HasZero β] [partial_order β] : (α →₀ β) ↪o (α → β) :=
  rel_embedding.mk (function.embedding.mk (fun (f : α →₀ β) (a : α) => coe_fn f a) sorry) sorry

@[simp] theorem order_embedding_to_fun_apply {α : Type u_1} {β : Type u_2} [HasZero β] [partial_order β] {f : α →₀ β} {a : α} : coe_fn order_embedding_to_fun f a = coe_fn f a :=
  rfl

theorem monotone_to_fun {α : Type u_1} {β : Type u_2} [HasZero β] [partial_order β] : monotone to_fun :=
  fun (f g : α →₀ β) (h : f ≤ g) (a : α) => iff.mp le_def h a

