/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Binder elimination
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.default
import Mathlib.PostPort

universes u v 

namespace Mathlib

namespace old_conv


/- congr should forward data! -/

end old_conv


/- Binder elimination:

We assume a binder `B : p → Π (α : Sort u), (α → t) → t`, where `t` is a type depending on `p`.
Examples:
  ∃: there is no `p` and `t` is `Prop`.
  ⨅, ⨆: here p is `β` and `[complete_lattice β]`, `p` is `β`

Problem: ∀x, _ should be a binder, but is not a constant!

Provide a mechanism to rewrite:

  B (x : α) ..x.. (h : x = t), p x  =  B ..x/t.., p t

Here ..x.. are binders, maybe also some constants which provide commutativity rules with `B`.

-/

theorem exists_elim_eq_left {α : Sort u} (a : α) (p : (a' : α) → a' = a → Prop) : (∃ (a' : α), ∃ (h : a' = a), p a' h) ↔ p a rfl := sorry

theorem exists_elim_eq_right {α : Sort u} (a : α) (p : (a' : α) → a = a' → Prop) : (∃ (a' : α), ∃ (h : a = a'), p a' h) ↔ p a rfl := sorry

theorem forall_comm {α : Sort u} {β : Sort v} (p : α → β → Prop) : (∀ (a : α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b :=
  { mp := fun (h : ∀ (a : α) (b : β), p a b) (b : β) (a : α) => h a b,
    mpr := fun (h : ∀ (b : β) (a : α), p a b) (b : α) (a : β) => h a b }

theorem forall_elim_eq_left {α : Sort u} (a : α) (p : (a' : α) → a' = a → Prop) : (∀ (a' : α) (h : a' = a), p a' h) ↔ p a rfl := sorry

theorem forall_elim_eq_right {α : Sort u} (a : α) (p : (a' : α) → a = a' → Prop) : (∀ (a' : α) (h : a = a'), p a' h) ↔ p a rfl := sorry

