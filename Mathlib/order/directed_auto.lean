/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.lattice
import Mathlib.data.set.basic
import Mathlib.PostPort

universes u w v u_1 l 

namespace Mathlib

/-- A family of elements of α is directed (with respect to a relation `≼` on α)
  if there is a member of the family `≼`-above any pair in the family.  -/
def directed {α : Type u} {ι : Sort w} (r : α → α → Prop) (f : ι → α) :=
  ∀ (x y : ι), ∃ (z : ι), r (f x) (f z) ∧ r (f y) (f z)

/-- A subset of α is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
def directed_on {α : Type u} (r : α → α → Prop) (s : set α) :=
  ∀ (x : α) (H : x ∈ s) (y : α) (H : y ∈ s), ∃ (z : α), ∃ (H : z ∈ s), r x z ∧ r y z

theorem directed_on_iff_directed {α : Type u} {r : α → α → Prop} {s : set α} :
    directed_on r s ↔ directed r coe :=
  sorry

theorem directed_on.directed_coe {α : Type u} {r : α → α → Prop} {s : set α} :
    directed_on r s → directed r coe :=
  iff.mp directed_on_iff_directed

theorem directed_on_image {α : Type u} {β : Type v} {r : α → α → Prop} {s : set β} {f : β → α} :
    directed_on r (f '' s) ↔ directed_on (f ⁻¹'o r) s :=
  sorry

theorem directed_on.mono {α : Type u} {r : α → α → Prop} {s : set α} (h : directed_on r s)
    {r' : α → α → Prop} (H : ∀ {a b : α}, r a b → r' a b) : directed_on r' s :=
  sorry

theorem directed_comp {α : Type u} {β : Type v} {r : α → α → Prop} {ι : Sort u_1} {f : ι → β}
    {g : β → α} : directed r (g ∘ f) ↔ directed (g ⁻¹'o r) f :=
  iff.rfl

theorem directed.mono {α : Type u} {r : α → α → Prop} {s : α → α → Prop} {ι : Sort u_1} {f : ι → α}
    (H : ∀ (a b : α), r a b → s a b) (h : directed r f) : directed s f :=
  sorry

theorem directed.mono_comp {α : Type u} {β : Type v} (r : α → α → Prop) {ι : Sort u_1}
    {rb : β → β → Prop} {g : α → β} {f : ι → α} (hg : ∀ {x y : α}, r x y → rb (g x) (g y))
    (hf : directed r f) : directed rb (g ∘ f) :=
  iff.mpr directed_comp (directed.mono hg hf)

/-- A monotone function on a sup-semilattice is directed. -/
theorem directed_of_sup {α : Type u} {β : Type v} [semilattice_sup α] {f : α → β} {r : β → β → Prop}
    (H : ∀ {i j : α}, i ≤ j → r (f i) (f j)) : directed r f :=
  fun (a b : α) => Exists.intro (a ⊔ b) { left := H le_sup_left, right := H le_sup_right }

/-- An antimonotone function on an inf-semilattice is directed. -/
theorem directed_of_inf {α : Type u} {β : Type v} [semilattice_inf α] {r : β → β → Prop} {f : α → β}
    (hf : ∀ (a₁ a₂ : α), a₁ ≤ a₂ → r (f a₂) (f a₁)) : directed r f :=
  fun (x y : α) =>
    Exists.intro (x ⊓ y) { left := hf (x ⊓ y) x inf_le_left, right := hf (x ⊓ y) y inf_le_right }

/-- A `preorder` is a `directed_order` if for any two elements `i`, `j`
there is an element `k` such that `i ≤ k` and `j ≤ k`. -/
class directed_order (α : Type u) extends preorder α where
  directed : ∀ (i j : α), ∃ (k : α), i ≤ k ∧ j ≤ k

protected instance linear_order.to_directed_order (α : Type u_1) [linear_order α] :
    directed_order α :=
  directed_order.mk sorry

end Mathlib