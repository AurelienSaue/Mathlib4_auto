/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.conditionally_complete_lattice
import Mathlib.logic.function.conjugate
import Mathlib.order.ord_continuous
import Mathlib.data.equiv.mul_add
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Semiconjugate by `Sup`

In this file we prove two facts about semiconjugate (families of) functions.

First, if an order isomorphism `fa : α → α` is semiconjugate to an order embedding `fb : β → β` by
`g : α → β`, then `fb` is semiconjugate to `fa` by `y ↦ Sup {x | g x ≤ y}`, see
`semiconj.symm_adjoint`.

Second, consider two actions `f₁ f₂ : G → α → α` of a group on a complete lattice by order
isomorphisms. Then the map `x ↦ ⨆ g : G, (f₁ g)⁻¹ (f₂ g x)` semiconjugates each `f₁ g'` to `f₂ g'`,
see `function.Sup_div_semiconj`.  In the case of a conditionally complete lattice, a similar
statement holds true under an additional assumption that each set `{(f₁ g)⁻¹ (f₂ g x) | g : G}` is
bounded above, see `function.cSup_div_semiconj`.

The lemmas come from [Étienne Ghys, Groupes d'homeomorphismes du cercle et cohomologie
bornee][ghys87:groupes], Proposition 2.1 and 5.4 respectively. In the paper they are formulated for
homeomorphisms of the circle, so in order to apply results from this file one has to lift these
homeomorphisms to the real line first.
-/

/-- We say that `g : β → α` is an order right adjoint function for `f : α → β` if it sends each `y`
to a least upper bound for `{x | f x ≤ y}`. If `α` is a partial order, and `f : α → β` has
a right adjoint, then this right adjoint is unique. -/
def is_order_right_adjoint {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (f : α → β) (g : β → α)  :=
  ∀ (y : β), is_lub (set_of fun (x : α) => f x ≤ y) (g y)

theorem is_order_right_adjoint_Sup {α : Type u_1} {β : Type u_2} [complete_lattice α] [preorder β] (f : α → β) : is_order_right_adjoint f fun (y : β) => Sup (set_of fun (x : α) => f x ≤ y) :=
  fun (y : β) => is_lub_Sup (set_of fun (x : α) => f x ≤ y)

theorem is_order_right_adjoint_cSup {α : Type u_1} {β : Type u_2} [conditionally_complete_lattice α] [preorder β] (f : α → β) (hne : ∀ (y : β), ∃ (x : α), f x ≤ y) (hbdd : ∀ (y : β), ∃ (b : α), ∀ (x : α), f x ≤ y → x ≤ b) : is_order_right_adjoint f fun (y : β) => Sup (set_of fun (x : α) => f x ≤ y) :=
  fun (y : β) => is_lub_cSup (hne y) (hbdd y)

theorem is_order_right_adjoint.unique {α : Type u_1} {β : Type u_2} [partial_order α] [preorder β] {f : α → β} {g₁ : β → α} {g₂ : β → α} (h₁ : is_order_right_adjoint f g₁) (h₂ : is_order_right_adjoint f g₂) : g₁ = g₂ :=
  funext fun (y : β) => is_lub.unique (h₁ y) (h₂ y)

theorem is_order_right_adjoint.right_mono {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] {f : α → β} {g : β → α} (h : is_order_right_adjoint f g) : monotone g :=
  fun (y₁ y₂ : β) (hy : y₁ ≤ y₂) =>
    is_lub.mono (h y₁) (h y₂) fun (x : α) (hx : x ∈ set_of fun (x : α) => f x ≤ y₁) => le_trans hx hy

namespace function


/-- If an order automorphism `fa` is semiconjugate to an order embedding `fb` by a function `g`
and `g'` is an order right adjoint of `g` (i.e. `g' y = Sup {x | f x ≤ y}`), then `fb` is
semiconjugate to `fa` by `g'`.

This is a version of Proposition 2.1 from [Étienne Ghys, Groupes d'homeomorphismes du cercle et
cohomologie bornee][ghys87:groupes]. -/
theorem semiconj.symm_adjoint {α : Type u_1} {β : Type u_2} [partial_order α] [preorder β] {fa : α ≃o α} {fb : β ↪o β} {g : α → β} (h : semiconj g ⇑fa ⇑fb) {g' : β → α} (hg' : is_order_right_adjoint g g') : semiconj g' ⇑fb ⇑fa := sorry

theorem semiconj_of_is_lub {α : Type u_1} {G : Type u_3} [partial_order α] [group G] (f₁ : G →* α ≃o α) (f₂ : G →* α ≃o α) {h : α → α} (H : ∀ (x : α), is_lub (set.range fun (g' : G) => coe_fn (coe_fn f₁ g'⁻¹) (coe_fn (coe_fn f₂ g') x)) (h x)) (g : G) : semiconj h ⇑(coe_fn f₂ g) ⇑(coe_fn f₁ g) := sorry

/-- Consider two actions `f₁ f₂ : G → α → α` of a group on a complete lattice by order
isomorphisms. Then the map `x ↦ ⨆ g : G, (f₁ g)⁻¹ (f₂ g x)` semiconjugates each `f₁ g'` to `f₂ g'`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homeomorphismes du cercle et
cohomologie bornee][ghys87:groupes]. -/
theorem Sup_div_semiconj {α : Type u_1} {G : Type u_3} [complete_lattice α] [group G] (f₁ : G →* α ≃o α) (f₂ : G →* α ≃o α) (g : G) : semiconj (fun (x : α) => supr fun (g' : G) => coe_fn (coe_fn f₁ g'⁻¹) (coe_fn (coe_fn f₂ g') x)) ⇑(coe_fn f₂ g)
  ⇑(coe_fn f₁ g) :=
  semiconj_of_is_lub f₁ f₂ (fun (x : α) => is_lub_supr) g

/-- Consider two actions `f₁ f₂ : G → α → α` of a group on a conditionally complete lattice by order
isomorphisms. Suppose that each set $s(x)=\{f_1(g)^{-1} (f_2(g)(x)) | g \in G\}$ is bounded above.
Then the map `x ↦ Sup s(x)` semiconjugates each `f₁ g'` to `f₂ g'`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homeomorphismes du cercle et
cohomologie bornee][ghys87:groupes]. -/
theorem cSup_div_semiconj {α : Type u_1} {G : Type u_3} [conditionally_complete_lattice α] [group G] (f₁ : G →* α ≃o α) (f₂ : G →* α ≃o α) (hbdd : ∀ (x : α), bdd_above (set.range fun (g : G) => coe_fn (coe_fn f₁ g⁻¹) (coe_fn (coe_fn f₂ g) x))) (g : G) : semiconj (fun (x : α) => supr fun (g' : G) => coe_fn (coe_fn f₁ g'⁻¹) (coe_fn (coe_fn f₂ g') x)) ⇑(coe_fn f₂ g)
  ⇑(coe_fn f₁ g) := sorry

