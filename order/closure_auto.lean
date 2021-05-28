/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.basic
import Mathlib.order.preorder_hom
import Mathlib.order.galois_connection
import Mathlib.tactic.monotonicity.default
import PostPort

universes u l 

namespace Mathlib

/-!
# Closure operators on a partial order

We define (bundled) closure operators on a partial order as an monotone (increasing), extensive
(inflationary) and idempotent function.
We define closed elements for the operator as elements which are fixed by it.

Note that there is close connection to Galois connections and Galois insertions: every closure
operator induces a Galois insertion (from the set of closed elements to the underlying type), and
every Galois connection induces a closure operator (namely the composition). In particular,
a Galois insertion can be seen as a general case of a closure operator, where the inclusion is given
by coercion, see `closure_operator.gi`.

## References

* https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets

-/

/--
A closure operator on the partial order `α` is a monotone function which is extensive (every `x`
is less than its closure) and idempotent.
-/
structure closure_operator (α : Type u) [partial_order α] 
extends α →ₘ α
where
  le_closure' : ∀ (x : α), x ≤ preorder_hom.to_fun _to_preorder_hom x
  idempotent' : ∀ (x : α),
  preorder_hom.to_fun _to_preorder_hom (preorder_hom.to_fun _to_preorder_hom x) = preorder_hom.to_fun _to_preorder_hom x

protected instance closure_operator.has_coe_to_fun (α : Type u) [partial_order α] : has_coe_to_fun (closure_operator α) :=
  has_coe_to_fun.mk (fun (c : closure_operator α) => α → α)
    fun (c : closure_operator α) => preorder_hom.to_fun (closure_operator.to_preorder_hom c)

namespace closure_operator


/-- The identity function as a closure operator. -/
@[simp] theorem id_to_preorder_hom_to_fun (α : Type u) [partial_order α] (x : α) : coe_fn (to_preorder_hom (id α)) x = x :=
  Eq.refl (coe_fn (to_preorder_hom (id α)) x)

protected instance inhabited (α : Type u) [partial_order α] : Inhabited (closure_operator α) :=
  { default := id α }

theorem ext {α : Type u} [partial_order α] (c₁ : closure_operator α) (c₂ : closure_operator α) : ⇑c₁ = ⇑c₂ → c₁ = c₂ := sorry

/-- Constructor for a closure operator using the weaker idempotency axiom: `f (f x) ≤ f x`. -/
def mk' {α : Type u} [partial_order α] (f : α → α) (hf₁ : monotone f) (hf₂ : ∀ (x : α), x ≤ f x) (hf₃ : ∀ (x : α), f (f x) ≤ f x) : closure_operator α :=
  mk (preorder_hom.mk f hf₁) hf₂ sorry

/--
theorem monotone {α : Type u} [partial_order α] (c : closure_operator α) : monotone ⇑c :=
  preorder_hom.monotone' (to_preorder_hom c)

Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationary.
-/
theorem le_closure {α : Type u} [partial_order α] (c : closure_operator α) (x : α) : x ≤ coe_fn c x :=
  le_closure' c x

@[simp] theorem idempotent {α : Type u} [partial_order α] (c : closure_operator α) (x : α) : coe_fn c (coe_fn c x) = coe_fn c x :=
  idempotent' c x

theorem le_closure_iff {α : Type u} [partial_order α] (c : closure_operator α) (x : α) (y : α) : x ≤ coe_fn c y ↔ coe_fn c x ≤ coe_fn c y :=
  { mp := fun (h : x ≤ coe_fn c y) => idempotent c y ▸ monotone c h,
    mpr := fun (h : coe_fn c x ≤ coe_fn c y) => le_trans (le_closure c x) h }

theorem closure_top {α : Type u} [order_top α] (c : closure_operator α) : coe_fn c ⊤ = ⊤ :=
  le_antisymm le_top (le_closure c ⊤)

theorem closure_inter_le {α : Type u} [semilattice_inf α] (c : closure_operator α) (x : α) (y : α) : coe_fn c (x ⊓ y) ≤ coe_fn c x ⊓ coe_fn c y :=
  le_inf (monotone c inf_le_left) (monotone c inf_le_right)

theorem closure_union_closure_le {α : Type u} [semilattice_sup α] (c : closure_operator α) (x : α) (y : α) : coe_fn c x ⊔ coe_fn c y ≤ coe_fn c (x ⊔ y) :=
  sup_le (monotone c le_sup_left) (monotone c le_sup_right)

/-- An element `x` is closed for the closure operator `c` if it is a fixed point for it. -/
def closed {α : Type u} [partial_order α] (c : closure_operator α) : set α :=
  fun (x : α) => coe_fn c x = x

theorem mem_closed_iff {α : Type u} [partial_order α] (c : closure_operator α) (x : α) : x ∈ closed c ↔ coe_fn c x = x :=
  iff.rfl

theorem mem_closed_iff_closure_le {α : Type u} [partial_order α] (c : closure_operator α) (x : α) : x ∈ closed c ↔ coe_fn c x ≤ x :=
  { mp := le_of_eq, mpr := fun (h : coe_fn c x ≤ x) => le_antisymm h (le_closure c x) }

theorem closure_eq_self_of_mem_closed {α : Type u} [partial_order α] (c : closure_operator α) {x : α} (h : x ∈ closed c) : coe_fn c x = x :=
  h

@[simp] theorem closure_is_closed {α : Type u} [partial_order α] (c : closure_operator α) (x : α) : coe_fn c x ∈ closed c :=
  idempotent c x

/-- The set of closed elements for `c` is exactly its range. -/
theorem closed_eq_range_close {α : Type u} [partial_order α] (c : closure_operator α) : closed c = set.range ⇑c := sorry

/-- Send an `x` to an element of the set of closed elements (by taking the closure). -/
def to_closed {α : Type u} [partial_order α] (c : closure_operator α) (x : α) : ↥(closed c) :=
  { val := coe_fn c x, property := closure_is_closed c x }

theorem top_mem_closed {α : Type u} [order_top α] (c : closure_operator α) : ⊤ ∈ closed c :=
  closure_top c

theorem closure_le_closed_iff_le {α : Type u} [partial_order α] (c : closure_operator α) {x : α} {y : α} (hy : closed c y) : x ≤ y ↔ coe_fn c x ≤ y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ≤ y ↔ coe_fn c x ≤ y)) (Eq.symm (closure_eq_self_of_mem_closed c hy))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x ≤ coe_fn c y ↔ coe_fn c x ≤ coe_fn c y)) (propext (le_closure_iff c x y))))
      (iff.refl (coe_fn c x ≤ coe_fn c y)))

/-- The set of closed elements has a Galois insertion to the underlying type. -/
def gi {α : Type u} [partial_order α] (c : closure_operator α) : galois_insertion (to_closed c) coe :=
  galois_insertion.mk (fun (x : α) (hx : ↑(to_closed c x) ≤ x) => { val := x, property := sorry }) sorry sorry sorry

end closure_operator


/--
Every Galois connection induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad.
-/
@[simp] theorem galois_connection.closure_operator_to_preorder_hom_to_fun {α : Type u} [partial_order α] {β : Type u} [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) (x : α) : coe_fn (closure_operator.to_preorder_hom (galois_connection.closure_operator gc)) x = u (l x) :=
  Eq.refl (coe_fn (closure_operator.to_preorder_hom (galois_connection.closure_operator gc)) x)

/--
The Galois insertion associated to a closure operator can be used to reconstruct the closure
operator.

Note that the inverse in the opposite direction does not hold in general.
-/
@[simp] theorem closure_operator_gi_self {α : Type u} [partial_order α] (c : closure_operator α) : galois_connection.closure_operator (galois_insertion.gc (closure_operator.gi c)) = c := sorry

