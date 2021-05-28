/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.complete_lattice
import Mathlib.order.rel_iso
import Mathlib.PostPort

universes u v x w u_1 u_2 l 

namespace Mathlib

/-!
# Galois connections, insertions and coinsertions

Galois connections are order theoretic adjoints, i.e. a pair of functions `u` and `l`,
  such that `∀a b, l a ≤ b ↔ a ≤ u b`.

## Main definitions

* `galois_connection`: A Galois connection is a pair of functions `l` and `u` satisfying
  `l a ≤ b ↔ a ≤ u b`. They are special cases of  adjoint functors in category theory,
  but do not depend on the category theory library in mathlib.
* `galois_insertion`: A Galois insertion is a Galois connection where `l ∘ u = id`
* `galois_coinsertion`: A Galois coinsertion is a Galois connection where `u ∘ l = id`

## Implementation details

Galois insertions can be used to lift order structures from one type to another.
For example if `α` is a complete lattice, and `l : α → β`, and `u : β → α` form
a Galois insertion, then `β` is also a complete lattice. `l` is the lower adjoint and
`u` is the upper adjoint.

An example of this is the Galois insertion is in group thery. If `G` is a topological space,
then there is a Galois insertion between the set of subsets of `G`, `set G`, and the
set of subgroups of `G`, `subgroup G`. The left adjoint is `subgroup.closure`,
taking the `subgroup` generated by a `set`, The right adjoint is the coercion from `subgroup G` to
`set G`, taking the underlying set of an subgroup.

Naively lifting a lattice structure along this Galois insertion would mean that the definition
of `inf` on subgroups would be `subgroup.closure (↑S ∩ ↑T)`. This is an undesirable definition
because the intersection of subgroups is already a subgroup, so there is no need to take the
closure. For this reason a `choice` function is added as a field to the `galois_insertion`
structure. It has type `Π S : set G, ↑(closure S) ≤ S → subgroup G`. When `↑(closure S) ≤ S`, then
`S` is already a subgroup, so this function can be defined using `subgroup.mk` and not `closure`.
This means the infimum of subgroups will be defined to be the intersection of sets, paired
with a proof that intersection of subgroups is a subgroup, rather than the closure of the
intersection.

-/

/-- A Galois connection is a pair of functions `l` and `u` satisfying
  `l a ≤ b ↔ a ≤ u b`. They are special cases of  adjoint functors in category theory,
    but do not depend on the category theory library in mathlib. -/
def galois_connection {α : Type u} {β : Type v} [preorder α] [preorder β] (l : α → β) (u : β → α)  :=
  ∀ (a : α) (b : β), l a ≤ b ↔ a ≤ u b

/-- Makes a Galois connection from an order-preserving bijection. -/
theorem order_iso.to_galois_connection {α : Type u} {β : Type v} [preorder α] [preorder β] (oi : α ≃o β) : galois_connection ⇑oi ⇑(order_iso.symm oi) :=
  fun (b : α) (g : β) => iff.symm (rel_iso.rel_symm_apply oi)

namespace galois_connection


theorem monotone_intro {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (hu : monotone u) (hl : monotone l) (hul : ∀ (a : α), a ≤ u (l a)) (hlu : ∀ (a : β), l (u a) ≤ a) : galois_connection l u :=
  fun (a : α) (b : β) =>
    { mp := fun (h : l a ≤ b) => le_trans (hul a) (hu h), mpr := fun (h : a ≤ u b) => le_trans (hl h) (hlu b) }

theorem l_le {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) {a : α} {b : β} : a ≤ u b → l a ≤ b :=
  iff.mpr (gc a b)

theorem le_u {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) {a : α} {b : β} : l a ≤ b → a ≤ u b :=
  iff.mp (gc a b)

theorem le_u_l {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) (a : α) : a ≤ u (l a) :=
  le_u gc (le_refl (l a))

theorem l_u_le {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) (a : β) : l (u a) ≤ a :=
  l_le gc (le_refl (u a))

theorem monotone_u {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) : monotone u :=
  fun (a b : β) (H : a ≤ b) => le_u gc (le_trans (l_u_le gc a) H)

theorem monotone_l {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) : monotone l :=
  fun (a b : α) (H : a ≤ b) => l_le gc (le_trans H (le_u_l gc b))

theorem upper_bounds_l_image_subset {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) {s : set α} : upper_bounds (l '' s) ⊆ u ⁻¹' upper_bounds s :=
  fun (b : β) (hb : b ∈ upper_bounds (l '' s)) (c : α) (this : c ∈ s) => le_u gc (hb (set.mem_image_of_mem l this))

theorem lower_bounds_u_image_subset {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) {s : set β} : lower_bounds (u '' s) ⊆ l ⁻¹' lower_bounds s :=
  fun (a : α) (ha : a ∈ lower_bounds (u '' s)) (c : β) (this : c ∈ s) => l_le gc (ha (set.mem_image_of_mem u this))

theorem is_lub_l_image {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) {s : set α} {a : α} (h : is_lub s a) : is_lub (l '' s) (l a) := sorry

theorem is_glb_u_image {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) {s : set β} {b : β} (h : is_glb s b) : is_glb (u '' s) (u b) := sorry

theorem is_glb_l {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) {a : α} : is_glb (set_of fun (b : β) => a ≤ u b) (l a) :=
  { left := fun (b : β) => l_le gc,
    right := fun (b : β) (h : b ∈ lower_bounds (set_of fun (b : β) => a ≤ u b)) => h (le_u_l gc a) }

theorem is_lub_u {α : Type u} {β : Type v} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) {b : β} : is_lub (set_of fun (a : α) => l a ≤ b) (u b) :=
  { left := fun (b_1 : α) => le_u gc,
    right := fun (b_1 : α) (h : b_1 ∈ upper_bounds (set_of fun (a : α) => l a ≤ b)) => h (l_u_le gc b) }

theorem u_l_u_eq_u {α : Type u} {β : Type v} [partial_order α] [partial_order β] {l : α → β} {u : β → α} (gc : galois_connection l u) : u ∘ l ∘ u = u :=
  funext fun (x : β) => le_antisymm (monotone_u gc (l_u_le gc x)) (le_u_l gc (u x))

theorem l_u_l_eq_l {α : Type u} {β : Type v} [partial_order α] [partial_order β] {l : α → β} {u : β → α} (gc : galois_connection l u) : l ∘ u ∘ l = l :=
  funext fun (x : α) => le_antisymm (l_u_le gc (l x)) (monotone_l gc (le_u_l gc x))

theorem l_unique {α : Type u} {β : Type v} [partial_order α] [partial_order β] {l : α → β} {u : β → α} (gc : galois_connection l u) {l' : α → β} {u' : β → α} (gc' : galois_connection l' u') (hu : ∀ (b : β), u b = u' b) {a : α} : l a = l' a :=
  le_antisymm (l_le gc (Eq.symm (hu (l' a)) ▸ le_u_l gc' a)) (l_le gc' (hu (l a) ▸ le_u_l gc a))

theorem u_unique {α : Type u} {β : Type v} [partial_order α] [partial_order β] {l : α → β} {u : β → α} (gc : galois_connection l u) {l' : α → β} {u' : β → α} (gc' : galois_connection l' u') (hl : ∀ (a : α), l a = l' a) {b : β} : u b = u' b :=
  le_antisymm (le_u gc' (hl (u b) ▸ l_u_le gc b)) (le_u gc (Eq.symm (hl (u' b)) ▸ l_u_le gc' b))

theorem u_top {α : Type u} {β : Type v} [order_top α] [order_top β] {l : α → β} {u : β → α} (gc : galois_connection l u) : u ⊤ = ⊤ := sorry

theorem l_bot {α : Type u} {β : Type v} [order_bot α] [order_bot β] {l : α → β} {u : β → α} (gc : galois_connection l u) : l ⊥ = ⊥ := sorry

theorem l_sup {α : Type u} {β : Type v} {a₁ : α} {a₂ : α} [semilattice_sup α] [semilattice_sup β] {l : α → β} {u : β → α} (gc : galois_connection l u) : l (a₁ ⊔ a₂) = l a₁ ⊔ l a₂ := sorry

theorem u_inf {α : Type u} {β : Type v} {b₁ : β} {b₂ : β} [semilattice_inf α] [semilattice_inf β] {l : α → β} {u : β → α} (gc : galois_connection l u) : u (b₁ ⊓ b₂) = u b₁ ⊓ u b₂ := sorry

theorem l_supr {α : Type u} {β : Type v} {ι : Sort x} [complete_lattice α] [complete_lattice β] {l : α → β} {u : β → α} (gc : galois_connection l u) {f : ι → α} : l (supr f) = supr fun (i : ι) => l (f i) := sorry

theorem u_infi {α : Type u} {β : Type v} {ι : Sort x} [complete_lattice α] [complete_lattice β] {l : α → β} {u : β → α} (gc : galois_connection l u) {f : ι → β} : u (infi f) = infi fun (i : ι) => u (f i) := sorry

theorem l_Sup {α : Type u} {β : Type v} [complete_lattice α] [complete_lattice β] {l : α → β} {u : β → α} (gc : galois_connection l u) {s : set α} : l (Sup s) = supr fun (a : α) => supr fun (H : a ∈ s) => l a := sorry

theorem u_Inf {α : Type u} {β : Type v} [complete_lattice α] [complete_lattice β] {l : α → β} {u : β → α} (gc : galois_connection l u) {s : set β} : u (Inf s) = infi fun (a : β) => infi fun (H : a ∈ s) => u a := sorry

/- Constructing Galois connections -/

protected theorem id {α : Type u} [pα : preorder α] : galois_connection id id :=
  fun (a b : α) => { mp := fun (x : id a ≤ b) => x, mpr := fun (x : a ≤ id b) => x }

protected theorem compose {α : Type u} {β : Type v} {γ : Type w} [preorder α] [preorder β] [preorder γ] (l1 : α → β) (u1 : β → α) (l2 : β → γ) (u2 : γ → β) (gc1 : galois_connection l1 u1) (gc2 : galois_connection l2 u2) : galois_connection (l2 ∘ l1) (u1 ∘ u2) := sorry

protected theorem dual {α : Type u} {β : Type v} [pα : preorder α] [pβ : preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) : galois_connection u l :=
  fun (a : order_dual β) (b : order_dual α) => iff.symm (gc b a)

protected theorem dfun {ι : Type u} {α : ι → Type v} {β : ι → Type w} [(i : ι) → preorder (α i)] [(i : ι) → preorder (β i)] (l : (i : ι) → α i → β i) (u : (i : ι) → β i → α i) (gc : ∀ (i : ι), galois_connection (l i) (u i)) : galois_connection (fun (a : (i : ι) → α i) (i : ι) => l i (a i)) fun (b : (i : ι) → β i) (i : ι) => u i (b i) :=
  fun (a : (i : ι) → α i) (b : (i : ι) → β i) => forall_congr fun (i : ι) => gc i (a i) (b i)

end galois_connection


namespace nat


theorem galois_connection_mul_div {k : ℕ} (h : 0 < k) : galois_connection (fun (n : ℕ) => n * k) fun (n : ℕ) => n / k :=
  fun (x y : ℕ) => iff.symm (le_div_iff_mul_le x y h)

end nat


/-- A Galois insertion is a Galois connection where `l ∘ u = id`. It also contains a constructive
choice function, to give better definitional equalities when lifting order structures. Dual
to `galois_coinsertion` -/
structure galois_insertion {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (l : α → β) (u : β → α) 
where
  choice : (x : α) → u (l x) ≤ x → β
  gc : galois_connection l u
  le_l_u : ∀ (x : β), x ≤ l (u x)
  choice_eq : ∀ (a : α) (h : u (l a) ≤ a), choice a h = l a

/-- A constructor for a Galois insertion with the trivial `choice` function. -/
def galois_insertion.monotone_intro {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] {l : α → β} {u : β → α} (hu : monotone u) (hl : monotone l) (hul : ∀ (a : α), a ≤ u (l a)) (hlu : ∀ (b : β), l (u b) = b) : galois_insertion l u :=
  galois_insertion.mk (fun (x : α) (_x : u (l x) ≤ x) => l x) sorry sorry sorry

/-- Makes a Galois insertion from an order-preserving bijection. -/
protected def rel_iso.to_galois_insertion {α : Type u} {β : Type v} [preorder α] [preorder β] (oi : α ≃o β) : galois_insertion ⇑oi ⇑(order_iso.symm oi) :=
  galois_insertion.mk (fun (b : α) (h : coe_fn (order_iso.symm oi) (coe_fn oi b) ≤ b) => coe_fn oi b)
    (order_iso.to_galois_connection oi) sorry sorry

/-- Make a `galois_insertion l u` from a `galois_connection l u` such that `∀ b, b ≤ l (u b)` -/
def galois_connection.to_galois_insertion {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) (h : ∀ (b : β), b ≤ l (u b)) : galois_insertion l u :=
  galois_insertion.mk (fun (x : α) (_x : u (l x) ≤ x) => l x) gc h sorry

/-- Lift the bottom along a Galois connection -/
def galois_connection.lift_order_bot {α : Type u_1} {β : Type u_2} [order_bot α] [partial_order β] {l : α → β} {u : β → α} (gc : galois_connection l u) : order_bot β :=
  order_bot.mk (l ⊥) partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans
    partial_order.le_antisymm sorry

namespace galois_insertion


theorem l_u_eq {α : Type u} {β : Type v} {l : α → β} {u : β → α} [preorder α] [partial_order β] (gi : galois_insertion l u) (b : β) : l (u b) = b :=
  le_antisymm (galois_connection.l_u_le (gc gi) b) (le_l_u gi b)

theorem l_surjective {α : Type u} {β : Type v} {l : α → β} {u : β → α} [preorder α] [partial_order β] (gi : galois_insertion l u) : function.surjective l :=
  fun (b : β) => Exists.intro (u b) (l_u_eq gi b)

theorem u_injective {α : Type u} {β : Type v} {l : α → β} {u : β → α} [preorder α] [partial_order β] (gi : galois_insertion l u) : function.injective u :=
  fun (a b : β) (h : u a = u b) => Eq.trans (Eq.trans (Eq.symm (l_u_eq gi a)) (congr_arg l h)) (l_u_eq gi b)

theorem l_sup_u {α : Type u} {β : Type v} {l : α → β} {u : β → α} [semilattice_sup α] [semilattice_sup β] (gi : galois_insertion l u) (a : β) (b : β) : l (u a ⊔ u b) = a ⊔ b := sorry

theorem l_supr_u {α : Type u} {β : Type v} {l : α → β} {u : β → α} [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u) {ι : Sort x} (f : ι → β) : l (supr fun (i : ι) => u (f i)) = supr fun (i : ι) => f i :=
  Eq.trans (galois_connection.l_supr (gc gi)) (congr_arg supr (funext fun (i : ι) => l_u_eq gi (f i)))

theorem l_supr_of_ul_eq_self {α : Type u} {β : Type v} {l : α → β} {u : β → α} [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u) {ι : Sort x} (f : ι → α) (hf : ∀ (i : ι), u (l (f i)) = f i) : l (supr fun (i : ι) => f i) = supr fun (i : ι) => l (f i) := sorry

theorem l_inf_u {α : Type u} {β : Type v} {l : α → β} {u : β → α} [semilattice_inf α] [semilattice_inf β] (gi : galois_insertion l u) (a : β) (b : β) : l (u a ⊓ u b) = a ⊓ b := sorry

theorem l_infi_u {α : Type u} {β : Type v} {l : α → β} {u : β → α} [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u) {ι : Sort x} (f : ι → β) : l (infi fun (i : ι) => u (f i)) = infi fun (i : ι) => f i :=
  Eq.trans (congr_arg l (Eq.symm (galois_connection.u_infi (gc gi)))) (l_u_eq gi (infi fun (i : ι) => f i))

theorem l_infi_of_ul_eq_self {α : Type u} {β : Type v} {l : α → β} {u : β → α} [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u) {ι : Sort x} (f : ι → α) (hf : ∀ (i : ι), u (l (f i)) = f i) : l (infi fun (i : ι) => f i) = infi fun (i : ι) => l (f i) := sorry

theorem u_le_u_iff {α : Type u} {β : Type v} {l : α → β} {u : β → α} [preorder α] [preorder β] (gi : galois_insertion l u) {a : β} {b : β} : u a ≤ u b ↔ a ≤ b :=
  { mp := fun (h : u a ≤ u b) => le_trans (le_l_u gi a) (galois_connection.l_le (gc gi) h),
    mpr := fun (h : a ≤ b) => galois_connection.monotone_u (gc gi) h }

theorem strict_mono_u {α : Type u} {β : Type v} {l : α → β} {u : β → α} [preorder α] [partial_order β] (gi : galois_insertion l u) : strict_mono u :=
  strict_mono_of_le_iff_le fun (_x _x_1 : β) => iff.symm (u_le_u_iff gi)

/-- Lift the suprema along a Galois insertion -/
def lift_semilattice_sup {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order β] [semilattice_sup α] (gi : galois_insertion l u) : semilattice_sup β :=
  semilattice_sup.mk (fun (a b : β) => l (u a ⊔ u b)) partial_order.le partial_order.lt partial_order.le_refl
    partial_order.le_trans partial_order.le_antisymm sorry sorry sorry

/-- Lift the infima along a Galois insertion -/
def lift_semilattice_inf {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order β] [semilattice_inf α] (gi : galois_insertion l u) : semilattice_inf β :=
  semilattice_inf.mk (fun (a b : β) => choice gi (u a ⊓ u b) sorry) partial_order.le partial_order.lt
    partial_order.le_refl partial_order.le_trans partial_order.le_antisymm sorry sorry sorry

/-- Lift the suprema and infima along a Galois insertion -/
def lift_lattice {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order β] [lattice α] (gi : galois_insertion l u) : lattice β :=
  lattice.mk semilattice_sup.sup semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

/-- Lift the top along a Galois insertion -/
def lift_order_top {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order β] [order_top α] (gi : galois_insertion l u) : order_top β :=
  order_top.mk (choice gi ⊤ sorry) partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans
    partial_order.le_antisymm sorry

/-- Lift the top, bottom, suprema, and infima along a Galois insertion -/
def lift_bounded_lattice {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order β] [bounded_lattice α] (gi : galois_insertion l u) : bounded_lattice β :=
  bounded_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    order_top.top sorry order_bot.bot sorry

/-- Lift all suprema and infima along a Galois insertion -/
def lift_complete_lattice {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order β] [complete_lattice α] (gi : galois_insertion l u) : complete_lattice β :=
  complete_lattice.mk bounded_lattice.sup bounded_lattice.le bounded_lattice.lt sorry sorry sorry sorry sorry sorry
    bounded_lattice.inf sorry sorry sorry bounded_lattice.top sorry bounded_lattice.bot sorry
    (fun (s : set β) => l (supr fun (b : β) => supr fun (H : b ∈ s) => u b))
    (fun (s : set β) => choice gi (infi fun (b : β) => infi fun (H : b ∈ s) => u b) sorry) sorry sorry sorry sorry

end galois_insertion


/-- A Galois coinsertion is a Galois connection where `u ∘ l = id`. It also contains a constructive
choice function, to give better definitional equalities when lifting order structures. Dual to
`galois_insertion` -/
structure galois_coinsertion {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] (l : α → β) (u : β → α) 
where
  choice : (x : β) → x ≤ l (u x) → α
  gc : galois_connection l u
  u_l_le : ∀ (x : α), u (l x) ≤ x
  choice_eq : ∀ (a : β) (h : a ≤ l (u a)), choice a h = u a

/-- Make a `galois_insertion u l` in the `order_dual`, from a `galois_coinsertion l u` -/
def galois_coinsertion.dual {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] {l : α → β} {u : β → α} : galois_coinsertion l u → galois_insertion u l :=
  fun (x : galois_coinsertion l u) =>
    galois_insertion.mk (galois_coinsertion.choice x) sorry (galois_coinsertion.u_l_le x) (galois_coinsertion.choice_eq x)

/-- Make a `galois_coinsertion u l` in the `order_dual`, from a `galois_insertion l u` -/
def galois_insertion.dual {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] {l : α → β} {u : β → α} : galois_insertion l u → galois_coinsertion u l :=
  fun (x : galois_insertion l u) =>
    galois_coinsertion.mk (galois_insertion.choice x) sorry (galois_insertion.le_l_u x) (galois_insertion.choice_eq x)

/-- Make a `galois_coinsertion l u` from a `galois_insertion l u` in the `order_dual` -/
def galois_coinsertion.of_dual {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] {l : α → β} {u : β → α} : galois_insertion u l → galois_coinsertion l u :=
  fun (x : galois_insertion u l) => galois_coinsertion.mk (galois_insertion.choice x) sorry sorry sorry

/-- Make a `galois_insertion l u` from a `galois_coinsertion l u` in the `order_dual` -/
def galois_insertion.of_dual {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] {l : α → β} {u : β → α} : galois_coinsertion u l → galois_insertion l u :=
  fun (x : galois_coinsertion u l) => galois_insertion.mk (galois_coinsertion.choice x) sorry sorry sorry

/-- Makes a Galois coinsertion from an order-preserving bijection. -/
protected def rel_iso.to_galois_coinsertion {α : Type u} {β : Type v} [preorder α] [preorder β] (oi : α ≃o β) : galois_coinsertion ⇑oi ⇑(order_iso.symm oi) :=
  galois_coinsertion.mk (fun (b : β) (h : b ≤ coe_fn oi (coe_fn (order_iso.symm oi) b)) => coe_fn (order_iso.symm oi) b)
    (order_iso.to_galois_connection oi) sorry sorry

/-- A constructor for a Galois coinsertion with the trivial `choice` function. -/
def galois_coinsertion.monotone_intro {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] {l : α → β} {u : β → α} (hu : monotone u) (hl : monotone l) (hlu : ∀ (b : β), l (u b) ≤ b) (hul : ∀ (a : α), u (l a) = a) : galois_coinsertion l u :=
  galois_coinsertion.of_dual (galois_insertion.monotone_intro (monotone.order_dual hl) (monotone.order_dual hu) hlu hul)

/-- Make a `galois_coinsertion l u` from a `galois_connection l u` such that `∀ b, b ≤ l (u b)` -/
def galois_connection.to_galois_coinsertion {α : Type u_1} {β : Type u_2} [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u) (h : ∀ (a : α), u (l a) ≤ a) : galois_coinsertion l u :=
  galois_coinsertion.mk (fun (x : β) (_x : x ≤ l (u x)) => u x) gc h sorry

/-- Lift the top along a Galois connection -/
def galois_connection.lift_order_top {α : Type u_1} {β : Type u_2} [partial_order α] [order_top β] {l : α → β} {u : β → α} (gc : galois_connection l u) : order_top α :=
  order_top.mk (u ⊤) partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans
    partial_order.le_antisymm sorry

namespace galois_coinsertion


theorem u_l_eq {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order α] [preorder β] (gi : galois_coinsertion l u) (a : α) : u (l a) = a :=
  galois_insertion.l_u_eq (dual gi) a

theorem u_surjective {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order α] [preorder β] (gi : galois_coinsertion l u) : function.surjective u :=
  galois_insertion.l_surjective (dual gi)

theorem l_injective {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order α] [preorder β] (gi : galois_coinsertion l u) : function.injective l :=
  galois_insertion.u_injective (dual gi)

theorem u_inf_l {α : Type u} {β : Type v} {l : α → β} {u : β → α} [semilattice_inf α] [semilattice_inf β] (gi : galois_coinsertion l u) (a : α) (b : α) : u (l a ⊓ l b) = a ⊓ b :=
  galois_insertion.l_sup_u (dual gi) a b

theorem u_infi_l {α : Type u} {β : Type v} {l : α → β} {u : β → α} [complete_lattice α] [complete_lattice β] (gi : galois_coinsertion l u) {ι : Sort x} (f : ι → α) : u (infi fun (i : ι) => l (f i)) = infi fun (i : ι) => f i :=
  galois_insertion.l_supr_u (dual gi) fun (i : ι) => f i

theorem u_infi_of_lu_eq_self {α : Type u} {β : Type v} {l : α → β} {u : β → α} [complete_lattice α] [complete_lattice β] (gi : galois_coinsertion l u) {ι : Sort x} (f : ι → β) (hf : ∀ (i : ι), l (u (f i)) = f i) : u (infi fun (i : ι) => f i) = infi fun (i : ι) => u (f i) :=
  galois_insertion.l_supr_of_ul_eq_self (dual gi) (fun (i : ι) => f i) hf

theorem u_sup_l {α : Type u} {β : Type v} {l : α → β} {u : β → α} [semilattice_sup α] [semilattice_sup β] (gi : galois_coinsertion l u) (a : α) (b : α) : u (l a ⊔ l b) = a ⊔ b :=
  galois_insertion.l_inf_u (dual gi) a b

theorem u_supr_l {α : Type u} {β : Type v} {l : α → β} {u : β → α} [complete_lattice α] [complete_lattice β] (gi : galois_coinsertion l u) {ι : Sort x} (f : ι → α) : u (supr fun (i : ι) => l (f i)) = supr fun (i : ι) => f i :=
  galois_insertion.l_infi_u (dual gi) fun (i : ι) => f i

theorem u_supr_of_lu_eq_self {α : Type u} {β : Type v} {l : α → β} {u : β → α} [complete_lattice α] [complete_lattice β] (gi : galois_coinsertion l u) {ι : Sort x} (f : ι → β) (hf : ∀ (i : ι), l (u (f i)) = f i) : u (supr fun (i : ι) => f i) = supr fun (i : ι) => u (f i) :=
  galois_insertion.l_infi_of_ul_eq_self (dual gi) (fun (i : ι) => f i) hf

theorem l_le_l_iff {α : Type u} {β : Type v} {l : α → β} {u : β → α} [preorder α] [preorder β] (gi : galois_coinsertion l u) {a : α} {b : α} : l a ≤ l b ↔ a ≤ b :=
  galois_insertion.u_le_u_iff (dual gi)

theorem strict_mono_l {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order α] [preorder β] (gi : galois_coinsertion l u) : strict_mono l :=
  fun (a b : α) (h : a < b) => galois_insertion.strict_mono_u (dual gi) h

/-- Lift the infima along a Galois coinsertion -/
def lift_semilattice_inf {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order α] [semilattice_inf β] (gi : galois_coinsertion l u) : semilattice_inf α :=
  semilattice_inf.mk (fun (a b : α) => u (l a ⊓ l b)) partial_order.le partial_order.lt partial_order.le_refl
    partial_order.le_trans partial_order.le_antisymm sorry sorry sorry

/-- Lift the suprema along a Galois coinsertion -/
def lift_semilattice_sup {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order α] [semilattice_sup β] (gi : galois_coinsertion l u) : semilattice_sup α :=
  semilattice_sup.mk (fun (a b : α) => choice gi (l a ⊔ l b) sorry) partial_order.le partial_order.lt
    partial_order.le_refl partial_order.le_trans partial_order.le_antisymm sorry sorry sorry

/-- Lift the suprema and infima along a Galois coinsertion -/
def lift_lattice {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order α] [lattice β] (gi : galois_coinsertion l u) : lattice α :=
  lattice.mk semilattice_sup.sup semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

/-- Lift the bot along a Galois coinsertion -/
def lift_order_bot {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order α] [order_bot β] (gi : galois_coinsertion l u) : order_bot α :=
  order_bot.mk (choice gi ⊥ sorry) partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans
    partial_order.le_antisymm sorry

/-- Lift the top, bottom, suprema, and infima along a Galois coinsertion -/
def lift_bounded_lattice {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order α] [bounded_lattice β] (gi : galois_coinsertion l u) : bounded_lattice α :=
  bounded_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    order_top.top sorry order_bot.bot sorry

/-- Lift all suprema and infima along a Galois coinsertion -/
def lift_complete_lattice {α : Type u} {β : Type v} {l : α → β} {u : β → α} [partial_order α] [complete_lattice β] (gi : galois_coinsertion l u) : complete_lattice α :=
  complete_lattice.mk bounded_lattice.sup bounded_lattice.le bounded_lattice.lt sorry sorry sorry sorry sorry sorry
    bounded_lattice.inf sorry sorry sorry bounded_lattice.top sorry bounded_lattice.bot sorry
    (fun (s : set α) => choice gi (supr fun (a : α) => supr fun (H : a ∈ s) => l a) sorry)
    (fun (s : set α) => u (infi fun (a : α) => infi fun (H : a ∈ s) => l a)) sorry sorry sorry sorry

end galois_coinsertion


/-- If `α` is a partial order with bottom element (e.g., `ℕ`, `ℝ≥0`), then
`λ o : with_bot α, o.get_or_else ⊥` and coercion form a Galois insertion. -/
def with_bot.gi_get_or_else_bot {α : Type u} [order_bot α] : galois_insertion (fun (o : with_bot α) => option.get_or_else o ⊥) coe :=
  galois_insertion.mk (fun (o : with_bot α) (ho : ↑(option.get_or_else o ⊥) ≤ o) => option.get_or_else o ⊥) sorry sorry
    sorry

