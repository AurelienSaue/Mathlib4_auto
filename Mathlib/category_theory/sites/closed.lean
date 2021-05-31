/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.sites.sheaf_of_types
import Mathlib.order.closure
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Closed sieves

A natural closure operator on sieves is a closure operator on `sieve X` for each `X` which commutes
with pullback.
We show that a Grothendieck topology `J` induces a natural closure operator, and define what the
closed sieves are. The collection of `J`-closed sieves forms a presheaf which is a sheaf for `J`,
and further this presheaf can be used to determine the Grothendieck topology from the sheaf
predicate.
Finally we show that a natural closure operator on sieves induces a Grothendieck topology, and hence
that natural closure operators are in bijection with Grothendieck topologies.

## Main definitions

* `category_theory.grothendieck_topology.close`: Sends a sieve `S` on `X` to the set of arrows
  which it covers. This has all the usual properties of a closure operator, as well as commuting
  with pullback.
* `category_theory.grothendieck_topology.closure_operator`: The bundled `closure_operator` given
  by `category_theory.grothendieck_topology.close`.
* `category_theory.grothendieck_topology.closed`: A sieve `S` on `X` is closed for the topology `J`
   if it contains every arrow it covers.
* `category_theory.functor.closed_sieves`: The presheaf sending `X` to the collection of `J`-closed
  sieves on `X`. This is additionally shown to be a sheaf for `J`, and if this is a sheaf for a
  different topology `J'`, then `J' ≤ J`.
* `category_theory.grothendieck_topology.topology_of_closure_operator`: A closure operator on the
  set of sieves on every object which commutes with pullback additionally induces a Grothendieck
  topology, giving a bijection with `category_theory.grothendieck_topology.closure_operator`.


## Tags

closed sieve, closure, Grothendieck topology

## References

* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/

namespace category_theory


namespace grothendieck_topology


/-- The `J`-closure of a sieve is the collection of arrows which it covers. -/
def close {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} (S : sieve X) : sieve X :=
  sieve.mk (fun (Y : C) (f : Y ⟶ X) => covers J₁ S f) sorry

/-- Any sieve is smaller than its closure. -/
theorem le_close {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} (S : sieve X) : S ≤ close J₁ S :=
  fun (Y : C) (g : Y ⟶ X) (hg : coe_fn S Y g) => covering_of_eq_top J₁ (sieve.pullback_eq_top_of_mem S hg)

/--
A sieve is closed for the Grothendieck topology if it contains every arrow it covers.
In the case of the usual topology on a topological space, this means that the open cover contains
every open set which it covers.

Note this has no relation to a closed subset of a topological space.
-/
def is_closed {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} (S : sieve X) :=
  ∀ {Y : C} (f : Y ⟶ X), covers J₁ S f → coe_fn S Y f

/-- If `S` is `J₁`-closed, then `S` covers exactly the arrows it contains. -/
theorem covers_iff_mem_of_closed {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} {S : sieve X} (h : is_closed J₁ S) {Y : C} (f : Y ⟶ X) : covers J₁ S f ↔ coe_fn S Y f :=
  { mp := h f, mpr := arrow_max J₁ f S }

/-- Being `J`-closed is stable under pullback. -/
theorem is_closed_pullback {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} {Y : C} (f : Y ⟶ X) (S : sieve X) : is_closed J₁ S → is_closed J₁ (sieve.pullback f S) := sorry

/--
The closure of a sieve `S` is the largest closed sieve which contains `S` (justifying the name
"closure").
-/
theorem le_close_of_is_closed {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} {S : sieve X} {T : sieve X} (h : S ≤ T) (hT : is_closed J₁ T) : close J₁ S ≤ T :=
  fun (Y : C) (f : Y ⟶ X) (hf : coe_fn (close J₁ S) Y f) => hT f (superset_covering J₁ (sieve.pullback_monotone f h) hf)

/-- The closure of a sieve is closed. -/
theorem close_is_closed {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} (S : sieve X) : is_closed J₁ (close J₁ S) :=
  fun (Y : C) (g : Y ⟶ X) (hg : covers J₁ (close J₁ S) g) =>
    arrow_trans J₁ g (close J₁ S) S hg fun (Z : C) (h : Z ⟶ X) (hS : coe_fn (close J₁ S) Z h) => hS

/-- The sieve `S` is closed iff its closure is equal to itself. -/
theorem is_closed_iff_close_eq_self {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} (S : sieve X) : is_closed J₁ S ↔ close J₁ S = S := sorry

theorem close_eq_self_of_is_closed {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} {S : sieve X} (hS : is_closed J₁ S) : close J₁ S = S :=
  iff.mp (is_closed_iff_close_eq_self J₁ S) hS

/-- Closing under `J` is stable under pullback. -/
theorem pullback_close {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} {Y : C} (f : Y ⟶ X) (S : sieve X) : close J₁ (sieve.pullback f S) = sieve.pullback f (close J₁ S) := sorry

theorem monotone_close {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} : monotone (close J₁) :=
  fun (S₁ S₂ : sieve X) (h : S₁ ≤ S₂) =>
    le_close_of_is_closed J₁ (has_le.le.trans h (le_close J₁ S₂)) (close_is_closed J₁ S₂)

@[simp] theorem close_close {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} (S : sieve X) : close J₁ (close J₁ S) = close J₁ S :=
  le_antisymm (le_close_of_is_closed J₁ (le_refl (close J₁ S)) (close_is_closed J₁ S)) (monotone_close J₁ (le_close J₁ S))

/--
The sieve `S` is in the topology iff its closure is the maximal sieve. This shows that the closure
operator determines the topology.
-/
theorem close_eq_top_iff_mem {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} (S : sieve X) : close J₁ S = ⊤ ↔ S ∈ coe_fn J₁ X := sorry

/-- A Grothendieck topology induces a natural family of closure operators on sieves. -/
@[simp] theorem closure_operator_to_preorder_hom_to_fun_apply {C : Type u} [small_category C] (J₁ : grothendieck_topology C) (X : C) (S : sieve X) (Y : C) (f : Y ⟶ X) : coe_fn (coe_fn (closure_operator.to_preorder_hom (closure_operator J₁ X)) S) Y f = covers J₁ S f :=
  Eq.refl (coe_fn (coe_fn (closure_operator.to_preorder_hom (closure_operator J₁ X)) S) Y f)

@[simp] theorem closed_iff_closed {C : Type u} [small_category C] (J₁ : grothendieck_topology C) {X : C} (S : sieve X) : S ∈ closure_operator.closed (closure_operator J₁ X) ↔ is_closed J₁ S :=
  iff.symm (is_closed_iff_close_eq_self J₁ S)

end grothendieck_topology


/--
The presheaf sending each object to the set of `J`-closed sieves on it. This presheaf is a `J`-sheaf
(and will turn out to be a subobject classifier for the category of `J`-sheaves).
-/
@[simp] theorem functor.closed_sieves_map_coe {C : Type u} [small_category C] (J₁ : grothendieck_topology C) (X : Cᵒᵖ) (Y : Cᵒᵖ) (f : X ⟶ Y) (S : Subtype fun (S : sieve (opposite.unop X)) => grothendieck_topology.is_closed J₁ S) : ↑(functor.map (functor.closed_sieves J₁) f S) = sieve.pullback (has_hom.hom.unop f) (subtype.val S) :=
  Eq.refl ↑(functor.map (functor.closed_sieves J₁) f S)

/--
The presheaf of `J`-closed sieves is a `J`-sheaf.
The proof of this is adapted from [MM92], Chatper III, Section 7, Lemma 1.
-/
theorem classifier_is_sheaf {C : Type u} [small_category C] (J₁ : grothendieck_topology C) : presieve.is_sheaf J₁ (functor.closed_sieves J₁) := sorry

/--
If presheaf of `J₁`-closed sieves is a `J₂`-sheaf then `J₁ ≤ J₂`. Note the converse is true by
`classifier_is_sheaf` and `is_sheaf_of_le`.
-/
theorem le_topology_of_closed_sieves_is_sheaf {C : Type u} [small_category C] {J₁ : grothendieck_topology C} {J₂ : grothendieck_topology C} (h : presieve.is_sheaf J₁ (functor.closed_sieves J₂)) : J₁ ≤ J₂ := sorry

/-- If being a sheaf for `J₁` is equivalent to being a sheaf for `J₂`, then `J₁ = J₂`. -/
theorem topology_eq_iff_same_sheaves {C : Type u} [small_category C] {J₁ : grothendieck_topology C} {J₂ : grothendieck_topology C} : J₁ = J₂ ↔ ∀ (P : Cᵒᵖ ⥤ Type u), presieve.is_sheaf J₁ P ↔ presieve.is_sheaf J₂ P := sorry

/--
A closure (increasing, inflationary and idempotent) operation on sieves that commutes with pullback
induces a Grothendieck topology.
In fact, such operations are in bijection with Grothendieck topologies.
-/
@[simp] theorem topology_of_closure_operator_sieves {C : Type u} [small_category C] (c : (X : C) → closure_operator (sieve X)) (hc : ∀ {X Y : C} (f : Y ⟶ X) (S : sieve X), coe_fn (c Y) (sieve.pullback f S) = sieve.pullback f (coe_fn (c X) S)) (X : C) : coe_fn (topology_of_closure_operator c hc) X = set_of fun (S : sieve X) => coe_fn (c X) S = ⊤ :=
  Eq.refl (coe_fn (topology_of_closure_operator c hc) X)

/--
The topology given by the closure operator `J.close` on a Grothendieck topology is the same as `J`.
-/
theorem topology_of_closure_operator_self {C : Type u} [small_category C] (J₁ : grothendieck_topology C) : (topology_of_closure_operator (grothendieck_topology.closure_operator J₁)
    fun (X Y : C) => grothendieck_topology.pullback_close J₁) =
  J₁ :=
  grothendieck_topology.ext
    (funext fun (X : C) => set.ext fun (S : sieve X) => grothendieck_topology.close_eq_top_iff_mem J₁ S)

theorem topology_of_closure_operator_close {C : Type u} [small_category C] (c : (X : C) → closure_operator (sieve X)) (pb : ∀ {X Y : C} (f : Y ⟶ X) (S : sieve X), coe_fn (c Y) (sieve.pullback f S) = sieve.pullback f (coe_fn (c X) S)) (X : C) (S : sieve X) : grothendieck_topology.close (topology_of_closure_operator c pb) S = coe_fn (c X) S := sorry

