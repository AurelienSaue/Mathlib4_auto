/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.list.chain
import Mathlib.category_theory.punit
import PostPort

universes v₁ u₁ l u_1 v₂ u₂ u_2 

namespace Mathlib

/-!
# Connected category

Define a connected category as a _nonempty_ category for which every functor
to a discrete category is isomorphic to the constant functor.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

We give some equivalent definitions:
- A nonempty category for which every functor to a discrete category is
  constant on objects.
  See `any_functor_const_on_obj` and `connected.of_any_functor_const_on_obj`.
- A nonempty category for which every function `F` for which the presence of a
  morphism `f : j₁ ⟶ j₂` implies `F j₁ = F j₂` must be constant everywhere.
  See `constant_of_preserves_morphisms` and `connected.of_constant_of_preserves_morphisms`.
- A nonempty category for which any subset of its elements containing the
  default and closed under morphisms is everything.
  See `induct_on_objects` and `connected.of_induct`.
- A nonempty category for which every object is related under the reflexive
  transitive closure of the relation "there is a morphism in some direction
  from `j₁` to `j₂`".
  See `connected_zigzag` and `zigzag_connected`.
- A nonempty category for which for any two objects there is a sequence of
  morphisms (some reversed) from one to the other.
  See `exists_zigzag'` and `connected_of_zigzag`.

We also prove the result that the functor given by `(X × -)` preserves any
connected limit. That is, any limit of shape `J` where `J` is a connected
category is preserved by the functor `(X × -)`. This appears in `category_theory.limits.connected`.
-/

namespace category_theory


/--
A possibly empty category for which every functor to a discrete category is constant.
-/
class is_preconnected (J : Type u₁) [category J] 
where
  iso_constant : ∀ {α : Type u₁} (F : J ⥤ discrete α) (j : J), Nonempty (F ≅ functor.obj (functor.const J) (functor.obj F j))

/--
We define a connected category as a _nonempty_ category for which every
functor to a discrete category is constant.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

This allows us to show that the functor X ⨯ - preserves connected limits.

See https://stacks.math.columbia.edu/tag/002S
-/
class is_connected (J : Type u₁) [category J] 
extends is_preconnected J
where
  is_nonempty : Nonempty J

/--
If `J` is connected, any functor `F : J ⥤ discrete α` is isomorphic to
the constant functor with value `F.obj j` (for any choice of `j`).
-/
def iso_constant {J : Type u₁} [category J] [is_preconnected J] {α : Type u₁} (F : J ⥤ discrete α) (j : J) : F ≅ functor.obj (functor.const J) (functor.obj F j) :=
  nonempty.some (is_preconnected.iso_constant F j)

/--
If J is connected, any functor to a discrete category is constant on objects.
The converse is given in `is_connected.of_any_functor_const_on_obj`.
-/
theorem any_functor_const_on_obj {J : Type u₁} [category J] [is_preconnected J] {α : Type u₁} (F : J ⥤ discrete α) (j : J) (j' : J) : functor.obj F j = functor.obj F j' :=
  plift.down (ulift.down (nat_trans.app (iso.hom (iso_constant F j')) j))

/--
If any functor to a discrete category is constant on objects, J is connected.
The converse of `any_functor_const_on_obj`.
-/
theorem is_connected.of_any_functor_const_on_obj {J : Type u₁} [category J] [Nonempty J] (h : ∀ {α : Type u₁} (F : J ⥤ discrete α) (j j' : J), functor.obj F j = functor.obj F j') : is_connected J :=
  is_connected.mk

/--
If `J` is connected, then given any function `F` such that the presence of a
morphism `j₁ ⟶ j₂` implies `F j₁ = F j₂`, we have that `F` is constant.
This can be thought of as a local-to-global property.

The converse is shown in `is_connected.of_constant_of_preserves_morphisms`
-/
theorem constant_of_preserves_morphisms {J : Type u₁} [category J] [is_preconnected J] {α : Type u₁} (F : J → α) (h : ∀ (j₁ j₂ : J), (j₁ ⟶ j₂) → F j₁ = F j₂) (j : J) (j' : J) : F j = F j' :=
  any_functor_const_on_obj (functor.mk F fun (_x _x_1 : J) (f : _x ⟶ _x_1) => eq_to_hom (h _x _x_1 f)) j j'

/--
`J` is connected if: given any function `F : J → α` which is constant for any
`j₁, j₂` for which there is a morphism `j₁ ⟶ j₂`, then `F` is constant.
This can be thought of as a local-to-global property.

The converse of `constant_of_preserves_morphisms`.
-/
theorem is_connected.of_constant_of_preserves_morphisms {J : Type u₁} [category J] [Nonempty J] (h : ∀ {α : Type u₁} (F : J → α), (∀ {j₁ j₂ : J}, (j₁ ⟶ j₂) → F j₁ = F j₂) → ∀ (j j' : J), F j = F j') : is_connected J :=
  is_connected.of_any_functor_const_on_obj
    fun (_x : Type u₁) (F : J ⥤ discrete _x) =>
      h (functor.obj F) fun (_x_1 _x_2 : J) (f : _x_1 ⟶ _x_2) => plift.down (ulift.down (functor.map F f))

/--
An inductive-like property for the objects of a connected category.
If the set `p` is nonempty, and `p` is closed under morphisms of `J`,
then `p` contains all of `J`.

The converse is given in `is_connected.of_induct`.
-/
theorem induct_on_objects {J : Type u₁} [category J] [is_preconnected J] (p : set J) {j₀ : J} (h0 : j₀ ∈ p) (h1 : ∀ {j₁ j₂ : J}, (j₁ ⟶ j₂) → (j₁ ∈ p ↔ j₂ ∈ p)) (j : J) : j ∈ p := sorry

/--
If any maximal connected component containing some element j₀ of J is all of J, then J is connected.

The converse of `induct_on_objects`.
-/
theorem is_connected.of_induct {J : Type u₁} [category J] [Nonempty J] {j₀ : J} (h : ∀ (p : set J), j₀ ∈ p → (∀ {j₁ j₂ : J}, (j₁ ⟶ j₂) → (j₁ ∈ p ↔ j₂ ∈ p)) → ∀ (j : J), j ∈ p) : is_connected J := sorry

/--
Another induction principle for `is_preconnected J`:
given a type family `Z : J → Sort*` and
a rule for transporting in *both* directions along a morphism in `J`,
we can transport an `x : Z j₀` to a point in `Z j` for any `j`.
-/
theorem is_preconnected_induction {J : Type u₁} [category J] [is_preconnected J] (Z : J → Sort u_1) (h₁ : {j₁ j₂ : J} → (j₁ ⟶ j₂) → Z j₁ → Z j₂) (h₂ : {j₁ j₂ : J} → (j₁ ⟶ j₂) → Z j₂ → Z j₁) {j₀ : J} (x : Z j₀) (j : J) : Nonempty (Z j) := sorry

/-- If `J` and `K` are equivalent, then if `J` is preconnected then `K` is as well. -/
theorem is_preconnected_of_equivalent {J : Type u₁} [category J] {K : Type u₁} [category K] [is_preconnected J] (e : J ≌ K) : is_preconnected K := sorry

/-- If `J` and `K` are equivalent, then if `J` is connected then `K` is as well. -/
theorem is_connected_of_equivalent {J : Type u₁} [category J] {K : Type u₁} [category K] (e : J ≌ K) [is_connected J] : is_connected K :=
  is_connected.mk

/-- j₁ and j₂ are related by `zag` if there is a morphism between them. -/
def zag {J : Type u₁} [category J] (j₁ : J) (j₂ : J)  :=
  Nonempty (j₁ ⟶ j₂) ∨ Nonempty (j₂ ⟶ j₁)

theorem zag_symmetric {J : Type u₁} [category J] : symmetric zag :=
  fun (j₂ j₁ : J) (h : zag j₂ j₁) => or.swap h

/--
`j₁` and `j₂` are related by `zigzag` if there is a chain of
morphisms from `j₁` to `j₂`, with backward morphisms allowed.
-/
def zigzag {J : Type u₁} [category J] : J → J → Prop :=
  relation.refl_trans_gen zag

theorem zigzag_symmetric {J : Type u₁} [category J] : symmetric zigzag :=
  relation.refl_trans_gen.symmetric zag_symmetric

theorem zigzag_equivalence {J : Type u₁} [category J] : equivalence zigzag :=
  mk_equivalence zigzag relation.reflexive_refl_trans_gen zigzag_symmetric relation.transitive_refl_trans_gen

/--
The setoid given by the equivalence relation `zigzag`. A quotient for this
setoid is a connected component of the category.
-/
def zigzag.setoid (J : Type u₂) [category J] : setoid J :=
  setoid.mk zigzag zigzag_equivalence

/--
If there is a zigzag from `j₁` to `j₂`, then there is a zigzag from `F j₁` to
`F j₂` as long as `F` is a functor.
-/
theorem zigzag_obj_of_zigzag {J : Type u₁} [category J] {K : Type u₂} [category K] (F : J ⥤ K) {j₁ : J} {j₂ : J} (h : zigzag j₁ j₂) : zigzag (functor.obj F j₁) (functor.obj F j₂) := sorry

-- TODO: figure out the right way to generalise this to `zigzag`.

theorem zag_of_zag_obj {J : Type u₁} [category J] {K : Type u₂} [category K] (F : J ⥤ K) [full F] {j₁ : J} {j₂ : J} (h : zag (functor.obj F j₁) (functor.obj F j₂)) : zag j₁ j₂ :=
  or.imp (nonempty.map (functor.preimage F)) (nonempty.map (functor.preimage F)) h

/-- Any equivalence relation containing (⟶) holds for all pairs of a connected category. -/
theorem equiv_relation {J : Type u₁} [category J] [is_connected J] (r : J → J → Prop) (hr : equivalence r) (h : ∀ {j₁ j₂ : J}, (j₁ ⟶ j₂) → r j₁ j₂) (j₁ : J) (j₂ : J) : r j₁ j₂ := sorry

/-- In a connected category, any two objects are related by `zigzag`. -/
theorem is_connected_zigzag {J : Type u₁} [category J] [is_connected J] (j₁ : J) (j₂ : J) : zigzag j₁ j₂ :=
  equiv_relation zigzag zigzag_equivalence
    (fun (_x _x_1 : J) (f : _x ⟶ _x_1) => relation.refl_trans_gen.single (Or.inl (Nonempty.intro f))) j₁ j₂

/--
If any two objects in an nonempty category are related by `zigzag`, the category is connected.
-/
theorem zigzag_is_connected {J : Type u₁} [category J] [Nonempty J] (h : ∀ (j₁ j₂ : J), zigzag j₁ j₂) : is_connected J := sorry

theorem exists_zigzag' {J : Type u₁} [category J] [is_connected J] (j₁ : J) (j₂ : J) : ∃ (l : List J), list.chain zag j₁ l ∧ list.last (j₁ :: l) (list.cons_ne_nil j₁ l) = j₂ :=
  list.exists_chain_of_relation_refl_trans_gen (is_connected_zigzag j₁ j₂)

/--
If any two objects in an nonempty category are linked by a sequence of (potentially reversed)
morphisms, then J is connected.

The converse of `exists_zigzag'`.
-/
theorem is_connected_of_zigzag {J : Type u₁} [category J] [Nonempty J] (h : ∀ (j₁ j₂ : J), ∃ (l : List J), list.chain zag j₁ l ∧ list.last (j₁ :: l) (list.cons_ne_nil j₁ l) = j₂) : is_connected J := sorry

/-- If `discrete α` is connected, then `α` is (type-)equivalent to `punit`. -/
def discrete_is_connected_equiv_punit {α : Type (max u_1 u_2)} [is_connected (discrete α)] : α ≃ PUnit :=
  discrete.equiv_of_equivalence
    (equivalence.mk' (functor.star α) (discrete.functor fun (_x : PUnit) => classical.arbitrary (discrete α))
      (iso_constant 𝟭 (classical.arbitrary (discrete α)))
      (functor.punit_ext ((discrete.functor fun (_x : PUnit) => classical.arbitrary (discrete α)) ⋙ functor.star α) 𝟭))

/--
For objects `X Y : C`, any natural transformation `α : const X ⟶ const Y` from a connected
category must be constant.
This is the key property of connected categories which we use to establish properties about limits.
-/
theorem nat_trans_from_is_connected {J : Type u₁} [category J] {C : Type u₂} [category C] [is_preconnected J] {X : C} {Y : C} (α : functor.obj (functor.const J) X ⟶ functor.obj (functor.const J) Y) (j : J) (j' : J) : nat_trans.app α j = nat_trans.app α j' := sorry

