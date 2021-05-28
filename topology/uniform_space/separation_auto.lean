/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.uniform_space.basic
import Mathlib.tactic.apply_fun
import PostPort

universes u u_1 v w 

namespace Mathlib

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

This file studies uniform spaces whose underlying topological spaces are separated
(also known as Hausdorff or T₂).
This turns out to be equivalent to asking that the intersection of all entourages
is the diagonal only. This condition actually implies the stronger separation property
that the space is regular (T₃), hence those conditions are equivalent for topologies coming from
a uniform structure.

More generally, the intersection `𝓢 X` of all entourages of `X`, which has type `set (X × X)` is an
equivalence relation on `X`. Points which are equivalent under the relation are basically
undistinguishable from the point of view of the uniform structure. For instance any uniformly
continuous function will send equivalent points to the same value.

The quotient `separation_quotient X` of `X` by `𝓢 X` has a natural uniform structure which is
separated, and satisfies a universal property: every uniformly continuous function
from `X` to a separated uniform space uniquely factors through `separation_quotient X`.
As usual, this allows to turn `separation_quotient` into a functor (but we don't use the
category theory library in this file).

These notions admit relative versions, one can ask that `s : set X` is separated, this
is equivalent to asking that the uniform structure induced on `s` is separated.

## Main definitions

* `separation_relation X : set (X × X)`: the separation relation
* `separated_space X`: a predicate class asserting that `X` is separated
* `is_separated s`: a predicate asserting that `s : set X` is separated
* `separation_quotient X`: the maximal separated quotient of `X`.
* `separation_quotient.lift f`: factors a map `f : X → Y` through the separation quotient of `X`.
* `separation_quotient.map f`: turns a map `f : X → Y` into a map between the separation quotients
  of `X` and `Y`.

## Main results

* `separated_iff_t2`: the equivalence between being separated and being Hausdorff for uniform
  spaces.
* `separation_quotient.uniform_continuous_lift`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `separation_quotient.uniform_continuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Notations

Localized in `uniformity`, we have the notation `𝓢 X` for the separation relation
on a uniform space `X`,

## Implementation notes

The separation setoid `separation_setoid` is not declared as a global instance.
It is made a local instance while building the theory of `separation_quotient`.
The factored map `separation_quotient.lift f` is defined without imposing any condition on
`f`, but returns junk if `f` is not uniformly continuous (constant junk hence it is always
uniformly continuous).

-/

/-!
### Separated uniform spaces
-/

/-- The separation relation is the intersection of all entourages.
  Two points which are related by the separation relation are "indistinguishable"
  according to the uniform structure. -/
protected def separation_rel (α : Type u) [u : uniform_space α] : set (α × α) :=
  ⋂₀filter.sets (uniformity α)

theorem separated_equiv {α : Type u} [uniform_space α] : equivalence fun (x y : α) => (x, y) ∈ Mathlib.separation_rel α := sorry

/-- A uniform space is separated if its separation relation is trivial (each point
is related only to itself). -/
def separated_space (α : Type u) [uniform_space α]  :=
  Mathlib.separation_rel α = id_rel

theorem separated_def {α : Type u} [uniform_space α] : separated_space α ↔ ∀ (x y : α), (∀ (r : set (α × α)), r ∈ uniformity α → (x, y) ∈ r) → x = y := sorry

theorem separated_def' {α : Type u} [uniform_space α] : separated_space α ↔ ∀ (x y : α), x ≠ y → ∃ (r : set (α × α)), ∃ (H : r ∈ uniformity α), ¬(x, y) ∈ r := sorry

theorem id_rel_sub_separation_relation (α : Type u_1) [uniform_space α] : id_rel ⊆ Mathlib.separation_rel α := sorry

theorem separation_rel_comap {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {f : α → β} (h : _inst_1 = uniform_space.comap f _inst_2) : Mathlib.separation_rel α = prod.map f f ⁻¹' Mathlib.separation_rel β := sorry

protected theorem filter.has_basis.separation_rel {α : Type u} [uniform_space α] {ι : Type u_1} {p : ι → Prop} {s : ι → set (α × α)} (h : filter.has_basis (uniformity α) p s) : Mathlib.separation_rel α = set.Inter fun (i : ι) => set.Inter fun (H : i ∈ set_of p) => s i := sorry

theorem separation_rel_eq_inter_closure {α : Type u} [uniform_space α] : Mathlib.separation_rel α = ⋂₀(closure '' filter.sets (uniformity α)) := sorry

theorem is_closed_separation_rel {α : Type u} [uniform_space α] : is_closed (Mathlib.separation_rel α) := sorry

theorem separated_iff_t2 {α : Type u} [uniform_space α] : separated_space α ↔ t2_space α := sorry

protected instance separated_regular {α : Type u} [uniform_space α] [separated_space α] : regular_space α :=
  regular_space.mk
    fun (s : set α) (a : α) (hs : is_closed s) (ha : ¬a ∈ s) =>
      (fun (this : sᶜ ∈ nhds a) =>
          (fun (this : (set_of fun (p : α × α) => prod.fst p = a → prod.snd p ∈ (sᶜ)) ∈ uniformity α) => sorry)
            (iff.mp mem_nhds_uniformity_iff_right this))
        (mem_nhds_sets hs ha)

/-!
### Separated sets
-/

/-- A set `s` in a uniform space `α` is separated if the separation relation `𝓢 α`
induces the trivial relation on `s`. -/
def is_separated {α : Type u} [uniform_space α] (s : set α)  :=
  ∀ (x y : α), x ∈ s → y ∈ s → (x, y) ∈ Mathlib.separation_rel α → x = y

theorem is_separated_def {α : Type u} [uniform_space α] (s : set α) : is_separated s ↔ ∀ (x y : α), x ∈ s → y ∈ s → (x, y) ∈ Mathlib.separation_rel α → x = y :=
  iff.rfl

theorem is_separated_def' {α : Type u} [uniform_space α] (s : set α) : is_separated s ↔ set.prod s s ∩ Mathlib.separation_rel α ⊆ id_rel := sorry

theorem univ_separated_iff {α : Type u} [uniform_space α] : is_separated set.univ ↔ separated_space α := sorry

theorem is_separated_of_separated_space {α : Type u} [uniform_space α] [separated_space α] (s : set α) : is_separated s := sorry

theorem is_separated_iff_induced {α : Type u} [uniform_space α] {s : set α} : is_separated s ↔ separated_space ↥s := sorry

theorem eq_of_uniformity_inf_nhds_of_is_separated {α : Type u} [uniform_space α] {s : set α} (hs : is_separated s) {x : α} {y : α} : x ∈ s → y ∈ s → cluster_pt (x, y) (uniformity α) → x = y := sorry

theorem eq_of_uniformity_inf_nhds {α : Type u} [uniform_space α] [separated_space α] {x : α} {y : α} : cluster_pt (x, y) (uniformity α) → x = y := sorry

/-!
### Separation quotient
-/

namespace uniform_space


/-- The separation relation of a uniform space seen as a setoid. -/
def separation_setoid (α : Type u) [uniform_space α] : setoid α :=
  setoid.mk (fun (x y : α) => (x, y) ∈ Mathlib.separation_rel α) separated_equiv

protected instance separation_setoid.uniform_space {α : Type u} [u : uniform_space α] : uniform_space (quotient (separation_setoid α)) :=
  mk
    (core.mk
      (filter.map (fun (p : α × α) => (quotient.mk (prod.fst p), quotient.mk (prod.snd p))) (core.uniformity to_core))
      sorry sorry sorry)
    sorry

theorem uniformity_quotient {α : Type u} [uniform_space α] : uniformity (quotient (separation_setoid α)) =
  filter.map (fun (p : α × α) => (quotient.mk (prod.fst p), quotient.mk (prod.snd p))) (uniformity α) :=
  rfl

theorem uniform_continuous_quotient_mk {α : Type u} [uniform_space α] : uniform_continuous quotient.mk :=
  le_refl (filter.map (fun (x : α × α) => (quotient.mk (prod.fst x), quotient.mk (prod.snd x))) (uniformity α))

theorem uniform_continuous_quotient {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {f : quotient (separation_setoid α) → β} (hf : uniform_continuous fun (x : α) => f (quotient.mk x)) : uniform_continuous f :=
  hf

theorem uniform_continuous_quotient_lift {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {f : α → β} {h : ∀ (a b : α), (a, b) ∈ Mathlib.separation_rel α → f a = f b} (hf : uniform_continuous f) : uniform_continuous fun (a : quotient (separation_setoid α)) => quotient.lift f h a :=
  uniform_continuous_quotient hf

theorem uniform_continuous_quotient_lift₂ {α : Type u} {β : Type v} {γ : Type w} [uniform_space α] [uniform_space β] [uniform_space γ] {f : α → β → γ} {h : ∀ (a : α) (c : β) (b : α) (d : β), (a, b) ∈ Mathlib.separation_rel α → (c, d) ∈ Mathlib.separation_rel β → f a c = f b d} (hf : uniform_continuous fun (p : α × β) => f (prod.fst p) (prod.snd p)) : uniform_continuous
  fun (p : quotient (separation_setoid α) × quotient (separation_setoid β)) =>
    quotient.lift₂ f h (prod.fst p) (prod.snd p) := sorry

theorem comap_quotient_le_uniformity {α : Type u} [uniform_space α] : filter.comap (fun (p : α × α) => (quotient.mk (prod.fst p), quotient.mk (prod.snd p)))
    (uniformity (quotient (separation_setoid α))) ≤
  uniformity α := sorry

theorem comap_quotient_eq_uniformity {α : Type u} [uniform_space α] : filter.comap (fun (p : α × α) => (quotient.mk (prod.fst p), quotient.mk (prod.snd p)))
    (uniformity (quotient (separation_setoid α))) =
  uniformity α :=
  le_antisymm comap_quotient_le_uniformity filter.le_comap_map

protected instance separated_separation {α : Type u} [uniform_space α] : separated_space (quotient (separation_setoid α)) :=
  set.ext fun (_x : quotient (separation_setoid α) × quotient (separation_setoid α)) => sorry

theorem separated_of_uniform_continuous {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {f : α → β} {x : α} {y : α} (H : uniform_continuous f) (h : x ≈ y) : f x ≈ f y :=
  fun (_x : set (β × β)) (h' : _x ∈ filter.sets (uniformity β)) =>
    h ((fun (x : α × α) => (f (prod.fst x), f (prod.snd x))) ⁻¹' _x) (H h')

theorem eq_of_separated_of_uniform_continuous {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] [separated_space β] {f : α → β} {x : α} {y : α} (H : uniform_continuous f) (h : x ≈ y) : f x = f y :=
  iff.mp separated_def _inst_4 (f x) (f y) (separated_of_uniform_continuous H h)

/-- The maximal separated quotient of a uniform space `α`. -/
def separation_quotient (α : Type u_1) [uniform_space α]  :=
  quotient (separation_setoid α)

namespace separation_quotient


protected instance uniform_space {α : Type u} [uniform_space α] : uniform_space (separation_quotient α) :=
  id separation_setoid.uniform_space

protected instance separated_space {α : Type u} [uniform_space α] : separated_space (separation_quotient α) :=
  id uniform_space.separated_separation

protected instance inhabited {α : Type u} [uniform_space α] [Inhabited α] : Inhabited (separation_quotient α) :=
  eq.mpr sorry quotient.inhabited

/-- Factoring functions to a separated space through the separation quotient. -/
def lift {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] [separated_space β] (f : α → β) : separation_quotient α → β :=
  dite (uniform_continuous f) (fun (h : uniform_continuous f) => quotient.lift f sorry)
    fun (h : ¬uniform_continuous f) (x : separation_quotient α) => f Inhabited.default

theorem lift_mk {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] [separated_space β] {f : α → β} (h : uniform_continuous f) (a : α) : lift f (quotient.mk a) = f a := sorry

theorem uniform_continuous_lift {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] [separated_space β] (f : α → β) : uniform_continuous (lift f) := sorry

/-- The separation quotient functor acting on functions. -/
def map {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] (f : α → β) : separation_quotient α → separation_quotient β :=
  lift (quotient.mk ∘ f)

theorem map_mk {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {f : α → β} (h : uniform_continuous f) (a : α) : map f (quotient.mk a) = quotient.mk (f a) := sorry

theorem uniform_continuous_map {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] (f : α → β) : uniform_continuous (map f) :=
  uniform_continuous_lift (quotient.mk ∘ f)

theorem map_unique {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {f : α → β} (hf : uniform_continuous f) {g : separation_quotient α → separation_quotient β} (comm : quotient.mk ∘ f = g ∘ quotient.mk) : map f = g :=
  funext fun (x : separation_quotient α) => quot.induction_on x fun (a : α) => Eq.trans (map_mk hf a) (congr_fun comm a)

theorem map_id {α : Type u} [uniform_space α] : map id = id :=
  map_unique uniform_continuous_id rfl

theorem map_comp {α : Type u} {β : Type v} {γ : Type w} [uniform_space α] [uniform_space β] [uniform_space γ] {f : α → β} {g : β → γ} (hf : uniform_continuous f) (hg : uniform_continuous g) : map g ∘ map f = map (g ∘ f) := sorry

end separation_quotient


theorem separation_prod {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ := sorry

protected instance separated.prod {α : Type u} {β : Type v} [uniform_space α] [uniform_space β] [separated_space α] [separated_space β] : separated_space (α × β) :=
  iff.mpr separated_def
    fun (x y : α × β) (H : ∀ (r : set ((α × β) × α × β)), r ∈ uniformity (α × β) → (x, y) ∈ r) =>
      prod.ext (eq_of_separated_of_uniform_continuous uniform_continuous_fst H)
        (eq_of_separated_of_uniform_continuous uniform_continuous_snd H)

