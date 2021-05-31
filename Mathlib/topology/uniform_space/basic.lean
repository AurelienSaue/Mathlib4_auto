/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.filter.lift
import Mathlib.topology.separation
import Mathlib.PostPort

universes u_1 u u_2 l u_3 u_4 u_6 

namespace Mathlib

/-!
# Uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* uniform continuity (in this file)
* completeness (in `cauchy.lean`)
* extension of uniform continuous functions to complete spaces (in `uniform_embedding.lean`)
* totally bounded sets (in `cauchy.lean`)
* totally bounded complete sets are compact (in `cauchy.lean`)

A uniform structure on a type `X` is a filter `𝓤 X` on `X × X` satisfying some conditions
which makes it reasonable to say that `∀ᶠ (p : X × X) in 𝓤 X, ...` means
"for all p.1 and p.2 in X close enough, ...". Elements of this filter are called entourages
of `X`. The two main examples are:

* If `X` is a metric space, `V ∈ 𝓤 X ↔ ∃ ε > 0, { p | dist p.1 p.2 < ε } ⊆ V`
* If `G` is an additive topological group, `V ∈ 𝓤 G ↔ ∃ U ∈ 𝓝 (0 : G), {p | p.2 - p.1 ∈ U} ⊆ V`

Those examples are generalizations in two different directions of the elementary example where
`X = ℝ` and `V ∈ 𝓤 ℝ ↔ ∃ ε > 0, { p | |p.2 - p.1| < ε } ⊆ V` which features both the topological
group structure on `ℝ` and its metric space structure.

Each uniform structure on `X` induces a topology on `X` characterized by

> `nhds_eq_comap_uniformity : ∀ {x : X}, 𝓝 x = comap (prod.mk x) (𝓤 X)`

where `prod.mk x : X → X × X := (λ y, (x, y))` is the partial evaluation of the product
constructor.

The dictionary with metric spaces includes:
* an upper bound for `dist x y` translates into `(x, y) ∈ V` for some `V ∈ 𝓤 X`
* a ball `ball x r` roughly corresponds to `uniform_space.ball x V := {y | (x, y) ∈ V}`
  for some `V ∈ 𝓤 X`, but the later is more general (it includes in
  particular both open and closed balls for suitable `V`).
  In particular we have:
  `is_open_iff_ball_subset {s : set X} : is_open s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 X, ball x V ⊆ s`

The triangle inequality is abstracted to a statement involving the composition of relations in `X`.
First note that the triangle inequality in a metric space is equivalent to
`∀ (x y z : X) (r r' : ℝ), dist x y ≤ r → dist y z ≤ r' → dist x z ≤ r + r'`.
Then, for any `V` and `W` with type `set (X × X)`, the composition `V ○ W : set (X × X)` is
defined as `{ p : X × X | ∃ z, (p.1, z) ∈ V ∧ (z, p.2) ∈ W }`.
In the metric space case, if `V = { p | dist p.1 p.2 ≤ r }` and `W = { p | dist p.1 p.2 ≤ r' }`
then the triangle inequality, as reformulated above, says `V ○ W` is contained in
`{p | dist p.1 p.2 ≤ r + r'}` which is the entourage associated to the radius `r + r'`.
In general we have `mem_ball_comp (h : y ∈ ball x V) (h' : z ∈ ball y W) : z ∈ ball x (V ○ W)`.
Note that this discussion does not depend on any axiom imposed on the uniformity filter,
it is simply captured by the definition of composition.

The uniform space axioms ask the filter `𝓤 X` to satisfy the following:
* every `V ∈ 𝓤 X` contains the diagonal `id_rel = { p | p.1 = p.2 }`. This abstracts the fact
  that `dist x x ≤ r` for every non-negative radius `r` in the metric space case and also that
  `x - x` belongs to every neighborhood of zero in the topological group case.
* `V ∈ 𝓤 X → prod.swap '' V ∈ 𝓤 X`. This is tightly related the fact that `dist x y = dist y x`
  in a metric space, and to continuity of negation in the topological group case.
* `∀ V ∈ 𝓤 X, ∃ W ∈ 𝓤 X, W ○ W ⊆ V`. In the metric space case, it corresponds
  to cutting the radius of a ball in half and applying the triangle inequality.
  In the topological group case, it comes from continuity of addition at `(0, 0)`.

These three axioms are stated more abstractly in the definition below, in terms of
operations on filters, without directly manipulating entourages.

## Main definitions

* `uniform_space X` is a uniform space structure on a type `X`
* `uniform_continuous f` is a predicate saying a function `f : α → β` between uniform spaces
  is uniformly continuous : `∀ r ∈ 𝓤 β, ∀ᶠ (x : α × α) in 𝓤 α, (f x.1, f x.2) ∈ r`

In this file we also define a complete lattice structure on the type `uniform_space X`
of uniform structures on `X`, as well as the pullback (`uniform_space.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notations

Localized in `uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`,
and `○` for composition of relations, seen as terms with type `set (X × X)`.

## Implementation notes

There is already a theory of relations in `data/rel.lean` where the main definition is
`def rel (α β : Type*) := α → β → Prop`.
The relations used in the current file involve only one type, but this is not the reason why
we don't reuse `data/rel.lean`. We use `set (α × α)`
instead of `rel α α` because we really need sets to use the filter library, and elements
of filters on `α × α` have type `set (α × α)`.

The structure `uniform_space X` bundles a uniform structure on `X`, a topology on `X` and
an assumption saying those are compatible. This may not seem mathematically reasonable at first,
but is in fact an instance of the forgetful inheritance pattern. See Note [forgetful inheritance]
below.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/

/-!
### Relations, seen as `set (α × α)`
-/

/-- The identity relation, or the graph of the identity function -/
def id_rel {α : Type u_1} : set (α × α) :=
  set_of fun (p : α × α) => prod.fst p = prod.snd p

@[simp] theorem mem_id_rel {α : Type u_1} {a : α} {b : α} : (a, b) ∈ id_rel ↔ a = b :=
  iff.rfl

@[simp] theorem id_rel_subset {α : Type u_1} {s : set (α × α)} : id_rel ⊆ s ↔ ∀ (a : α), (a, a) ∈ s := sorry

/-- The composition of relations -/
def comp_rel {α : Type u} (r₁ : set (α × α)) (r₂ : set (α × α)) : set (α × α) :=
  set_of fun (p : α × α) => ∃ (z : α), (prod.fst p, z) ∈ r₁ ∧ (z, prod.snd p) ∈ r₂

@[simp] theorem mem_comp_rel {α : Type u_1} {r₁ : set (α × α)} {r₂ : set (α × α)} {x : α} {y : α} : (x, y) ∈ comp_rel r₁ r₂ ↔ ∃ (z : α), (x, z) ∈ r₁ ∧ (z, y) ∈ r₂ :=
  iff.rfl

@[simp] theorem swap_id_rel {α : Type u_1} : prod.swap '' id_rel = id_rel := sorry

theorem monotone_comp_rel {α : Type u_1} {β : Type u_2} [preorder β] {f : β → set (α × α)} {g : β → set (α × α)} (hf : monotone f) (hg : monotone g) : monotone fun (x : β) => comp_rel (f x) (g x) := sorry

theorem comp_rel_mono {α : Type u_1} {f : set (α × α)} {g : set (α × α)} {h : set (α × α)} {k : set (α × α)} (h₁ : f ⊆ h) (h₂ : g ⊆ k) : comp_rel f g ⊆ comp_rel h k := sorry

theorem prod_mk_mem_comp_rel {α : Type u_1} {a : α} {b : α} {c : α} {s : set (α × α)} {t : set (α × α)} (h₁ : (a, c) ∈ s) (h₂ : (c, b) ∈ t) : (a, b) ∈ comp_rel s t :=
  Exists.intro c { left := h₁, right := h₂ }

@[simp] theorem id_comp_rel {α : Type u_1} {r : set (α × α)} : comp_rel id_rel r = r := sorry

theorem comp_rel_assoc {α : Type u_1} {r : set (α × α)} {s : set (α × α)} {t : set (α × α)} : comp_rel (comp_rel r s) t = comp_rel r (comp_rel s t) := sorry

theorem subset_comp_self {α : Type u_1} {s : set (α × α)} (h : id_rel ⊆ s) : s ⊆ comp_rel s s := sorry

/-- The relation is invariant under swapping factors. -/
def symmetric_rel {α : Type u_1} (V : set (α × α)) :=
  prod.swap ⁻¹' V = V

/-- The maximal symmetric relation contained in a given relation. -/
def symmetrize_rel {α : Type u_1} (V : set (α × α)) : set (α × α) :=
  V ∩ prod.swap ⁻¹' V

theorem symmetric_symmetrize_rel {α : Type u_1} (V : set (α × α)) : symmetric_rel (symmetrize_rel V) := sorry

theorem symmetrize_rel_subset_self {α : Type u_1} (V : set (α × α)) : symmetrize_rel V ⊆ V :=
  set.sep_subset V fun (a : α × α) => a ∈ prod.swap ⁻¹' V

theorem symmetrize_mono {α : Type u_1} {V : set (α × α)} {W : set (α × α)} (h : V ⊆ W) : symmetrize_rel V ⊆ symmetrize_rel W :=
  set.inter_subset_inter h (set.preimage_mono h)

theorem symmetric_rel_inter {α : Type u_1} {U : set (α × α)} {V : set (α × α)} (hU : symmetric_rel U) (hV : symmetric_rel V) : symmetric_rel (U ∩ V) := sorry

/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure uniform_space.core (α : Type u) 
where
  uniformity : filter (α × α)
  refl : filter.principal id_rel ≤ uniformity
  symm : filter.tendsto prod.swap uniformity uniformity
  comp : (filter.lift' uniformity fun (s : set (α × α)) => comp_rel s s) ≤ uniformity

/-- An alternative constructor for `uniform_space.core`. This version unfolds various
`filter`-related definitions. -/
def uniform_space.core.mk' {α : Type u} (U : filter (α × α)) (refl : ∀ (r : set (α × α)), r ∈ U → ∀ (x : α), (x, x) ∈ r) (symm : ∀ (r : set (α × α)), r ∈ U → prod.swap ⁻¹' r ∈ U) (comp : ∀ (r : set (α × α)) (H : r ∈ U), ∃ (t : set (α × α)), ∃ (H : t ∈ U), comp_rel t t ⊆ r) : uniform_space.core α :=
  uniform_space.core.mk U sorry symm sorry

/-- A uniform space generates a topological space -/
def uniform_space.core.to_topological_space {α : Type u} (u : uniform_space.core α) : topological_space α :=
  topological_space.mk
    (fun (s : set α) =>
      ∀ (x : α), x ∈ s → (set_of fun (p : α × α) => prod.fst p = x → prod.snd p ∈ s) ∈ uniform_space.core.uniformity u)
    sorry sorry sorry

theorem uniform_space.core_eq {α : Type u_1} {u₁ : uniform_space.core α} {u₂ : uniform_space.core α} : uniform_space.core.uniformity u₁ = uniform_space.core.uniformity u₂ → u₁ = u₂ := sorry

/-- Suppose that one can put two mathematical structures on a type, a rich one `R` and a poor one
`P`, and that one can deduce the poor structure from the rich structure through a map `F` (called a
forgetful functor) (think `R = metric_space` and `P = topological_space`). A possible
implementation would be to have a type class `rich` containing a field `R`, a type class `poor`
containing a field `P`, and an instance from `rich` to `poor`. However, this creates diamond
problems, and a better approach is to let `rich` extend `poor` and have a field saying that
`F R = P`.

To illustrate this, consider the pair `metric_space` / `topological_space`. Consider the topology
on a product of two metric spaces. With the first approach, it could be obtained by going first from
each metric space to its topology, and then taking the product topology. But it could also be
obtained by considering the product metric space (with its sup distance) and then the topology
coming from this distance. These would be the same topology, but not definitionally, which means
that from the point of view of Lean's kernel, there would be two different `topological_space`
instances on the product. This is not compatible with the way instances are designed and used:
there should be at most one instance of a kind on each type. This approach has created an instance
diamond that does not commute definitionally.

The second approach solves this issue. Now, a metric space contains both a distance, a topology, and
a proof that the topology coincides with the one coming from the distance. When one defines the
product of two metric spaces, one uses the sup distance and the product topology, and one has to
give the proof that the sup distance induces the product topology. Following both sides of the
instance diamond then gives rise (definitionally) to the product topology on the product space.

Another approach would be to have the rich type class take the poor type class as an instance
parameter. It would solve the diamond problem, but it would lead to a blow up of the number
of type classes one would need to declare to work with complicated classes, say a real inner
product space, and would create exponential complexity when working with products of
such complicated spaces, that are avoided by bundling things carefully as above.

Note that this description of this specific case of the product of metric spaces is oversimplified
compared to mathlib, as there is an intermediate typeclass between `metric_space` and
`topological_space` called `uniform_space`. The above scheme is used at both levels, embedding a
topology in the uniform space structure, and a uniform structure in the metric space structure.

Note also that, when `P` is a proposition, there is no such issue as any two proofs of `P` are
definitionally equivalent in Lean.

To avoid boilerplate, there are some designs that can automatically fill the poor fields when
creating a rich structure if one doesn't want to do something special about them. For instance,
in the definition of metric spaces, default tactics fill the uniform space fields if they are
not given explicitly. One can also have a helper function creating the rich structure from a
structure with less fields, where the helper function fills the remaining fields. See for instance
`uniform_space.of_core` or `real_inner_product.of_core`.

For more details on this question, called the forgetful inheritance pattern, see [Competing
inheritance paths in dependent type theory: a case study in functional
analysis](https://hal.inria.fr/hal-02463336).
-/
/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `α × α` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
class uniform_space (α : Type u) 
extends uniform_space.core α, topological_space α
where
  is_open_uniformity : ∀ (s : set α),
  topological_space.is_open _to_topological_space s ↔
    ∀ (x : α),
      x ∈ s → (set_of fun (p : α × α) => prod.fst p = x → prod.snd p ∈ s) ∈ uniform_space.core.uniformity _to_core

/-- Alternative constructor for `uniform_space α` when a topology is already given. -/
def uniform_space.mk' {α : Type u_1} (t : topological_space α) (c : uniform_space.core α) (is_open_uniformity : ∀ (s : set α),
  topological_space.is_open t s ↔
    ∀ (x : α), x ∈ s → (set_of fun (p : α × α) => prod.fst p = x → prod.snd p ∈ s) ∈ uniform_space.core.uniformity c) : uniform_space α :=
  uniform_space.mk c is_open_uniformity

/-- Construct a `uniform_space` from a `uniform_space.core`. -/
def uniform_space.of_core {α : Type u} (u : uniform_space.core α) : uniform_space α :=
  uniform_space.mk u sorry

/-- Construct a `uniform_space` from a `u : uniform_space.core` and a `topological_space` structure
that is equal to `u.to_topological_space`. -/
def uniform_space.of_core_eq {α : Type u} (u : uniform_space.core α) (t : topological_space α) (h : t = uniform_space.core.to_topological_space u) : uniform_space α :=
  uniform_space.mk u sorry

theorem uniform_space.to_core_to_topological_space {α : Type u_1} (u : uniform_space α) : uniform_space.core.to_topological_space uniform_space.to_core = uniform_space.to_topological_space := sorry

theorem uniform_space_eq {α : Type u_1} {u₁ : uniform_space α} {u₂ : uniform_space α} : uniform_space.core.uniformity uniform_space.to_core = uniform_space.core.uniformity uniform_space.to_core → u₁ = u₂ := sorry

theorem uniform_space.of_core_eq_to_core {α : Type u_1} (u : uniform_space α) (t : topological_space α) (h : t = uniform_space.core.to_topological_space uniform_space.to_core) : uniform_space.of_core_eq uniform_space.to_core t h = u :=
  uniform_space_eq rfl

/-- The uniformity is a filter on α × α (inferred from an ambient uniform space
  structure on α). -/
def uniformity (α : Type u) [uniform_space α] : filter (α × α) :=
  uniform_space.core.uniformity uniform_space.to_core

theorem is_open_uniformity {α : Type u_1} [uniform_space α] {s : set α} : is_open s ↔ ∀ (x : α), x ∈ s → (set_of fun (p : α × α) => prod.fst p = x → prod.snd p ∈ s) ∈ uniformity α :=
  uniform_space.is_open_uniformity s

theorem refl_le_uniformity {α : Type u_1} [uniform_space α] : filter.principal id_rel ≤ uniformity α :=
  uniform_space.core.refl uniform_space.to_core

theorem refl_mem_uniformity {α : Type u_1} [uniform_space α] {x : α} {s : set (α × α)} (h : s ∈ uniformity α) : (x, x) ∈ s :=
  refl_le_uniformity h rfl

theorem symm_le_uniformity {α : Type u_1} [uniform_space α] : filter.map prod.swap (uniformity α) ≤ uniformity α :=
  uniform_space.core.symm uniform_space.to_core

theorem comp_le_uniformity {α : Type u_1} [uniform_space α] : (filter.lift' (uniformity α) fun (s : set (α × α)) => comp_rel s s) ≤ uniformity α :=
  uniform_space.core.comp uniform_space.to_core

theorem tendsto_swap_uniformity {α : Type u_1} [uniform_space α] : filter.tendsto prod.swap (uniformity α) (uniformity α) :=
  symm_le_uniformity

theorem comp_mem_uniformity_sets {α : Type u_1} [uniform_space α] {s : set (α × α)} (hs : s ∈ uniformity α) : ∃ (t : set (α × α)), ∃ (H : t ∈ uniformity α), comp_rel t t ⊆ s :=
  (fun (this : s ∈ filter.lift' (uniformity α) fun (t : set (α × α)) => comp_rel t t) =>
      iff.mp (filter.mem_lift'_sets (monotone_comp_rel monotone_id monotone_id)) this)
    (comp_le_uniformity hs)

/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is transitive. -/
theorem filter.tendsto.uniformity_trans {α : Type u_1} {β : Type u_2} [uniform_space α] {l : filter β} {f₁ : β → α} {f₂ : β → α} {f₃ : β → α} (h₁₂ : filter.tendsto (fun (x : β) => (f₁ x, f₂ x)) l (uniformity α)) (h₂₃ : filter.tendsto (fun (x : β) => (f₂ x, f₃ x)) l (uniformity α)) : filter.tendsto (fun (x : β) => (f₁ x, f₃ x)) l (uniformity α) := sorry

/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is symmetric -/
theorem filter.tendsto.uniformity_symm {α : Type u_1} {β : Type u_2} [uniform_space α] {l : filter β} {f : β → α × α} (h : filter.tendsto f l (uniformity α)) : filter.tendsto (fun (x : β) => (prod.snd (f x), prod.fst (f x))) l (uniformity α) :=
  filter.tendsto.comp tendsto_swap_uniformity h

/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is reflexive. -/
theorem tendsto_diag_uniformity {α : Type u_1} {β : Type u_2} [uniform_space α] (f : β → α) (l : filter β) : filter.tendsto (fun (x : β) => (f x, f x)) l (uniformity α) :=
  fun (s : set (α × α)) (hs : s ∈ uniformity α) =>
    iff.mpr filter.mem_map (filter.univ_mem_sets' fun (x : β) => refl_mem_uniformity hs)

theorem tendsto_const_uniformity {α : Type u_1} {β : Type u_2} [uniform_space α] {a : α} {f : filter β} : filter.tendsto (fun (_x : β) => (a, a)) f (uniformity α) :=
  tendsto_diag_uniformity (fun (_x : β) => a) f

theorem symm_of_uniformity {α : Type u_1} [uniform_space α] {s : set (α × α)} (hs : s ∈ uniformity α) : ∃ (t : set (α × α)), ∃ (H : t ∈ uniformity α), (∀ (a b : α), (a, b) ∈ t → (b, a) ∈ t) ∧ t ⊆ s := sorry

theorem comp_symm_of_uniformity {α : Type u_1} [uniform_space α] {s : set (α × α)} (hs : s ∈ uniformity α) : ∃ (t : set (α × α)), ∃ (H : t ∈ uniformity α), (∀ {a b : α}, (a, b) ∈ t → (b, a) ∈ t) ∧ comp_rel t t ⊆ s := sorry

theorem uniformity_le_symm {α : Type u_1} [uniform_space α] : uniformity α ≤ prod.swap <$> uniformity α :=
  eq.mpr (id (Eq._oldrec (Eq.refl (uniformity α ≤ prod.swap <$> uniformity α)) filter.map_swap_eq_comap_swap))
    (iff.mp filter.map_le_iff_le_comap tendsto_swap_uniformity)

theorem uniformity_eq_symm {α : Type u_1} [uniform_space α] : uniformity α = prod.swap <$> uniformity α :=
  le_antisymm uniformity_le_symm symm_le_uniformity

theorem symmetrize_mem_uniformity {α : Type u_1} [uniform_space α] {V : set (α × α)} (h : V ∈ uniformity α) : symmetrize_rel V ∈ uniformity α := sorry

theorem uniformity_lift_le_swap {α : Type u_1} {β : Type u_2} [uniform_space α] {g : set (α × α) → filter β} {f : filter β} (hg : monotone g) (h : (filter.lift (uniformity α) fun (s : set (α × α)) => g (prod.swap ⁻¹' s)) ≤ f) : filter.lift (uniformity α) g ≤ f := sorry

theorem uniformity_lift_le_comp {α : Type u_1} {β : Type u_2} [uniform_space α] {f : set (α × α) → filter β} (h : monotone f) : (filter.lift (uniformity α) fun (s : set (α × α)) => f (comp_rel s s)) ≤ filter.lift (uniformity α) f := sorry

theorem comp_le_uniformity3 {α : Type u_1} [uniform_space α] : (filter.lift' (uniformity α) fun (s : set (α × α)) => comp_rel s (comp_rel s s)) ≤ uniformity α := sorry

theorem comp_symm_mem_uniformity_sets {α : Type u_1} [uniform_space α] {s : set (α × α)} (hs : s ∈ uniformity α) : ∃ (t : set (α × α)), ∃ (H : t ∈ uniformity α), symmetric_rel t ∧ comp_rel t t ⊆ s := sorry

theorem subset_comp_self_of_mem_uniformity {α : Type u_1} [uniform_space α] {s : set (α × α)} (h : s ∈ uniformity α) : s ⊆ comp_rel s s :=
  subset_comp_self (refl_le_uniformity h)

theorem comp_comp_symm_mem_uniformity_sets {α : Type u_1} [uniform_space α] {s : set (α × α)} (hs : s ∈ uniformity α) : ∃ (t : set (α × α)), ∃ (H : t ∈ uniformity α), symmetric_rel t ∧ comp_rel (comp_rel t t) t ⊆ s := sorry

/-!
### Balls in uniform spaces
-/

/-- The ball around `(x : β)` with respect to `(V : set (β × β))`. Intended to be
used for `V ∈ 𝓤 β`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`.  -/
def uniform_space.ball {β : Type u_2} (x : β) (V : set (β × β)) : set β :=
  Prod.mk x ⁻¹' V

theorem uniform_space.mem_ball_self {α : Type u_1} [uniform_space α] (x : α) {V : set (α × α)} (hV : V ∈ uniformity α) : x ∈ uniform_space.ball x V :=
  refl_mem_uniformity hV

/-- The triangle inequality for `uniform_space.ball` -/
theorem mem_ball_comp {β : Type u_2} {V : set (β × β)} {W : set (β × β)} {x : β} {y : β} {z : β} (h : y ∈ uniform_space.ball x V) (h' : z ∈ uniform_space.ball y W) : z ∈ uniform_space.ball x (comp_rel V W) :=
  prod_mk_mem_comp_rel h h'

theorem ball_subset_of_comp_subset {β : Type u_2} {V : set (β × β)} {W : set (β × β)} {x : β} {y : β} (h : x ∈ uniform_space.ball y W) (h' : comp_rel W W ⊆ V) : uniform_space.ball x W ⊆ uniform_space.ball y V :=
  fun (z : β) (z_in : z ∈ uniform_space.ball x W) => h' (mem_ball_comp h z_in)

theorem ball_mono {β : Type u_2} {V : set (β × β)} {W : set (β × β)} (h : V ⊆ W) (x : β) : uniform_space.ball x V ⊆ uniform_space.ball x W :=
  id fun (a : β) (ᾰ : a ∈ uniform_space.ball x V) => h ᾰ

theorem mem_ball_symmetry {β : Type u_2} {V : set (β × β)} (hV : symmetric_rel V) {x : β} {y : β} : x ∈ uniform_space.ball y V ↔ y ∈ uniform_space.ball x V := sorry

theorem ball_eq_of_symmetry {β : Type u_2} {V : set (β × β)} (hV : symmetric_rel V) {x : β} : uniform_space.ball x V = set_of fun (y : β) => (y, x) ∈ V := sorry

theorem mem_comp_of_mem_ball {β : Type u_2} {V : set (β × β)} {W : set (β × β)} {x : β} {y : β} {z : β} (hV : symmetric_rel V) (hx : x ∈ uniform_space.ball z V) (hy : y ∈ uniform_space.ball z W) : (x, y) ∈ comp_rel V W :=
  Exists.intro z
    { left := eq.mp (Eq._oldrec (Eq.refl (x ∈ uniform_space.ball z V)) (propext (mem_ball_symmetry hV))) hx, right := hy }

theorem uniform_space.is_open_ball {α : Type u_1} [uniform_space α] (x : α) {V : set (α × α)} (hV : is_open V) : is_open (uniform_space.ball x V) :=
  is_open.preimage (continuous.prod_mk continuous_const continuous_id) hV

theorem mem_comp_comp {β : Type u_2} {V : set (β × β)} {W : set (β × β)} {M : set (β × β)} (hW' : symmetric_rel W) {p : β × β} : p ∈ comp_rel (comp_rel V M) W ↔
  set.nonempty (set.prod (uniform_space.ball (prod.fst p) V) (uniform_space.ball (prod.snd p) W) ∩ M) := sorry

/-!
### Neighborhoods in uniform spaces
-/

theorem mem_nhds_uniformity_iff_right {α : Type u_1} [uniform_space α] {x : α} {s : set α} : s ∈ nhds x ↔ (set_of fun (p : α × α) => prod.fst p = x → prod.snd p ∈ s) ∈ uniformity α := sorry

theorem mem_nhds_uniformity_iff_left {α : Type u_1} [uniform_space α] {x : α} {s : set α} : s ∈ nhds x ↔ (set_of fun (p : α × α) => prod.snd p = x → prod.fst p ∈ s) ∈ uniformity α := sorry

theorem nhds_eq_comap_uniformity_aux {α : Type u} {x : α} {s : set α} {F : filter (α × α)} : (set_of fun (p : α × α) => prod.fst p = x → prod.snd p ∈ s) ∈ F ↔ s ∈ filter.comap (Prod.mk x) F := sorry

theorem nhds_eq_comap_uniformity {α : Type u_1} [uniform_space α] {x : α} : nhds x = filter.comap (Prod.mk x) (uniformity α) := sorry

theorem is_open_iff_ball_subset {α : Type u_1} [uniform_space α] {s : set α} : is_open s ↔ ∀ (x : α) (H : x ∈ s), ∃ (V : set (α × α)), ∃ (H : V ∈ uniformity α), uniform_space.ball x V ⊆ s := sorry

theorem nhds_basis_uniformity' {α : Type u_1} {β : Type u_2} [uniform_space α] {p : β → Prop} {s : β → set (α × α)} (h : filter.has_basis (uniformity α) p s) {x : α} : filter.has_basis (nhds x) p fun (i : β) => uniform_space.ball x (s i) := sorry

theorem nhds_basis_uniformity {α : Type u_1} {β : Type u_2} [uniform_space α] {p : β → Prop} {s : β → set (α × α)} (h : filter.has_basis (uniformity α) p s) {x : α} : filter.has_basis (nhds x) p fun (i : β) => set_of fun (y : α) => (y, x) ∈ s i := sorry

theorem uniform_space.mem_nhds_iff {α : Type u_1} [uniform_space α] {x : α} {s : set α} : s ∈ nhds x ↔ ∃ (V : set (α × α)), ∃ (H : V ∈ uniformity α), uniform_space.ball x V ⊆ s := sorry

theorem uniform_space.ball_mem_nhds {α : Type u_1} [uniform_space α] (x : α) {V : set (α × α)} (V_in : V ∈ uniformity α) : uniform_space.ball x V ∈ nhds x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (uniform_space.ball x V ∈ nhds x)) (propext uniform_space.mem_nhds_iff)))
    (Exists.intro V (Exists.intro V_in (set.subset.refl (uniform_space.ball x V))))

theorem uniform_space.mem_nhds_iff_symm {α : Type u_1} [uniform_space α] {x : α} {s : set α} : s ∈ nhds x ↔ ∃ (V : set (α × α)), ∃ (H : V ∈ uniformity α), symmetric_rel V ∧ uniform_space.ball x V ⊆ s := sorry

theorem uniform_space.has_basis_nhds {α : Type u_1} [uniform_space α] (x : α) : filter.has_basis (nhds x) (fun (s : set (α × α)) => s ∈ uniformity α ∧ symmetric_rel s)
  fun (s : set (α × α)) => uniform_space.ball x s := sorry

theorem uniform_space.has_basis_nhds_prod {α : Type u_1} [uniform_space α] (x : α) (y : α) : filter.has_basis (nhds (x, y)) (fun (s : set (α × α)) => s ∈ uniformity α ∧ symmetric_rel s)
  fun (s : set (α × α)) => set.prod (uniform_space.ball x s) (uniform_space.ball y s) := sorry

theorem nhds_eq_uniformity {α : Type u_1} [uniform_space α] {x : α} : nhds x = filter.lift' (uniformity α) (uniform_space.ball x) :=
  filter.has_basis.eq_binfi (nhds_basis_uniformity' (filter.basis_sets (uniformity α)))

theorem mem_nhds_left {α : Type u_1} [uniform_space α] (x : α) {s : set (α × α)} (h : s ∈ uniformity α) : (set_of fun (y : α) => (x, y) ∈ s) ∈ nhds x :=
  uniform_space.ball_mem_nhds x h

theorem mem_nhds_right {α : Type u_1} [uniform_space α] (y : α) {s : set (α × α)} (h : s ∈ uniformity α) : (set_of fun (x : α) => (x, y) ∈ s) ∈ nhds y :=
  mem_nhds_left y (symm_le_uniformity h)

theorem tendsto_right_nhds_uniformity {α : Type u_1} [uniform_space α] {a : α} : filter.tendsto (fun (a' : α) => (a', a)) (nhds a) (uniformity α) :=
  fun (s : set (α × α)) => mem_nhds_right a

theorem tendsto_left_nhds_uniformity {α : Type u_1} [uniform_space α] {a : α} : filter.tendsto (fun (a' : α) => (a, a')) (nhds a) (uniformity α) :=
  fun (s : set (α × α)) => mem_nhds_left a

theorem lift_nhds_left {α : Type u_1} {β : Type u_2} [uniform_space α] {x : α} {g : set α → filter β} (hg : monotone g) : filter.lift (nhds x) g = filter.lift (uniformity α) fun (s : set (α × α)) => g (set_of fun (y : α) => (x, y) ∈ s) := sorry

theorem lift_nhds_right {α : Type u_1} {β : Type u_2} [uniform_space α] {x : α} {g : set α → filter β} (hg : monotone g) : filter.lift (nhds x) g = filter.lift (uniformity α) fun (s : set (α × α)) => g (set_of fun (y : α) => (y, x) ∈ s) := sorry

theorem nhds_nhds_eq_uniformity_uniformity_prod {α : Type u_1} [uniform_space α] {a : α} {b : α} : filter.prod (nhds a) (nhds b) =
  filter.lift (uniformity α)
    fun (s : set (α × α)) =>
      filter.lift' (uniformity α)
        fun (t : set (α × α)) => set.prod (set_of fun (y : α) => (y, a) ∈ s) (set_of fun (y : α) => (b, y) ∈ t) := sorry

theorem nhds_eq_uniformity_prod {α : Type u_1} [uniform_space α] {a : α} {b : α} : nhds (a, b) =
  filter.lift' (uniformity α)
    fun (s : set (α × α)) => set.prod (set_of fun (y : α) => (y, a) ∈ s) (set_of fun (y : α) => (b, y) ∈ s) := sorry

theorem nhdset_of_mem_uniformity {α : Type u_1} [uniform_space α] {d : set (α × α)} (s : set (α × α)) (hd : d ∈ uniformity α) : ∃ (t : set (α × α)),
  is_open t ∧
    s ⊆ t ∧ t ⊆ set_of fun (p : α × α) => ∃ (x : α), ∃ (y : α), (prod.fst p, x) ∈ d ∧ (x, y) ∈ s ∧ (y, prod.snd p) ∈ d := sorry

/-- Entourages are neighborhoods of the diagonal. -/
theorem nhds_le_uniformity {α : Type u_1} [uniform_space α] (x : α) : nhds (x, x) ≤ uniformity α := sorry

/-- Entourages are neighborhoods of the diagonal. -/
theorem supr_nhds_le_uniformity {α : Type u_1} [uniform_space α] : (supr fun (x : α) => nhds (x, x)) ≤ uniformity α :=
  supr_le nhds_le_uniformity

/-!
### Closure and interior in uniform spaces
-/

theorem closure_eq_uniformity {α : Type u_1} [uniform_space α] (s : set (α × α)) : closure s =
  set.Inter
    fun (V : set (α × α)) =>
      set.Inter
        fun (H : V ∈ set_of fun (V : set (α × α)) => V ∈ uniformity α ∧ symmetric_rel V) => comp_rel (comp_rel V s) V := sorry

theorem uniformity_has_basis_closed {α : Type u_1} [uniform_space α] : filter.has_basis (uniformity α) (fun (V : set (α × α)) => V ∈ uniformity α ∧ is_closed V) id := sorry

/-- Closed entourages form a basis of the uniformity filter. -/
theorem uniformity_has_basis_closure {α : Type u_1} [uniform_space α] : filter.has_basis (uniformity α) (fun (V : set (α × α)) => V ∈ uniformity α) closure := sorry

theorem closure_eq_inter_uniformity {α : Type u_1} [uniform_space α] {t : set (α × α)} : closure t = set.Inter fun (d : set (α × α)) => set.Inter fun (H : d ∈ uniformity α) => comp_rel d (comp_rel t d) := sorry

theorem uniformity_eq_uniformity_closure {α : Type u_1} [uniform_space α] : uniformity α = filter.lift' (uniformity α) closure := sorry

theorem uniformity_eq_uniformity_interior {α : Type u_1} [uniform_space α] : uniformity α = filter.lift' (uniformity α) interior := sorry

theorem interior_mem_uniformity {α : Type u_1} [uniform_space α] {s : set (α × α)} (hs : s ∈ uniformity α) : interior s ∈ uniformity α :=
  eq.mpr (id (Eq._oldrec (Eq.refl (interior s ∈ uniformity α)) uniformity_eq_uniformity_interior)) (filter.mem_lift' hs)

theorem mem_uniformity_is_closed {α : Type u_1} [uniform_space α] {s : set (α × α)} (h : s ∈ uniformity α) : ∃ (t : set (α × α)), ∃ (H : t ∈ uniformity α), is_closed t ∧ t ⊆ s := sorry

/-- The uniform neighborhoods of all points of a dense set cover the whole space. -/
theorem dense.bUnion_uniformity_ball {α : Type u_1} [uniform_space α] {s : set α} {U : set (α × α)} (hs : dense s) (hU : U ∈ uniformity α) : (set.Union fun (x : α) => set.Union fun (H : x ∈ s) => uniform_space.ball x U) = set.univ := sorry

/-!
### Uniformity bases
-/

/-- Open elements of `𝓤 α` form a basis of `𝓤 α`. -/
theorem uniformity_has_basis_open {α : Type u_1} [uniform_space α] : filter.has_basis (uniformity α) (fun (V : set (α × α)) => V ∈ uniformity α ∧ is_open V) id := sorry

theorem filter.has_basis.mem_uniformity_iff {α : Type u_1} {β : Type u_2} [uniform_space α] {p : β → Prop} {s : β → set (α × α)} (h : filter.has_basis (uniformity α) p s) {t : set (α × α)} : t ∈ uniformity α ↔ ∃ (i : β), ∃ (hi : p i), ∀ (a b : α), (a, b) ∈ s i → (a, b) ∈ t := sorry

/-- Symmetric entourages form a basis of `𝓤 α` -/
theorem uniform_space.has_basis_symmetric {α : Type u_1} [uniform_space α] : filter.has_basis (uniformity α) (fun (s : set (α × α)) => s ∈ uniformity α ∧ symmetric_rel s) id := sorry

/-- Open elements `s : set (α × α)` of `𝓤 α` such that `(x, y) ∈ s ↔ (y, x) ∈ s` form a basis
of `𝓤 α`. -/
theorem uniformity_has_basis_open_symmetric {α : Type u_1} [uniform_space α] : filter.has_basis (uniformity α) (fun (V : set (α × α)) => V ∈ uniformity α ∧ is_open V ∧ symmetric_rel V) id := sorry

theorem uniform_space.has_seq_basis {α : Type u_1} [uniform_space α] (h : filter.is_countably_generated (uniformity α)) : ∃ (V : ℕ → set (α × α)),
  filter.has_antimono_basis (uniformity α) (fun (_x : ℕ) => True) V ∧ ∀ (n : ℕ), symmetric_rel (V n) := sorry

/-! ### Uniform continuity -/

/-- A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `α`. -/
def uniform_continuous {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] (f : α → β) :=
  filter.tendsto (fun (x : α × α) => (f (prod.fst x), f (prod.snd x))) (uniformity α) (uniformity β)

/-- A function `f : α → β` is *uniformly continuous* on `s : set α` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s.prod s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`.-/
def uniform_continuous_on {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] (f : α → β) (s : set α) :=
  filter.tendsto (fun (x : α × α) => (f (prod.fst x), f (prod.snd x))) (uniformity α ⊓ filter.principal (set.prod s s))
    (uniformity β)

theorem uniform_continuous_def {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {f : α → β} : uniform_continuous f ↔
  ∀ (r : set (β × β)),
    r ∈ uniformity β → (set_of fun (x : α × α) => (f (prod.fst x), f (prod.snd x)) ∈ r) ∈ uniformity α :=
  iff.rfl

theorem uniform_continuous_iff_eventually {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {f : α → β} : uniform_continuous f ↔
  ∀ (r : set (β × β)),
    r ∈ uniformity β → filter.eventually (fun (x : α × α) => (f (prod.fst x), f (prod.snd x)) ∈ r) (uniformity α) :=
  iff.rfl

theorem uniform_continuous_of_const {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {c : α → β} (h : ∀ (a b : α), c a = c b) : uniform_continuous c := sorry

theorem uniform_continuous_id {α : Type u_1} [uniform_space α] : uniform_continuous id := sorry

theorem uniform_continuous_const {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {b : β} : uniform_continuous fun (a : α) => b :=
  uniform_continuous_of_const fun (_x _x : α) => rfl

theorem uniform_continuous.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α] [uniform_space β] [uniform_space γ] {g : β → γ} {f : α → β} (hg : uniform_continuous g) (hf : uniform_continuous f) : uniform_continuous (g ∘ f) :=
  filter.tendsto.comp hg hf

theorem filter.has_basis.uniform_continuous_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [uniform_space α] [uniform_space β] {p : γ → Prop} {s : γ → set (α × α)} (ha : filter.has_basis (uniformity α) p s) {q : δ → Prop} {t : δ → set (β × β)} (hb : filter.has_basis (uniformity β) q t) {f : α → β} : uniform_continuous f ↔ ∀ (i : δ), q i → ∃ (j : γ), ∃ (hj : p j), ∀ (x y : α), (x, y) ∈ s j → (f x, f y) ∈ t i := sorry

theorem filter.has_basis.uniform_continuous_on_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [uniform_space α] [uniform_space β] {p : γ → Prop} {s : γ → set (α × α)} (ha : filter.has_basis (uniformity α) p s) {q : δ → Prop} {t : δ → set (β × β)} (hb : filter.has_basis (uniformity β) q t) {f : α → β} {S : set α} : uniform_continuous_on f S ↔
  ∀ (i : δ), q i → ∃ (j : γ), ∃ (hj : p j), ∀ (x y : α), x ∈ S → y ∈ S → (x, y) ∈ s j → (f x, f y) ∈ t i := sorry

protected instance uniform_space.partial_order {α : Type u_1} : partial_order (uniform_space α) :=
  partial_order.mk
    (fun (t s : uniform_space α) =>
      uniform_space.core.uniformity uniform_space.to_core ≤ uniform_space.core.uniformity uniform_space.to_core)
    (preorder.lt._default
      fun (t s : uniform_space α) =>
        uniform_space.core.uniformity uniform_space.to_core ≤ uniform_space.core.uniformity uniform_space.to_core)
    sorry sorry sorry

protected instance uniform_space.has_Inf {α : Type u_1} : has_Inf (uniform_space α) :=
  has_Inf.mk
    fun (s : set (uniform_space α)) =>
      uniform_space.of_core
        (uniform_space.core.mk (infi fun (u : uniform_space α) => infi fun (H : u ∈ s) => uniformity α) sorry sorry sorry)

protected instance uniform_space.has_top {α : Type u_1} : has_top (uniform_space α) :=
  has_top.mk (uniform_space.of_core (uniform_space.core.mk ⊤ sorry sorry sorry))

protected instance uniform_space.has_bot {α : Type u_1} : has_bot (uniform_space α) :=
  has_bot.mk (uniform_space.mk (uniform_space.core.mk (filter.principal id_rel) sorry sorry sorry) sorry)

protected instance uniform_space.complete_lattice {α : Type u_1} : complete_lattice (uniform_space α) :=
  complete_lattice.mk (fun (a b : uniform_space α) => Inf (set_of fun (x : uniform_space α) => a ≤ x ∧ b ≤ x))
    partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry
    (fun (a b : uniform_space α) => Inf (insert a (singleton b))) sorry sorry sorry ⊤ sorry ⊥ sorry
    (fun (tt : set (uniform_space α)) =>
      Inf (set_of fun (t : uniform_space α) => ∀ (t' : uniform_space α), t' ∈ tt → t' ≤ t))
    Inf sorry sorry sorry sorry

theorem infi_uniformity {α : Type u_1} {ι : Sort u_2} {u : ι → uniform_space α} : uniform_space.core.uniformity uniform_space.to_core =
  infi fun (i : ι) => uniform_space.core.uniformity uniform_space.to_core := sorry

theorem inf_uniformity {α : Type u_1} {u : uniform_space α} {v : uniform_space α} : uniform_space.core.uniformity uniform_space.to_core =
  uniform_space.core.uniformity uniform_space.to_core ⊓ uniform_space.core.uniformity uniform_space.to_core := sorry

protected instance inhabited_uniform_space {α : Type u_1} : Inhabited (uniform_space α) :=
  { default := ⊥ }

protected instance inhabited_uniform_space_core {α : Type u_1} : Inhabited (uniform_space.core α) :=
  { default := uniform_space.to_core }

/-- Given `f : α → β` and a uniformity `u` on `β`, the inverse image of `u` under `f`
  is the inverse image in the filter sense of the induced function `α × α → β × β`. -/
def uniform_space.comap {α : Type u_1} {β : Type u_2} (f : α → β) (u : uniform_space β) : uniform_space α :=
  uniform_space.mk
    (uniform_space.core.mk
      (filter.comap (fun (p : α × α) => (f (prod.fst p), f (prod.snd p)))
        (uniform_space.core.uniformity uniform_space.to_core))
      sorry sorry sorry)
    sorry

theorem uniformity_comap {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {f : α → β} (h : _inst_1 = uniform_space.comap f _inst_2) : uniformity α = filter.comap (prod.map f f) (uniformity β) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (uniformity α = filter.comap (prod.map f f) (uniformity β))) h))
    (Eq.refl (uniformity α))

theorem uniform_space_comap_id {α : Type u_1} : uniform_space.comap id = id := sorry

theorem uniform_space.comap_comap {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uγ : uniform_space γ] {f : α → β} {g : β → γ} : uniform_space.comap (g ∘ f) uγ = uniform_space.comap f (uniform_space.comap g uγ) := sorry

theorem uniform_continuous_iff {α : Type u_1} {β : Type u_2} [uα : uniform_space α] [uβ : uniform_space β] {f : α → β} : uniform_continuous f ↔ uα ≤ uniform_space.comap f uβ :=
  filter.map_le_iff_le_comap

theorem uniform_continuous_comap {α : Type u_1} {β : Type u_2} {f : α → β} [u : uniform_space β] : uniform_continuous f :=
  filter.tendsto_comap

theorem to_topological_space_comap {α : Type u_1} {β : Type u_2} {f : α → β} {u : uniform_space β} : uniform_space.to_topological_space = topological_space.induced f uniform_space.to_topological_space :=
  rfl

theorem uniform_continuous_comap' {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : γ → β} {g : α → γ} [v : uniform_space β] [u : uniform_space α] (h : uniform_continuous (f ∘ g)) : uniform_continuous g :=
  iff.mpr filter.tendsto_comap_iff h

theorem to_topological_space_mono {α : Type u_1} {u₁ : uniform_space α} {u₂ : uniform_space α} (h : u₁ ≤ u₂) : uniform_space.to_topological_space ≤ uniform_space.to_topological_space := sorry

theorem uniform_continuous.continuous {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {f : α → β} (hf : uniform_continuous f) : continuous f :=
  iff.mpr continuous_iff_le_induced (to_topological_space_mono (iff.mp uniform_continuous_iff hf))

theorem to_topological_space_bot {α : Type u_1} : uniform_space.to_topological_space = ⊥ :=
  rfl

theorem to_topological_space_top {α : Type u_1} : uniform_space.to_topological_space = ⊤ := sorry

theorem to_topological_space_infi {α : Type u_1} {ι : Sort u_2} {u : ι → uniform_space α} : uniform_space.to_topological_space = infi fun (i : ι) => uniform_space.to_topological_space := sorry

theorem to_topological_space_Inf {α : Type u_1} {s : set (uniform_space α)} : uniform_space.to_topological_space =
  infi fun (i : uniform_space α) => infi fun (H : i ∈ s) => uniform_space.to_topological_space := sorry

theorem to_topological_space_inf {α : Type u_1} {u : uniform_space α} {v : uniform_space α} : uniform_space.to_topological_space = uniform_space.to_topological_space ⊓ uniform_space.to_topological_space := sorry

protected instance empty.uniform_space : uniform_space empty :=
  ⊥

protected instance unit.uniform_space : uniform_space Unit :=
  ⊥

protected instance bool.uniform_space : uniform_space Bool :=
  ⊥

protected instance nat.uniform_space : uniform_space ℕ :=
  ⊥

protected instance int.uniform_space : uniform_space ℤ :=
  ⊥

protected instance subtype.uniform_space {α : Type u_1} {p : α → Prop} [t : uniform_space α] : uniform_space (Subtype p) :=
  uniform_space.comap subtype.val t

theorem uniformity_subtype {α : Type u_1} {p : α → Prop} [t : uniform_space α] : uniformity (Subtype p) =
  filter.comap (fun (q : Subtype p × Subtype p) => (subtype.val (prod.fst q), subtype.val (prod.snd q))) (uniformity α) :=
  rfl

theorem uniform_continuous_subtype_val {α : Type u_1} {p : α → Prop} [uniform_space α] : uniform_continuous subtype.val :=
  uniform_continuous_comap

theorem uniform_continuous_subtype_mk {α : Type u_1} {β : Type u_2} {p : α → Prop} [uniform_space α] [uniform_space β] {f : β → α} (hf : uniform_continuous f) (h : ∀ (x : β), p (f x)) : uniform_continuous fun (x : β) => { val := f x, property := h x } :=
  uniform_continuous_comap' hf

theorem uniform_continuous_on_iff_restrict {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {f : α → β} {s : set α} : uniform_continuous_on f s ↔ uniform_continuous (set.restrict f s) := sorry

theorem tendsto_of_uniform_continuous_subtype {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {f : α → β} {s : set α} {a : α} (hf : uniform_continuous fun (x : ↥s) => f (subtype.val x)) (ha : s ∈ nhds a) : filter.tendsto f (nhds a) (nhds (f a)) := sorry

theorem uniform_continuous_on.continuous_on {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {f : α → β} {s : set α} (h : uniform_continuous_on f s) : continuous_on f s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (continuous_on f s)) (propext continuous_on_iff_continuous_restrict)))
    (uniform_continuous.continuous
      (eq.mp (Eq._oldrec (Eq.refl (uniform_continuous_on f s)) (propext uniform_continuous_on_iff_restrict)) h))

/- a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/

protected instance prod.uniform_space {α : Type u_1} {β : Type u_2} [u₁ : uniform_space α] [u₂ : uniform_space β] : uniform_space (α × β) :=
  uniform_space.of_core_eq uniform_space.to_core prod.topological_space sorry

theorem uniformity_prod {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] : uniformity (α × β) =
  filter.comap (fun (p : (α × β) × α × β) => (prod.fst (prod.fst p), prod.fst (prod.snd p))) (uniformity α) ⊓
    filter.comap (fun (p : (α × β) × α × β) => (prod.snd (prod.fst p), prod.snd (prod.snd p))) (uniformity β) :=
  inf_uniformity

theorem uniformity_prod_eq_prod {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] : uniformity (α × β) =
  filter.map
    (fun (p : (α × α) × β × β) =>
      ((prod.fst (prod.fst p), prod.fst (prod.snd p)), prod.snd (prod.fst p), prod.snd (prod.snd p)))
    (filter.prod (uniformity α) (uniformity β)) := sorry

theorem mem_map_sets_iff' {α : Type u_1} {β : Type u_2} {f : filter α} {m : α → β} {t : set β} : t ∈ filter.sets (filter.map m f) ↔ ∃ (s : set α), ∃ (H : s ∈ f), m '' s ⊆ t :=
  filter.mem_map_sets_iff

theorem mem_uniformity_of_uniform_continuous_invariant {α : Type u_1} [uniform_space α] {s : set (α × α)} {f : α → α → α} (hf : uniform_continuous fun (p : α × α) => f (prod.fst p) (prod.snd p)) (hs : s ∈ uniformity α) : ∃ (u : set (α × α)), ∃ (H : u ∈ uniformity α), ∀ (a b c : α), (a, b) ∈ u → (f a c, f b c) ∈ s := sorry

theorem mem_uniform_prod {α : Type u_1} {β : Type u_2} [t₁ : uniform_space α] [t₂ : uniform_space β] {a : set (α × α)} {b : set (β × β)} (ha : a ∈ uniformity α) (hb : b ∈ uniformity β) : (set_of
    fun (p : (α × β) × α × β) =>
      (prod.fst (prod.fst p), prod.fst (prod.snd p)) ∈ a ∧ (prod.snd (prod.fst p), prod.snd (prod.snd p)) ∈ b) ∈
  uniformity (α × β) := sorry

theorem tendsto_prod_uniformity_fst {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] : filter.tendsto (fun (p : (α × β) × α × β) => (prod.fst (prod.fst p), prod.fst (prod.snd p))) (uniformity (α × β))
  (uniformity α) :=
  le_trans (filter.map_mono inf_le_left) filter.map_comap_le

theorem tendsto_prod_uniformity_snd {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] : filter.tendsto (fun (p : (α × β) × α × β) => (prod.snd (prod.fst p), prod.snd (prod.snd p))) (uniformity (α × β))
  (uniformity β) :=
  le_trans (filter.map_mono inf_le_right) filter.map_comap_le

theorem uniform_continuous_fst {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] : uniform_continuous fun (p : α × β) => prod.fst p :=
  tendsto_prod_uniformity_fst

theorem uniform_continuous_snd {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] : uniform_continuous fun (p : α × β) => prod.snd p :=
  tendsto_prod_uniformity_snd

theorem uniform_continuous.prod_mk {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α] [uniform_space β] [uniform_space γ] {f₁ : α → β} {f₂ : α → γ} (h₁ : uniform_continuous f₁) (h₂ : uniform_continuous f₂) : uniform_continuous fun (a : α) => (f₁ a, f₂ a) := sorry

theorem uniform_continuous.prod_mk_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α] [uniform_space β] [uniform_space γ] {f : α × β → γ} (h : uniform_continuous f) (b : β) : uniform_continuous fun (a : α) => f (a, b) :=
  uniform_continuous.comp h (uniform_continuous.prod_mk uniform_continuous_id uniform_continuous_const)

theorem uniform_continuous.prod_mk_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α] [uniform_space β] [uniform_space γ] {f : α × β → γ} (h : uniform_continuous f) (a : α) : uniform_continuous fun (b : β) => f (a, b) :=
  uniform_continuous.comp h (uniform_continuous.prod_mk uniform_continuous_const uniform_continuous_id)

theorem uniform_continuous.prod_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [uniform_space α] [uniform_space β] [uniform_space γ] [uniform_space δ] {f : α → γ} {g : β → δ} (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (prod.map f g) :=
  uniform_continuous.prod_mk (uniform_continuous.comp hf uniform_continuous_fst)
    (uniform_continuous.comp hg uniform_continuous_snd)

theorem to_topological_space_prod {α : Type u_1} {β : Type u_2} [u : uniform_space α] [v : uniform_space β] : uniform_space.to_topological_space = prod.topological_space :=
  rfl

/-- Uniform continuity for functions of two variables. -/
def uniform_continuous₂ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α] [uniform_space β] [uniform_space γ] (f : α → β → γ) :=
  uniform_continuous (function.uncurry f)

theorem uniform_continuous₂_def {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α] [uniform_space β] [uniform_space γ] (f : α → β → γ) : uniform_continuous₂ f ↔ uniform_continuous (function.uncurry f) :=
  iff.rfl

theorem uniform_continuous₂.uniform_continuous {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α] [uniform_space β] [uniform_space γ] {f : α → β → γ} (h : uniform_continuous₂ f) : uniform_continuous (function.uncurry f) :=
  h

theorem uniform_continuous₂_curry {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α] [uniform_space β] [uniform_space γ] (f : α × β → γ) : uniform_continuous₂ (function.curry f) ↔ uniform_continuous f := sorry

theorem uniform_continuous₂.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [uniform_space α] [uniform_space β] [uniform_space γ] [uniform_space δ] {f : α → β → γ} {g : γ → δ} (hg : uniform_continuous g) (hf : uniform_continuous₂ f) : uniform_continuous₂ (function.bicompr g f) :=
  uniform_continuous.comp hg hf

theorem uniform_continuous₂.bicompl {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {δ' : Type u_6} [uniform_space α] [uniform_space β] [uniform_space γ] [uniform_space δ] [uniform_space δ'] {f : α → β → γ} {ga : δ → α} {gb : δ' → β} (hf : uniform_continuous₂ f) (hga : uniform_continuous ga) (hgb : uniform_continuous gb) : uniform_continuous₂ (function.bicompl f ga gb) :=
  uniform_continuous.comp (uniform_continuous₂.uniform_continuous hf) (uniform_continuous.prod_map hga hgb)

theorem to_topological_space_subtype {α : Type u_1} [u : uniform_space α] {p : α → Prop} : uniform_space.to_topological_space = subtype.topological_space :=
  rfl

/-- Uniformity on a disjoint union. Entourages of the diagonal in the union are obtained
by taking independently an entourage of the diagonal in the first part, and an entourage of
the diagonal in the second part. -/
def uniform_space.core.sum {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] : uniform_space.core (α ⊕ β) :=
  uniform_space.core.mk'
    (filter.map (fun (p : α × α) => (sum.inl (prod.fst p), sum.inl (prod.snd p))) (uniformity α) ⊔
      filter.map (fun (p : β × β) => (sum.inr (prod.fst p), sum.inr (prod.snd p))) (uniformity β))
    sorry sorry sorry

/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage
of the diagonal. -/
theorem union_mem_uniformity_sum {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {a : set (α × α)} (ha : a ∈ uniformity α) {b : set (β × β)} (hb : b ∈ uniformity β) : (fun (p : α × α) => (sum.inl (prod.fst p), sum.inl (prod.snd p))) '' a ∪
    (fun (p : β × β) => (sum.inr (prod.fst p), sum.inr (prod.snd p))) '' b ∈
  uniform_space.core.uniformity uniform_space.core.sum := sorry

/- To prove that the topology defined by the uniform structure on the disjoint union coincides with
the disjoint union topology, we need two lemmas saying that open sets can be characterized by
the uniform structure -/

theorem uniformity_sum_of_open_aux {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {s : set (α ⊕ β)} (hs : is_open s) {x : α ⊕ β} (xs : x ∈ s) : (set_of fun (p : (α ⊕ β) × (α ⊕ β)) => prod.fst p = x → prod.snd p ∈ s) ∈
  uniform_space.core.uniformity uniform_space.core.sum := sorry

theorem open_of_uniformity_sum_aux {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {s : set (α ⊕ β)} (hs : ∀ (x : α ⊕ β),
  x ∈ s →
    (set_of fun (p : (α ⊕ β) × (α ⊕ β)) => prod.fst p = x → prod.snd p ∈ s) ∈
      uniform_space.core.uniformity uniform_space.core.sum) : is_open s := sorry

/- We can now define the uniform structure on the disjoint union -/

protected instance sum.uniform_space {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] : uniform_space (α ⊕ β) :=
  uniform_space.mk uniform_space.core.sum sorry

theorem sum.uniformity {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] : uniformity (α ⊕ β) =
  filter.map (fun (p : α × α) => (sum.inl (prod.fst p), sum.inl (prod.snd p))) (uniformity α) ⊔
    filter.map (fun (p : β × β) => (sum.inr (prod.fst p), sum.inr (prod.snd p))) (uniformity β) :=
  rfl

-- For a version of the Lebesgue number lemma assuming only a sequentially compact space,

-- see topology/sequences.lean

/-- Let `c : ι → set α` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `c i`. -/
theorem lebesgue_number_lemma {α : Type u} [uniform_space α] {s : set α} {ι : Sort u_1} {c : ι → set α} (hs : is_compact s) (hc₁ : ∀ (i : ι), is_open (c i)) (hc₂ : s ⊆ set.Union fun (i : ι) => c i) : ∃ (n : set (α × α)), ∃ (H : n ∈ uniformity α), ∀ (x : α), x ∈ s → ∃ (i : ι), (set_of fun (y : α) => (x, y) ∈ n) ⊆ c i := sorry

/-- Let `c : set (set α)` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `t ∈ c`. -/
theorem lebesgue_number_lemma_sUnion {α : Type u} [uniform_space α] {s : set α} {c : set (set α)} (hs : is_compact s) (hc₁ : ∀ (t : set α), t ∈ c → is_open t) (hc₂ : s ⊆ ⋃₀c) : ∃ (n : set (α × α)),
  ∃ (H : n ∈ uniformity α), ∀ (x : α) (H : x ∈ s), ∃ (t : set α), ∃ (H : t ∈ c), ∀ (y : α), (x, y) ∈ n → y ∈ t := sorry

/-!
### Expressing continuity properties in uniform spaces

We reformulate the various continuity properties of functions taking values in a uniform space
in terms of the uniformity in the target. Since the same lemmas (essentially with the same names)
also exist for metric spaces and emetric spaces (reformulating things in terms of the distance or
the edistance in the target), we put them in a namespace `uniform` here.

In the metric and emetric space setting, there are also similar lemmas where one assumes that
both the source and the target are metric spaces, reformulating things in terms of the distance
on both sides. These lemmas are generally written without primes, and the versions where only
the target is a metric space is primed. We follow the same convention here, thus giving lemmas
with primes.
-/

namespace uniform


theorem tendsto_nhds_right {α : Type u_1} {β : Type u_2} [uniform_space α] {f : filter β} {u : β → α} {a : α} : filter.tendsto u f (nhds a) ↔ filter.tendsto (fun (x : β) => (a, u x)) f (uniformity α) := sorry

theorem tendsto_nhds_left {α : Type u_1} {β : Type u_2} [uniform_space α] {f : filter β} {u : β → α} {a : α} : filter.tendsto u f (nhds a) ↔ filter.tendsto (fun (x : β) => (u x, a)) f (uniformity α) := sorry

theorem continuous_at_iff'_right {α : Type u_1} {β : Type u_2} [uniform_space α] [topological_space β] {f : β → α} {b : β} : continuous_at f b ↔ filter.tendsto (fun (x : β) => (f b, f x)) (nhds b) (uniformity α) := sorry

theorem continuous_at_iff'_left {α : Type u_1} {β : Type u_2} [uniform_space α] [topological_space β] {f : β → α} {b : β} : continuous_at f b ↔ filter.tendsto (fun (x : β) => (f x, f b)) (nhds b) (uniformity α) := sorry

theorem continuous_at_iff_prod {α : Type u_1} {β : Type u_2} [uniform_space α] [topological_space β] {f : β → α} {b : β} : continuous_at f b ↔ filter.tendsto (fun (x : β × β) => (f (prod.fst x), f (prod.snd x))) (nhds (b, b)) (uniformity α) := sorry

theorem continuous_within_at_iff'_right {α : Type u_1} {β : Type u_2} [uniform_space α] [topological_space β] {f : β → α} {b : β} {s : set β} : continuous_within_at f s b ↔ filter.tendsto (fun (x : β) => (f b, f x)) (nhds_within b s) (uniformity α) := sorry

theorem continuous_within_at_iff'_left {α : Type u_1} {β : Type u_2} [uniform_space α] [topological_space β] {f : β → α} {b : β} {s : set β} : continuous_within_at f s b ↔ filter.tendsto (fun (x : β) => (f x, f b)) (nhds_within b s) (uniformity α) := sorry

theorem continuous_on_iff'_right {α : Type u_1} {β : Type u_2} [uniform_space α] [topological_space β] {f : β → α} {s : set β} : continuous_on f s ↔ ∀ (b : β), b ∈ s → filter.tendsto (fun (x : β) => (f b, f x)) (nhds_within b s) (uniformity α) := sorry

theorem continuous_on_iff'_left {α : Type u_1} {β : Type u_2} [uniform_space α] [topological_space β] {f : β → α} {s : set β} : continuous_on f s ↔ ∀ (b : β), b ∈ s → filter.tendsto (fun (x : β) => (f x, f b)) (nhds_within b s) (uniformity α) := sorry

theorem continuous_iff'_right {α : Type u_1} {β : Type u_2} [uniform_space α] [topological_space β] {f : β → α} : continuous f ↔ ∀ (b : β), filter.tendsto (fun (x : β) => (f b, f x)) (nhds b) (uniformity α) :=
  iff.trans continuous_iff_continuous_at (forall_congr fun (b : β) => tendsto_nhds_right)

theorem continuous_iff'_left {α : Type u_1} {β : Type u_2} [uniform_space α] [topological_space β] {f : β → α} : continuous f ↔ ∀ (b : β), filter.tendsto (fun (x : β) => (f x, f b)) (nhds b) (uniformity α) :=
  iff.trans continuous_iff_continuous_at (forall_congr fun (b : β) => tendsto_nhds_left)

end uniform


theorem filter.tendsto.congr_uniformity {α : Type u_1} {β : Type u_2} [uniform_space β] {f : α → β} {g : α → β} {l : filter α} {b : β} (hf : filter.tendsto f l (nhds b)) (hg : filter.tendsto (fun (x : α) => (f x, g x)) l (uniformity β)) : filter.tendsto g l (nhds b) :=
  iff.mpr uniform.tendsto_nhds_right (filter.tendsto.uniformity_trans (iff.mp uniform.tendsto_nhds_right hf) hg)

theorem uniform.tendsto_congr {α : Type u_1} {β : Type u_2} [uniform_space β] {f : α → β} {g : α → β} {l : filter α} {b : β} (hfg : filter.tendsto (fun (x : α) => (f x, g x)) l (uniformity β)) : filter.tendsto f l (nhds b) ↔ filter.tendsto g l (nhds b) :=
  { mp := fun (h : filter.tendsto f l (nhds b)) => filter.tendsto.congr_uniformity h hfg,
    mpr :=
      fun (h : filter.tendsto g l (nhds b)) => filter.tendsto.congr_uniformity h (filter.tendsto.uniformity_symm hfg) }

