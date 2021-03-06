/-
Copyright (c) 2017 Johannes HΓΆlzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes HΓΆlzl, Mario Carneiro, Patrick Massot
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

A uniform structure on a type `X` is a filter `π€ X` on `X Γ X` satisfying some conditions
which makes it reasonable to say that `βαΆ  (p : X Γ X) in π€ X, ...` means
"for all p.1 and p.2 in X close enough, ...". Elements of this filter are called entourages
of `X`. The two main examples are:

* If `X` is a metric space, `V β π€ X β β Ξ΅ > 0, { p | dist p.1 p.2 < Ξ΅ } β V`
* If `G` is an additive topological group, `V β π€ G β β U β π (0 : G), {p | p.2 - p.1 β U} β V`

Those examples are generalizations in two different directions of the elementary example where
`X = β` and `V β π€ β β β Ξ΅ > 0, { p | |p.2 - p.1| < Ξ΅ } β V` which features both the topological
group structure on `β` and its metric space structure.

Each uniform structure on `X` induces a topology on `X` characterized by

> `nhds_eq_comap_uniformity : β {x : X}, π x = comap (prod.mk x) (π€ X)`

where `prod.mk x : X β X Γ X := (Ξ» y, (x, y))` is the partial evaluation of the product
constructor.

The dictionary with metric spaces includes:
* an upper bound for `dist x y` translates into `(x, y) β V` for some `V β π€ X`
* a ball `ball x r` roughly corresponds to `uniform_space.ball x V := {y | (x, y) β V}`
  for some `V β π€ X`, but the later is more general (it includes in
  particular both open and closed balls for suitable `V`).
  In particular we have:
  `is_open_iff_ball_subset {s : set X} : is_open s β β x β s, β V β π€ X, ball x V β s`

The triangle inequality is abstracted to a statement involving the composition of relations in `X`.
First note that the triangle inequality in a metric space is equivalent to
`β (x y z : X) (r r' : β), dist x y β€ r β dist y z β€ r' β dist x z β€ r + r'`.
Then, for any `V` and `W` with type `set (X Γ X)`, the composition `V β W : set (X Γ X)` is
defined as `{ p : X Γ X | β z, (p.1, z) β V β§ (z, p.2) β W }`.
In the metric space case, if `V = { p | dist p.1 p.2 β€ r }` and `W = { p | dist p.1 p.2 β€ r' }`
then the triangle inequality, as reformulated above, says `V β W` is contained in
`{p | dist p.1 p.2 β€ r + r'}` which is the entourage associated to the radius `r + r'`.
In general we have `mem_ball_comp (h : y β ball x V) (h' : z β ball y W) : z β ball x (V β W)`.
Note that this discussion does not depend on any axiom imposed on the uniformity filter,
it is simply captured by the definition of composition.

The uniform space axioms ask the filter `π€ X` to satisfy the following:
* every `V β π€ X` contains the diagonal `id_rel = { p | p.1 = p.2 }`. This abstracts the fact
  that `dist x x β€ r` for every non-negative radius `r` in the metric space case and also that
  `x - x` belongs to every neighborhood of zero in the topological group case.
* `V β π€ X β prod.swap '' V β π€ X`. This is tightly related the fact that `dist x y = dist y x`
  in a metric space, and to continuity of negation in the topological group case.
* `β V β π€ X, β W β π€ X, W β W β V`. In the metric space case, it corresponds
  to cutting the radius of a ball in half and applying the triangle inequality.
  In the topological group case, it comes from continuity of addition at `(0, 0)`.

These three axioms are stated more abstractly in the definition below, in terms of
operations on filters, without directly manipulating entourages.

##Β Main definitions

* `uniform_space X` is a uniform space structure on a type `X`
* `uniform_continuous f` is a predicate saying a function `f : Ξ± β Ξ²` between uniform spaces
  is uniformly continuous : `β r β π€ Ξ², βαΆ  (x : Ξ± Γ Ξ±) in π€ Ξ±, (f x.1, f x.2) β r`

In this file we also define a complete lattice structure on the type `uniform_space X`
of uniform structures on `X`, as well as the pullback (`uniform_space.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notations

Localized in `uniformity`, we have the notation `π€ X` for the uniformity on a uniform space `X`,
and `β` for composition of relations, seen as terms with type `set (X Γ X)`.

## Implementation notes

There is already a theory of relations in `data/rel.lean` where the main definition is
`def rel (Ξ± Ξ² : Type*) := Ξ± β Ξ² β Prop`.
The relations used in the current file involve only one type, but this is not the reason why
we don't reuse `data/rel.lean`. We use `set (Ξ± Γ Ξ±)`
instead of `rel Ξ± Ξ±` because we really need sets to use the filter library, and elements
of filters on `Ξ± Γ Ξ±` have type `set (Ξ± Γ Ξ±)`.

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
### Relations, seen as `set (Ξ± Γ Ξ±)`
-/

/-- The identity relation, or the graph of the identity function -/
def id_rel {Ξ± : Type u_1} : set (Ξ± Γ Ξ±) :=
  set_of fun (p : Ξ± Γ Ξ±) => prod.fst p = prod.snd p

@[simp] theorem mem_id_rel {Ξ± : Type u_1} {a : Ξ±} {b : Ξ±} : (a, b) β id_rel β a = b :=
  iff.rfl

@[simp] theorem id_rel_subset {Ξ± : Type u_1} {s : set (Ξ± Γ Ξ±)} : id_rel β s β β (a : Ξ±), (a, a) β s := sorry

/-- The composition of relations -/
def comp_rel {Ξ± : Type u} (rβ : set (Ξ± Γ Ξ±)) (rβ : set (Ξ± Γ Ξ±)) : set (Ξ± Γ Ξ±) :=
  set_of fun (p : Ξ± Γ Ξ±) => β (z : Ξ±), (prod.fst p, z) β rβ β§ (z, prod.snd p) β rβ

@[simp] theorem mem_comp_rel {Ξ± : Type u_1} {rβ : set (Ξ± Γ Ξ±)} {rβ : set (Ξ± Γ Ξ±)} {x : Ξ±} {y : Ξ±} : (x, y) β comp_rel rβ rβ β β (z : Ξ±), (x, z) β rβ β§ (z, y) β rβ :=
  iff.rfl

@[simp] theorem swap_id_rel {Ξ± : Type u_1} : prod.swap '' id_rel = id_rel := sorry

theorem monotone_comp_rel {Ξ± : Type u_1} {Ξ² : Type u_2} [preorder Ξ²] {f : Ξ² β set (Ξ± Γ Ξ±)} {g : Ξ² β set (Ξ± Γ Ξ±)} (hf : monotone f) (hg : monotone g) : monotone fun (x : Ξ²) => comp_rel (f x) (g x) := sorry

theorem comp_rel_mono {Ξ± : Type u_1} {f : set (Ξ± Γ Ξ±)} {g : set (Ξ± Γ Ξ±)} {h : set (Ξ± Γ Ξ±)} {k : set (Ξ± Γ Ξ±)} (hβ : f β h) (hβ : g β k) : comp_rel f g β comp_rel h k := sorry

theorem prod_mk_mem_comp_rel {Ξ± : Type u_1} {a : Ξ±} {b : Ξ±} {c : Ξ±} {s : set (Ξ± Γ Ξ±)} {t : set (Ξ± Γ Ξ±)} (hβ : (a, c) β s) (hβ : (c, b) β t) : (a, b) β comp_rel s t :=
  Exists.intro c { left := hβ, right := hβ }

@[simp] theorem id_comp_rel {Ξ± : Type u_1} {r : set (Ξ± Γ Ξ±)} : comp_rel id_rel r = r := sorry

theorem comp_rel_assoc {Ξ± : Type u_1} {r : set (Ξ± Γ Ξ±)} {s : set (Ξ± Γ Ξ±)} {t : set (Ξ± Γ Ξ±)} : comp_rel (comp_rel r s) t = comp_rel r (comp_rel s t) := sorry

theorem subset_comp_self {Ξ± : Type u_1} {s : set (Ξ± Γ Ξ±)} (h : id_rel β s) : s β comp_rel s s := sorry

/-- The relation is invariant under swapping factors. -/
def symmetric_rel {Ξ± : Type u_1} (V : set (Ξ± Γ Ξ±)) :=
  prod.swap β»ΒΉ' V = V

/-- The maximal symmetric relation contained in a given relation. -/
def symmetrize_rel {Ξ± : Type u_1} (V : set (Ξ± Γ Ξ±)) : set (Ξ± Γ Ξ±) :=
  V β© prod.swap β»ΒΉ' V

theorem symmetric_symmetrize_rel {Ξ± : Type u_1} (V : set (Ξ± Γ Ξ±)) : symmetric_rel (symmetrize_rel V) := sorry

theorem symmetrize_rel_subset_self {Ξ± : Type u_1} (V : set (Ξ± Γ Ξ±)) : symmetrize_rel V β V :=
  set.sep_subset V fun (a : Ξ± Γ Ξ±) => a β prod.swap β»ΒΉ' V

theorem symmetrize_mono {Ξ± : Type u_1} {V : set (Ξ± Γ Ξ±)} {W : set (Ξ± Γ Ξ±)} (h : V β W) : symmetrize_rel V β symmetrize_rel W :=
  set.inter_subset_inter h (set.preimage_mono h)

theorem symmetric_rel_inter {Ξ± : Type u_1} {U : set (Ξ± Γ Ξ±)} {V : set (Ξ± Γ Ξ±)} (hU : symmetric_rel U) (hV : symmetric_rel V) : symmetric_rel (U β© V) := sorry

/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure uniform_space.core (Ξ± : Type u) 
where
  uniformity : filter (Ξ± Γ Ξ±)
  refl : filter.principal id_rel β€ uniformity
  symm : filter.tendsto prod.swap uniformity uniformity
  comp : (filter.lift' uniformity fun (s : set (Ξ± Γ Ξ±)) => comp_rel s s) β€ uniformity

/-- An alternative constructor for `uniform_space.core`. This version unfolds various
`filter`-related definitions. -/
def uniform_space.core.mk' {Ξ± : Type u} (U : filter (Ξ± Γ Ξ±)) (refl : β (r : set (Ξ± Γ Ξ±)), r β U β β (x : Ξ±), (x, x) β r) (symm : β (r : set (Ξ± Γ Ξ±)), r β U β prod.swap β»ΒΉ' r β U) (comp : β (r : set (Ξ± Γ Ξ±)) (H : r β U), β (t : set (Ξ± Γ Ξ±)), β (H : t β U), comp_rel t t β r) : uniform_space.core Ξ± :=
  uniform_space.core.mk U sorry symm sorry

/-- A uniform space generates a topological space -/
def uniform_space.core.to_topological_space {Ξ± : Type u} (u : uniform_space.core Ξ±) : topological_space Ξ± :=
  topological_space.mk
    (fun (s : set Ξ±) =>
      β (x : Ξ±), x β s β (set_of fun (p : Ξ± Γ Ξ±) => prod.fst p = x β prod.snd p β s) β uniform_space.core.uniformity u)
    sorry sorry sorry

theorem uniform_space.core_eq {Ξ± : Type u_1} {uβ : uniform_space.core Ξ±} {uβ : uniform_space.core Ξ±} : uniform_space.core.uniformity uβ = uniform_space.core.uniformity uβ β uβ = uβ := sorry

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
  metric space. It consists of a filter on `Ξ± Γ Ξ±` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
class uniform_space (Ξ± : Type u) 
extends uniform_space.core Ξ±, topological_space Ξ±
where
  is_open_uniformity : β (s : set Ξ±),
  topological_space.is_open _to_topological_space s β
    β (x : Ξ±),
      x β s β (set_of fun (p : Ξ± Γ Ξ±) => prod.fst p = x β prod.snd p β s) β uniform_space.core.uniformity _to_core

/-- Alternative constructor for `uniform_space Ξ±` when a topology is already given. -/
def uniform_space.mk' {Ξ± : Type u_1} (t : topological_space Ξ±) (c : uniform_space.core Ξ±) (is_open_uniformity : β (s : set Ξ±),
  topological_space.is_open t s β
    β (x : Ξ±), x β s β (set_of fun (p : Ξ± Γ Ξ±) => prod.fst p = x β prod.snd p β s) β uniform_space.core.uniformity c) : uniform_space Ξ± :=
  uniform_space.mk c is_open_uniformity

/-- Construct a `uniform_space` from a `uniform_space.core`. -/
def uniform_space.of_core {Ξ± : Type u} (u : uniform_space.core Ξ±) : uniform_space Ξ± :=
  uniform_space.mk u sorry

/-- Construct a `uniform_space` from a `u : uniform_space.core` and a `topological_space` structure
that is equal to `u.to_topological_space`. -/
def uniform_space.of_core_eq {Ξ± : Type u} (u : uniform_space.core Ξ±) (t : topological_space Ξ±) (h : t = uniform_space.core.to_topological_space u) : uniform_space Ξ± :=
  uniform_space.mk u sorry

theorem uniform_space.to_core_to_topological_space {Ξ± : Type u_1} (u : uniform_space Ξ±) : uniform_space.core.to_topological_space uniform_space.to_core = uniform_space.to_topological_space := sorry

theorem uniform_space_eq {Ξ± : Type u_1} {uβ : uniform_space Ξ±} {uβ : uniform_space Ξ±} : uniform_space.core.uniformity uniform_space.to_core = uniform_space.core.uniformity uniform_space.to_core β uβ = uβ := sorry

theorem uniform_space.of_core_eq_to_core {Ξ± : Type u_1} (u : uniform_space Ξ±) (t : topological_space Ξ±) (h : t = uniform_space.core.to_topological_space uniform_space.to_core) : uniform_space.of_core_eq uniform_space.to_core t h = u :=
  uniform_space_eq rfl

/-- The uniformity is a filter on Ξ± Γ Ξ± (inferred from an ambient uniform space
  structure on Ξ±). -/
def uniformity (Ξ± : Type u) [uniform_space Ξ±] : filter (Ξ± Γ Ξ±) :=
  uniform_space.core.uniformity uniform_space.to_core

theorem is_open_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {s : set Ξ±} : is_open s β β (x : Ξ±), x β s β (set_of fun (p : Ξ± Γ Ξ±) => prod.fst p = x β prod.snd p β s) β uniformity Ξ± :=
  uniform_space.is_open_uniformity s

theorem refl_le_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] : filter.principal id_rel β€ uniformity Ξ± :=
  uniform_space.core.refl uniform_space.to_core

theorem refl_mem_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {x : Ξ±} {s : set (Ξ± Γ Ξ±)} (h : s β uniformity Ξ±) : (x, x) β s :=
  refl_le_uniformity h rfl

theorem symm_le_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] : filter.map prod.swap (uniformity Ξ±) β€ uniformity Ξ± :=
  uniform_space.core.symm uniform_space.to_core

theorem comp_le_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] : (filter.lift' (uniformity Ξ±) fun (s : set (Ξ± Γ Ξ±)) => comp_rel s s) β€ uniformity Ξ± :=
  uniform_space.core.comp uniform_space.to_core

theorem tendsto_swap_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] : filter.tendsto prod.swap (uniformity Ξ±) (uniformity Ξ±) :=
  symm_le_uniformity

theorem comp_mem_uniformity_sets {Ξ± : Type u_1} [uniform_space Ξ±] {s : set (Ξ± Γ Ξ±)} (hs : s β uniformity Ξ±) : β (t : set (Ξ± Γ Ξ±)), β (H : t β uniformity Ξ±), comp_rel t t β s :=
  (fun (this : s β filter.lift' (uniformity Ξ±) fun (t : set (Ξ± Γ Ξ±)) => comp_rel t t) =>
      iff.mp (filter.mem_lift'_sets (monotone_comp_rel monotone_id monotone_id)) this)
    (comp_le_uniformity hs)

/-- Relation `Ξ» f g, tendsto (Ξ» x, (f x, g x)) l (π€ Ξ±)` is transitive. -/
theorem filter.tendsto.uniformity_trans {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {l : filter Ξ²} {fβ : Ξ² β Ξ±} {fβ : Ξ² β Ξ±} {fβ : Ξ² β Ξ±} (hββ : filter.tendsto (fun (x : Ξ²) => (fβ x, fβ x)) l (uniformity Ξ±)) (hββ : filter.tendsto (fun (x : Ξ²) => (fβ x, fβ x)) l (uniformity Ξ±)) : filter.tendsto (fun (x : Ξ²) => (fβ x, fβ x)) l (uniformity Ξ±) := sorry

/-- Relation `Ξ» f g, tendsto (Ξ» x, (f x, g x)) l (π€ Ξ±)` is symmetric -/
theorem filter.tendsto.uniformity_symm {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {l : filter Ξ²} {f : Ξ² β Ξ± Γ Ξ±} (h : filter.tendsto f l (uniformity Ξ±)) : filter.tendsto (fun (x : Ξ²) => (prod.snd (f x), prod.fst (f x))) l (uniformity Ξ±) :=
  filter.tendsto.comp tendsto_swap_uniformity h

/-- Relation `Ξ» f g, tendsto (Ξ» x, (f x, g x)) l (π€ Ξ±)` is reflexive. -/
theorem tendsto_diag_uniformity {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] (f : Ξ² β Ξ±) (l : filter Ξ²) : filter.tendsto (fun (x : Ξ²) => (f x, f x)) l (uniformity Ξ±) :=
  fun (s : set (Ξ± Γ Ξ±)) (hs : s β uniformity Ξ±) =>
    iff.mpr filter.mem_map (filter.univ_mem_sets' fun (x : Ξ²) => refl_mem_uniformity hs)

theorem tendsto_const_uniformity {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {a : Ξ±} {f : filter Ξ²} : filter.tendsto (fun (_x : Ξ²) => (a, a)) f (uniformity Ξ±) :=
  tendsto_diag_uniformity (fun (_x : Ξ²) => a) f

theorem symm_of_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {s : set (Ξ± Γ Ξ±)} (hs : s β uniformity Ξ±) : β (t : set (Ξ± Γ Ξ±)), β (H : t β uniformity Ξ±), (β (a b : Ξ±), (a, b) β t β (b, a) β t) β§ t β s := sorry

theorem comp_symm_of_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {s : set (Ξ± Γ Ξ±)} (hs : s β uniformity Ξ±) : β (t : set (Ξ± Γ Ξ±)), β (H : t β uniformity Ξ±), (β {a b : Ξ±}, (a, b) β t β (b, a) β t) β§ comp_rel t t β s := sorry

theorem uniformity_le_symm {Ξ± : Type u_1} [uniform_space Ξ±] : uniformity Ξ± β€ prod.swap <$> uniformity Ξ± :=
  eq.mpr (id (Eq._oldrec (Eq.refl (uniformity Ξ± β€ prod.swap <$> uniformity Ξ±)) filter.map_swap_eq_comap_swap))
    (iff.mp filter.map_le_iff_le_comap tendsto_swap_uniformity)

theorem uniformity_eq_symm {Ξ± : Type u_1} [uniform_space Ξ±] : uniformity Ξ± = prod.swap <$> uniformity Ξ± :=
  le_antisymm uniformity_le_symm symm_le_uniformity

theorem symmetrize_mem_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {V : set (Ξ± Γ Ξ±)} (h : V β uniformity Ξ±) : symmetrize_rel V β uniformity Ξ± := sorry

theorem uniformity_lift_le_swap {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {g : set (Ξ± Γ Ξ±) β filter Ξ²} {f : filter Ξ²} (hg : monotone g) (h : (filter.lift (uniformity Ξ±) fun (s : set (Ξ± Γ Ξ±)) => g (prod.swap β»ΒΉ' s)) β€ f) : filter.lift (uniformity Ξ±) g β€ f := sorry

theorem uniformity_lift_le_comp {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {f : set (Ξ± Γ Ξ±) β filter Ξ²} (h : monotone f) : (filter.lift (uniformity Ξ±) fun (s : set (Ξ± Γ Ξ±)) => f (comp_rel s s)) β€ filter.lift (uniformity Ξ±) f := sorry

theorem comp_le_uniformity3 {Ξ± : Type u_1} [uniform_space Ξ±] : (filter.lift' (uniformity Ξ±) fun (s : set (Ξ± Γ Ξ±)) => comp_rel s (comp_rel s s)) β€ uniformity Ξ± := sorry

theorem comp_symm_mem_uniformity_sets {Ξ± : Type u_1} [uniform_space Ξ±] {s : set (Ξ± Γ Ξ±)} (hs : s β uniformity Ξ±) : β (t : set (Ξ± Γ Ξ±)), β (H : t β uniformity Ξ±), symmetric_rel t β§ comp_rel t t β s := sorry

theorem subset_comp_self_of_mem_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {s : set (Ξ± Γ Ξ±)} (h : s β uniformity Ξ±) : s β comp_rel s s :=
  subset_comp_self (refl_le_uniformity h)

theorem comp_comp_symm_mem_uniformity_sets {Ξ± : Type u_1} [uniform_space Ξ±] {s : set (Ξ± Γ Ξ±)} (hs : s β uniformity Ξ±) : β (t : set (Ξ± Γ Ξ±)), β (H : t β uniformity Ξ±), symmetric_rel t β§ comp_rel (comp_rel t t) t β s := sorry

/-!
###Β Balls in uniform spaces
-/

/-- The ball around `(x : Ξ²)` with respect to `(V : set (Ξ² Γ Ξ²))`. Intended to be
used for `V β π€ Ξ²`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`.  -/
def uniform_space.ball {Ξ² : Type u_2} (x : Ξ²) (V : set (Ξ² Γ Ξ²)) : set Ξ² :=
  Prod.mk x β»ΒΉ' V

theorem uniform_space.mem_ball_self {Ξ± : Type u_1} [uniform_space Ξ±] (x : Ξ±) {V : set (Ξ± Γ Ξ±)} (hV : V β uniformity Ξ±) : x β uniform_space.ball x V :=
  refl_mem_uniformity hV

/-- The triangle inequality for `uniform_space.ball` -/
theorem mem_ball_comp {Ξ² : Type u_2} {V : set (Ξ² Γ Ξ²)} {W : set (Ξ² Γ Ξ²)} {x : Ξ²} {y : Ξ²} {z : Ξ²} (h : y β uniform_space.ball x V) (h' : z β uniform_space.ball y W) : z β uniform_space.ball x (comp_rel V W) :=
  prod_mk_mem_comp_rel h h'

theorem ball_subset_of_comp_subset {Ξ² : Type u_2} {V : set (Ξ² Γ Ξ²)} {W : set (Ξ² Γ Ξ²)} {x : Ξ²} {y : Ξ²} (h : x β uniform_space.ball y W) (h' : comp_rel W W β V) : uniform_space.ball x W β uniform_space.ball y V :=
  fun (z : Ξ²) (z_in : z β uniform_space.ball x W) => h' (mem_ball_comp h z_in)

theorem ball_mono {Ξ² : Type u_2} {V : set (Ξ² Γ Ξ²)} {W : set (Ξ² Γ Ξ²)} (h : V β W) (x : Ξ²) : uniform_space.ball x V β uniform_space.ball x W :=
  id fun (a : Ξ²) (αΎ° : a β uniform_space.ball x V) => h αΎ°

theorem mem_ball_symmetry {Ξ² : Type u_2} {V : set (Ξ² Γ Ξ²)} (hV : symmetric_rel V) {x : Ξ²} {y : Ξ²} : x β uniform_space.ball y V β y β uniform_space.ball x V := sorry

theorem ball_eq_of_symmetry {Ξ² : Type u_2} {V : set (Ξ² Γ Ξ²)} (hV : symmetric_rel V) {x : Ξ²} : uniform_space.ball x V = set_of fun (y : Ξ²) => (y, x) β V := sorry

theorem mem_comp_of_mem_ball {Ξ² : Type u_2} {V : set (Ξ² Γ Ξ²)} {W : set (Ξ² Γ Ξ²)} {x : Ξ²} {y : Ξ²} {z : Ξ²} (hV : symmetric_rel V) (hx : x β uniform_space.ball z V) (hy : y β uniform_space.ball z W) : (x, y) β comp_rel V W :=
  Exists.intro z
    { left := eq.mp (Eq._oldrec (Eq.refl (x β uniform_space.ball z V)) (propext (mem_ball_symmetry hV))) hx, right := hy }

theorem uniform_space.is_open_ball {Ξ± : Type u_1} [uniform_space Ξ±] (x : Ξ±) {V : set (Ξ± Γ Ξ±)} (hV : is_open V) : is_open (uniform_space.ball x V) :=
  is_open.preimage (continuous.prod_mk continuous_const continuous_id) hV

theorem mem_comp_comp {Ξ² : Type u_2} {V : set (Ξ² Γ Ξ²)} {W : set (Ξ² Γ Ξ²)} {M : set (Ξ² Γ Ξ²)} (hW' : symmetric_rel W) {p : Ξ² Γ Ξ²} : p β comp_rel (comp_rel V M) W β
  set.nonempty (set.prod (uniform_space.ball (prod.fst p) V) (uniform_space.ball (prod.snd p) W) β© M) := sorry

/-!
### Neighborhoods in uniform spaces
-/

theorem mem_nhds_uniformity_iff_right {Ξ± : Type u_1} [uniform_space Ξ±] {x : Ξ±} {s : set Ξ±} : s β nhds x β (set_of fun (p : Ξ± Γ Ξ±) => prod.fst p = x β prod.snd p β s) β uniformity Ξ± := sorry

theorem mem_nhds_uniformity_iff_left {Ξ± : Type u_1} [uniform_space Ξ±] {x : Ξ±} {s : set Ξ±} : s β nhds x β (set_of fun (p : Ξ± Γ Ξ±) => prod.snd p = x β prod.fst p β s) β uniformity Ξ± := sorry

theorem nhds_eq_comap_uniformity_aux {Ξ± : Type u} {x : Ξ±} {s : set Ξ±} {F : filter (Ξ± Γ Ξ±)} : (set_of fun (p : Ξ± Γ Ξ±) => prod.fst p = x β prod.snd p β s) β F β s β filter.comap (Prod.mk x) F := sorry

theorem nhds_eq_comap_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {x : Ξ±} : nhds x = filter.comap (Prod.mk x) (uniformity Ξ±) := sorry

theorem is_open_iff_ball_subset {Ξ± : Type u_1} [uniform_space Ξ±] {s : set Ξ±} : is_open s β β (x : Ξ±) (H : x β s), β (V : set (Ξ± Γ Ξ±)), β (H : V β uniformity Ξ±), uniform_space.ball x V β s := sorry

theorem nhds_basis_uniformity' {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {p : Ξ² β Prop} {s : Ξ² β set (Ξ± Γ Ξ±)} (h : filter.has_basis (uniformity Ξ±) p s) {x : Ξ±} : filter.has_basis (nhds x) p fun (i : Ξ²) => uniform_space.ball x (s i) := sorry

theorem nhds_basis_uniformity {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {p : Ξ² β Prop} {s : Ξ² β set (Ξ± Γ Ξ±)} (h : filter.has_basis (uniformity Ξ±) p s) {x : Ξ±} : filter.has_basis (nhds x) p fun (i : Ξ²) => set_of fun (y : Ξ±) => (y, x) β s i := sorry

theorem uniform_space.mem_nhds_iff {Ξ± : Type u_1} [uniform_space Ξ±] {x : Ξ±} {s : set Ξ±} : s β nhds x β β (V : set (Ξ± Γ Ξ±)), β (H : V β uniformity Ξ±), uniform_space.ball x V β s := sorry

theorem uniform_space.ball_mem_nhds {Ξ± : Type u_1} [uniform_space Ξ±] (x : Ξ±) {V : set (Ξ± Γ Ξ±)} (V_in : V β uniformity Ξ±) : uniform_space.ball x V β nhds x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (uniform_space.ball x V β nhds x)) (propext uniform_space.mem_nhds_iff)))
    (Exists.intro V (Exists.intro V_in (set.subset.refl (uniform_space.ball x V))))

theorem uniform_space.mem_nhds_iff_symm {Ξ± : Type u_1} [uniform_space Ξ±] {x : Ξ±} {s : set Ξ±} : s β nhds x β β (V : set (Ξ± Γ Ξ±)), β (H : V β uniformity Ξ±), symmetric_rel V β§ uniform_space.ball x V β s := sorry

theorem uniform_space.has_basis_nhds {Ξ± : Type u_1} [uniform_space Ξ±] (x : Ξ±) : filter.has_basis (nhds x) (fun (s : set (Ξ± Γ Ξ±)) => s β uniformity Ξ± β§ symmetric_rel s)
  fun (s : set (Ξ± Γ Ξ±)) => uniform_space.ball x s := sorry

theorem uniform_space.has_basis_nhds_prod {Ξ± : Type u_1} [uniform_space Ξ±] (x : Ξ±) (y : Ξ±) : filter.has_basis (nhds (x, y)) (fun (s : set (Ξ± Γ Ξ±)) => s β uniformity Ξ± β§ symmetric_rel s)
  fun (s : set (Ξ± Γ Ξ±)) => set.prod (uniform_space.ball x s) (uniform_space.ball y s) := sorry

theorem nhds_eq_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {x : Ξ±} : nhds x = filter.lift' (uniformity Ξ±) (uniform_space.ball x) :=
  filter.has_basis.eq_binfi (nhds_basis_uniformity' (filter.basis_sets (uniformity Ξ±)))

theorem mem_nhds_left {Ξ± : Type u_1} [uniform_space Ξ±] (x : Ξ±) {s : set (Ξ± Γ Ξ±)} (h : s β uniformity Ξ±) : (set_of fun (y : Ξ±) => (x, y) β s) β nhds x :=
  uniform_space.ball_mem_nhds x h

theorem mem_nhds_right {Ξ± : Type u_1} [uniform_space Ξ±] (y : Ξ±) {s : set (Ξ± Γ Ξ±)} (h : s β uniformity Ξ±) : (set_of fun (x : Ξ±) => (x, y) β s) β nhds y :=
  mem_nhds_left y (symm_le_uniformity h)

theorem tendsto_right_nhds_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {a : Ξ±} : filter.tendsto (fun (a' : Ξ±) => (a', a)) (nhds a) (uniformity Ξ±) :=
  fun (s : set (Ξ± Γ Ξ±)) => mem_nhds_right a

theorem tendsto_left_nhds_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {a : Ξ±} : filter.tendsto (fun (a' : Ξ±) => (a, a')) (nhds a) (uniformity Ξ±) :=
  fun (s : set (Ξ± Γ Ξ±)) => mem_nhds_left a

theorem lift_nhds_left {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {x : Ξ±} {g : set Ξ± β filter Ξ²} (hg : monotone g) : filter.lift (nhds x) g = filter.lift (uniformity Ξ±) fun (s : set (Ξ± Γ Ξ±)) => g (set_of fun (y : Ξ±) => (x, y) β s) := sorry

theorem lift_nhds_right {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {x : Ξ±} {g : set Ξ± β filter Ξ²} (hg : monotone g) : filter.lift (nhds x) g = filter.lift (uniformity Ξ±) fun (s : set (Ξ± Γ Ξ±)) => g (set_of fun (y : Ξ±) => (y, x) β s) := sorry

theorem nhds_nhds_eq_uniformity_uniformity_prod {Ξ± : Type u_1} [uniform_space Ξ±] {a : Ξ±} {b : Ξ±} : filter.prod (nhds a) (nhds b) =
  filter.lift (uniformity Ξ±)
    fun (s : set (Ξ± Γ Ξ±)) =>
      filter.lift' (uniformity Ξ±)
        fun (t : set (Ξ± Γ Ξ±)) => set.prod (set_of fun (y : Ξ±) => (y, a) β s) (set_of fun (y : Ξ±) => (b, y) β t) := sorry

theorem nhds_eq_uniformity_prod {Ξ± : Type u_1} [uniform_space Ξ±] {a : Ξ±} {b : Ξ±} : nhds (a, b) =
  filter.lift' (uniformity Ξ±)
    fun (s : set (Ξ± Γ Ξ±)) => set.prod (set_of fun (y : Ξ±) => (y, a) β s) (set_of fun (y : Ξ±) => (b, y) β s) := sorry

theorem nhdset_of_mem_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {d : set (Ξ± Γ Ξ±)} (s : set (Ξ± Γ Ξ±)) (hd : d β uniformity Ξ±) : β (t : set (Ξ± Γ Ξ±)),
  is_open t β§
    s β t β§ t β set_of fun (p : Ξ± Γ Ξ±) => β (x : Ξ±), β (y : Ξ±), (prod.fst p, x) β d β§ (x, y) β s β§ (y, prod.snd p) β d := sorry

/-- Entourages are neighborhoods of the diagonal. -/
theorem nhds_le_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] (x : Ξ±) : nhds (x, x) β€ uniformity Ξ± := sorry

/-- Entourages are neighborhoods of the diagonal. -/
theorem supr_nhds_le_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] : (supr fun (x : Ξ±) => nhds (x, x)) β€ uniformity Ξ± :=
  supr_le nhds_le_uniformity

/-!
### Closure and interior in uniform spaces
-/

theorem closure_eq_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] (s : set (Ξ± Γ Ξ±)) : closure s =
  set.Inter
    fun (V : set (Ξ± Γ Ξ±)) =>
      set.Inter
        fun (H : V β set_of fun (V : set (Ξ± Γ Ξ±)) => V β uniformity Ξ± β§ symmetric_rel V) => comp_rel (comp_rel V s) V := sorry

theorem uniformity_has_basis_closed {Ξ± : Type u_1} [uniform_space Ξ±] : filter.has_basis (uniformity Ξ±) (fun (V : set (Ξ± Γ Ξ±)) => V β uniformity Ξ± β§ is_closed V) id := sorry

/-- Closed entourages form a basis of the uniformity filter. -/
theorem uniformity_has_basis_closure {Ξ± : Type u_1} [uniform_space Ξ±] : filter.has_basis (uniformity Ξ±) (fun (V : set (Ξ± Γ Ξ±)) => V β uniformity Ξ±) closure := sorry

theorem closure_eq_inter_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {t : set (Ξ± Γ Ξ±)} : closure t = set.Inter fun (d : set (Ξ± Γ Ξ±)) => set.Inter fun (H : d β uniformity Ξ±) => comp_rel d (comp_rel t d) := sorry

theorem uniformity_eq_uniformity_closure {Ξ± : Type u_1} [uniform_space Ξ±] : uniformity Ξ± = filter.lift' (uniformity Ξ±) closure := sorry

theorem uniformity_eq_uniformity_interior {Ξ± : Type u_1} [uniform_space Ξ±] : uniformity Ξ± = filter.lift' (uniformity Ξ±) interior := sorry

theorem interior_mem_uniformity {Ξ± : Type u_1} [uniform_space Ξ±] {s : set (Ξ± Γ Ξ±)} (hs : s β uniformity Ξ±) : interior s β uniformity Ξ± :=
  eq.mpr (id (Eq._oldrec (Eq.refl (interior s β uniformity Ξ±)) uniformity_eq_uniformity_interior)) (filter.mem_lift' hs)

theorem mem_uniformity_is_closed {Ξ± : Type u_1} [uniform_space Ξ±] {s : set (Ξ± Γ Ξ±)} (h : s β uniformity Ξ±) : β (t : set (Ξ± Γ Ξ±)), β (H : t β uniformity Ξ±), is_closed t β§ t β s := sorry

/-- The uniform neighborhoods of all points of a dense set cover the whole space. -/
theorem dense.bUnion_uniformity_ball {Ξ± : Type u_1} [uniform_space Ξ±] {s : set Ξ±} {U : set (Ξ± Γ Ξ±)} (hs : dense s) (hU : U β uniformity Ξ±) : (set.Union fun (x : Ξ±) => set.Union fun (H : x β s) => uniform_space.ball x U) = set.univ := sorry

/-!
### Uniformity bases
-/

/-- Open elements of `π€ Ξ±` form a basis of `π€ Ξ±`. -/
theorem uniformity_has_basis_open {Ξ± : Type u_1} [uniform_space Ξ±] : filter.has_basis (uniformity Ξ±) (fun (V : set (Ξ± Γ Ξ±)) => V β uniformity Ξ± β§ is_open V) id := sorry

theorem filter.has_basis.mem_uniformity_iff {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {p : Ξ² β Prop} {s : Ξ² β set (Ξ± Γ Ξ±)} (h : filter.has_basis (uniformity Ξ±) p s) {t : set (Ξ± Γ Ξ±)} : t β uniformity Ξ± β β (i : Ξ²), β (hi : p i), β (a b : Ξ±), (a, b) β s i β (a, b) β t := sorry

/-- Symmetric entourages form a basis of `π€ Ξ±` -/
theorem uniform_space.has_basis_symmetric {Ξ± : Type u_1} [uniform_space Ξ±] : filter.has_basis (uniformity Ξ±) (fun (s : set (Ξ± Γ Ξ±)) => s β uniformity Ξ± β§ symmetric_rel s) id := sorry

/-- Open elements `s : set (Ξ± Γ Ξ±)` of `π€ Ξ±` such that `(x, y) β s β (y, x) β s` form a basis
of `π€ Ξ±`. -/
theorem uniformity_has_basis_open_symmetric {Ξ± : Type u_1} [uniform_space Ξ±] : filter.has_basis (uniformity Ξ±) (fun (V : set (Ξ± Γ Ξ±)) => V β uniformity Ξ± β§ is_open V β§ symmetric_rel V) id := sorry

theorem uniform_space.has_seq_basis {Ξ± : Type u_1} [uniform_space Ξ±] (h : filter.is_countably_generated (uniformity Ξ±)) : β (V : β β set (Ξ± Γ Ξ±)),
  filter.has_antimono_basis (uniformity Ξ±) (fun (_x : β) => True) V β§ β (n : β), symmetric_rel (V n) := sorry

/-! ### Uniform continuity -/

/-- A function `f : Ξ± β Ξ²` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `Ξ±`. -/
def uniform_continuous {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] (f : Ξ± β Ξ²) :=
  filter.tendsto (fun (x : Ξ± Γ Ξ±) => (f (prod.fst x), f (prod.snd x))) (uniformity Ξ±) (uniformity Ξ²)

/-- A function `f : Ξ± β Ξ²` is *uniformly continuous* on `s : set Ξ±` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s.prod s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`.-/
def uniform_continuous_on {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] (f : Ξ± β Ξ²) (s : set Ξ±) :=
  filter.tendsto (fun (x : Ξ± Γ Ξ±) => (f (prod.fst x), f (prod.snd x))) (uniformity Ξ± β filter.principal (set.prod s s))
    (uniformity Ξ²)

theorem uniform_continuous_def {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²} : uniform_continuous f β
  β (r : set (Ξ² Γ Ξ²)),
    r β uniformity Ξ² β (set_of fun (x : Ξ± Γ Ξ±) => (f (prod.fst x), f (prod.snd x)) β r) β uniformity Ξ± :=
  iff.rfl

theorem uniform_continuous_iff_eventually {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²} : uniform_continuous f β
  β (r : set (Ξ² Γ Ξ²)),
    r β uniformity Ξ² β filter.eventually (fun (x : Ξ± Γ Ξ±) => (f (prod.fst x), f (prod.snd x)) β r) (uniformity Ξ±) :=
  iff.rfl

theorem uniform_continuous_of_const {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {c : Ξ± β Ξ²} (h : β (a b : Ξ±), c a = c b) : uniform_continuous c := sorry

theorem uniform_continuous_id {Ξ± : Type u_1} [uniform_space Ξ±] : uniform_continuous id := sorry

theorem uniform_continuous_const {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {b : Ξ²} : uniform_continuous fun (a : Ξ±) => b :=
  uniform_continuous_of_const fun (_x _x : Ξ±) => rfl

theorem uniform_continuous.comp {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] {g : Ξ² β Ξ³} {f : Ξ± β Ξ²} (hg : uniform_continuous g) (hf : uniform_continuous f) : uniform_continuous (g β f) :=
  filter.tendsto.comp hg hf

theorem filter.has_basis.uniform_continuous_iff {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} {Ξ΄ : Type u_4} [uniform_space Ξ±] [uniform_space Ξ²] {p : Ξ³ β Prop} {s : Ξ³ β set (Ξ± Γ Ξ±)} (ha : filter.has_basis (uniformity Ξ±) p s) {q : Ξ΄ β Prop} {t : Ξ΄ β set (Ξ² Γ Ξ²)} (hb : filter.has_basis (uniformity Ξ²) q t) {f : Ξ± β Ξ²} : uniform_continuous f β β (i : Ξ΄), q i β β (j : Ξ³), β (hj : p j), β (x y : Ξ±), (x, y) β s j β (f x, f y) β t i := sorry

theorem filter.has_basis.uniform_continuous_on_iff {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} {Ξ΄ : Type u_4} [uniform_space Ξ±] [uniform_space Ξ²] {p : Ξ³ β Prop} {s : Ξ³ β set (Ξ± Γ Ξ±)} (ha : filter.has_basis (uniformity Ξ±) p s) {q : Ξ΄ β Prop} {t : Ξ΄ β set (Ξ² Γ Ξ²)} (hb : filter.has_basis (uniformity Ξ²) q t) {f : Ξ± β Ξ²} {S : set Ξ±} : uniform_continuous_on f S β
  β (i : Ξ΄), q i β β (j : Ξ³), β (hj : p j), β (x y : Ξ±), x β S β y β S β (x, y) β s j β (f x, f y) β t i := sorry

protected instance uniform_space.partial_order {Ξ± : Type u_1} : partial_order (uniform_space Ξ±) :=
  partial_order.mk
    (fun (t s : uniform_space Ξ±) =>
      uniform_space.core.uniformity uniform_space.to_core β€ uniform_space.core.uniformity uniform_space.to_core)
    (preorder.lt._default
      fun (t s : uniform_space Ξ±) =>
        uniform_space.core.uniformity uniform_space.to_core β€ uniform_space.core.uniformity uniform_space.to_core)
    sorry sorry sorry

protected instance uniform_space.has_Inf {Ξ± : Type u_1} : has_Inf (uniform_space Ξ±) :=
  has_Inf.mk
    fun (s : set (uniform_space Ξ±)) =>
      uniform_space.of_core
        (uniform_space.core.mk (infi fun (u : uniform_space Ξ±) => infi fun (H : u β s) => uniformity Ξ±) sorry sorry sorry)

protected instance uniform_space.has_top {Ξ± : Type u_1} : has_top (uniform_space Ξ±) :=
  has_top.mk (uniform_space.of_core (uniform_space.core.mk β€ sorry sorry sorry))

protected instance uniform_space.has_bot {Ξ± : Type u_1} : has_bot (uniform_space Ξ±) :=
  has_bot.mk (uniform_space.mk (uniform_space.core.mk (filter.principal id_rel) sorry sorry sorry) sorry)

protected instance uniform_space.complete_lattice {Ξ± : Type u_1} : complete_lattice (uniform_space Ξ±) :=
  complete_lattice.mk (fun (a b : uniform_space Ξ±) => Inf (set_of fun (x : uniform_space Ξ±) => a β€ x β§ b β€ x))
    partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry
    (fun (a b : uniform_space Ξ±) => Inf (insert a (singleton b))) sorry sorry sorry β€ sorry β₯ sorry
    (fun (tt : set (uniform_space Ξ±)) =>
      Inf (set_of fun (t : uniform_space Ξ±) => β (t' : uniform_space Ξ±), t' β tt β t' β€ t))
    Inf sorry sorry sorry sorry

theorem infi_uniformity {Ξ± : Type u_1} {ΞΉ : Sort u_2} {u : ΞΉ β uniform_space Ξ±} : uniform_space.core.uniformity uniform_space.to_core =
  infi fun (i : ΞΉ) => uniform_space.core.uniformity uniform_space.to_core := sorry

theorem inf_uniformity {Ξ± : Type u_1} {u : uniform_space Ξ±} {v : uniform_space Ξ±} : uniform_space.core.uniformity uniform_space.to_core =
  uniform_space.core.uniformity uniform_space.to_core β uniform_space.core.uniformity uniform_space.to_core := sorry

protected instance inhabited_uniform_space {Ξ± : Type u_1} : Inhabited (uniform_space Ξ±) :=
  { default := β₯ }

protected instance inhabited_uniform_space_core {Ξ± : Type u_1} : Inhabited (uniform_space.core Ξ±) :=
  { default := uniform_space.to_core }

/-- Given `f : Ξ± β Ξ²` and a uniformity `u` on `Ξ²`, the inverse image of `u` under `f`
  is the inverse image in the filter sense of the induced function `Ξ± Γ Ξ± β Ξ² Γ Ξ²`. -/
def uniform_space.comap {Ξ± : Type u_1} {Ξ² : Type u_2} (f : Ξ± β Ξ²) (u : uniform_space Ξ²) : uniform_space Ξ± :=
  uniform_space.mk
    (uniform_space.core.mk
      (filter.comap (fun (p : Ξ± Γ Ξ±) => (f (prod.fst p), f (prod.snd p)))
        (uniform_space.core.uniformity uniform_space.to_core))
      sorry sorry sorry)
    sorry

theorem uniformity_comap {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²} (h : _inst_1 = uniform_space.comap f _inst_2) : uniformity Ξ± = filter.comap (prod.map f f) (uniformity Ξ²) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (uniformity Ξ± = filter.comap (prod.map f f) (uniformity Ξ²))) h))
    (Eq.refl (uniformity Ξ±))

theorem uniform_space_comap_id {Ξ± : Type u_1} : uniform_space.comap id = id := sorry

theorem uniform_space.comap_comap {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} [uΞ³ : uniform_space Ξ³] {f : Ξ± β Ξ²} {g : Ξ² β Ξ³} : uniform_space.comap (g β f) uΞ³ = uniform_space.comap f (uniform_space.comap g uΞ³) := sorry

theorem uniform_continuous_iff {Ξ± : Type u_1} {Ξ² : Type u_2} [uΞ± : uniform_space Ξ±] [uΞ² : uniform_space Ξ²] {f : Ξ± β Ξ²} : uniform_continuous f β uΞ± β€ uniform_space.comap f uΞ² :=
  filter.map_le_iff_le_comap

theorem uniform_continuous_comap {Ξ± : Type u_1} {Ξ² : Type u_2} {f : Ξ± β Ξ²} [u : uniform_space Ξ²] : uniform_continuous f :=
  filter.tendsto_comap

theorem to_topological_space_comap {Ξ± : Type u_1} {Ξ² : Type u_2} {f : Ξ± β Ξ²} {u : uniform_space Ξ²} : uniform_space.to_topological_space = topological_space.induced f uniform_space.to_topological_space :=
  rfl

theorem uniform_continuous_comap' {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} {f : Ξ³ β Ξ²} {g : Ξ± β Ξ³} [v : uniform_space Ξ²] [u : uniform_space Ξ±] (h : uniform_continuous (f β g)) : uniform_continuous g :=
  iff.mpr filter.tendsto_comap_iff h

theorem to_topological_space_mono {Ξ± : Type u_1} {uβ : uniform_space Ξ±} {uβ : uniform_space Ξ±} (h : uβ β€ uβ) : uniform_space.to_topological_space β€ uniform_space.to_topological_space := sorry

theorem uniform_continuous.continuous {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²} (hf : uniform_continuous f) : continuous f :=
  iff.mpr continuous_iff_le_induced (to_topological_space_mono (iff.mp uniform_continuous_iff hf))

theorem to_topological_space_bot {Ξ± : Type u_1} : uniform_space.to_topological_space = β₯ :=
  rfl

theorem to_topological_space_top {Ξ± : Type u_1} : uniform_space.to_topological_space = β€ := sorry

theorem to_topological_space_infi {Ξ± : Type u_1} {ΞΉ : Sort u_2} {u : ΞΉ β uniform_space Ξ±} : uniform_space.to_topological_space = infi fun (i : ΞΉ) => uniform_space.to_topological_space := sorry

theorem to_topological_space_Inf {Ξ± : Type u_1} {s : set (uniform_space Ξ±)} : uniform_space.to_topological_space =
  infi fun (i : uniform_space Ξ±) => infi fun (H : i β s) => uniform_space.to_topological_space := sorry

theorem to_topological_space_inf {Ξ± : Type u_1} {u : uniform_space Ξ±} {v : uniform_space Ξ±} : uniform_space.to_topological_space = uniform_space.to_topological_space β uniform_space.to_topological_space := sorry

protected instance empty.uniform_space : uniform_space empty :=
  β₯

protected instance unit.uniform_space : uniform_space Unit :=
  β₯

protected instance bool.uniform_space : uniform_space Bool :=
  β₯

protected instance nat.uniform_space : uniform_space β :=
  β₯

protected instance int.uniform_space : uniform_space β€ :=
  β₯

protected instance subtype.uniform_space {Ξ± : Type u_1} {p : Ξ± β Prop} [t : uniform_space Ξ±] : uniform_space (Subtype p) :=
  uniform_space.comap subtype.val t

theorem uniformity_subtype {Ξ± : Type u_1} {p : Ξ± β Prop} [t : uniform_space Ξ±] : uniformity (Subtype p) =
  filter.comap (fun (q : Subtype p Γ Subtype p) => (subtype.val (prod.fst q), subtype.val (prod.snd q))) (uniformity Ξ±) :=
  rfl

theorem uniform_continuous_subtype_val {Ξ± : Type u_1} {p : Ξ± β Prop} [uniform_space Ξ±] : uniform_continuous subtype.val :=
  uniform_continuous_comap

theorem uniform_continuous_subtype_mk {Ξ± : Type u_1} {Ξ² : Type u_2} {p : Ξ± β Prop} [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ² β Ξ±} (hf : uniform_continuous f) (h : β (x : Ξ²), p (f x)) : uniform_continuous fun (x : Ξ²) => { val := f x, property := h x } :=
  uniform_continuous_comap' hf

theorem uniform_continuous_on_iff_restrict {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²} {s : set Ξ±} : uniform_continuous_on f s β uniform_continuous (set.restrict f s) := sorry

theorem tendsto_of_uniform_continuous_subtype {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²} {s : set Ξ±} {a : Ξ±} (hf : uniform_continuous fun (x : β₯s) => f (subtype.val x)) (ha : s β nhds a) : filter.tendsto f (nhds a) (nhds (f a)) := sorry

theorem uniform_continuous_on.continuous_on {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²} {s : set Ξ±} (h : uniform_continuous_on f s) : continuous_on f s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (continuous_on f s)) (propext continuous_on_iff_continuous_restrict)))
    (uniform_continuous.continuous
      (eq.mp (Eq._oldrec (Eq.refl (uniform_continuous_on f s)) (propext uniform_continuous_on_iff_restrict)) h))

/- a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/

protected instance prod.uniform_space {Ξ± : Type u_1} {Ξ² : Type u_2} [uβ : uniform_space Ξ±] [uβ : uniform_space Ξ²] : uniform_space (Ξ± Γ Ξ²) :=
  uniform_space.of_core_eq uniform_space.to_core prod.topological_space sorry

theorem uniformity_prod {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] : uniformity (Ξ± Γ Ξ²) =
  filter.comap (fun (p : (Ξ± Γ Ξ²) Γ Ξ± Γ Ξ²) => (prod.fst (prod.fst p), prod.fst (prod.snd p))) (uniformity Ξ±) β
    filter.comap (fun (p : (Ξ± Γ Ξ²) Γ Ξ± Γ Ξ²) => (prod.snd (prod.fst p), prod.snd (prod.snd p))) (uniformity Ξ²) :=
  inf_uniformity

theorem uniformity_prod_eq_prod {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] : uniformity (Ξ± Γ Ξ²) =
  filter.map
    (fun (p : (Ξ± Γ Ξ±) Γ Ξ² Γ Ξ²) =>
      ((prod.fst (prod.fst p), prod.fst (prod.snd p)), prod.snd (prod.fst p), prod.snd (prod.snd p)))
    (filter.prod (uniformity Ξ±) (uniformity Ξ²)) := sorry

theorem mem_map_sets_iff' {Ξ± : Type u_1} {Ξ² : Type u_2} {f : filter Ξ±} {m : Ξ± β Ξ²} {t : set Ξ²} : t β filter.sets (filter.map m f) β β (s : set Ξ±), β (H : s β f), m '' s β t :=
  filter.mem_map_sets_iff

theorem mem_uniformity_of_uniform_continuous_invariant {Ξ± : Type u_1} [uniform_space Ξ±] {s : set (Ξ± Γ Ξ±)} {f : Ξ± β Ξ± β Ξ±} (hf : uniform_continuous fun (p : Ξ± Γ Ξ±) => f (prod.fst p) (prod.snd p)) (hs : s β uniformity Ξ±) : β (u : set (Ξ± Γ Ξ±)), β (H : u β uniformity Ξ±), β (a b c : Ξ±), (a, b) β u β (f a c, f b c) β s := sorry

theorem mem_uniform_prod {Ξ± : Type u_1} {Ξ² : Type u_2} [tβ : uniform_space Ξ±] [tβ : uniform_space Ξ²] {a : set (Ξ± Γ Ξ±)} {b : set (Ξ² Γ Ξ²)} (ha : a β uniformity Ξ±) (hb : b β uniformity Ξ²) : (set_of
    fun (p : (Ξ± Γ Ξ²) Γ Ξ± Γ Ξ²) =>
      (prod.fst (prod.fst p), prod.fst (prod.snd p)) β a β§ (prod.snd (prod.fst p), prod.snd (prod.snd p)) β b) β
  uniformity (Ξ± Γ Ξ²) := sorry

theorem tendsto_prod_uniformity_fst {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] : filter.tendsto (fun (p : (Ξ± Γ Ξ²) Γ Ξ± Γ Ξ²) => (prod.fst (prod.fst p), prod.fst (prod.snd p))) (uniformity (Ξ± Γ Ξ²))
  (uniformity Ξ±) :=
  le_trans (filter.map_mono inf_le_left) filter.map_comap_le

theorem tendsto_prod_uniformity_snd {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] : filter.tendsto (fun (p : (Ξ± Γ Ξ²) Γ Ξ± Γ Ξ²) => (prod.snd (prod.fst p), prod.snd (prod.snd p))) (uniformity (Ξ± Γ Ξ²))
  (uniformity Ξ²) :=
  le_trans (filter.map_mono inf_le_right) filter.map_comap_le

theorem uniform_continuous_fst {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] : uniform_continuous fun (p : Ξ± Γ Ξ²) => prod.fst p :=
  tendsto_prod_uniformity_fst

theorem uniform_continuous_snd {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] : uniform_continuous fun (p : Ξ± Γ Ξ²) => prod.snd p :=
  tendsto_prod_uniformity_snd

theorem uniform_continuous.prod_mk {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] {fβ : Ξ± β Ξ²} {fβ : Ξ± β Ξ³} (hβ : uniform_continuous fβ) (hβ : uniform_continuous fβ) : uniform_continuous fun (a : Ξ±) => (fβ a, fβ a) := sorry

theorem uniform_continuous.prod_mk_left {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] {f : Ξ± Γ Ξ² β Ξ³} (h : uniform_continuous f) (b : Ξ²) : uniform_continuous fun (a : Ξ±) => f (a, b) :=
  uniform_continuous.comp h (uniform_continuous.prod_mk uniform_continuous_id uniform_continuous_const)

theorem uniform_continuous.prod_mk_right {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] {f : Ξ± Γ Ξ² β Ξ³} (h : uniform_continuous f) (a : Ξ±) : uniform_continuous fun (b : Ξ²) => f (a, b) :=
  uniform_continuous.comp h (uniform_continuous.prod_mk uniform_continuous_const uniform_continuous_id)

theorem uniform_continuous.prod_map {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} {Ξ΄ : Type u_4} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] [uniform_space Ξ΄] {f : Ξ± β Ξ³} {g : Ξ² β Ξ΄} (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (prod.map f g) :=
  uniform_continuous.prod_mk (uniform_continuous.comp hf uniform_continuous_fst)
    (uniform_continuous.comp hg uniform_continuous_snd)

theorem to_topological_space_prod {Ξ± : Type u_1} {Ξ² : Type u_2} [u : uniform_space Ξ±] [v : uniform_space Ξ²] : uniform_space.to_topological_space = prod.topological_space :=
  rfl

/-- Uniform continuity for functions of two variables. -/
def uniform_continuousβ {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] (f : Ξ± β Ξ² β Ξ³) :=
  uniform_continuous (function.uncurry f)

theorem uniform_continuousβ_def {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] (f : Ξ± β Ξ² β Ξ³) : uniform_continuousβ f β uniform_continuous (function.uncurry f) :=
  iff.rfl

theorem uniform_continuousβ.uniform_continuous {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] {f : Ξ± β Ξ² β Ξ³} (h : uniform_continuousβ f) : uniform_continuous (function.uncurry f) :=
  h

theorem uniform_continuousβ_curry {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] (f : Ξ± Γ Ξ² β Ξ³) : uniform_continuousβ (function.curry f) β uniform_continuous f := sorry

theorem uniform_continuousβ.comp {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} {Ξ΄ : Type u_4} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] [uniform_space Ξ΄] {f : Ξ± β Ξ² β Ξ³} {g : Ξ³ β Ξ΄} (hg : uniform_continuous g) (hf : uniform_continuousβ f) : uniform_continuousβ (function.bicompr g f) :=
  uniform_continuous.comp hg hf

theorem uniform_continuousβ.bicompl {Ξ± : Type u_1} {Ξ² : Type u_2} {Ξ³ : Type u_3} {Ξ΄ : Type u_4} {Ξ΄' : Type u_6} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] [uniform_space Ξ΄] [uniform_space Ξ΄'] {f : Ξ± β Ξ² β Ξ³} {ga : Ξ΄ β Ξ±} {gb : Ξ΄' β Ξ²} (hf : uniform_continuousβ f) (hga : uniform_continuous ga) (hgb : uniform_continuous gb) : uniform_continuousβ (function.bicompl f ga gb) :=
  uniform_continuous.comp (uniform_continuousβ.uniform_continuous hf) (uniform_continuous.prod_map hga hgb)

theorem to_topological_space_subtype {Ξ± : Type u_1} [u : uniform_space Ξ±] {p : Ξ± β Prop} : uniform_space.to_topological_space = subtype.topological_space :=
  rfl

/-- Uniformity on a disjoint union. Entourages of the diagonal in the union are obtained
by taking independently an entourage of the diagonal in the first part, and an entourage of
the diagonal in the second part. -/
def uniform_space.core.sum {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] : uniform_space.core (Ξ± β Ξ²) :=
  uniform_space.core.mk'
    (filter.map (fun (p : Ξ± Γ Ξ±) => (sum.inl (prod.fst p), sum.inl (prod.snd p))) (uniformity Ξ±) β
      filter.map (fun (p : Ξ² Γ Ξ²) => (sum.inr (prod.fst p), sum.inr (prod.snd p))) (uniformity Ξ²))
    sorry sorry sorry

/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage
of the diagonal. -/
theorem union_mem_uniformity_sum {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {a : set (Ξ± Γ Ξ±)} (ha : a β uniformity Ξ±) {b : set (Ξ² Γ Ξ²)} (hb : b β uniformity Ξ²) : (fun (p : Ξ± Γ Ξ±) => (sum.inl (prod.fst p), sum.inl (prod.snd p))) '' a βͺ
    (fun (p : Ξ² Γ Ξ²) => (sum.inr (prod.fst p), sum.inr (prod.snd p))) '' b β
  uniform_space.core.uniformity uniform_space.core.sum := sorry

/- To prove that the topology defined by the uniform structure on the disjoint union coincides with
the disjoint union topology, we need two lemmas saying that open sets can be characterized by
the uniform structure -/

theorem uniformity_sum_of_open_aux {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {s : set (Ξ± β Ξ²)} (hs : is_open s) {x : Ξ± β Ξ²} (xs : x β s) : (set_of fun (p : (Ξ± β Ξ²) Γ (Ξ± β Ξ²)) => prod.fst p = x β prod.snd p β s) β
  uniform_space.core.uniformity uniform_space.core.sum := sorry

theorem open_of_uniformity_sum_aux {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] {s : set (Ξ± β Ξ²)} (hs : β (x : Ξ± β Ξ²),
  x β s β
    (set_of fun (p : (Ξ± β Ξ²) Γ (Ξ± β Ξ²)) => prod.fst p = x β prod.snd p β s) β
      uniform_space.core.uniformity uniform_space.core.sum) : is_open s := sorry

/- We can now define the uniform structure on the disjoint union -/

protected instance sum.uniform_space {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] : uniform_space (Ξ± β Ξ²) :=
  uniform_space.mk uniform_space.core.sum sorry

theorem sum.uniformity {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [uniform_space Ξ²] : uniformity (Ξ± β Ξ²) =
  filter.map (fun (p : Ξ± Γ Ξ±) => (sum.inl (prod.fst p), sum.inl (prod.snd p))) (uniformity Ξ±) β
    filter.map (fun (p : Ξ² Γ Ξ²) => (sum.inr (prod.fst p), sum.inr (prod.snd p))) (uniformity Ξ²) :=
  rfl

-- For a version of the Lebesgue number lemma assuming only a sequentially compact space,

-- see topology/sequences.lean

/-- Let `c : ΞΉ β set Ξ±` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x β s` its `n`-neighborhood is contained in some `c i`. -/
theorem lebesgue_number_lemma {Ξ± : Type u} [uniform_space Ξ±] {s : set Ξ±} {ΞΉ : Sort u_1} {c : ΞΉ β set Ξ±} (hs : is_compact s) (hcβ : β (i : ΞΉ), is_open (c i)) (hcβ : s β set.Union fun (i : ΞΉ) => c i) : β (n : set (Ξ± Γ Ξ±)), β (H : n β uniformity Ξ±), β (x : Ξ±), x β s β β (i : ΞΉ), (set_of fun (y : Ξ±) => (x, y) β n) β c i := sorry

/-- Let `c : set (set Ξ±)` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x β s` its `n`-neighborhood is contained in some `t β c`. -/
theorem lebesgue_number_lemma_sUnion {Ξ± : Type u} [uniform_space Ξ±] {s : set Ξ±} {c : set (set Ξ±)} (hs : is_compact s) (hcβ : β (t : set Ξ±), t β c β is_open t) (hcβ : s β ββc) : β (n : set (Ξ± Γ Ξ±)),
  β (H : n β uniformity Ξ±), β (x : Ξ±) (H : x β s), β (t : set Ξ±), β (H : t β c), β (y : Ξ±), (x, y) β n β y β t := sorry

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


theorem tendsto_nhds_right {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {f : filter Ξ²} {u : Ξ² β Ξ±} {a : Ξ±} : filter.tendsto u f (nhds a) β filter.tendsto (fun (x : Ξ²) => (a, u x)) f (uniformity Ξ±) := sorry

theorem tendsto_nhds_left {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] {f : filter Ξ²} {u : Ξ² β Ξ±} {a : Ξ±} : filter.tendsto u f (nhds a) β filter.tendsto (fun (x : Ξ²) => (u x, a)) f (uniformity Ξ±) := sorry

theorem continuous_at_iff'_right {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [topological_space Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} : continuous_at f b β filter.tendsto (fun (x : Ξ²) => (f b, f x)) (nhds b) (uniformity Ξ±) := sorry

theorem continuous_at_iff'_left {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [topological_space Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} : continuous_at f b β filter.tendsto (fun (x : Ξ²) => (f x, f b)) (nhds b) (uniformity Ξ±) := sorry

theorem continuous_at_iff_prod {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [topological_space Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} : continuous_at f b β filter.tendsto (fun (x : Ξ² Γ Ξ²) => (f (prod.fst x), f (prod.snd x))) (nhds (b, b)) (uniformity Ξ±) := sorry

theorem continuous_within_at_iff'_right {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [topological_space Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} {s : set Ξ²} : continuous_within_at f s b β filter.tendsto (fun (x : Ξ²) => (f b, f x)) (nhds_within b s) (uniformity Ξ±) := sorry

theorem continuous_within_at_iff'_left {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [topological_space Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} {s : set Ξ²} : continuous_within_at f s b β filter.tendsto (fun (x : Ξ²) => (f x, f b)) (nhds_within b s) (uniformity Ξ±) := sorry

theorem continuous_on_iff'_right {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [topological_space Ξ²] {f : Ξ² β Ξ±} {s : set Ξ²} : continuous_on f s β β (b : Ξ²), b β s β filter.tendsto (fun (x : Ξ²) => (f b, f x)) (nhds_within b s) (uniformity Ξ±) := sorry

theorem continuous_on_iff'_left {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [topological_space Ξ²] {f : Ξ² β Ξ±} {s : set Ξ²} : continuous_on f s β β (b : Ξ²), b β s β filter.tendsto (fun (x : Ξ²) => (f x, f b)) (nhds_within b s) (uniformity Ξ±) := sorry

theorem continuous_iff'_right {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [topological_space Ξ²] {f : Ξ² β Ξ±} : continuous f β β (b : Ξ²), filter.tendsto (fun (x : Ξ²) => (f b, f x)) (nhds b) (uniformity Ξ±) :=
  iff.trans continuous_iff_continuous_at (forall_congr fun (b : Ξ²) => tendsto_nhds_right)

theorem continuous_iff'_left {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ±] [topological_space Ξ²] {f : Ξ² β Ξ±} : continuous f β β (b : Ξ²), filter.tendsto (fun (x : Ξ²) => (f x, f b)) (nhds b) (uniformity Ξ±) :=
  iff.trans continuous_iff_continuous_at (forall_congr fun (b : Ξ²) => tendsto_nhds_left)

end uniform


theorem filter.tendsto.congr_uniformity {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ²] {f : Ξ± β Ξ²} {g : Ξ± β Ξ²} {l : filter Ξ±} {b : Ξ²} (hf : filter.tendsto f l (nhds b)) (hg : filter.tendsto (fun (x : Ξ±) => (f x, g x)) l (uniformity Ξ²)) : filter.tendsto g l (nhds b) :=
  iff.mpr uniform.tendsto_nhds_right (filter.tendsto.uniformity_trans (iff.mp uniform.tendsto_nhds_right hf) hg)

theorem uniform.tendsto_congr {Ξ± : Type u_1} {Ξ² : Type u_2} [uniform_space Ξ²] {f : Ξ± β Ξ²} {g : Ξ± β Ξ²} {l : filter Ξ±} {b : Ξ²} (hfg : filter.tendsto (fun (x : Ξ±) => (f x, g x)) l (uniformity Ξ²)) : filter.tendsto f l (nhds b) β filter.tendsto g l (nhds b) :=
  { mp := fun (h : filter.tendsto f l (nhds b)) => filter.tendsto.congr_uniformity h hfg,
    mpr :=
      fun (h : filter.tendsto g l (nhds b)) => filter.tendsto.congr_uniformity h (filter.tendsto.uniformity_symm hfg) }

