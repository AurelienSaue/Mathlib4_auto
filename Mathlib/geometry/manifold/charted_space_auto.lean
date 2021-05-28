/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.local_homeomorph
import PostPort

universes u l u_5 u_1 u_6 u_2 u_3 u_4 

namespace Mathlib

/-!
# Charted spaces

A smooth manifold is a topological space `M` locally modelled on a euclidean space (or a euclidean
half-space for manifolds with boundaries, or an infinite dimensional vector space for more general
notions of manifolds), i.e., the manifold is covered by open subsets on which there are local
homeomorphisms (the charts) going to a model space `H`, and the changes of charts should be smooth
maps.

In this file, we introduce a general framework describing these notions, where the model space is an
arbitrary topological space. We avoid the word *manifold*, which should be reserved for the
situation where the model space is a (subset of a) vector space, and use the terminology
*charted space* instead.

If the changes of charts satisfy some additional property (for instance if they are smooth), then
`M` inherits additional structure (it makes sense to talk about smooth manifolds). There are
therefore two different ingredients in a charted space:
* the set of charts, which is data
* the fact that changes of charts belong to some group (in fact groupoid), which is additional Prop.

We separate these two parts in the definition: the charted space structure is just the set of
charts, and then the different smoothness requirements (smooth manifold, orientable manifold,
contact manifold, and so on) are additional properties of these charts. These properties are
formalized through the notion of structure groupoid, i.e., a set of local homeomorphisms stable
under composition and inverse, to which the change of coordinates should belong.

## Main definitions

* `structure_groupoid H` : a subset of local homeomorphisms of `H` stable under composition,
  inverse and restriction (ex: local diffeos).
* `continuous_groupoid H` : the groupoid of all local homeomorphisms of `H`
* `charted_space H M` : charted space structure on `M` modelled on `H`, given by an atlas of
  local homeomorphisms from `M` to `H` whose sources cover `M`. This is a type class.
* `has_groupoid M G` : when `G` is a structure groupoid on `H` and `M` is a charted space
  modelled on `H`, require that all coordinate changes belong to `G`. This is a type class.
* `atlas H M` : when `M` is a charted space modelled on `H`, the atlas of this charted
  space structure, i.e., the set of charts.
* `G.maximal_atlas M` : when `M` is a charted space modelled on `H` and admitting `G` as a
  structure groupoid, one can consider all the local homeomorphisms from `M` to `H` such that
  changing coordinate from any chart to them belongs to `G`. This is a larger atlas, called the
  maximal atlas (for the groupoid `G`).
* `structomorph G M M'` : the type of diffeomorphisms between the charted spaces `M` and `M'` for
  the groupoid `G`. We avoid the word diffeomorphism, keeping it for the smooth category.

As a basic example, we give the instance
`instance charted_space_model_space (H : Type*) [topological_space H] : charted_space H H`
saying that a topological space is a charted space over itself, with the identity as unique chart.
This charted space structure is compatible with any groupoid.

Additional useful definitions:

* `pregroupoid H` : a subset of local mas of `H` stable under composition and
  restriction, but not inverse (ex: smooth maps)
* `groupoid_of_pregroupoid` : construct a groupoid from a pregroupoid, by requiring that a map and
  its inverse both belong to the pregroupoid (ex: construct diffeos from smooth maps)
* `chart_at H x` is a preferred chart at `x : M` when `M` has a charted space structure modelled on
  `H`.
* `G.compatible he he'` states that, for any two charts `e` and `e'` in the atlas, the composition
  of `e.symm` and `e'` belongs to the groupoid `G` when `M` admits `G` as a structure groupoid.
* `G.compatible_of_mem_maximal_atlas he he'` states that, for any two charts `e` and `e'` in the
  maximal atlas associated to the groupoid `G`, the composition of `e.symm` and `e'` belongs to the
  `G` if `M` admits `G` as a structure groupoid.
* `charted_space_core.to_charted_space`: consider a space without a topology, but endowed with a set
  of charts (which are local equivs) for which the change of coordinates are local homeos. Then
  one can construct a topology on the space for which the charts become local homeos, defining
  a genuine charted space structure.

## Implementation notes

The atlas in a charted space is *not* a maximal atlas in general: the notion of maximality depends
on the groupoid one considers, and changing groupoids changes the maximal atlas. With the current
formalization, it makes sense first to choose the atlas, and then to ask whether this precise atlas
defines a smooth manifold, an orientable manifold, and so on. A consequence is that structomorphisms
between `M` and `M'` do *not* induce a bijection between the atlases of `M` and `M'`: the
definition is only that, read in charts, the structomorphism locally belongs to the groupoid under
consideration. (This is equivalent to inducing a bijection between elements of the maximal atlas).
A consequence is that the invariance under structomorphisms of properties defined in terms of the
atlas is not obvious in general, and could require some work in theory (amounting to the fact
that these properties only depend on the maximal atlas, for instance). In practice, this does not
create any real difficulty.

We use the letter `H` for the model space thinking of the case of manifolds with boundary, where the
model space is a half space.

Manifolds are sometimes defined as topological spaces with an atlas of local diffeomorphisms, and
sometimes as spaces with an atlas from which a topology is deduced. We use the former approach:
otherwise, there would be an instance from manifolds to topological spaces, which means that any
instance search for topological spaces would try to find manifold structures involving a yet
unknown model space, leading to problems. However, we also introduce the latter approach,
through a structure `charted_space_core` making it possible to construct a topology out of a set of
local equivs with compatibility conditions (but we do not register it as an instance).

In the definition of a charted space, the model space is written as an explicit parameter as there
can be several model spaces for a given topological space. For instance, a complex manifold
(modelled over `ℂ^n`) will also be seen sometimes as a real manifold modelled over `ℝ^(2n)`.

## Notations

In the locale `manifold`, we denote the composition of local homeomorphisms with `≫ₕ`, and the
composition of local equivs with `≫`.
-/

/- Notational shortcut for the composition of local homeomorphisms and local equivs, i.e.,
`local_homeomorph.trans` and `local_equiv.trans`.
Note that, as is usual for equivs, the composition is from left to right, hence the direction of
the arrow. -/

/- `simp` looks for subsingleton instances at every call. This turns out to be very
inefficient, especially in `simp`-heavy parts of the library such as the manifold code.
Disable two such instances to speed up things.
NB: this is just a hack. TODO: fix `simp` properly. -/

/-! ### Structure groupoids-/

/-! One could add to the definition of a structure groupoid the fact that the restriction of an
element of the groupoid to any open set still belongs to the groupoid.
(This is in Kobayashi-Nomizu.)
I am not sure I want this, for instance on `H × E` where `E` is a vector space, and the groupoid is
made of functions respecting the fibers and linear in the fibers (so that a charted space over this
groupoid is naturally a vector bundle) I prefer that the members of the groupoid are always
defined on sets of the form `s × E`.  There is a typeclass `closed_under_restriction` for groupoids
which have the restriction property.

The only nontrivial requirement is locality: if a local homeomorphism belongs to the groupoid
around each point in its domain of definition, then it belongs to the groupoid. Without this
requirement, the composition of structomorphisms does not have to be a structomorphism. Note that
this implies that a local homeomorphism with empty source belongs to any structure groupoid, as
it trivially satisfies this condition.

There is also a technical point, related to the fact that a local homeomorphism is by definition a
global map which is a homeomorphism when restricted to its source subset (and its values outside
of the source are not relevant). Therefore, we also require that being a member of the groupoid only
depends on the values on the source.

We use primes in the structure names as we will reformulate them below (without primes) using a
`has_mem` instance, writing `e ∈ G` instead of `e ∈ G.members`.
-/

/-- A structure groupoid is a set of local homeomorphisms of a topological space stable under
composition and inverse. They appear in the definition of the smoothness class of a manifold. -/
structure structure_groupoid (H : Type u) [topological_space H] 
where
  members : set (local_homeomorph H H)
  trans' : ∀ (e e' : local_homeomorph H H), e ∈ members → e' ∈ members → local_homeomorph.trans e e' ∈ members
  symm' : ∀ (e : local_homeomorph H H), e ∈ members → local_homeomorph.symm e ∈ members
  id_mem' : local_homeomorph.refl H ∈ members
  locality' : ∀ (e : local_homeomorph H H),
  (∀ (x : H),
      x ∈ local_equiv.source (local_homeomorph.to_local_equiv e) →
        ∃ (s : set H), is_open s ∧ x ∈ s ∧ local_homeomorph.restr e s ∈ members) →
    e ∈ members
  eq_on_source' : ∀ (e e' : local_homeomorph H H), e ∈ members → e' ≈ e → e' ∈ members

protected instance structure_groupoid.has_mem {H : Type u} [topological_space H] : has_mem (local_homeomorph H H) (structure_groupoid H) :=
  has_mem.mk fun (e : local_homeomorph H H) (G : structure_groupoid H) => e ∈ structure_groupoid.members G

theorem structure_groupoid.trans {H : Type u} [topological_space H] (G : structure_groupoid H) {e : local_homeomorph H H} {e' : local_homeomorph H H} (he : e ∈ G) (he' : e' ∈ G) : local_homeomorph.trans e e' ∈ G :=
  structure_groupoid.trans' G e e' he he'

theorem structure_groupoid.symm {H : Type u} [topological_space H] (G : structure_groupoid H) {e : local_homeomorph H H} (he : e ∈ G) : local_homeomorph.symm e ∈ G :=
  structure_groupoid.symm' G e he

theorem structure_groupoid.id_mem {H : Type u} [topological_space H] (G : structure_groupoid H) : local_homeomorph.refl H ∈ G :=
  structure_groupoid.id_mem' G

theorem structure_groupoid.locality {H : Type u} [topological_space H] (G : structure_groupoid H) {e : local_homeomorph H H} (h : ∀ (x : H),
  x ∈ local_equiv.source (local_homeomorph.to_local_equiv e) →
    ∃ (s : set H), is_open s ∧ x ∈ s ∧ local_homeomorph.restr e s ∈ G) : e ∈ G :=
  structure_groupoid.locality' G e h

theorem structure_groupoid.eq_on_source {H : Type u} [topological_space H] (G : structure_groupoid H) {e : local_homeomorph H H} {e' : local_homeomorph H H} (he : e ∈ G) (h : e' ≈ e) : e' ∈ G :=
  structure_groupoid.eq_on_source' G e e' he h

/-- Partial order on the set of groupoids, given by inclusion of the members of the groupoid -/
protected instance structure_groupoid.partial_order {H : Type u} [topological_space H] : partial_order (structure_groupoid H) :=
  partial_order.lift structure_groupoid.members sorry

theorem structure_groupoid.le_iff {H : Type u} [topological_space H] {G₁ : structure_groupoid H} {G₂ : structure_groupoid H} : G₁ ≤ G₂ ↔ ∀ (e : local_homeomorph H H), e ∈ G₁ → e ∈ G₂ :=
  iff.rfl

/-- The trivial groupoid, containing only the identity (and maps with empty source, as this is
necessary from the definition) -/
def id_groupoid (H : Type u) [topological_space H] : structure_groupoid H :=
  structure_groupoid.mk
    (singleton (local_homeomorph.refl H) ∪
      set_of fun (e : local_homeomorph H H) => local_equiv.source (local_homeomorph.to_local_equiv e) = ∅)
    sorry sorry sorry sorry sorry

/-- Every structure groupoid contains the identity groupoid -/
protected instance structure_groupoid.order_bot {H : Type u} [topological_space H] : order_bot (structure_groupoid H) :=
  order_bot.mk (id_groupoid H) partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance structure_groupoid.inhabited (H : Type u) [topological_space H] : Inhabited (structure_groupoid H) :=
  { default := id_groupoid H }

/-- To construct a groupoid, one may consider classes of local homeos such that both the function
and its inverse have some property. If this property is stable under composition,
one gets a groupoid. `pregroupoid` bundles the properties needed for this construction, with the
groupoid of smooth functions with smooth inverses as an application. -/
structure pregroupoid (H : Type u_5) [topological_space H] 
where
  property : (H → H) → set H → Prop
  comp : ∀ {f g : H → H} {u v : set H},
  property f u → property g v → is_open u → is_open v → is_open (u ∩ f ⁻¹' v) → property (g ∘ f) (u ∩ f ⁻¹' v)
  id_mem : property id set.univ
  locality : ∀ {f : H → H} {u : set H},
  is_open u → (∀ (x : H), x ∈ u → ∃ (v : set H), is_open v ∧ x ∈ v ∧ property f (u ∩ v)) → property f u
  congr : ∀ {f g : H → H} {u : set H}, is_open u → (∀ (x : H), x ∈ u → g x = f x) → property f u → property g u

/-- Construct a groupoid of local homeos for which the map and its inverse have some property,
from a pregroupoid asserting that this property is stable under composition. -/
def pregroupoid.groupoid {H : Type u} [topological_space H] (PG : pregroupoid H) : structure_groupoid H :=
  structure_groupoid.mk
    (set_of
      fun (e : local_homeomorph H H) =>
        pregroupoid.property PG (⇑e) (local_equiv.source (local_homeomorph.to_local_equiv e)) ∧
          pregroupoid.property PG (⇑(local_homeomorph.symm e)) (local_equiv.target (local_homeomorph.to_local_equiv e)))
    sorry sorry sorry sorry sorry

theorem mem_groupoid_of_pregroupoid {H : Type u} [topological_space H] {PG : pregroupoid H} {e : local_homeomorph H H} : e ∈ pregroupoid.groupoid PG ↔
  pregroupoid.property PG (⇑e) (local_equiv.source (local_homeomorph.to_local_equiv e)) ∧
    pregroupoid.property PG (⇑(local_homeomorph.symm e)) (local_equiv.target (local_homeomorph.to_local_equiv e)) :=
  iff.rfl

theorem groupoid_of_pregroupoid_le {H : Type u} [topological_space H] (PG₁ : pregroupoid H) (PG₂ : pregroupoid H) (h : ∀ (f : H → H) (s : set H), pregroupoid.property PG₁ f s → pregroupoid.property PG₂ f s) : pregroupoid.groupoid PG₁ ≤ pregroupoid.groupoid PG₂ := sorry

theorem mem_pregroupoid_of_eq_on_source {H : Type u} [topological_space H] (PG : pregroupoid H) {e : local_homeomorph H H} {e' : local_homeomorph H H} (he' : e ≈ e') (he : pregroupoid.property PG (⇑e) (local_equiv.source (local_homeomorph.to_local_equiv e))) : pregroupoid.property PG (⇑e') (local_equiv.source (local_homeomorph.to_local_equiv e')) := sorry

/-- The pregroupoid of all local maps on a topological space `H` -/
def continuous_pregroupoid (H : Type u_1) [topological_space H] : pregroupoid H :=
  pregroupoid.mk (fun (f : H → H) (s : set H) => True) sorry trivial sorry sorry

protected instance pregroupoid.inhabited (H : Type u_1) [topological_space H] : Inhabited (pregroupoid H) :=
  { default := continuous_pregroupoid H }

/-- The groupoid of all local homeomorphisms on a topological space `H` -/
def continuous_groupoid (H : Type u_1) [topological_space H] : structure_groupoid H :=
  pregroupoid.groupoid (continuous_pregroupoid H)

/-- Every structure groupoid is contained in the groupoid of all local homeomorphisms -/
protected instance structure_groupoid.order_top {H : Type u} [topological_space H] : order_top (structure_groupoid H) :=
  order_top.mk (continuous_groupoid H) partial_order.le partial_order.lt sorry sorry sorry sorry

/-- A groupoid is closed under restriction if it contains all restrictions of its element local
homeomorphisms to open subsets of the source. -/
class closed_under_restriction {H : Type u} [topological_space H] (G : structure_groupoid H) 
where
  closed_under_restriction : ∀ {e : local_homeomorph H H}, e ∈ G → ∀ (s : set H), is_open s → local_homeomorph.restr e s ∈ G

theorem closed_under_restriction' {H : Type u} [topological_space H] {G : structure_groupoid H} [closed_under_restriction G] {e : local_homeomorph H H} (he : e ∈ G) {s : set H} (hs : is_open s) : local_homeomorph.restr e s ∈ G :=
  closed_under_restriction.closed_under_restriction he s hs

/-- The trivial restriction-closed groupoid, containing only local homeomorphisms equivalent to the
restriction of the identity to the various open subsets. -/
def id_restr_groupoid {H : Type u} [topological_space H] : structure_groupoid H :=
  structure_groupoid.mk
    (set_of
      fun (e : local_homeomorph H H) => Exists fun {s : set H} => ∃ (h : is_open s), e ≈ local_homeomorph.of_set s h)
    sorry sorry sorry sorry sorry

theorem id_restr_groupoid_mem {H : Type u} [topological_space H] {s : set H} (hs : is_open s) : local_homeomorph.of_set s hs ∈ id_restr_groupoid :=
  Exists.intro s (Exists.intro hs (setoid.refl (local_homeomorph.of_set s hs)))

/-- The trivial restriction-closed groupoid is indeed `closed_under_restriction`. -/
protected instance closed_under_restriction_id_restr_groupoid {H : Type u} [topological_space H] : closed_under_restriction id_restr_groupoid := sorry

/-- A groupoid is closed under restriction if and only if it contains the trivial restriction-closed
groupoid. -/
theorem closed_under_restriction_iff_id_le {H : Type u} [topological_space H] (G : structure_groupoid H) : closed_under_restriction G ↔ id_restr_groupoid ≤ G := sorry

/-- The groupoid of all local homeomorphisms on a topological space `H` is closed under restriction.
-/
protected instance continuous_groupoid.closed_under_restriction {H : Type u} [topological_space H] : closed_under_restriction (continuous_groupoid H) :=
  iff.mpr (closed_under_restriction_iff_id_le (continuous_groupoid H))
    (eq.mpr
      ((fun (ᾰ ᾰ_1 : structure_groupoid H) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : structure_groupoid H) (e_3 : ᾰ_2 = ᾰ_3) =>
          congr (congr_arg LessEq e_2) e_3)
        id_restr_groupoid id_restr_groupoid (Eq.refl id_restr_groupoid) (continuous_groupoid H) ⊤
        (Eq.refl (continuous_groupoid H)))
      le_top)

/-! ### Charted spaces -/

/-- A charted space is a topological space endowed with an atlas, i.e., a set of local
homeomorphisms taking value in a model space `H`, called charts, such that the domains of the charts
cover the whole space. We express the covering property by chosing for each `x` a member
`chart_at H x` of the atlas containing `x` in its source: in the smooth case, this is convenient to
construct the tangent bundle in an efficient way.
The model space is written as an explicit parameter as there can be several model spaces for a
given topological space. For instance, a complex manifold (modelled over `ℂ^n`) will also be seen
sometimes as a real manifold over `ℝ^(2n)`.
-/
class charted_space (H : Type u_5) [topological_space H] (M : Type u_6) [topological_space M] 
where
  atlas : set (local_homeomorph M H)
  chart_at : M → local_homeomorph M H
  mem_chart_source : ∀ (x : M), x ∈ local_equiv.source (local_homeomorph.to_local_equiv (chart_at x))
  chart_mem_atlas : ∀ (x : M), chart_at x ∈ atlas

/-- Any space is a charted_space modelled over itself, by just using the identity chart -/
protected instance charted_space_self (H : Type u_1) [topological_space H] : charted_space H H :=
  charted_space.mk (singleton (local_homeomorph.refl H)) (fun (x : H) => local_homeomorph.refl H) sorry sorry

/-- In the trivial charted_space structure of a space modelled over itself through the identity, the
atlas members are just the identity -/
@[simp] theorem charted_space_self_atlas {H : Type u_1} [topological_space H] {e : local_homeomorph H H} : e ∈ charted_space.atlas H H ↔ e = local_homeomorph.refl H := sorry

/-- In the model space, chart_at is always the identity -/
@[simp] theorem chart_at_self_eq {H : Type u_1} [topological_space H] {x : H} : charted_space.chart_at H x = local_homeomorph.refl H :=
  eq.mpr (id (Eq.refl (charted_space.chart_at H x = local_homeomorph.refl H)))
    (eq.mp (propext charted_space_self_atlas) (charted_space.chart_mem_atlas H x))

/-- Same thing as `H × H'`. We introduce it for technical reasons: a charted space `M` with model `H`
is a set of local charts from `M` to `H` covering the space. Every space is registered as a charted
space over itself, using the only chart `id`, in `manifold_model_space`. You can also define a product
of charted space `M` and `M'` (with model space `H × H'`) by taking the products of the charts. Now,
on `H × H'`, there are two charted space structures with model space `H × H'` itself, the one coming
from `manifold_model_space`, and the one coming from the product of the two `manifold_model_space` on
each component. They are equal, but not defeq (because the product of `id` and `id` is not defeq to
`id`), which is bad as we know. This expedient of renaming `H × H'` solves this problem. -/
def model_prod (H : Type u_1) (H' : Type u_2)  :=
  H × H'

protected instance model_prod_inhabited {α : Type u_1} {β : Type u_2} [Inhabited α] [Inhabited β] : Inhabited (model_prod α β) :=
  { default := (Inhabited.default, Inhabited.default) }

protected instance model_prod.topological_space (H : Type u_1) [topological_space H] (H' : Type u_2) [topological_space H'] : topological_space (model_prod H H') :=
  prod.topological_space

/- Next lemma shows up often when dealing with derivatives, register it as simp. -/

@[simp] theorem model_prod_range_prod_id {H : Type u_1} {H' : Type u_2} {α : Type u_3} (f : H → α) : (set.range fun (p : model_prod H H') => (f (prod.fst p), prod.snd p)) = set.prod (set.range f) set.univ := sorry

/-- The product of two charted spaces is naturally a charted space, with the canonical
construction of the atlas of product maps. -/
protected instance prod_charted_space (H : Type u_1) [topological_space H] (M : Type u_2) [topological_space M] [charted_space H M] (H' : Type u_3) [topological_space H'] (M' : Type u_4) [topological_space M'] [charted_space H' M'] : charted_space (model_prod H H') (M × M') :=
  charted_space.mk
    (set_of
      fun (f : local_homeomorph (M × M') (model_prod H H')) =>
        ∃ (g : local_homeomorph M H),
          ∃ (H_1 : g ∈ charted_space.atlas H M),
            ∃ (h : local_homeomorph M' H'), ∃ (H_2 : h ∈ charted_space.atlas H' M'), f = local_homeomorph.prod g h)
    (fun (x : M × M') =>
      local_homeomorph.prod (charted_space.chart_at H (prod.fst x)) (charted_space.chart_at H' (prod.snd x)))
    sorry sorry

@[simp] theorem prod_charted_space_chart_at {H : Type u} {H' : Type u_1} {M : Type u_2} {M' : Type u_3} [topological_space H] [topological_space M] [charted_space H M] [topological_space H'] [topological_space M'] [charted_space H' M'] {x : M × M'} : charted_space.chart_at (model_prod H H') x =
  local_homeomorph.prod (charted_space.chart_at H (prod.fst x)) (charted_space.chart_at H' (prod.snd x)) :=
  rfl

/-! ### Constructing a topology from an atlas -/

/-- Sometimes, one may want to construct a charted space structure on a space which does not yet
have a topological structure, where the topology would come from the charts. For this, one needs
charts that are only local equivs, and continuity properties for their composition.
This is formalised in `charted_space_core`. -/
structure charted_space_core (H : Type u_5) [topological_space H] (M : Type u_6) 
where
  atlas : set (local_equiv M H)
  chart_at : M → local_equiv M H
  mem_chart_source : ∀ (x : M), x ∈ local_equiv.source (chart_at x)
  chart_mem_atlas : ∀ (x : M), chart_at x ∈ atlas
  open_source : ∀ (e e' : local_equiv M H),
  e ∈ atlas → e' ∈ atlas → is_open (local_equiv.source (local_equiv.trans (local_equiv.symm e) e'))
  continuous_to_fun : ∀ (e e' : local_equiv M H),
  e ∈ atlas →
    e' ∈ atlas →
      continuous_on (⇑(local_equiv.trans (local_equiv.symm e) e'))
        (local_equiv.source (local_equiv.trans (local_equiv.symm e) e'))

namespace charted_space_core


/-- Topology generated by a set of charts on a Type. -/
protected def to_topological_space {H : Type u} {M : Type u_2} [topological_space H] (c : charted_space_core H M) : topological_space M :=
  topological_space.generate_from
    (set.Union
      fun (e : local_equiv M H) =>
        set.Union
          fun (he : e ∈ atlas c) =>
            set.Union
              fun (s : set H) => set.Union fun (s_open : is_open s) => singleton (⇑e ⁻¹' s ∩ local_equiv.source e))

theorem open_source' {H : Type u} {M : Type u_2} [topological_space H] (c : charted_space_core H M) {e : local_equiv M H} (he : e ∈ atlas c) : is_open (local_equiv.source e) := sorry

theorem open_target {H : Type u} {M : Type u_2} [topological_space H] (c : charted_space_core H M) {e : local_equiv M H} (he : e ∈ atlas c) : is_open (local_equiv.target e) := sorry

/-- An element of the atlas in a charted space without topology becomes a local homeomorphism
for the topology constructed from this atlas. The `local_homeomorph` version is given in this
definition. -/
def local_homeomorph {H : Type u} {M : Type u_2} [topological_space H] (c : charted_space_core H M) (e : local_equiv M H) (he : e ∈ atlas c) : local_homeomorph M H :=
  local_homeomorph.mk
    (local_equiv.mk (local_equiv.to_fun e) (local_equiv.inv_fun e) (local_equiv.source e) (local_equiv.target e)
      (local_equiv.map_source' e) (local_equiv.map_target' e) (local_equiv.left_inv' e) (local_equiv.right_inv' e))
    sorry sorry sorry sorry

/-- Given a charted space without topology, endow it with a genuine charted space structure with
respect to the topology constructed from the atlas. -/
def to_charted_space {H : Type u} {M : Type u_2} [topological_space H] (c : charted_space_core H M) : charted_space H M :=
  charted_space.mk
    (set.Union fun (e : local_equiv M H) => set.Union fun (he : e ∈ atlas c) => singleton (local_homeomorph c e he))
    (fun (x : M) => local_homeomorph c (chart_at c x) (chart_mem_atlas c x)) sorry sorry

end charted_space_core


/-! ### Charted space with a given structure groupoid -/

/-- A charted space has an atlas in a groupoid `G` if the change of coordinates belong to the
groupoid -/
class has_groupoid {H : Type u_5} [topological_space H] (M : Type u_6) [topological_space M] [charted_space H M] (G : structure_groupoid H) 
where
  compatible : ∀ {e e' : local_homeomorph M H},
  e ∈ charted_space.atlas H M → e' ∈ charted_space.atlas H M → local_homeomorph.trans (local_homeomorph.symm e) e' ∈ G

/-- Reformulate in the `structure_groupoid` namespace the compatibility condition of charts in a
charted space admitting a structure groupoid, to make it more easily accessible with dot
notation. -/
theorem structure_groupoid.compatible {H : Type u_1} [topological_space H] (G : structure_groupoid H) {M : Type u_2} [topological_space M] [charted_space H M] [has_groupoid M G] {e : local_homeomorph M H} {e' : local_homeomorph M H} (he : e ∈ charted_space.atlas H M) (he' : e' ∈ charted_space.atlas H M) : local_homeomorph.trans (local_homeomorph.symm e) e' ∈ G :=
  has_groupoid.compatible G he he'

theorem has_groupoid_of_le {H : Type u} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G₁ : structure_groupoid H} {G₂ : structure_groupoid H} (h : has_groupoid M G₁) (hle : G₁ ≤ G₂) : has_groupoid M G₂ :=
  has_groupoid.mk
    fun (e e' : local_homeomorph M H) (he : e ∈ charted_space.atlas H M) (he' : e' ∈ charted_space.atlas H M) =>
      hle (has_groupoid.compatible G₁ he he')

theorem has_groupoid_of_pregroupoid {H : Type u} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] (PG : pregroupoid H) (h : ∀ {e e' : local_homeomorph M H},
  e ∈ charted_space.atlas H M →
    e' ∈ charted_space.atlas H M →
      pregroupoid.property PG (⇑(local_homeomorph.trans (local_homeomorph.symm e) e'))
        (local_equiv.source (local_homeomorph.to_local_equiv (local_homeomorph.trans (local_homeomorph.symm e) e')))) : has_groupoid M (pregroupoid.groupoid PG) :=
  has_groupoid.mk
    fun (e e' : local_homeomorph M H) (he : e ∈ charted_space.atlas H M) (he' : e' ∈ charted_space.atlas H M) =>
      iff.mpr mem_groupoid_of_pregroupoid { left := h he he', right := h he' he }

/-- The trivial charted space structure on the model space is compatible with any groupoid -/
protected instance has_groupoid_model_space (H : Type u_1) [topological_space H] (G : structure_groupoid H) : has_groupoid H G := sorry

/-- Any charted space structure is compatible with the groupoid of all local homeomorphisms -/
protected instance has_groupoid_continuous_groupoid {H : Type u} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] : has_groupoid M (continuous_groupoid H) :=
  has_groupoid.mk
    fun (e e' : local_homeomorph M H) (he : e ∈ charted_space.atlas H M) (he' : e' ∈ charted_space.atlas H M) =>
      eq.mpr
        (id
          (Eq._oldrec (Eq.refl (local_homeomorph.trans (local_homeomorph.symm e) e' ∈ continuous_groupoid H))
            (continuous_groupoid.equations._eqn_1 H)))
        (eq.mpr
          (id
            (Eq._oldrec
              (Eq.refl
                (local_homeomorph.trans (local_homeomorph.symm e) e' ∈ pregroupoid.groupoid (continuous_pregroupoid H)))
              (propext mem_groupoid_of_pregroupoid)))
          (eq.mpr (id (propext (and_self True))) trivial))

/-- Given a charted space admitting a structure groupoid, the maximal atlas associated to this
structure groupoid is the set of all local charts that are compatible with the atlas, i.e., such
that changing coordinates with an atlas member gives an element of the groupoid. -/
def structure_groupoid.maximal_atlas {H : Type u} (M : Type u_2) [topological_space H] [topological_space M] [charted_space H M] (G : structure_groupoid H) : set (local_homeomorph M H) :=
  set_of
    fun (e : local_homeomorph M H) =>
      ∀ (e' : local_homeomorph M H),
        e' ∈ charted_space.atlas H M →
          local_homeomorph.trans (local_homeomorph.symm e) e' ∈ G ∧
            local_homeomorph.trans (local_homeomorph.symm e') e ∈ G

/-- The elements of the atlas belong to the maximal atlas for any structure groupoid -/
theorem structure_groupoid.mem_maximal_atlas_of_mem_atlas {H : Type u} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] (G : structure_groupoid H) [has_groupoid M G] {e : local_homeomorph M H} (he : e ∈ charted_space.atlas H M) : e ∈ structure_groupoid.maximal_atlas M G :=
  fun (e' : local_homeomorph M H) (he' : e' ∈ charted_space.atlas H M) =>
    { left := structure_groupoid.compatible G he he', right := structure_groupoid.compatible G he' he }

theorem structure_groupoid.chart_mem_maximal_atlas {H : Type u} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] (G : structure_groupoid H) [has_groupoid M G] (x : M) : charted_space.chart_at H x ∈ structure_groupoid.maximal_atlas M G :=
  structure_groupoid.mem_maximal_atlas_of_mem_atlas G (charted_space.chart_mem_atlas H x)

theorem mem_maximal_atlas_iff {H : Type u} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G : structure_groupoid H} {e : local_homeomorph M H} : e ∈ structure_groupoid.maximal_atlas M G ↔
  ∀ (e' : local_homeomorph M H),
    e' ∈ charted_space.atlas H M →
      local_homeomorph.trans (local_homeomorph.symm e) e' ∈ G ∧ local_homeomorph.trans (local_homeomorph.symm e') e ∈ G :=
  iff.rfl

/-- Changing coordinates between two elements of the maximal atlas gives rise to an element
of the structure groupoid. -/
theorem structure_groupoid.compatible_of_mem_maximal_atlas {H : Type u} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G : structure_groupoid H} {e : local_homeomorph M H} {e' : local_homeomorph M H} (he : e ∈ structure_groupoid.maximal_atlas M G) (he' : e' ∈ structure_groupoid.maximal_atlas M G) : local_homeomorph.trans (local_homeomorph.symm e) e' ∈ G := sorry

/-- In the model space, the identity is in any maximal atlas. -/
theorem structure_groupoid.id_mem_maximal_atlas {H : Type u} [topological_space H] (G : structure_groupoid H) : local_homeomorph.refl H ∈ structure_groupoid.maximal_atlas H G :=
  structure_groupoid.mem_maximal_atlas_of_mem_atlas G
    (eq.mpr (id (Eq.trans (propext charted_space_self_atlas) (propext (eq_self_iff_true (local_homeomorph.refl H)))))
      trivial)

/-- If a single local homeomorphism `e` from a space `α` into `H` has source covering the whole
space `α`, then that local homeomorphism induces an `H`-charted space structure on `α`.
(This condition is equivalent to `e` being an open embedding of `α` into `H`; see
`local_homeomorph.to_open_embedding` and `open_embedding.to_local_homeomorph`.) -/
def singleton_charted_space {H : Type u} [topological_space H] {α : Type u_5} [topological_space α] (e : local_homeomorph α H) (h : local_equiv.source (local_homeomorph.to_local_equiv e) = set.univ) : charted_space H α :=
  charted_space.mk (singleton e) (fun (_x : α) => e) sorry sorry

theorem singleton_charted_space_one_chart {H : Type u} [topological_space H] {α : Type u_5} [topological_space α] (e : local_homeomorph α H) (h : local_equiv.source (local_homeomorph.to_local_equiv e) = set.univ) (e' : local_homeomorph α H) (h' : e' ∈ charted_space.atlas H α) : e' = e :=
  h'

/-- Given a local homeomorphism `e` from a space `α` into `H`, if its source covers the whole
space `α`, then the induced charted space structure on `α` is `has_groupoid G` for any structure
groupoid `G` which is closed under restrictions. -/
theorem singleton_has_groupoid {H : Type u} [topological_space H] {α : Type u_5} [topological_space α] (e : local_homeomorph α H) (h : local_equiv.source (local_homeomorph.to_local_equiv e) = set.univ) (G : structure_groupoid H) [closed_under_restriction G] : has_groupoid α G := sorry

namespace topological_space.opens


/-- An open subset of a charted space is naturally a charted space. -/
protected instance charted_space {H : Type u} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] (s : opens M) : charted_space H ↥s :=
  charted_space.mk
    (set.Union fun (x : ↥s) => singleton (local_homeomorph.subtype_restr (charted_space.chart_at H (subtype.val x)) s))
    (fun (x : ↥s) => local_homeomorph.subtype_restr (charted_space.chart_at H (subtype.val x)) s) sorry sorry

/-- If a groupoid `G` is `closed_under_restriction`, then an open subset of a space which is
`has_groupoid G` is naturally `has_groupoid G`. -/
protected instance has_groupoid {H : Type u} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] (G : structure_groupoid H) [has_groupoid M G] (s : opens M) [closed_under_restriction G] : has_groupoid (↥s) G := sorry

end topological_space.opens


/-! ### Structomorphisms -/

/-- A `G`-diffeomorphism between two charted spaces is a homeomorphism which, when read in the
charts, belongs to `G`. We avoid the word diffeomorph as it is too related to the smooth category,
and use structomorph instead. -/
structure structomorph {H : Type u} [topological_space H] (G : structure_groupoid H) (M : Type u_5) (M' : Type u_6) [topological_space M] [topological_space M'] [charted_space H M] [charted_space H M'] 
extends M ≃ₜ M'
where
  mem_groupoid : ∀ (c : local_homeomorph M H) (c' : local_homeomorph M' H),
  c ∈ charted_space.atlas H M →
    c' ∈ charted_space.atlas H M' →
      local_homeomorph.trans (local_homeomorph.symm c)
          (local_homeomorph.trans (homeomorph.to_local_homeomorph _to_homeomorph) c') ∈
        G

/-- The identity is a diffeomorphism of any charted space, for any groupoid. -/
def structomorph.refl {H : Type u} [topological_space H] {G : structure_groupoid H} (M : Type u_1) [topological_space M] [charted_space H M] [has_groupoid M G] : structomorph G M M :=
  structomorph.mk (homeomorph.mk (homeomorph.to_equiv (homeomorph.refl M))) sorry

/-- The inverse of a structomorphism is a structomorphism -/
def structomorph.symm {H : Type u} {M : Type u_2} {M' : Type u_3} [topological_space H] [topological_space M] [charted_space H M] [topological_space M'] {G : structure_groupoid H} [charted_space H M'] (e : structomorph G M M') : structomorph G M' M :=
  structomorph.mk (homeomorph.mk (homeomorph.to_equiv (homeomorph.symm (structomorph.to_homeomorph e)))) sorry

/-- The composition of structomorphisms is a structomorphism -/
def structomorph.trans {H : Type u} {M : Type u_2} {M' : Type u_3} {M'' : Type u_4} [topological_space H] [topological_space M] [charted_space H M] [topological_space M'] [topological_space M''] {G : structure_groupoid H} [charted_space H M'] [charted_space H M''] (e : structomorph G M M') (e' : structomorph G M' M'') : structomorph G M M'' :=
  structomorph.mk
    (homeomorph.mk
      (homeomorph.to_equiv (homeomorph.trans (structomorph.to_homeomorph e) (structomorph.to_homeomorph e'))))
    sorry

