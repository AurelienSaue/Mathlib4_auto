/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.local_homeomorph
import PostPort

universes u_2 u_3 u_4 l u_5 u_6 u_1 

namespace Mathlib

/-!
# Fiber bundles

A topological fiber bundle with fiber `F` over a base `B` is a space projecting on `B` for which the
fibers are all homeomorphic to `F`, such that the local situation around each point is a direct
product. We define a predicate `is_topological_fiber_bundle F p` saying that `p : Z → B` is a
topological fiber bundle with fiber `F`.

It is in general nontrivial to construct a fiber bundle. A way is to start from the knowledge of
how changes of local trivializations act on the fiber. From this, one can construct the total space
of the bundle and its topology by a suitable gluing construction. The main content of this file is
an implementation of this construction: starting from an object of type
`topological_fiber_bundle_core` registering the trivialization changes, one gets the corresponding
fiber bundle and projection.

## Main definitions

* `bundle_trivialization F p` : structure extending local homeomorphisms, defining a local
                  trivialization of a topological space `Z` with projection `p` and fiber `F`.
* `is_topological_fiber_bundle F p` : Prop saying that the map `p` between topological spaces is a
                  fiber bundle with fiber `F`.

* `topological_fiber_bundle_core ι B F` : structure registering how changes of coordinates act
  on the fiber `F` above open subsets of `B`, where local trivializations are indexed by `ι`.

Let `Z : topological_fiber_bundle_core ι B F`. Then we define

* `Z.total_space` : the total space of `Z`, defined as a `Type` as `Σ (b : B), F`, but with a
  twisted topology coming from the fiber bundle structure
* `Z.proj`        : projection from `Z.total_space` to `B`. It is continuous.
* `Z.fiber x`     : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
* `Z.local_triv i`: for `i : ι`, a local homeomorphism from `Z.total_space` to `B × F`, that
  realizes a trivialization above the set `Z.base_set i`, which is an open set in `B`.

## Implementation notes

A topological fiber bundle with fiber `F` over a base `B` is a family of spaces isomorphic to `F`,
indexed by `B`, which is locally trivial in the following sense: there is a covering of `B` by open
sets such that, on each such open set `s`, the bundle is isomorphic to `s × F`.

To construct a fiber bundle formally, the main data is what happens when one changes trivializations
from `s × F` to `s' × F` on `s ∩ s'`: one should get a family of homeomorphisms of `F`, depending
continuously on the base point, satisfying basic compatibility conditions (cocycle property).
Useful classes of bundles can then be specified by requiring that these homeomorphisms of `F`
belong to some subgroup, preserving some structure (the "structure group of the bundle"): then
these structures are inherited by the fibers of the bundle.

Given such trivialization change data (encoded below in a structure called
`topological_fiber_bundle_core`), one can construct the fiber bundle. The intrinsic canonical
mathematical construction is the following.
The fiber above `x` is the disjoint union of `F` over all trivializations, modulo the gluing
identifications: one gets a fiber which is isomorphic to `F`, but non-canonically
(each choice of one of the trivializations around `x` gives such an isomorphism). Given a
trivialization over a set `s`, one gets an isomorphism between `s × F` and `proj^{-1} s`, by using
the identification corresponding to this trivialization. One chooses the topology on the bundle that
makes all of these into homeomorphisms.

For the practical implementation, it turns out to be more convenient to avoid completely the
gluing and quotienting construction above, and to declare above each `x` that the fiber is `F`,
but thinking that it corresponds to the `F` coming from the choice of one trivialization around `x`.
This has several practical advantages:
* without any work, one gets a topological space structure on the fiber. And if `F` has more
structure it is inherited for free by the fiber.
* In the case of the tangent bundle of manifolds, this implies that on vector spaces the derivative
(from `F` to `F`) and the manifold derivative (from `tangent_space I x` to `tangent_space I' (f x)`)
are equal.

A drawback is that some silly constructions will typecheck: in the case of the tangent bundle, one
can add two vectors in different tangent spaces (as they both are elements of `F` from the point of
view of Lean). To solve this, one could mark the tangent space as irreducible, but then one would
lose the identification of the tangent space to `F` with `F`. There is however a big advantage of
this situation: even if Lean can not check that two basepoints are defeq, it will accept the fact
that the tangent spaces are the same. For instance, if two maps `f` and `g` are locally inverse to
each other, one can express that the composition of their derivatives is the identity of
`tangent_space I x`. One could fear issues as this composition goes from `tangent_space I x` to
`tangent_space I (g (f x))` (which should be the same, but should not be obvious to Lean
as it does not know that `g (f x) = x`). As these types are the same to Lean (equal to `F`), there
are in fact no dependent type difficulties here!

For this construction of a fiber bundle from a `topological_fiber_bundle_core`, we should thus
choose for each `x` one specific trivialization around it. We include this choice in the definition
of the `topological_fiber_bundle_core`, as it makes some constructions more
functorial and it is a nice way to say that the trivializations cover the whole space `B`.

With this definition, the type of the fiber bundle space constructed from the core data is just
`Σ (b : B), F `, but the topology is not the product one, in general.

We also take the indexing type (indexing all the trivializations) as a parameter to the fiber bundle
core: it could always be taken as a subtype of all the maps from open subsets of `B` to continuous
maps of `F`, but in practice it will sometimes be something else. For instance, on a manifold, one
will use the set of charts as a good parameterization for the trivializations of the tangent bundle.
Or for the pullback of a `topological_fiber_bundle_core`, the indexing type will be the same as
for the initial bundle.

## Tags
Fiber bundle, topological bundle, vector bundle, local trivialization, structure group
-/

/--
A structure extending local homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a local homeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
structure bundle_trivialization {B : Type u_2} (F : Type u_3) {Z : Type u_4} [topological_space B] [topological_space Z] [topological_space F] (proj : Z → B) 
extends local_homeomorph Z (B × F)
where
  base_set : set B
  open_base_set : is_open base_set
  source_eq : local_equiv.source (local_homeomorph.to_local_equiv _to_local_homeomorph) = proj ⁻¹' base_set
  target_eq : local_equiv.target (local_homeomorph.to_local_equiv _to_local_homeomorph) = set.prod base_set set.univ
  proj_to_fun : ∀ (p : Z),
  p ∈ local_equiv.source (local_homeomorph.to_local_equiv _to_local_homeomorph) →
    prod.fst (local_equiv.to_fun (local_homeomorph.to_local_equiv _to_local_homeomorph) p) = proj p

protected instance bundle_trivialization.has_coe_to_fun {B : Type u_2} (F : Type u_3) {Z : Type u_4} [topological_space B] [topological_space Z] [topological_space F] (proj : Z → B) : has_coe_to_fun (bundle_trivialization F proj) :=
  has_coe_to_fun.mk (fun (e : bundle_trivialization F proj) => Z → B × F)
    fun (e : bundle_trivialization F proj) =>
      local_equiv.to_fun (local_homeomorph.to_local_equiv (bundle_trivialization.to_local_homeomorph e))

@[simp] theorem bundle_trivialization.coe_coe {B : Type u_2} (F : Type u_3) {Z : Type u_4} [topological_space B] [topological_space Z] [topological_space F] (proj : Z → B) (e : bundle_trivialization F proj) (x : Z) : coe_fn (bundle_trivialization.to_local_homeomorph e) x = coe_fn e x :=
  rfl

@[simp] theorem bundle_trivialization.coe_mk {B : Type u_2} (F : Type u_3) {Z : Type u_4} [topological_space B] [topological_space Z] [topological_space F] (proj : Z → B) (e : local_homeomorph Z (B × F)) (i : set B) (j : is_open i) (k : local_equiv.source (local_homeomorph.to_local_equiv e) = proj ⁻¹' i) (l : local_equiv.target (local_homeomorph.to_local_equiv e) = set.prod i set.univ) (m : ∀ (p : Z),
  p ∈ local_equiv.source (local_homeomorph.to_local_equiv e) →
    prod.fst (local_equiv.to_fun (local_homeomorph.to_local_equiv e) p) = proj p) (x : Z) : coe_fn (bundle_trivialization.mk e i j k l m) x = coe_fn e x :=
  rfl

/-- A topological fiber bundle with fiber F over a base B is a space projecting on B for which the
fibers are all homeomorphic to F, such that the local situation around each point is a direct
product. -/
def is_topological_fiber_bundle {B : Type u_2} (F : Type u_3) {Z : Type u_4} [topological_space B] [topological_space Z] [topological_space F] (proj : Z → B)  :=
  ∀ (x : Z),
    ∃ (e : bundle_trivialization F proj),
      x ∈ local_equiv.source (local_homeomorph.to_local_equiv (bundle_trivialization.to_local_homeomorph e))

@[simp] theorem bundle_trivialization.coe_fst {B : Type u_2} {F : Type u_3} {Z : Type u_4} [topological_space B] [topological_space Z] [topological_space F] {proj : Z → B} (e : bundle_trivialization F proj) {x : Z} (ex : x ∈ local_equiv.source (local_homeomorph.to_local_equiv (bundle_trivialization.to_local_homeomorph e))) : prod.fst (coe_fn e x) = proj x :=
  bundle_trivialization.proj_to_fun e x ex

/-- In the domain of a bundle trivialization, the projection is continuous-/
theorem bundle_trivialization.continuous_at_proj {B : Type u_2} {F : Type u_3} {Z : Type u_4} [topological_space B] [topological_space Z] [topological_space F] {proj : Z → B} (e : bundle_trivialization F proj) {x : Z} (ex : x ∈ local_equiv.source (local_homeomorph.to_local_equiv (bundle_trivialization.to_local_homeomorph e))) : continuous_at proj x := sorry

/-- The projection from a topological fiber bundle to its base is continuous. -/
theorem is_topological_fiber_bundle.continuous_proj {B : Type u_2} {F : Type u_3} {Z : Type u_4} [topological_space B] [topological_space Z] [topological_space F] {proj : Z → B} (h : is_topological_fiber_bundle F proj) : continuous proj := sorry

/-- The projection from a topological fiber bundle to its base is an open map. -/
theorem is_topological_fiber_bundle.is_open_map_proj {B : Type u_2} {F : Type u_3} {Z : Type u_4} [topological_space B] [topological_space Z] [topological_space F] {proj : Z → B} (h : is_topological_fiber_bundle F proj) : is_open_map proj := sorry

/-- The first projection in a product is a topological fiber bundle. -/
theorem is_topological_fiber_bundle_fst {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] : is_topological_fiber_bundle F prod.fst := sorry

/-- The second projection in a product is a topological fiber bundle. -/
theorem is_topological_fiber_bundle_snd {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] : is_topological_fiber_bundle F prod.snd := sorry

/-- Core data defining a locally trivial topological bundle with fiber `F` over a topological
space `B`. Note that "bundle" is used in its mathematical sense. This is the (computer science)
bundled version, i.e., all the relevant data is contained in the following structure. A family of
local trivializations is indexed by a type ι, on open subsets `base_set i` for each `i : ι`.
Trivialization changes from `i` to `j` are given by continuous maps `coord_change i j` from
`base_set i ∩ base_set j` to the set of homeomorphisms of `F`, but we express them as maps
`B → F → F` and require continuity on `(base_set i ∩ base_set j) × F` to avoid the topology on the
space of continuous maps on `F`. -/
structure topological_fiber_bundle_core (ι : Type u_4) (B : Type u_5) [topological_space B] (F : Type u_6) [topological_space F] 
where
  base_set : ι → set B
  is_open_base_set : ∀ (i : ι), is_open (base_set i)
  index_at : B → ι
  mem_base_set_at : ∀ (x : B), x ∈ base_set (index_at x)
  coord_change : ι → ι → B → F → F
  coord_change_self : ∀ (i : ι) (x : B), x ∈ base_set i → ∀ (v : F), coord_change i i x v = v
  coord_change_continuous : ∀ (i j : ι),
  continuous_on (fun (p : B × F) => coord_change i j (prod.fst p) (prod.snd p))
    (set.prod (base_set i ∩ base_set j) set.univ)
  coord_change_comp : ∀ (i j k : ι) (x : B),
  x ∈ base_set i ∩ base_set j ∩ base_set k → ∀ (v : F), coord_change j k x (coord_change i j x v) = coord_change i k x v

namespace topological_fiber_bundle_core


/-- The index set of a topological fiber bundle core, as a convenience function for dot notation -/
def index {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F)  :=
  ι

/-- The base space of a topological fiber bundle core, as a convenience function for dot notation -/
def base {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F)  :=
  B

/-- The fiber of a topological fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
def fiber {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (x : B)  :=
  F

protected instance topological_space_fiber {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (x : B) : topological_space (fiber Z x) :=
  id _inst_2

/-- Total space of a topological bundle created from core. It is equal to `Σ (x : B), F` as a type,
but the fiber above `x` is registered as `Z.fiber x` to make sure that it is possible to register
additional type classes on these fibers. -/
def total_space {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F)  :=
  sigma fun (x : B) => fiber Z x

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[simp] def proj {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) : total_space Z → B :=
  fun (p : total_space Z) => sigma.fst p

/-- Local homeomorphism version of the trivialization change. -/
def triv_change {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (j : ι) : local_homeomorph (B × F) (B × F) :=
  local_homeomorph.mk
    (local_equiv.mk (fun (p : B × F) => (prod.fst p, coord_change Z i j (prod.fst p) (prod.snd p)))
      (fun (p : B × F) => (prod.fst p, coord_change Z j i (prod.fst p) (prod.snd p)))
      (set.prod (base_set Z i ∩ base_set Z j) set.univ) (set.prod (base_set Z i ∩ base_set Z j) set.univ) sorry sorry
      sorry sorry)
    sorry sorry sorry sorry

@[simp] theorem mem_triv_change_source {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (j : ι) (p : B × F) : p ∈ local_equiv.source (local_homeomorph.to_local_equiv (triv_change Z i j)) ↔ prod.fst p ∈ base_set Z i ∩ base_set Z j := sorry

/-- Associate to a trivialization index `i : ι` the corresponding trivialization, i.e., a bijection
between `proj ⁻¹ (base_set i)` and `base_set i × F`. As the fiber above `x` is `F` but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by definition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be a local homeomorphism. For now, we only introduce the
local equiv version, denoted with a prime. In further developments, avoid this auxiliary version,
and use Z.local_triv instead.
-/
def local_triv' {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) : local_equiv (total_space Z) (B × F) :=
  local_equiv.mk
    (fun (p : total_space Z) => (sigma.fst p, coord_change Z (index_at Z (sigma.fst p)) i (sigma.fst p) (sigma.snd p)))
    (fun (p : B × F) => sigma.mk (prod.fst p) (coord_change Z i (index_at Z (prod.fst p)) (prod.fst p) (prod.snd p)))
    (proj Z ⁻¹' base_set Z i) (set.prod (base_set Z i) set.univ) sorry sorry sorry sorry

@[simp] theorem mem_local_triv'_source {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (p : total_space Z) : p ∈ local_equiv.source (local_triv' Z i) ↔ sigma.fst p ∈ base_set Z i :=
  iff.refl (p ∈ local_equiv.source (local_triv' Z i))

@[simp] theorem mem_local_triv'_target {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (p : B × F) : p ∈ local_equiv.target (local_triv' Z i) ↔ prod.fst p ∈ base_set Z i := sorry

@[simp] theorem local_triv'_apply {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (p : total_space Z) : coe_fn (local_triv' Z i) p = (sigma.fst p, coord_change Z (index_at Z (sigma.fst p)) i (sigma.fst p) (sigma.snd p)) :=
  rfl

@[simp] theorem local_triv'_symm_apply {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (p : B × F) : coe_fn (local_equiv.symm (local_triv' Z i)) p =
  sigma.mk (prod.fst p) (coord_change Z i (index_at Z (prod.fst p)) (prod.fst p) (prod.snd p)) :=
  rfl

/-- The composition of two local trivializations is the trivialization change Z.triv_change i j. -/
theorem local_triv'_trans {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (j : ι) : local_equiv.trans (local_equiv.symm (local_triv' Z i)) (local_triv' Z j) ≈
  local_homeomorph.to_local_equiv (triv_change Z i j) := sorry

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
protected instance to_topological_space {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) : topological_space (total_space Z) :=
  topological_space.generate_from
    (set.Union
      fun (i : ι) =>
        set.Union
          fun (s : set (B × F)) =>
            set.Union
              fun (s_open : is_open s) => singleton (local_equiv.source (local_triv' Z i) ∩ ⇑(local_triv' Z i) ⁻¹' s))

theorem open_source' {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) : is_open (local_equiv.source (local_triv' Z i)) := sorry

theorem open_target' {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) : is_open (local_equiv.target (local_triv' Z i)) :=
  is_open.prod (is_open_base_set Z i) is_open_univ

/-- Local trivialization of a topological bundle created from core, as a local homeomorphism. -/
def local_triv {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) : local_homeomorph (total_space Z) (B × F) :=
  local_homeomorph.mk
    (local_equiv.mk (local_equiv.to_fun (local_triv' Z i)) (local_equiv.inv_fun (local_triv' Z i))
      (local_equiv.source (local_triv' Z i)) (local_equiv.target (local_triv' Z i)) sorry sorry sorry sorry)
    (open_source' Z i) (open_target' Z i) sorry sorry

/- We will now state again the basic properties of the local trivializations, but without primes,
i.e., for the local homeomorphism instead of the local equiv. -/

@[simp] theorem mem_local_triv_source {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (p : total_space Z) : p ∈ local_equiv.source (local_homeomorph.to_local_equiv (local_triv Z i)) ↔ sigma.fst p ∈ base_set Z i :=
  iff.refl (p ∈ local_equiv.source (local_homeomorph.to_local_equiv (local_triv Z i)))

@[simp] theorem mem_local_triv_target {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (p : B × F) : p ∈ local_equiv.target (local_homeomorph.to_local_equiv (local_triv Z i)) ↔ prod.fst p ∈ base_set Z i := sorry

@[simp] theorem local_triv_apply {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (p : total_space Z) : coe_fn (local_triv Z i) p = (sigma.fst p, coord_change Z (index_at Z (sigma.fst p)) i (sigma.fst p) (sigma.snd p)) :=
  rfl

@[simp] theorem local_triv_symm_fst {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (p : B × F) : coe_fn (local_homeomorph.symm (local_triv Z i)) p =
  sigma.mk (prod.fst p) (coord_change Z i (index_at Z (prod.fst p)) (prod.fst p) (prod.snd p)) :=
  rfl

/-- The composition of two local trivializations is the trivialization change Z.triv_change i j. -/
theorem local_triv_trans {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) (j : ι) : local_homeomorph.trans (local_homeomorph.symm (local_triv Z i)) (local_triv Z j) ≈ triv_change Z i j :=
  local_triv'_trans Z i j

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv_ext {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (i : ι) : bundle_trivialization F (proj Z) :=
  bundle_trivialization.mk
    (local_homeomorph.mk (local_homeomorph.to_local_equiv (local_triv Z i)) sorry sorry sorry sorry) (base_set Z i)
    (is_open_base_set Z i) sorry sorry sorry

/-- A topological fiber bundle constructed from core is indeed a topological fiber bundle. -/
theorem is_topological_fiber_bundle {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) : is_topological_fiber_bundle F (proj Z) := sorry

/-- The projection on the base of a topological bundle created from core is continuous -/
theorem continuous_proj {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) : continuous (proj Z) :=
  is_topological_fiber_bundle.continuous_proj (is_topological_fiber_bundle Z)

/-- The projection on the base of a topological bundle created from core is an open map -/
theorem is_open_map_proj {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) : is_open_map (proj Z) :=
  is_topological_fiber_bundle.is_open_map_proj (is_topological_fiber_bundle Z)

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a local homeomorphism -/
def local_triv_at {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (p : total_space Z) : local_homeomorph (total_space Z) (B × F) :=
  local_triv Z (index_at Z (proj Z p))

@[simp] theorem mem_local_triv_at_source {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (p : total_space Z) : p ∈ local_equiv.source (local_homeomorph.to_local_equiv (local_triv_at Z p)) := sorry

@[simp] theorem local_triv_at_fst {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (p : total_space Z) (q : total_space Z) : prod.fst (coe_fn (local_triv_at Z p) q) = sigma.fst q :=
  rfl

@[simp] theorem local_triv_at_symm_fst {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (p : total_space Z) (q : B × F) : sigma.fst (coe_fn (local_homeomorph.symm (local_triv_at Z p)) q) = prod.fst q :=
  rfl

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at_ext {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (p : total_space Z) : bundle_trivialization F (proj Z) :=
  local_triv_ext Z (index_at Z (proj Z p))

@[simp] theorem local_triv_at_ext_to_local_homeomorph {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (p : total_space Z) : bundle_trivialization.to_local_homeomorph (local_triv_at_ext Z p) = local_triv_at Z p :=
  rfl

/-- If an element of `F` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is continuous. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity 
section of the endomorphism bundle of a vector bundle. -/
theorem continuous_const_section {ι : Type u_1} {B : Type u_2} {F : Type u_3} [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F) (v : F) (h : ∀ (i j : ι) (x : B), x ∈ base_set Z i ∩ base_set Z j → coord_change Z i j x v = v) : continuous ((fun (this : B → total_space Z) => this) fun (x : B) => sigma.mk x v) := sorry

