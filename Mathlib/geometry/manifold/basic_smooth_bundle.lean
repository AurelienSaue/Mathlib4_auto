/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.topological_fiber_bundle
import Mathlib.geometry.manifold.smooth_manifold_with_corners
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 l 

namespace Mathlib

/-!
# Basic smooth bundles

In general, a smooth bundle is a bundle over a smooth manifold, whose fiber is a manifold, and
for which the coordinate changes are smooth. In this definition, there are charts involved at
several places: in the manifold structure of the base, in the manifold structure of the fibers, and
in the local trivializations. This makes it a complicated object in general. There is however a
specific situation where things are much simpler: when the fiber is a vector space (no need for
charts for the fibers), and when the local trivializations of the bundle and the charts of the base
coincide. Then everything is expressed in terms of the charts of the base, making for a much
simpler overall structure, which is easier to manipulate formally.

Most vector bundles that naturally occur in differential geometry are of this form:
the tangent bundle, the cotangent bundle, differential forms (used to define de Rham cohomology)
and the bundle of Riemannian metrics. Therefore, it is worth defining a specific constructor for
this kind of bundle, that we call basic smooth bundles.

A basic smooth bundle is thus a smooth bundle over a smooth manifold whose fiber is a vector space,
and which is trivial in the coordinate charts of the base. (We recall that in our notion of manifold
there is a distinguished atlas, which does not need to be maximal: we require the triviality above
this specific atlas). It can be constructed from a basic smooth bundled core, defined below,
specifying the changes in the fiber when one goes from one coordinate chart to another one. We do
not require that this changes in fiber are linear, but only diffeomorphisms.

## Main definitions

* `basic_smooth_bundle_core I M F`: assuming that `M` is a smooth manifold over the model with
  corners `I` on `(𝕜, E, H)`, and `F` is a normed vector space over `𝕜`, this structure registers,
  for each pair of charts of `M`, a smooth change of coordinates on `F`. This is the core structure
  from which one will build a smooth bundle with fiber `F` over `M`.

Let `Z` be a basic smooth bundle core over `M` with fiber `F`. We define
`Z.to_topological_fiber_bundle_core`, the (topological) fiber bundle core associated to `Z`. From it,
we get a space `Z.to_topological_fiber_bundle_core.total_space` (which as a Type is just
`Σ (x : M), F`), with the fiber bundle topology. It inherits a manifold structure (where the
charts are in bijection with the charts of the basis). We show that this manifold is smooth.

Then we use this machinery to construct the tangent bundle of a smooth manifold.

* `tangent_bundle_core I M`: the basic smooth bundle core associated to a smooth manifold `M` over a
  model with corners `I`.
* `tangent_bundle I M`     : the total space of `tangent_bundle_core I M`. It is itself a
  smooth manifold over the model with corners `I.tangent`, the product of `I` and the trivial model
  with corners on `E`.
* `tangent_space I x`      : the tangent space to `M` at `x`
* `tangent_bundle.proj I M`: the projection from the tangent bundle to the base manifold

## Implementation notes

In the definition of a basic smooth bundle core, we do not require that the coordinate changes of
the fibers are linear map, only that they are diffeomorphisms. Therefore, the fibers of the
resulting fiber bundle do not inherit a vector space structure (as an algebraic object) in general.
As the fiber, as a type, is just `F`, one can still always register the vector space structure, but
it does not make sense to do so (i.e., it will not lead to any useful theorem) unless this structure
is canonical, i.e., the coordinate changes are linear maps.

For instance, we register the vector space structure on the fibers of the tangent bundle. However,
we do not register the normed space structure coming from that of `F` (as it is not canonical, and
we also want to keep the possibility to add a Riemannian structure on the manifold later on without
having two competing normed space instances on the tangent spaces).

We require `F` to be a normed space, and not just a topological vector space, as we want to talk
about smooth functions on `F`. The notion of derivative requires a norm to be defined.

## TODO
construct the cotangent bundle, and the bundles of differential forms. They should follow
functorially from the description of the tangent bundle as a basic smooth bundle.

## Tags
Smooth fiber bundle, vector bundle, tangent space, tangent bundle
-/

/-- Core structure used to create a smooth bundle above `M` (a manifold over the model with
corner `I`) with fiber the normed vector space `F` over `𝕜`, which is trivial in the chart domains
of `M`. This structure registers the changes in the fibers when one changes coordinate charts in the
base. We do not require the change of coordinates of the fibers to be linear, only smooth.
Therefore, the fibers of the resulting bundle will not inherit a canonical vector space structure
in general. -/
structure basic_smooth_bundle_core {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) (M : Type u_4) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (F : Type u_5) [normed_group F] [normed_space 𝕜 F] 
where
  coord_change : ↥(charted_space.atlas H M) → ↥(charted_space.atlas H M) → H → F → F
  coord_change_self : ∀ (i : ↥(charted_space.atlas H M)) (x : H),
  x ∈ local_equiv.target (local_homeomorph.to_local_equiv (subtype.val i)) → ∀ (v : F), coord_change i i x v = v
  coord_change_comp : ∀ (i j k : ↥(charted_space.atlas H M)) (x : H),
  x ∈
      local_equiv.source
        (local_homeomorph.to_local_equiv
          (local_homeomorph.trans (local_homeomorph.trans (local_homeomorph.symm (subtype.val i)) (subtype.val j))
            (local_homeomorph.trans (local_homeomorph.symm (subtype.val j)) (subtype.val k)))) →
    ∀ (v : F),
      coord_change j k (coe_fn (local_homeomorph.trans (local_homeomorph.symm (subtype.val i)) (subtype.val j)) x)
          (coord_change i j x v) =
        coord_change i k x v
  coord_change_smooth : ∀ (i j : ↥(charted_space.atlas H M)),
  times_cont_diff_on 𝕜 ⊤
    (fun (p : E × F) => coord_change i j (coe_fn (model_with_corners.symm I) (prod.fst p)) (prod.snd p))
    (set.prod
      (⇑I ''
        local_equiv.source
          (local_homeomorph.to_local_equiv
            (local_homeomorph.trans (local_homeomorph.symm (subtype.val i)) (subtype.val j))))
      set.univ)

/-- The trivial basic smooth bundle core, in which all the changes of coordinates are the
identity. -/
def trivial_basic_smooth_bundle_core {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) (M : Type u_4) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (F : Type u_5) [normed_group F] [normed_space 𝕜 F] : basic_smooth_bundle_core I M F :=
  basic_smooth_bundle_core.mk (fun (i j : ↥(charted_space.atlas H M)) (x : H) (v : F) => v) sorry sorry sorry

namespace basic_smooth_bundle_core


protected instance inhabited {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {F : Type u_5} [normed_group F] [normed_space 𝕜 F] : Inhabited (basic_smooth_bundle_core I M F) :=
  { default := trivial_basic_smooth_bundle_core I M F }

/-- Fiber bundle core associated to a basic smooth bundle core -/
def to_topological_fiber_bundle_core {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {F : Type u_5} [normed_group F] [normed_space 𝕜 F] (Z : basic_smooth_bundle_core I M F) : topological_fiber_bundle_core (↥(charted_space.atlas H M)) M F :=
  topological_fiber_bundle_core.mk
    (fun (i : ↥(charted_space.atlas H M)) => local_equiv.source (local_homeomorph.to_local_equiv (subtype.val i))) sorry
    (fun (x : M) => { val := charted_space.chart_at H x, property := charted_space.chart_mem_atlas H x }) sorry
    (fun (i j : ↥(charted_space.atlas H M)) (x : M) (v : F) => coord_change Z i j (coe_fn (subtype.val i) x) v) sorry
    sorry sorry

@[simp] theorem base_set {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {F : Type u_5} [normed_group F] [normed_space 𝕜 F] (Z : basic_smooth_bundle_core I M F) (i : ↥(charted_space.atlas H M)) : topological_fiber_bundle_core.base_set (to_topological_fiber_bundle_core Z) i =
  local_equiv.source (local_homeomorph.to_local_equiv (subtype.val i)) :=
  rfl

/-- Local chart for the total space of a basic smooth bundle -/
def chart {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {F : Type u_5} [normed_group F] [normed_space 𝕜 F] (Z : basic_smooth_bundle_core I M F) {e : local_homeomorph M H} (he : e ∈ charted_space.atlas H M) : local_homeomorph (topological_fiber_bundle_core.total_space (to_topological_fiber_bundle_core Z)) (model_prod H F) :=
  local_homeomorph.trans
    (topological_fiber_bundle_core.local_triv (to_topological_fiber_bundle_core Z) { val := e, property := he })
    (local_homeomorph.prod e (local_homeomorph.refl F))

@[simp] theorem chart_source {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {F : Type u_5} [normed_group F] [normed_space 𝕜 F] (Z : basic_smooth_bundle_core I M F) (e : local_homeomorph M H) (he : e ∈ charted_space.atlas H M) : local_equiv.source (local_homeomorph.to_local_equiv (chart Z he)) =
  topological_fiber_bundle_core.proj (to_topological_fiber_bundle_core Z) ⁻¹'
    local_equiv.source (local_homeomorph.to_local_equiv e) := sorry

@[simp] theorem chart_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {F : Type u_5} [normed_group F] [normed_space 𝕜 F] (Z : basic_smooth_bundle_core I M F) (e : local_homeomorph M H) (he : e ∈ charted_space.atlas H M) : local_equiv.target (local_homeomorph.to_local_equiv (chart Z he)) =
  set.prod (local_equiv.target (local_homeomorph.to_local_equiv e)) set.univ := sorry

/-- The total space of a basic smooth bundle is endowed with a charted space structure, where the
charts are in bijection with the charts of the basis. -/
protected instance to_charted_space {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {F : Type u_5} [normed_group F] [normed_space 𝕜 F] (Z : basic_smooth_bundle_core I M F) : charted_space (model_prod H F) (topologi