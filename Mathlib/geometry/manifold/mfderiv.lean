/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.geometry.manifold.basic_smooth_bundle
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 

namespace Mathlib

/-!
# The derivative of functions between smooth manifolds

Let `M` and `M'` be two smooth manifolds with corners over a field `𝕜` (with respective models with
corners `I` on `(E, H)` and `I'` on `(E', H')`), and let `f : M → M'`. We define the
derivative of the function at a point, within a set or along the whole space, mimicking the API
for (Fréchet) derivatives. It is denoted by `mfderiv I I' f x`, where "m" stands for "manifold" and
"f" for "Fréchet" (as in the usual derivative `fderiv 𝕜 f x`).

## Main definitions

* `unique_mdiff_on I s` : predicate saying that, at each point of the set `s`, a function can have
  at most one derivative. This technical condition is important when we define
  `mfderiv_within` below, as otherwise there is an arbitrary choice in the derivative,
  and many properties will fail (for instance the chain rule). This is analogous to
  `unique_diff_on 𝕜 s` in a vector space.

Let `f` be a map between smooth manifolds. The following definitions follow the `fderiv` API.

* `mfderiv I I' f x` : the derivative of `f` at `x`, as a continuous linear map from the tangent
  space at `x` to the tangent space at `f x`. If the map is not differentiable, this is `0`.
* `mfderiv_within I I' f s x` : the derivative of `f` at `x` within `s`, as a continuous linear map
  from the tangent space at `x` to the tangent space at `f x`. If the map is not differentiable
  within `s`, this is `0`.
* `mdifferentiable_at I I' f x` : Prop expressing whether `f` is differentiable at `x`.
* `mdifferentiable_within_at 𝕜 f s x` : Prop expressing whether `f` is differentiable within `s`
  at `x`.
* `has_mfderiv_at I I' f s x f'` : Prop expressing whether `f` has `f'` as a derivative at `x`.
* `has_mfderiv_within_at I I' f s x f'` : Prop expressing whether `f` has `f'` as a derivative
  within `s` at `x`.
* `mdifferentiable_on I I' f s` : Prop expressing that `f` is differentiable on the set `s`.
* `mdifferentiable I I' f` : Prop expressing that `f` is differentiable everywhere.
* `tangent_map I I' f` : the derivative of `f`, as a map from the tangent bundle of `M` to the
  tangent bundle of `M'`.

We also establish results on the differential of the identity, constant functions, charts, extended
charts. For functions between vector spaces, we show that the usual notions and the manifold notions
coincide.

## Implementation notes

The tangent bundle is constructed using the machinery of topological fiber bundles, for which one
can define bundled morphisms and construct canonically maps from the total space of one bundle to
the total space of another one. One could use this mechanism to construct directly the derivative
of a smooth map. However, we want to define the derivative of any map (and let it be zero if the map
is not differentiable) to avoid proof arguments everywhere. This means we have to go back to the
details of the definition of the total space of a fiber bundle constructed from core, to cook up a
suitable definition of the derivative. It is the following: at each point, we have a preferred chart
(used to identify the fiber above the point with the model vector space in fiber bundles). Then one
should read the function using these preferred charts at `x` and `f x`, and take the derivative
of `f` in these charts.

Due to the fact that we are working in a model with corners, with an additional embedding `I` of the
model space `H` in the model vector space `E`, the charts taking values in `E` are not the original
charts of the manifold, but those ones composed with `I`, called extended charts. We define
`written_in_ext_chart I I' x f` for the function `f` written in the preferred extended charts.  Then
the manifold derivative of `f`, at `x`, is just the usual derivative of `written_in_ext_chart I I' x
f`, at the point `(ext_chart_at I x) x`.

There is a subtelty with respect to continuity: if the function is not continuous, then the image
of a small open set around `x` will not be contained in the source of the preferred chart around
`f x`, which means that when reading `f` in the chart one is losing some information. To avoid this,
we include continuity in the definition of differentiablity (which is reasonable since with any
definition, differentiability implies continuity).

*Warning*: the derivative (even within a subset) is a linear map on the whole tangent space. Suppose
that one is given a smooth submanifold `N`, and a function which is smooth on `N` (i.e., its
restriction to the subtype  `N` is smooth). Then, in the whole manifold `M`, the property
`mdifferentiable_on I I' f N` holds. However, `mfderiv_within I I' f N` is not uniquely defined
(what values would one choose for vectors that are transverse to `N`?), which can create issues down
the road. The problem here is that knowing the value of `f` along `N` does not determine the
differential of `f` in all directions. This is in contrast to the case where `N` would be an open
subset, or a submanifold with boundary of maximal dimension, where this issue does not appear.
The predicate `unique_mdiff_on I N` indicates that the derivative along `N` is unique if it exists,
and is an assumption in most statements requiring a form of uniqueness.

On a vector space, the manifold derivative and the usual derivative are equal. This means in
particular that they live on the same space, i.e., the tangent space is defeq to the original vector
space. To get this property is a motivation for our definition of the tangent space as a single
copy of the vector space, instead of more usual definitions such as the space of derivations, or
the space of equivalence classes of smooth curves in the manifold.

## Tags
Derivative, manifold
-/

/-!
### Derivative of maps between manifolds

The derivative of a smooth map `f` between smooth manifold `M` and `M'` at `x` is a bounded linear
map from the tangent space to `M` at `x`, to the tangent space to `M'` at `f x`. Since we defined
the tangent space using one specific chart, the formula for the derivative is written in terms of
this specific chart.

We use the names `mdifferentiable` and `mfderiv`, where the prefix letter `m` means "manifold".
-/

/-- Predicate ensuring that, at a point and within a set, a function can have at most one
derivative. This is expressed using the preferred chart at the considered point. -/
def unique_mdiff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (s : set M) (x : M) :=
  unique_diff_within_at 𝕜 (⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s ∩ set.range ⇑I) (coe_fn (ext_chart_at I x) x)

/-- Predicate ensuring that, at all points of a set, a function can have at most one derivative. -/
def unique_mdiff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] (s : set M) :=
  ∀ (x : M), x ∈ s → unique_mdiff_within_at I s x

/-- Conjugating a function to write it in the preferred charts around `x`. The manifold derivative
of `f` will just be the derivative of this conjugated function. -/
@[simp] def written_in_ext_chart_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (x : M) (f : M → M') : E → E' :=
  ⇑(ext_chart_at I' (f x)) ∘ f ∘ ⇑(local_equiv.symm (ext_chart_at I x))

/-- `mdifferentiable_within_at I I' f s x` indicates that the function `f` between manifolds
has a derivative at the point `x` within the set `s`.
This is a generalization of `differentiable_within_at` to manifolds.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def mdifferentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (f : M → M') (s : set M) (x : M) :=
  continuous_within_at f s x ∧
    differentiable_within_at 𝕜 (written_in_ext_chart_at I I' x f)
      (⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s ∩ set.range ⇑I) (coe_fn (ext_chart_at I x) x)

/-- `mdifferentiable_at I I' f x` indicates that the function `f` between manifolds
has a derivative at the point `x`.
This is a generalization of `differentiable_at` to manifolds.

We require continuity in the definition, as otherwise points close to `x` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def mdifferentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (f : M → M') (x : M) :=
  continuous_at f x ∧
    differentiable_within_at 𝕜 (written_in_ext_chart_at I I' x f) (set.range ⇑I) (coe_fn (ext_chart_at I x) x)

/-- `mdifferentiable_on I I' f s` indicates that the function `f` between manifolds
has a derivative within `s` at all points of `s`.
This is a generalization of `differentiable_on` to manifolds. -/
def mdifferentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (f : M → M') (s : set M) :=
  ∀ (x : M), x ∈ s → mdifferentiable_within_at I I' f s x

/-- `mdifferentiable I I' f` indicates that the function `f` between manifolds
has a derivative everywhere.
This is a generalization of `differentiable` to manifolds. -/
def mdifferentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (f : M → M') :=
  ∀ (x : M), mdifferentiable_at I I' f x

/-- Prop registering if a local homeomorphism is a local diffeomorphism on its source -/
def local_homeomorph.mdifferentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (f : local_homeomorph M M') :=
  mdifferentiable_on I I' (⇑f) (local_equiv.source (local_homeomorph.to_local_equiv f)) ∧
    mdifferentiable_on I' I (⇑(local_homeomorph.symm f)) (local_equiv.target (local_homeomorph.to_local_equiv f))

/-- `has_mfderiv_within_at I I' f s x f'` indicates that the function `f` between manifolds
has, at the point `x` and within the set `s`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

This is a generalization of `has_fderiv_within_at` to manifolds (as indicated by the prefix `m`).
The order of arguments is changed as the type of the derivative `f'` depends on the choice of `x`.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def has_mfderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] (f : M → M') (s : set M) (x : M) (f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))) :=
  continuous_within_at f s x ∧
    has_fderiv_within_at (written_in_ext_chart_at I I' x f) f'
      (⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s ∩ set.range ⇑I) (coe_fn (ext_chart_at I x) x)

/-- `has_mfderiv_at I I' f x f'` indicates that the function `f` between manifolds
has, at the point `x`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

We require continuity in the definition, as otherwise points close to `x` `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def has_mfderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] (f : M → M') (x : M) (f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))) :=
  continuous_at f x ∧
    has_fderiv_within_at (written_in_ext_chart_at I I' x f) f' (set.range ⇑I) (coe_fn (ext_chart_at I x) x)

/-- Let `f` be a function between two smooth manifolds. Then `mfderiv_within I I' f s x` is the
derivative of `f` at `x` within `s`, as a continuous linear map from the tangent space at `x` to the
tangent space at `f x`. -/
def mfderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] (f : M → M') (s : set M) (x : M) : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x)) :=
  dite (mdifferentiable_within_at I I' f s x)
    (fun (h : mdifferentiable_within_at I I' f s x) =>
      fderiv_within 𝕜 (written_in_ext_chart_at I I' x f) (⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s ∩ set.range ⇑I)
        (coe_fn (ext_chart_at I x) x))
    fun (h : ¬mdifferentiable_within_at I I' f s x) => 0

/-- Let `f` be a function between two smooth manifolds. Then `mfderiv I I' f x` is the derivative of
`f` at `x`, as a continuous linear map from the tangent space at `x` to the tangent space at
`f x`. -/
def mfderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] (f : M → M') (x : M) : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x)) :=
  dite (mdifferentiable_at I I' f x)
    (fun (h : mdifferentiable_at I I' f x) =>
      fderiv_within 𝕜 (written_in_ext_chart_at I I' x f) (set.range ⇑I) (coe_fn (ext_chart_at I x) x))
    fun (h : ¬mdifferentiable_at I I' f x) => 0

/-- The derivative within a set, as a map between the tangent bundles -/
def tangent_map_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] (f : M → M') (s : set M) : tangent_bundle I M → tangent_bundle I' M' :=
  fun (p : tangent_bundle I M) =>
    sigma.mk (f (sigma.fst p)) (coe_fn (mfderiv_within I I' f s (sigma.fst p)) (sigma.snd p))

/-- The derivative, as a map between the tangent bundles -/
def tangent_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] (f : M → M') : tangent_bundle I M → tangent_bundle I' M' :=
  fun (p : tangent_bundle I M) => sigma.mk (f (sigma.fst p)) (coe_fn (mfderiv I I' f (sigma.fst p)) (sigma.snd p))

/-! ### Unique differentiability sets in manifolds -/

theorem unique_mdiff_within_at_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {x : M} : unique_mdiff_within_at I set.univ x := sorry

theorem unique_mdiff_within_at_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {s : set M} {x : M} : unique_mdiff_within_at I s x ↔
  unique_diff_within_at 𝕜 (⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s ∩ local_equiv.target (ext_chart_at I x))
    (coe_fn (ext_chart_at I x) x) := sorry

theorem unique_mdiff_within_at.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {x : M} {s : set M} {t : set M} (h : unique_mdiff_within_at I s x) (st : s ⊆ t) : unique_mdiff_within_at I t x :=
  unique_diff_within_at.mono h (set.inter_subset_inter (set.preimage_mono st) (set.subset.refl (set.range ⇑I)))

theorem unique_mdiff_within_at.inter' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {x : M} {s : set M} {t : set M} (hs : unique_mdiff_within_at I s x) (ht : t ∈ nhds_within x s) : unique_mdiff_within_at I (s ∩ t) x := sorry

theorem unique_mdiff_within_at.inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {x : M} {s : set M} {t : set M} (hs : unique_mdiff_within_at I s x) (ht : t ∈ nhds x) : unique_mdiff_within_at I (s ∩ t) x := sorry

theorem is_open.unique_mdiff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {x : M} {s : set M} (xs : x ∈ s) (hs : is_open s) : unique_mdiff_within_at I s x :=
  eq.mp (Eq._oldrec (Eq.refl (unique_mdiff_within_at I (set.univ ∩ s) x)) (set.univ_inter s))
    (unique_mdiff_within_at.inter (unique_mdiff_within_at_univ I) (mem_nhds_sets hs xs))

theorem unique_mdiff_on.inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {s : set M} {t : set M} (hs : unique_mdiff_on I s) (ht : is_open t) : unique_mdiff_on I (s ∩ t) :=
  fun (x : M) (hx : x ∈ s ∩ t) => unique_mdiff_within_at.inter (hs x (and.left hx)) (mem_nhds_sets ht (and.right hx))

theorem is_open.unique_mdiff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {s : set M} (hs : is_open s) : unique_mdiff_on I s :=
  fun (x : M) (hx : x ∈ s) => is_open.unique_mdiff_within_at hx hs

theorem unique_mdiff_on_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] : unique_mdiff_on I set.univ :=
  is_open.unique_mdiff_on is_open_univ

/- We name the typeclass variables related to `smooth_manifold_with_corners` structure as they are
necessary in lemmas mentioning the derivative, but not in lemmas about differentiability, so we
want to include them or omit them when necessary. -/

/-- `unique_mdiff_within_at` achieves its goal: it implies the uniqueness of the derivative. -/
theorem unique_mdiff_within_at.eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} {f₁' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (U : unique_mdiff_within_at I s x) (h : has_mfderiv_within_at I I' f s x f') (h₁ : has_mfderiv_within_at I I' f s x f₁') : f' = f₁' :=
  unique_diff_within_at.eq U (and.right h) (and.right h₁)

theorem unique_mdiff_on.eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} {f₁' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (U : unique_mdiff_on I s) (hx : x ∈ s) (h : has_mfderiv_within_at I I' f s x f') (h₁ : has_mfderiv_within_at I I' f s x f₁') : f' = f₁' :=
  unique_mdiff_within_at.eq (U x hx) h h₁

/-!
### General lemmas on derivatives of functions between manifolds

We mimick the API for functions between vector spaces
-/

theorem mdifferentiable_within_at_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} : mdifferentiable_within_at I I' f s x ↔
  continuous_within_at f s x ∧
    differentiable_within_at 𝕜 (written_in_ext_chart_at I I' x f)
      (local_equiv.target (ext_chart_at I x) ∩ ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s)
      (coe_fn (ext_chart_at I x) x) := sorry

theorem mfderiv_within_zero_of_not_mdifferentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : ¬mdifferentiable_within_at I I' f s x) : mfderiv_within I I' f s x = 0 := sorry

theorem mfderiv_zero_of_not_mdifferentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : ¬mdifferentiable_at I I' f x) : mfderiv I I' f x = 0 := sorry

theorem has_mfderiv_within_at.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_within_at I I' f t x f') (hst : s ⊆ t) : has_mfderiv_within_at I I' f s x f' := sorry

theorem has_mfderiv_at.has_mfderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_at I I' f x f') : has_mfderiv_within_at I I' f s x f' := sorry

theorem has_mfderiv_within_at.mdifferentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_within_at I I' f s x f') : mdifferentiable_within_at I I' f s x :=
  { left := and.left h, right := Exists.intro f' (and.right h) }

theorem has_mfderiv_at.mdifferentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_at I I' f x f') : mdifferentiable_at I I' f x :=
  { left := and.left h, right := Exists.intro f' (and.right h) }

@[simp] theorem has_mfderiv_within_at_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} : has_mfderiv_within_at I I' f set.univ x f' ↔ has_mfderiv_at I I' f x f' := sorry

theorem has_mfderiv_at_unique {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f₀' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} {f₁' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h₀ : has_mfderiv_at I I' f x f₀') (h₁ : has_mfderiv_at I I' f x f₁') : f₀' = f₁' :=
  unique_mdiff_within_at.eq (unique_mdiff_within_at_univ I)
    (eq.mp (Eq._oldrec (Eq.refl (has_mfderiv_at I I' f x f₀')) (Eq.symm (propext has_mfderiv_within_at_univ))) h₀)
    (eq.mp (Eq._oldrec (Eq.refl (has_mfderiv_at I I' f x f₁')) (Eq.symm (propext has_mfderiv_within_at_univ))) h₁)

theorem has_mfderiv_within_at_inter' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : t ∈ nhds_within x s) : has_mfderiv_within_at I I' f (s ∩ t) x f' ↔ has_mfderiv_within_at I I' f s x f' := sorry

theorem has_mfderiv_within_at_inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : t ∈ nhds x) : has_mfderiv_within_at I I' f (s ∩ t) x f' ↔ has_mfderiv_within_at I I' f s x f' := sorry

theorem has_mfderiv_within_at.union {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (hs : has_mfderiv_within_at I I' f s x f') (ht : has_mfderiv_within_at I I' f t x f') : has_mfderiv_within_at I I' f (s ∪ t) x f' := sorry

theorem has_mfderiv_within_at.nhds_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_within_at I I' f s x f') (ht : s ∈ nhds_within x t) : has_mfderiv_within_at I I' f t x f' :=
  iff.mp (has_mfderiv_within_at_inter' ht) (has_mfderiv_within_at.mono h (set.inter_subset_right t s))

theorem has_mfderiv_within_at.has_mfderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_within_at I I' f s x f') (hs : s ∈ nhds x) : has_mfderiv_at I I' f x f' := sorry

theorem mdifferentiable_within_at.has_mfderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : mdifferentiable_within_at I I' f s x) : has_mfderiv_within_at I I' f s x (mfderiv_within I I' f s x) := sorry

theorem mdifferentiable_within_at.mfderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : mdifferentiable_within_at I I' f s x) : mfderiv_within I I' f s x =
  fderiv_within 𝕜 (written_in_ext_chart_at I I' x f) (⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s ∩ set.range ⇑I)
    (coe_fn (ext_chart_at I x) x) := sorry

theorem mdifferentiable_at.has_mfderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : mdifferentiable_at I I' f x) : has_mfderiv_at I I' f x (mfderiv I I' f x) := sorry

theorem mdifferentiable_at.mfderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : mdifferentiable_at I I' f x) : mfderiv I I' f x = fderiv_within 𝕜 (written_in_ext_chart_at I I' x f) (set.range ⇑I) (coe_fn (ext_chart_at I x) x) := sorry

theorem has_mfderiv_at.mfderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_at I I' f x f') : mfderiv I I' f x = f' := sorry

theorem has_mfderiv_within_at.mfderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_within_at I I' f s x f') (hxs : unique_mdiff_within_at I s x) : mfderiv_within I I' f s x = f' := sorry

theorem mdifferentiable.mfderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : mdifferentiable_at I I' f x) (hxs : unique_mdiff_within_at I s x) : mfderiv_within I I' f s x = mfderiv I I' f x :=
  has_mfderiv_within_at.mfderiv_within (has_mfderiv_at.has_mfderiv_within_at (mdifferentiable_at.has_mfderiv_at h)) hxs

theorem mfderiv_within_subset {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (st : s ⊆ t) (hs : unique_mdiff_within_at I s x) (h : mdifferentiable_within_at I I' f t x) : mfderiv_within I I' f s x = mfderiv_within I I' f t x :=
  has_mfderiv_within_at.mfderiv_within (has_mfderiv_within_at.mono (mdifferentiable_within_at.has_mfderiv_within_at h) st)
    hs

theorem mdifferentiable_within_at.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} {t : set M} (hst : s ⊆ t) (h : mdifferentiable_within_at I I' f t x) : mdifferentiable_within_at I I' f s x := sorry

theorem mdifferentiable_within_at_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} : mdifferentiable_within_at I I' f set.univ x ↔ mdifferentiable_at I I' f x := sorry

theorem mdifferentiable_within_at_inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} {t : set M} (ht : t ∈ nhds x) : mdifferentiable_within_at I I' f (s ∩ t) x ↔ mdifferentiable_within_at I I' f s x := sorry

theorem mdifferentiable_within_at_inter' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} {t : set M} (ht : t ∈ nhds_within x s) : mdifferentiable_within_at I I' f (s ∩ t) x ↔ mdifferentiable_within_at I I' f s x := sorry

theorem mdifferentiable_at.mdifferentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} (h : mdifferentiable_at I I' f x) : mdifferentiable_within_at I I' f s x :=
  mdifferentiable_within_at.mono (set.subset_univ s) (iff.mpr mdifferentiable_within_at_univ h)

theorem mdifferentiable_within_at.mdifferentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} (h : mdifferentiable_within_at I I' f s x) (hs : s ∈ nhds x) : mdifferentiable_at I I' f x := sorry

theorem mdifferentiable_on.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {t : set M} (h : mdifferentiable_on I I' f t) (st : s ⊆ t) : mdifferentiable_on I I' f s :=
  fun (x : M) (hx : x ∈ s) => mdifferentiable_within_at.mono st (h x (st hx))

theorem mdifferentiable_on_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} : mdifferentiable_on I I' f set.univ ↔ mdifferentiable I I' f := sorry

theorem mdifferentiable.mdifferentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} (h : mdifferentiable I I' f) : mdifferentiable_on I I' f s :=
  mdifferentiable_on.mono (iff.mpr mdifferentiable_on_univ h) (set.subset_univ s)

theorem mdifferentiable_on_of_locally_mdifferentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} (h : ∀ (x : M), x ∈ s → ∃ (u : set M), is_open u ∧ x ∈ u ∧ mdifferentiable_on I I' f (s ∩ u)) : mdifferentiable_on I I' f s := sorry

@[simp] theorem mfderiv_within_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] : mfderiv_within I I' f set.univ = mfderiv I I' f := sorry

theorem mfderiv_within_inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (ht : t ∈ nhds x) (hs : unique_mdiff_within_at I s x) : mfderiv_within I I' f (s ∩ t) x = mfderiv_within I I' f s x := sorry

/-! ### Deriving continuity from differentiability on manifolds -/

theorem has_mfderiv_within_at.continuous_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} (h : mdifferentiable_within_at I I' f s x) : continuous_within_at f s x :=
  and.left h

theorem has_mfderiv_at.continuous_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_at I I' f x f') : continuous_at f x :=
  and.left h

theorem mdifferentiable_within_at.continuous_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {s : set M} (h : mdifferentiable_within_at I I' f s x) : continuous_within_at f s x :=
  and.left h

theorem mdifferentiable_at.continuous_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} (h : mdifferentiable_at I I' f x) : continuous_at f x :=
  and.left h

theorem mdifferentiable_on.continuous_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} (h : mdifferentiable_on I I' f s) : continuous_on f s :=
  fun (x : M) (hx : x ∈ s) => mdifferentiable_within_at.continuous_within_at (h x hx)

theorem mdifferentiable.continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} (h : mdifferentiable I I' f) : continuous f :=
  iff.mpr continuous_iff_continuous_at fun (x : M) => mdifferentiable_at.continuous_at (h x)

theorem tangent_map_within_subset {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {p : tangent_bundle I M} (st : s ⊆ t) (hs : unique_mdiff_within_at I s (sigma.fst p)) (h : mdifferentiable_within_at I I' f t (sigma.fst p)) : tangent_map_within I I' f s p = tangent_map_within I I' f t p := sorry

theorem tangent_map_within_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] : tangent_map_within I I' f set.univ = tangent_map I I' f := sorry

theorem tangent_map_within_eq_tangent_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {p : tangent_bundle I M} (hs : unique_mdiff_within_at I s (sigma.fst p)) (h : mdifferentiable_at I I' f (sigma.fst p)) : tangent_map_within I I' f s p = tangent_map I I' f p := sorry

@[simp] theorem tangent_map_within_tangent_bundle_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {p : tangent_bundle I M} : tangent_bundle.proj I' M' (tangent_map_within I I' f s p) = f (tangent_bundle.proj I M p) :=
  rfl

@[simp] theorem tangent_map_within_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {p : tangent_bundle I M} : sigma.fst (tangent_map_within I I' f s p) = f (sigma.fst p) :=
  rfl

@[simp] theorem tangent_map_tangent_bundle_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {p : tangent_bundle I M} : tangent_bundle.proj I' M' (tangent_map I I' f p) = f (tangent_bundle.proj I M p) :=
  rfl

@[simp] theorem tangent_map_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {p : tangent_bundle I M} : sigma.fst (tangent_map I I' f p) = f (sigma.fst p) :=
  rfl

/-! ### Congruence lemmas for derivatives on manifolds -/

theorem has_mfderiv_within_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_within_at I I' f s x f') (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) : has_mfderiv_within_at I I' f₁ s x f' := sorry

theorem has_mfderiv_within_at.congr_mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_within_at I I' f s x f') (ht : ∀ (x : M), x ∈ t → f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) : has_mfderiv_within_at I I' f₁ t x f' :=
  has_mfderiv_within_at.congr_of_eventually_eq (has_mfderiv_within_at.mono h h₁) (filter.mem_inf_sets_of_right ht) hx

theorem has_mfderiv_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} (h : has_mfderiv_at I I' f x f') (h₁ : filter.eventually_eq (nhds x) f₁ f) : has_mfderiv_at I I' f₁ x f' := sorry

theorem mdifferentiable_within_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : mdifferentiable_within_at I I' f s x) (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) : mdifferentiable_within_at I I' f₁ s x :=
  has_mfderiv_within_at.mdifferentiable_within_at
    (has_mfderiv_within_at.congr_of_eventually_eq (mdifferentiable_within_at.has_mfderiv_within_at h) h₁ hx)

theorem filter.eventually_eq.mdifferentiable_within_at_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) : mdifferentiable_within_at I I' f s x ↔ mdifferentiable_within_at I I' f₁ s x := sorry

theorem mdifferentiable_within_at.congr_mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : mdifferentiable_within_at I I' f s x) (ht : ∀ (x : M), x ∈ t → f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) : mdifferentiable_within_at I I' f₁ t x :=
  has_mfderiv_within_at.mdifferentiable_within_at
    (has_mfderiv_within_at.congr_mono (mdifferentiable_within_at.has_mfderiv_within_at h) ht hx h₁)

theorem mdifferentiable_within_at.congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : mdifferentiable_within_at I I' f s x) (ht : ∀ (x : M), x ∈ s → f₁ x = f x) (hx : f₁ x = f x) : mdifferentiable_within_at I I' f₁ s x :=
  has_mfderiv_within_at.mdifferentiable_within_at
    (has_mfderiv_within_at.congr_mono (mdifferentiable_within_at.has_mfderiv_within_at h) ht hx (set.subset.refl s))

theorem mdifferentiable_on.congr_mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : mdifferentiable_on I I' f s) (h' : ∀ (x : M), x ∈ t → f₁ x = f x) (h₁ : t ⊆ s) : mdifferentiable_on I I' f₁ t :=
  fun (x : M) (hx : x ∈ t) => mdifferentiable_within_at.congr_mono (h x (h₁ hx)) h' (h' x hx) h₁

theorem mdifferentiable_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : mdifferentiable_at I I' f x) (hL : filter.eventually_eq (nhds x) f₁ f) : mdifferentiable_at I I' f₁ x :=
  has_mfderiv_at.mdifferentiable_at (has_mfderiv_at.congr_of_eventually_eq (mdifferentiable_at.has_mfderiv_at h) hL)

theorem mdifferentiable_within_at.mfderiv_within_congr_mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} {s : set M} {t : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : mdifferentiable_within_at I I' f s x) (hs : ∀ (x : M), x ∈ t → f₁ x = f x) (hx : f₁ x = f x) (hxt : unique_mdiff_within_at I t x) (h₁ : t ⊆ s) : mfderiv_within I I' f₁ t x = mfderiv_within I I' f s x :=
  has_mfderiv_within_at.mfderiv_within
    (has_mfderiv_within_at.congr_mono (mdifferentiable_within_at.has_mfderiv_within_at h) hs hx h₁) hxt

theorem filter.eventually_eq.mfderiv_within_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (hs : unique_mdiff_within_at I s x) (hL : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) : mfderiv_within I I' f₁ s x = mfderiv_within I I' f s x := sorry

theorem mfderiv_within_congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (hs : unique_mdiff_within_at I s x) (hL : ∀ (x : M), x ∈ s → f₁ x = f x) (hx : f₁ x = f x) : mfderiv_within I I' f₁ s x = mfderiv_within I I' f s x :=
  filter.eventually_eq.mfderiv_within_eq hs (filter.eventually_eq_of_mem self_mem_nhds_within hL) hx

theorem tangent_map_within_congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {s : set M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (h : ∀ (x : M), x ∈ s → f x = f₁ x) (p : tangent_bundle I M) (hp : sigma.fst p ∈ s) (hs : unique_mdiff_within_at I s (sigma.fst p)) : tangent_map_within I I' f s p = tangent_map_within I I' f₁ s p := sorry

theorem filter.eventually_eq.mfderiv_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] (hL : filter.eventually_eq (nhds x) f₁ f) : mfderiv I I' f₁ x = mfderiv I I' f x := sorry

/-! ### Composition lemmas -/

theorem written_in_ext_chart_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} {x : M} {s : set M} {g : M' → M''} (h : continuous_within_at f s x) : (set_of
    fun (y : E) =>
      written_in_ext_chart_at I I'' x (g ∘ f) y =
        function.comp (written_in_ext_chart_at I' I'' (f x) g) (written_in_ext_chart_at I I' x f) y) ∈
  nhds_within (coe_fn (ext_chart_at I x) x) (⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s ∩ set.range ⇑I) := sorry

theorem has_mfderiv_within_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} (x : M) {s : set M} {g : M' → M''} {u : set M'} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} {g' : continuous_linear_map 𝕜 (tangent_space I' (f x)) (tangent_space I'' (g (f x)))} (hg : has_mfderiv_within_at I' I'' g u (f x) g') (hf : has_mfderiv_within_at I I' f s x f') (hst : s ⊆ f ⁻¹' u) : has_mfderiv_within_at I I'' (g ∘ f) s x (continuous_linear_map.comp g' f') := sorry

/-- The chain rule. -/
theorem has_mfderiv_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} (x : M) {g : M' → M''} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} {g' : continuous_linear_map 𝕜 (tangent_space I' (f x)) (tangent_space I'' (g (f x)))} (hg : has_mfderiv_at I' I'' g (f x) g') (hf : has_mfderiv_at I I' f x f') : has_mfderiv_at I I'' (g ∘ f) x (continuous_linear_map.comp g' f') := sorry

theorem has_mfderiv_at.comp_has_mfderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} (x : M) {s : set M} {g : M' → M''} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] {f' : continuous_linear_map 𝕜 (tangent_space I x) (tangent_space I' (f x))} {g' : continuous_linear_map 𝕜 (tangent_space I' (f x)) (tangent_space I'' (g (f x)))} (hg : has_mfderiv_at I' I'' g (f x) g') (hf : has_mfderiv_within_at I I' f s x f') : has_mfderiv_within_at I I'' (g ∘ f) s x (continuous_linear_map.comp g' f') := sorry

theorem mdifferentiable_within_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} (x : M) {s : set M} {g : M' → M''} {u : set M'} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] (hg : mdifferentiable_within_at I' I'' g u (f x)) (hf : mdifferentiable_within_at I I' f s x) (h : s ⊆ f ⁻¹' u) : mdifferentiable_within_at I I'' (g ∘ f) s x := sorry

theorem mdifferentiable_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} (x : M) {g : M' → M''} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] (hg : mdifferentiable_at I' I'' g (f x)) (hf : mdifferentiable_at I I' f x) : mdifferentiable_at I I'' (g ∘ f) x :=
  has_mfderiv_at.mdifferentiable_at
    (has_mfderiv_at.comp x (mdifferentiable_at.has_mfderiv_at hg) (mdifferentiable_at.has_mfderiv_at hf))

theorem mfderiv_within_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} (x : M) {s : set M} {g : M' → M''} {u : set M'} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] (hg : mdifferentiable_within_at I' I'' g u (f x)) (hf : mdifferentiable_within_at I I' f s x) (h : s ⊆ f ⁻¹' u) (hxs : unique_mdiff_within_at I s x) : mfderiv_within I I'' (g ∘ f) s x =
  continuous_linear_map.comp (mfderiv_within I' I'' g u (f x)) (mfderiv_within I I' f s x) := sorry

theorem mfderiv_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} (x : M) {g : M' → M''} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] (hg : mdifferentiable_at I' I'' g (f x)) (hf : mdifferentiable_at I I' f x) : mfderiv I I'' (g ∘ f) x = continuous_linear_map.comp (mfderiv I' I'' g (f x)) (mfderiv I I' f x) :=
  has_mfderiv_at.mfderiv
    (has_mfderiv_at.comp x (mdifferentiable_at.has_mfderiv_at hg) (mdifferentiable_at.has_mfderiv_at hf))

theorem mdifferentiable_on.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} {s : set M} {g : M' → M''} {u : set M'} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] (hg : mdifferentiable_on I' I'' g u) (hf : mdifferentiable_on I I' f s) (st : s ⊆ f ⁻¹' u) : mdifferentiable_on I I'' (g ∘ f) s :=
  fun (x : M) (hx : x ∈ s) => mdifferentiable_within_at.comp x (hg (f x) (st hx)) (hf x hx) st

theorem mdifferentiable.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} {g : M' → M''} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] (hg : mdifferentiable I' I'' g) (hf : mdifferentiable I I' f) : mdifferentiable I I'' (g ∘ f) :=
  fun (x : M) => mdifferentiable_at.comp x (hg (f x)) (hf x)

theorem tangent_map_within_comp_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} {s : set M} {g : M' → M''} {u : set M'} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] (p : tangent_bundle I M) (hg : mdifferentiable_within_at I' I'' g u (f (sigma.fst p))) (hf : mdifferentiable_within_at I I' f s (sigma.fst p)) (h : s ⊆ f ⁻¹' u) (hps : unique_mdiff_within_at I s (sigma.fst p)) : tangent_map_within I I'' (g ∘ f) s p = tangent_map_within I' I'' g u (tangent_map_within I I' f s p) := sorry

theorem tangent_map_comp_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} {g : M' → M''} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] (p : tangent_bundle I M) (hg : mdifferentiable_at I' I'' g (f (sigma.fst p))) (hf : mdifferentiable_at I I' f (sigma.fst p)) : tangent_map I I'' (g ∘ f) p = tangent_map I' I'' g (tangent_map I I' f p) := sorry

theorem tangent_map_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {f : M → M'} {g : M' → M''} [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M'] [I''s : smooth_manifold_with_corners I'' M''] (hg : mdifferentiable I' I'' g) (hf : mdifferentiable I I' f) : tangent_map I I'' (g ∘ f) = tangent_map I' I'' g ∘ tangent_map I I' f :=
  funext fun (p : tangent_bundle I M) => tangent_map_comp_at p (hg (f (sigma.fst p))) (hf (sigma.fst p))

/-! ### Differentiability of specific functions -/

/-! #### Identity -/

theorem has_mfderiv_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (x : M) : has_mfderiv_at I I id x (continuous_linear_map.id 𝕜 (tangent_space I x)) := sorry

theorem has_mfderiv_within_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (s : set M) (x : M) : has_mfderiv_within_at I I id s x (continuous_linear_map.id 𝕜 (tangent_space I x)) :=
  has_mfderiv_at.has_mfderiv_within_at (has_mfderiv_at_id I x)

theorem mdifferentiable_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {x : M} : mdifferentiable_at I I id x :=
  has_mfderiv_at.mdifferentiable_at (has_mfderiv_at_id I x)

theorem mdifferentiable_within_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {s : set M} {x : M} : mdifferentiable_within_at I I id s x :=
  mdifferentiable_at.mdifferentiable_within_at (mdifferentiable_at_id I)

theorem mdifferentiable_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] : mdifferentiable I I id :=
  fun (x : M) => mdifferentiable_at_id I

theorem mdifferentiable_on_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {s : set M} : mdifferentiable_on I I id s :=
  mdifferentiable.mdifferentiable_on (mdifferentiable_id I)

@[simp] theorem mfderiv_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {x : M} : mfderiv I I id x = continuous_linear_map.id 𝕜 (tangent_space I x) :=
  has_mfderiv_at.mfderiv (has_mfderiv_at_id I x)

theorem mfderiv_within_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {s : set M} {x : M} (hxs : unique_mdiff_within_at I s x) : mfderiv_within I I id s x = continuous_linear_map.id 𝕜 (tangent_space I x) := sorry

@[simp] theorem tangent_map_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] : tangent_map I I id = id := sorry

theorem tangent_map_within_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {s : set M} {p : tangent_bundle I M} (hs : unique_mdiff_within_at I s (tangent_bundle.proj I M p)) : tangent_map_within I I id s p = p := sorry

/-! #### Constants -/

theorem has_mfderiv_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (c : M') (x : M) : has_mfderiv_at I I' (fun (y : M) => c) x 0 := sorry

theorem has_mfderiv_within_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (c : M') (s : set M) (x : M) : has_mfderiv_within_at I I' (fun (y : M) => c) s x 0 :=
  has_mfderiv_at.has_mfderiv_within_at (has_mfderiv_at_const I I' c x)

theorem mdifferentiable_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {x : M} {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {c : M'} : mdifferentiable_at I I' (fun (y : M) => c) x :=
  has_mfderiv_at.mdifferentiable_at (has_mfderiv_at_const I I' c x)

theorem mdifferentiable_within_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {s : set M} {x : M} {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {c : M'} : mdifferentiable_within_at I I' (fun (y : M) => c) s x :=
  mdifferentiable_at.mdifferentiable_within_at (mdifferentiable_at_const I I')

theorem mdifferentiable_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {c : M'} : mdifferentiable I I' fun (y : M) => c :=
  fun (x : M) => mdifferentiable_at_const I I'

theorem mdifferentiable_on_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {s : set M} {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {c : M'} : mdifferentiable_on I I' (fun (y : M) => c) s :=
  mdifferentiable.mdifferentiable_on (mdifferentiable_const I I')

@[simp] theorem mfderiv_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {x : M} {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {c : M'} : mfderiv I I' (fun (y : M) => c) x = 0 :=
  has_mfderiv_at.mfderiv (has_mfderiv_at_const I I' c x)

theorem mfderiv_within_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {s : set M} {x : M} {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {c : M'} (hxs : unique_mdiff_within_at I s x) : mfderiv_within I I' (fun (y : M) => c) s x = 0 := sorry

/-! #### Model with corners -/

theorem model_with_corners.mdifferentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : mdifferentiable I (model_with_corners_self 𝕜 E) ⇑I := sorry

theorem model_with_corners.mdifferentiable_on_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) : mdifferentiable_on (model_with_corners_self 𝕜 E) I (⇑(model_with_corners.symm I)) (set.range ⇑I) := sorry

theorem mdifferentiable_at_atlas {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {e : local_homeomorph M H} (h : e ∈ charted_space.atlas H M) {x : M} (hx : x ∈ local_equiv.source (local_homeomorph.to_local_equiv e)) : mdifferentiable_at I I (⇑e) x := sorry

theorem mdifferentiable_on_atlas {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {e : local_homeomorph M H} (h : e ∈ charted_space.atlas H M) : mdifferentiable_on I I (⇑e) (local_equiv.source (local_homeomorph.to_local_equiv e)) :=
  fun (x : M) (hx : x ∈ local_equiv.source (local_homeomorph.to_local_equiv e)) =>
    mdifferentiable_at.mdifferentiable_within_at (mdifferentiable_at_atlas I h hx)

theorem mdifferentiable_at_atlas_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {e : local_homeomorph M H} (h : e ∈ charted_space.atlas H M) {x : H} (hx : x ∈ local_equiv.target (local_homeomorph.to_local_equiv e)) : mdifferentiable_at I I (⇑(local_homeomorph.symm e)) x := sorry

theorem mdifferentiable_on_atlas_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {e : local_homeomorph M H} (h : e ∈ charted_space.atlas H M) : mdifferentiable_on I I (⇑(local_homeomorph.symm e)) (local_equiv.target (local_homeomorph.to_local_equiv e)) :=
  fun (x : H) (hx : x ∈ local_equiv.target (local_homeomorph.to_local_equiv e)) =>
    mdifferentiable_at.mdifferentiable_within_at (mdifferentiable_at_atlas_symm I h hx)

theorem mdifferentiable_of_mem_atlas {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {e : local_homeomorph M H} (h : e ∈ charted_space.atlas H M) : local_homeomorph.mdifferentiable I I e :=
  { left := mdifferentiable_on_atlas I h, right := mdifferentiable_on_atlas_symm I h }

theorem mdifferentiable_chart {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (x : M) : local_homeomorph.mdifferentiable I I (charted_space.chart_at H x) :=
  mdifferentiable_of_mem_atlas I (charted_space.chart_mem_atlas H x)

/-- The derivative of the chart at a base point is the chart of the tangent bundle, composed with
the identification between the tangent bundle of the model space and the product space. -/
theorem tangent_map_chart {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {p : tangent_bundle I M} {q : tangent_bundle I M} (h : sigma.fst q ∈ local_equiv.source (local_homeomorph.to_local_equiv (charted_space.chart_at H (sigma.fst p)))) : tangent_map I I (⇑(charted_space.chart_at H (sigma.fst p))) q =
  coe_fn (equiv.symm (equiv.sigma_equiv_prod H E)) (coe_fn (charted_space.chart_at (model_prod H E) p) q) := sorry

/-- The derivative of the inverse of the chart at a base point is the inverse of the chart of the
tangent bundle, composed with the identification between the tangent bundle of the model space and
the product space. -/
theorem tangent_map_chart_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {p : tangent_bundle I M} {q : tangent_bundle I H} (h : sigma.fst q ∈ local_equiv.target (local_homeomorph.to_local_equiv (charted_space.chart_at H (sigma.fst p)))) : tangent_map I I (⇑(local_homeomorph.symm (charted_space.chart_at H (sigma.fst p)))) q =
  coe_fn (local_homeomorph.symm (charted_space.chart_at (model_prod H E) p)) (coe_fn (equiv.sigma_equiv_prod H E) q) := sorry

/-!
### Relations between vector space derivative and manifold derivative

The manifold derivative `mfderiv`, when considered on the model vector space with its trivial
manifold structure, coincides with the usual Frechet derivative `fderiv`. In this section, we prove
this and related statements.
-/

theorem unique_mdiff_within_at_iff_unique_diff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {s : set E} {x : E} : unique_mdiff_within_at (model_with_corners_self 𝕜 E) s x ↔ unique_diff_within_at 𝕜 s x := sorry

theorem unique_mdiff_on_iff_unique_diff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {s : set E} : unique_mdiff_on (model_with_corners_self 𝕜 E) s ↔ unique_diff_on 𝕜 s := sorry

@[simp] theorem written_in_ext_chart_model_space {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {f : E → E'} {x : E} : written_in_ext_chart_at (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') x f = f := sorry

/-- For maps between vector spaces, `mdifferentiable_within_at` and `fdifferentiable_within_at`
coincide -/
theorem mdifferentiable_within_at_iff_differentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {f : E → E'} {s : set E} {x : E} : mdifferentiable_within_at (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') f s x ↔
  differentiable_within_at 𝕜 f s x := sorry

/-- For maps between vector spaces, `mdifferentiable_at` and `differentiable_at` coincide -/
theorem mdifferentiable_at_iff_differentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {f : E → E'} {x : E} : mdifferentiable_at (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') f x ↔ differentiable_at 𝕜 f x := sorry

/-- For maps between vector spaces, `mdifferentiable_on` and `differentiable_on` coincide -/
theorem mdifferentiable_on_iff_differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {f : E → E'} {s : set E} : mdifferentiable_on (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') f s ↔ differentiable_on 𝕜 f s := sorry

/-- For maps between vector spaces, `mdifferentiable` and `differentiable` coincide -/
theorem mdifferentiable_iff_differentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {f : E → E'} : mdifferentiable (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') f ↔ differentiable 𝕜 f := sorry

/-- For maps between vector spaces, `mfderiv_within` and `fderiv_within` coincide -/
theorem mfderiv_within_eq_fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {f : E → E'} {s : set E} {x : E} : mfderiv_within (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') f s x = fderiv_within 𝕜 f s x := sorry

/-- For maps between vector spaces, `mfderiv` and `fderiv` coincide -/
theorem mfderiv_eq_fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {f : E → E'} {x : E} : mfderiv (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') f x = fderiv 𝕜 f x := sorry

/-! ### Differentiable local homeomorphisms -/

namespace local_homeomorph.mdifferentiable


theorem symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {e : local_homeomorph M M'} (he : mdifferentiable I I' e) : mdifferentiable I' I (local_homeomorph.symm e) :=
  { left := and.right he, right := and.left he }

protected theorem mdifferentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {e : local_homeomorph M M'} (he : mdifferentiable I I' e) {x : M} (hx : x ∈ local_equiv.source (to_local_equiv e)) : mdifferentiable_at I I' (⇑e) x :=
  mdifferentiable_within_at.mdifferentiable_at (and.left he x hx) (mem_nhds_sets (open_source e) hx)

theorem mdifferentiable_at_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {e : local_homeomorph M M'} (he : mdifferentiable I I' e) {x : M'} (hx : x ∈ local_equiv.target (to_local_equiv e)) : mdifferentiable_at I' I (⇑(local_homeomorph.symm e)) x :=
  mdifferentiable_within_at.mdifferentiable_at (and.right he x hx) (mem_nhds_sets (open_target e) hx)

theorem symm_comp_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {e : local_homeomorph M M'} (he : mdifferentiable I I' e) [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] {x : M} (hx : x ∈ local_equiv.source (to_local_equiv e)) : continuous_linear_map.comp (mfderiv I' I (⇑(local_homeomorph.symm e)) (coe_fn e x)) (mfderiv I I' (⇑e) x) =
  continuous_linear_map.id 𝕜 (tangent_space I x) := sorry

theorem comp_symm_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {e : local_homeomorph M M'} (he : mdifferentiable I I' e) [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] {x : M'} (hx : x ∈ local_equiv.target (to_local_equiv e)) : continuous_linear_map.comp (mfderiv I I' (⇑e) (coe_fn (local_homeomorph.symm e) x))
    (mfderiv I' I (⇑(local_homeomorph.symm e)) x) =
  continuous_linear_map.id 𝕜 (tangent_space I' x) :=
  symm_comp_deriv (symm he) hx

/-- The derivative of a differentiable local homeomorphism, as a continuous linear equivalence
between the tangent spaces at `x` and `e x`. -/
protected def mfderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {e : local_homeomorph M M'} (he : mdifferentiable I I' e) [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] {x : M} (hx : x ∈ local_equiv.source (to_local_equiv e)) : continuous_linear_equiv 𝕜 (tangent_space I x) (tangent_space I' (coe_fn e x)) :=
  continuous_linear_equiv.mk
    (linear_equiv.mk (linear_map.to_fun (continuous_linear_map.to_linear_map (mfderiv I I' (⇑e) x))) sorry sorry
      ⇑(mfderiv I' I (⇑(local_homeomorph.symm e)) (coe_fn e x)) sorry sorry)

theorem mfderiv_bijective {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {e : local_homeomorph M M'} (he : mdifferentiable I I' e) [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] {x : M} (hx : x ∈ local_equiv.source (to_local_equiv e)) : function.bijective ⇑(mfderiv I I' (⇑e) x) :=
  continuous_linear_equiv.bijective (mdifferentiable.mfderiv he hx)

theorem mfderiv_surjective {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {e : local_homeomorph M M'} (he : mdifferentiable I I' e) [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] {x : M} (hx : x ∈ local_equiv.source (to_local_equiv e)) : function.surjective ⇑(mfderiv I I' (⇑e) x) :=
  continuous_linear_equiv.surjective (mdifferentiable.mfderiv he hx)

theorem range_mfderiv_eq_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {e : local_homeomorph M M'} (he : mdifferentiable I I' e) [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] {x : M} (hx : x ∈ local_equiv.source (to_local_equiv e)) : set.range ⇑(mfderiv I I' (⇑e) x) = set.univ :=
  function.surjective.range_eq (mfderiv_surjective he hx)

theorem trans {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] {e : local_homeomorph M M'} (he : mdifferentiable I I' e) {e' : local_homeomorph M' M''} [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M'] [smooth_manifold_with_corners I'' M''] (he' : mdifferentiable I' I'' e') : mdifferentiable I I'' (local_homeomorph.trans e e') := sorry

end local_homeomorph.mdifferentiable


/-! ### Unique derivative sets in manifolds -/

/-- If a set has the unique differential property, then its image under a local
diffeomorphism also has the unique differential property. -/
theorem unique_mdiff_on.unique_mdiff_on_preimage {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {s : set M} [smooth_manifold_with_corners I' M'] (hs : unique_mdiff_on I s) {e : local_homeomorph M M'} (he : local_homeomorph.mdifferentiable I I' e) : unique_mdiff_on I' (local_equiv.target (local_homeomorph.to_local_equiv e) ∩ ⇑(local_homeomorph.symm e) ⁻¹' s) := sorry

/-- If a set in a manifold has the unique derivative property, then its pullback by any extended
chart, in the vector space, also has the unique derivative property. -/
theorem unique_mdiff_on.unique_diff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {s : set M} (hs : unique_mdiff_on I s) (x : M) : unique_diff_on 𝕜 (local_equiv.target (ext_chart_at I x) ∩ ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' s) := sorry

/-- When considering functions between manifolds, this statement shows up often. It entails
the unique differential of the pullback in extended charts of the set where the function can
be read in the charts. -/
theorem unique_mdiff_on.unique_diff_on_inter_preimage {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {s : set M} (hs : unique_mdiff_on I s) (x : M) (y : M') {f : M → M'} (hf : continuous_on f s) : unique_diff_on 𝕜
  (local_equiv.target (ext_chart_at I x) ∩
    ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' (s ∩ f ⁻¹' local_equiv.source (ext_chart_at I' y))) := sorry

/-- In a smooth fiber bundle constructed from core, the preimage under the projection of a set with
unique differential in the basis also has unique differential. -/
theorem unique_mdiff_on.smooth_bundle_preimage {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {s : set M} {F : Type u_8} [normed_group F] [normed_space 𝕜 F] (Z : basic_smooth_bundle_core I M F) (hs : unique_mdiff_on I s) : unique_mdiff_on (model_with_corners.prod I (model_with_corners_self 𝕜 F))
  (topological_fiber_bundle_core.proj (basic_smooth_bundle_core.to_topological_fiber_bundle_core Z) ⁻¹' s) := sorry

theorem unique_mdiff_on.tangent_bundle_proj_preimage {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {s : set M} (hs : unique_mdiff_on I s) : unique_mdiff_on (model_with_corners.tangent I) (tangent_bundle.proj I M ⁻¹' s) :=
  unique_mdiff_on.smooth_bundle_preimage (tangent_bundle_core I M) hs

