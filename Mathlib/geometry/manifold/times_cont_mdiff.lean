/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.geometry.manifold.mfderiv
import Mathlib.geometry.manifold.local_invariant_properties
import Mathlib.PostPort

universes u_1 u_2 u_3 u_5 u_6 u_4 u_7 u_14 u_15 u_16 u_11 u_12 u_13 u_8 u_9 u_10 

namespace Mathlib

/-!
# Smooth functions between smooth manifolds

We define `Cⁿ` functions between smooth manifolds, as functions which are `Cⁿ` in charts, and prove
basic properties of these notions.

## Main definitions and statements

Let `M ` and `M'` be two smooth manifolds, with respect to model with corners `I` and `I'`. Let
`f : M → M'`.

* `times_cont_mdiff_within_at I I' n f s x` states that the function `f` is `Cⁿ` within the set `s`
  around the point `x`.
* `times_cont_mdiff_at I I' n f x` states that the function `f` is `Cⁿ` around `x`.
* `times_cont_mdiff_on I I' n f s` states that the function `f` is `Cⁿ` on the set `s`
* `times_cont_mdiff I I' n f` states that the function `f` is `Cⁿ`.
* `times_cont_mdiff_on.comp` gives the invariance of the `Cⁿ` property under composition
* `times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within` states that the bundled derivative
  of a `Cⁿ` function in a domain is `Cᵐ` when `m + 1 ≤ n`.
* `times_cont_mdiff.times_cont_mdiff_tangent_map` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`.
* `times_cont_mdiff_iff_times_cont_diff` states that, for functions between vector spaces,
  manifold-smoothness is equivalent to usual smoothness.

We also give many basic properties of smooth functions between manifolds, following the API of
smooth functions between vector spaces.

## Implementation details

Many properties follow for free from the corresponding properties of functions in vector spaces,
as being `Cⁿ` is a local property invariant under the smooth groupoid. We take advantage of the
general machinery developed in `local_invariant_properties.lean` to get these properties
automatically. For instance, the fact that being `Cⁿ` does not depend on the chart one considers
is given by `lift_prop_within_at_indep_chart`.

For this to work, the definition of `times_cont_mdiff_within_at` and friends has to
follow definitionally the setup of local invariant properties. Still, we recast the definition
in terms of extended charts in `times_cont_mdiff_on_iff` and `times_cont_mdiff_iff`.
-/

/-! ### Definition of smooth functions between manifolds -/

-- declare a smooth manifold `M` over the pair `(E, H)`.

-- declare a smooth manifold `M'` over the pair `(E', H')`.

-- declare a smooth manifold `N` over the pair `(F, G)`.

-- declare a smooth manifold `N'` over the pair `(F', G')`.

-- declare functions, sets, points and smoothness indices

/-- Property in the model space of a model with corners of being `C^n` within at set at a point,
when read in the model vector space. This property will be lifted to manifolds to define smooth
functions between manifolds. -/
def times_cont_diff_within_at_prop {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') (n : with_top ℕ) (f : H → H') (s : set H) (x : H) :=
  times_cont_diff_within_at 𝕜 n (⇑I' ∘ f ∘ ⇑(model_with_corners.symm I))
    (set.range ⇑I ∩ ⇑(model_with_corners.symm I) ⁻¹' s) (coe_fn I x)

/-- Being `Cⁿ` in the model space is a local property, invariant under smooth maps. Therefore,
it will lift nicely to manifolds. -/
theorem times_cont_diff_within_at_local_invariant_prop {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') (n : with_top ℕ) : structure_groupoid.local_invariant_prop (times_cont_diff_groupoid ⊤ I) (times_cont_diff_groupoid ⊤ I')
  (times_cont_diff_within_at_prop I I' n) := sorry

theorem times_cont_diff_within_at_local_invariant_prop_mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') (n : with_top ℕ) {s : set H} {x : H} {t : set H} {f : H → H'} (hts : t ⊆ s) (h : times_cont_diff_within_at_prop I I' n f s x) : times_cont_diff_within_at_prop I I' n f t x := sorry

theorem times_cont_diff_within_at_local_invariant_prop_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) (x : H) : times_cont_diff_within_at_prop I I ⊤ id set.univ x := sorry

/-- A function is `n` times continuously differentiable within a set at a point in a manifold if
it is continuous and it is `n` times continuously differentiable in this set around this point, when
read in the preferred chart at this point. -/
def times_cont_mdiff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (n : with_top ℕ) (f : M → M') (s : set M) (x : M) :=
  charted_space.lift_prop_within_at (times_cont_diff_within_at_prop I I' n) f s x

/-- Abbreviation for `times_cont_mdiff_within_at I I' ⊤ f s x`. See also documentation for `smooth`.
-/
def smooth_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (f : M → M') (s : set M) (x : M) :=
  times_cont_mdiff_within_at I I' ⊤ f s x

/-- A function is `n` times continuously differentiable at a point in a manifold if
it is continuous and it is `n` times continuously differentiable around this point, when
read in the preferred chart at this point. -/
def times_cont_mdiff_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (n : with_top ℕ) (f : M → M') (x : M) :=
  times_cont_mdiff_within_at I I' n f set.univ x

/-- Abbreviation for `times_cont_mdiff_at I I' ⊤ f x`. See also documentation for `smooth`. -/
def smooth_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (f : M → M') (x : M) :=
  times_cont_mdiff_at I I' ⊤ f x

/-- A function is `n` times continuously differentiable in a set of a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable on this set in the charts
around these points. -/
def times_cont_mdiff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (n : with_top ℕ) (f : M → M') (s : set M) :=
  ∀ (x : M), x ∈ s → times_cont_mdiff_within_at I I' n f s x

/-- Abbreviation for `times_cont_mdiff_on I I' ⊤ f s`. See also documentation for `smooth`. -/
def smooth_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (f : M → M') (s : set M) :=
  times_cont_mdiff_on I I' ⊤ f s

/-- A function is `n` times continuously differentiable in a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable in the charts
around these points. -/
def times_cont_mdiff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (n : with_top ℕ) (f : M → M') :=
  ∀ (x : M), times_cont_mdiff_at I I' n f x

/-- Abbreviation for `times_cont_mdiff I I' ⊤ f`.
Short note to work with these abbreviations: a lemma of the form `times_cont_mdiff_foo.bar` will
apply fine to an assumption `smooth_foo` using dot notation or normal notation.
If the consequence `bar` of the lemma involves `times_cont_diff`, it is still better to restate
the lemma replacing `times_cont_diff` with `smooth` both in the assumption and in the conclusion,
to make it possible to use `smooth` consistently.
This also applies to `smooth_at`, `smooth_on` and `smooth_within_at`.-/
def smooth {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') {M' : Type u_7} [topological_space M'] [charted_space H' M'] (f : M → M') :=
  times_cont_mdiff I I' ⊤ f

/-! ### Basic properties of smooth functions between manifolds -/

theorem times_cont_mdiff.smooth {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} (h : times_cont_mdiff I I' ⊤ f) : smooth I I' f :=
  h

theorem smooth.times_cont_mdiff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} (h : smooth I I' f) : times_cont_mdiff I I' ⊤ f :=
  h

theorem times_cont_mdiff_on.smooth_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} (h : times_cont_mdiff_on I I' ⊤ f s) : smooth_on I I' f s :=
  h

theorem smooth_on.times_cont_mdiff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} (h : smooth_on I I' f s) : times_cont_mdiff_on I I' ⊤ f s :=
  h

theorem times_cont_mdiff_at.smooth_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} (h : times_cont_mdiff_at I I' ⊤ f x) : smooth_at I I' f x :=
  h

theorem smooth_at.times_cont_mdiff_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} (h : smooth_at I I' f x) : times_cont_mdiff_at I I' ⊤ f x :=
  h

theorem times_cont_mdiff_within_at.smooth_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} (h : times_cont_mdiff_within_at I I' ⊤ f s x) : smooth_within_at I I' f s x :=
  h

theorem smooth_within_at.times_cont_mdiff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} (h : smooth_within_at I I' f s x) : times_cont_mdiff_within_at I I' ⊤ f s x :=
  h

theorem times_cont_mdiff.times_cont_mdiff_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {n : with_top ℕ} (h : times_cont_mdiff I I' n f) : times_cont_mdiff_at I I' n f x :=
  h x

theorem smooth.smooth_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} (h : smooth I I' f) : smooth_at I I' f x :=
  times_cont_mdiff.times_cont_mdiff_at h

theorem times_cont_mdiff_within_at_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {n : with_top ℕ} : times_cont_mdiff_within_at I I' n f set.univ x ↔ times_cont_mdiff_at I I' n f x :=
  iff.rfl

theorem smooth_at_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} : smooth_within_at I I' f set.univ x ↔ smooth_at I I' f x :=
  times_cont_mdiff_within_at_univ

theorem times_cont_mdiff_on_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {n : with_top ℕ} : times_cont_mdiff_on I I' n f set.univ ↔ times_cont_mdiff I I' n f := sorry

theorem smooth_on_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} : smooth_on I I' f set.univ ↔ smooth I I' f :=
  times_cont_mdiff_on_univ

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. -/
theorem times_cont_mdiff_within_at_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} {n : with_top ℕ} : times_cont_mdiff_within_at I I' n f s x ↔
  continuous_within_at f s x ∧
    times_cont_diff_within_at 𝕜 n (⇑(ext_chart_at I' (f x)) ∘ f ∘ ⇑(local_equiv.symm (ext_chart_at I x)))
      (local_equiv.target (ext_chart_at I x) ∩
        ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' (s ∩ f ⁻¹' local_equiv.source (ext_chart_at I' (f x))))
      (coe_fn (ext_chart_at I x) x) := sorry

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart in the target. -/
theorem times_cont_mdiff_within_at_iff_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} {n : with_top ℕ} : times_cont_mdiff_within_at I I' n f s x ↔
  continuous_within_at f s x ∧
    times_cont_mdiff_within_at I (model_with_corners_self 𝕜 E') n (⇑(ext_chart_at I' (f x)) ∘ f)
      (s ∩ f ⁻¹' local_equiv.source (ext_chart_at I' (f x))) x := sorry

theorem smooth_within_at_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} : smooth_within_at I I' f s x ↔
  continuous_within_at f s x ∧
    times_cont_diff_within_at 𝕜 ⊤ (⇑(ext_chart_at I' (f x)) ∘ f ∘ ⇑(local_equiv.symm (ext_chart_at I x)))
      (local_equiv.target (ext_chart_at I x) ∩
        ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' (s ∩ f ⁻¹' local_equiv.source (ext_chart_at I' (f x))))
      (coe_fn (ext_chart_at I x) x) :=
  times_cont_mdiff_within_at_iff

theorem smooth_within_at_iff_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} : smooth_within_at I I' f s x ↔
  continuous_within_at f s x ∧
    smooth_within_at I (model_with_corners_self 𝕜 E') (⇑(ext_chart_at I' (f x)) ∘ f)
      (s ∩ f ⁻¹' local_equiv.source (ext_chart_at I' (f x))) x :=
  times_cont_mdiff_within_at_iff_target

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart. -/
theorem times_cont_mdiff_on_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {s : set M} {n : with_top ℕ} : times_cont_mdiff_on I I' n f s ↔
  continuous_on f s ∧
    ∀ (x : M) (y : M'),
      times_cont_diff_on 𝕜 n (⇑(ext_chart_at I' y) ∘ f ∘ ⇑(local_equiv.symm (ext_chart_at I x)))
        (local_equiv.target (ext_chart_at I x) ∩
          ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' (s ∩ f ⁻¹' local_equiv.source (ext_chart_at I' y))) := sorry

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart in the target. -/
theorem times_cont_mdiff_on_iff_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {s : set M} {n : with_top ℕ} : times_cont_mdiff_on I I' n f s ↔
  continuous_on f s ∧
    ∀ (y : M'),
      times_cont_mdiff_on I (model_with_corners_self 𝕜 E') n (⇑(ext_chart_at I' y) ∘ f)
        (s ∩ f ⁻¹' local_equiv.source (ext_chart_at I' y)) := sorry

theorem smooth_on_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {s : set M} : smooth_on I I' f s ↔
  continuous_on f s ∧
    ∀ (x : M) (y : M'),
      times_cont_diff_on 𝕜 ⊤ (⇑(ext_chart_at I' y) ∘ f ∘ ⇑(local_equiv.symm (ext_chart_at I x)))
        (local_equiv.target (ext_chart_at I x) ∩
          ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' (s ∩ f ⁻¹' local_equiv.source (ext_chart_at I' y))) :=
  times_cont_mdiff_on_iff

theorem smooth_on_iff_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {s : set M} : smooth_on I I' f s ↔
  continuous_on f s ∧
    ∀ (y : M'),
      smooth_on I (model_with_corners_self 𝕜 E') (⇑(ext_chart_at I' y) ∘ f)
        (s ∩ f ⁻¹' local_equiv.source (ext_chart_at I' y)) :=
  times_cont_mdiff_on_iff_target

/-- One can reformulate smoothness as continuity and smoothness in any extended chart. -/
theorem times_cont_mdiff_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {n : with_top ℕ} : times_cont_mdiff I I' n f ↔
  continuous f ∧
    ∀ (x : M) (y : M'),
      times_cont_diff_on 𝕜 n (⇑(ext_chart_at I' y) ∘ f ∘ ⇑(local_equiv.symm (ext_chart_at I x)))
        (local_equiv.target (ext_chart_at I x) ∩
          ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' (f ⁻¹' local_equiv.source (ext_chart_at I' y))) := sorry

/-- One can reformulate smoothness as continuity and smoothness in any extended chart in the
target. -/
theorem times_cont_mdiff_iff_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {n : with_top ℕ} : times_cont_mdiff I I' n f ↔
  continuous f ∧
    ∀ (y : M'),
      times_cont_mdiff_on I (model_with_corners_self 𝕜 E') n (⇑(ext_chart_at I' y) ∘ f)
        (f ⁻¹' local_equiv.source (ext_chart_at I' y)) := sorry

theorem smooth_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} : smooth I I' f ↔
  continuous f ∧
    ∀ (x : M) (y : M'),
      times_cont_diff_on 𝕜 ⊤ (⇑(ext_chart_at I' y) ∘ f ∘ ⇑(local_equiv.symm (ext_chart_at I x)))
        (local_equiv.target (ext_chart_at I x) ∩
          ⇑(local_equiv.symm (ext_chart_at I x)) ⁻¹' (f ⁻¹' local_equiv.source (ext_chart_at I' y))) :=
  times_cont_mdiff_iff

theorem smooth_iff_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} : smooth I I' f ↔
  continuous f ∧
    ∀ (y : M'),
      smooth_on I (model_with_corners_self 𝕜 E') (⇑(ext_chart_at I' y) ∘ f)
        (f ⁻¹' local_equiv.source (ext_chart_at I' y)) :=
  times_cont_mdiff_iff_target

/-! ### Deducing smoothness from higher smoothness -/

theorem times_cont_mdiff_within_at.of_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} {m : with_top ℕ} {n : with_top ℕ} (hf : times_cont_mdiff_within_at I I' n f s x) (le : m ≤ n) : times_cont_mdiff_within_at I I' m f s x :=
  { left := and.left hf, right := times_cont_diff_within_at.of_le (and.right hf) le }

theorem times_cont_mdiff_at.of_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {m : with_top ℕ} {n : with_top ℕ} (hf : times_cont_mdiff_at I I' n f x) (le : m ≤ n) : times_cont_mdiff_at I I' m f x :=
  times_cont_mdiff_within_at.of_le hf le

theorem times_cont_mdiff_on.of_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {m : with_top ℕ} {n : with_top ℕ} (hf : times_cont_mdiff_on I I' n f s) (le : m ≤ n) : times_cont_mdiff_on I I' m f s :=
  fun (x : M) (hx : x ∈ s) => times_cont_mdiff_within_at.of_le (hf x hx) le

theorem times_cont_mdiff.of_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {m : with_top ℕ} {n : with_top ℕ} (hf : times_cont_mdiff I I' n f) (le : m ≤ n) : times_cont_mdiff I I' m f :=
  fun (x : M) => times_cont_mdiff_at.of_le (hf x) le

/-! ### Deducing smoothness from smoothness one step beyond -/

theorem times_cont_mdiff_within_at.of_succ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} {n : ℕ} (h : times_cont_mdiff_within_at I I' (↑(Nat.succ n)) f s x) : times_cont_mdiff_within_at I I' (↑n) f s x :=
  times_cont_mdiff_within_at.of_le h (iff.mpr with_top.coe_le_coe (nat.le_succ n))

theorem times_cont_mdiff_at.of_succ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {n : ℕ} (h : times_cont_mdiff_at I I' (↑(Nat.succ n)) f x) : times_cont_mdiff_at I I' (↑n) f x :=
  times_cont_mdiff_within_at.of_succ h

theorem times_cont_mdiff_on.of_succ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {n : ℕ} (h : times_cont_mdiff_on I I' (↑(Nat.succ n)) f s) : times_cont_mdiff_on I I' (↑n) f s :=
  fun (x : M) (hx : x ∈ s) => times_cont_mdiff_within_at.of_succ (h x hx)

theorem times_cont_mdiff.of_succ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {n : ℕ} (h : times_cont_mdiff I I' (↑(Nat.succ n)) f) : times_cont_mdiff I I' (↑n) f :=
  fun (x : M) => times_cont_mdiff_at.of_succ (h x)

/-! ### Deducing continuity from smoothness-/

theorem times_cont_mdiff_within_at.continuous_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} {n : with_top ℕ} (hf : times_cont_mdiff_within_at I I' n f s x) : continuous_within_at f s x :=
  and.left hf

theorem times_cont_mdiff_at.continuous_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {n : with_top ℕ} (hf : times_cont_mdiff_at I I' n f x) : continuous_at f x :=
  iff.mp (continuous_within_at_univ f x) (times_cont_mdiff_within_at.continuous_within_at hf)

theorem times_cont_mdiff_on.continuous_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {n : with_top ℕ} (hf : times_cont_mdiff_on I I' n f s) : continuous_on f s :=
  fun (x : M) (hx : x ∈ s) => times_cont_mdiff_within_at.continuous_within_at (hf x hx)

theorem times_cont_mdiff.continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {n : with_top ℕ} (hf : times_cont_mdiff I I' n f) : continuous f :=
  iff.mpr continuous_iff_continuous_at fun (x : M) => times_cont_mdiff_at.continuous_at (hf x)

/-! ### Deducing differentiability from smoothness -/

theorem times_cont_mdiff_within_at.mdifferentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} {n : with_top ℕ} (hf : times_cont_mdiff_within_at I I' n f s x) (hn : 1 ≤ n) : mdifferentiable_within_at I I' f s x := sorry

theorem times_cont_mdiff_at.mdifferentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} {n : with_top ℕ} (hf : times_cont_mdiff_at I I' n f x) (hn : 1 ≤ n) : mdifferentiable_at I I' f x :=
  iff.mp mdifferentiable_within_at_univ (times_cont_mdiff_within_at.mdifferentiable_within_at hf hn)

theorem times_cont_mdiff_on.mdifferentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {n : with_top ℕ} (hf : times_cont_mdiff_on I I' n f s) (hn : 1 ≤ n) : mdifferentiable_on I I' f s :=
  fun (x : M) (hx : x ∈ s) => times_cont_mdiff_within_at.mdifferentiable_within_at (hf x hx) hn

theorem times_cont_mdiff.mdifferentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {n : with_top ℕ} (hf : times_cont_mdiff I I' n f) (hn : 1 ≤ n) : mdifferentiable I I' f :=
  fun (x : M) => times_cont_mdiff_at.mdifferentiable_at (hf x) hn

theorem smooth.mdifferentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} (hf : smooth I I' f) : mdifferentiable I I' f :=
  times_cont_mdiff.mdifferentiable hf le_top

theorem smooth.mdifferentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} (hf : smooth I I' f) : mdifferentiable_at I I' f x :=
  smooth.mdifferentiable hf x

theorem smooth.mdifferentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} (hf : smooth I I' f) : mdifferentiable_within_at I I' f s x :=
  mdifferentiable_at.mdifferentiable_within_at (smooth.mdifferentiable_at hf)

/-! ### `C^∞` smoothness -/

theorem times_cont_mdiff_within_at_top {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} : smooth_within_at I I' f s x ↔ ∀ (n : ℕ), times_cont_mdiff_within_at I I' (↑n) f s x := sorry

theorem times_cont_mdiff_at_top {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {x : M} : smooth_at I I' f x ↔ ∀ (n : ℕ), times_cont_mdiff_at I I' (↑n) f x :=
  times_cont_mdiff_within_at_top

theorem times_cont_mdiff_on_top {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} : smooth_on I I' f s ↔ ∀ (n : ℕ), times_cont_mdiff_on I I' (↑n) f s := sorry

theorem times_cont_mdiff_top {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} : smooth I I' f ↔ ∀ (n : ℕ), times_cont_mdiff I I' (↑n) f := sorry

theorem times_cont_mdiff_within_at_iff_nat {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} {n : with_top ℕ} : times_cont_mdiff_within_at I I' n f s x ↔ ∀ (m : ℕ), ↑m ≤ n → times_cont_mdiff_within_at I I' (↑m) f s x := sorry

/-! ### Restriction to a smaller set -/

theorem times_cont_mdiff_within_at.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {t : set M} {x : M} {n : with_top ℕ} (hf : times_cont_mdiff_within_at I I' n f s x) (hts : t ⊆ s) : times_cont_mdiff_within_at I I' n f t x :=
  structure_groupoid.local_invariant_prop.lift_prop_within_at_mono
    (times_cont_diff_within_at_local_invariant_prop_mono I I' n) hf hts

theorem times_cont_mdiff_at.times_cont_mdiff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} {n : with_top ℕ} (hf : times_cont_mdiff_at I I' n f x) : times_cont_mdiff_within_at I I' n f s x :=
  times_cont_mdiff_within_at.mono hf (set.subset_univ s)

theorem smooth_at.smooth_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} (hf : smooth_at I I' f x) : smooth_within_at I I' f s x :=
  times_cont_mdiff_at.times_cont_mdiff_within_at hf

theorem times_cont_mdiff_on.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {t : set M} {n : with_top ℕ} (hf : times_cont_mdiff_on I I' n f s) (hts : t ⊆ s) : times_cont_mdiff_on I I' n f t :=
  fun (x : M) (hx : x ∈ t) => times_cont_mdiff_within_at.mono (hf x (hts hx)) hts

theorem times_cont_mdiff.times_cont_mdiff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {n : with_top ℕ} (hf : times_cont_mdiff I I' n f) : times_cont_mdiff_on I I' n f s :=
  fun (x : M) (hx : x ∈ s) => times_cont_mdiff_at.times_cont_mdiff_within_at (hf x)

theorem smooth.smooth_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} (hf : smooth I I' f) : smooth_on I I' f s :=
  times_cont_mdiff.times_cont_mdiff_on hf

theorem times_cont_mdiff_within_at_inter' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {t : set M} {x : M} {n : with_top ℕ} (ht : t ∈ nhds_within x s) : times_cont_mdiff_within_at I I' n f (s ∩ t) x ↔ times_cont_mdiff_within_at I I' n f s x :=
  structure_groupoid.local_invariant_prop.lift_prop_within_at_inter'
    (times_cont_diff_within_at_local_invariant_prop I I' n) ht

theorem times_cont_mdiff_within_at_inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {t : set M} {x : M} {n : with_top ℕ} (ht : t ∈ nhds x) : times_cont_mdiff_within_at I I' n f (s ∩ t) x ↔ times_cont_mdiff_within_at I I' n f s x :=
  structure_groupoid.local_invariant_prop.lift_prop_within_at_inter
    (times_cont_diff_within_at_local_invariant_prop I I' n) ht

theorem times_cont_mdiff_within_at.times_cont_mdiff_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} {n : with_top ℕ} (h : times_cont_mdiff_within_at I I' n f s x) (ht : s ∈ nhds x) : times_cont_mdiff_at I I' n f x :=
  structure_groupoid.local_invariant_prop.lift_prop_at_of_lift_prop_within_at
    (times_cont_diff_within_at_local_invariant_prop I I' n) h ht

theorem smooth_within_at.smooth_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {x : M} (h : smooth_within_at I I' f s x) (ht : s ∈ nhds x) : smooth_at I I' f x :=
  times_cont_mdiff_within_at.times_cont_mdiff_at h ht

/-- A function is `C^n` within a set at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
theorem times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {s : set M} {x : M} {n : ℕ} : times_cont_mdiff_within_at I I' (↑n) f s x ↔
  ∃ (u : set M), ∃ (H_1 : u ∈ nhds_within x (insert x s)), times_cont_mdiff_on I I' (↑n) f u := sorry

/-- A function is `C^n` at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
theorem times_cont_mdiff_at_iff_times_cont_mdiff_on_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {x : M} {n : ℕ} : times_cont_mdiff_at I I' (↑n) f x ↔ ∃ (u : set M), ∃ (H_1 : u ∈ nhds x), times_cont_mdiff_on I I' (↑n) f u := sorry

/-! ### Congruence lemmas -/

theorem times_cont_mdiff_within_at.congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {s : set M} {x : M} {n : with_top ℕ} (h : times_cont_mdiff_within_at I I' n f s x) (h₁ : ∀ (y : M), y ∈ s → f₁ y = f y) (hx : f₁ x = f x) : times_cont_mdiff_within_at I I' n f₁ s x :=
  structure_groupoid.local_invariant_prop.lift_prop_within_at_congr
    (times_cont_diff_within_at_local_invariant_prop I I' n) h h₁ hx

theorem times_cont_mdiff_within_at_congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {s : set M} {x : M} {n : with_top ℕ} (h₁ : ∀ (y : M), y ∈ s → f₁ y = f y) (hx : f₁ x = f x) : times_cont_mdiff_within_at I I' n f₁ s x ↔ times_cont_mdiff_within_at I I' n f s x :=
  structure_groupoid.local_invariant_prop.lift_prop_within_at_congr_iff
    (times_cont_diff_within_at_local_invariant_prop I I' n) h₁ hx

theorem times_cont_mdiff_within_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {s : set M} {x : M} {n : with_top ℕ} (h : times_cont_mdiff_within_at I I' n f s x) (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) : times_cont_mdiff_within_at I I' n f₁ s x :=
  structure_groupoid.local_invariant_prop.lift_prop_within_at_congr_of_eventually_eq
    (times_cont_diff_within_at_local_invariant_prop I I' n) h h₁ hx

theorem filter.eventually_eq.times_cont_mdiff_within_at_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {s : set M} {x : M} {n : with_top ℕ} (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) : times_cont_mdiff_within_at I I' n f₁ s x ↔ times_cont_mdiff_within_at I I' n f s x :=
  structure_groupoid.local_invariant_prop.lift_prop_within_at_congr_iff_of_eventually_eq
    (times_cont_diff_within_at_local_invariant_prop I I' n) h₁ hx

theorem times_cont_mdiff_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} {n : with_top ℕ} (h : times_cont_mdiff_at I I' n f x) (h₁ : filter.eventually_eq (nhds x) f₁ f) : times_cont_mdiff_at I I' n f₁ x :=
  structure_groupoid.local_invariant_prop.lift_prop_at_congr_of_eventually_eq
    (times_cont_diff_within_at_local_invariant_prop I I' n) h h₁

theorem filter.eventually_eq.times_cont_mdiff_at_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {x : M} {n : with_top ℕ} (h₁ : filter.eventually_eq (nhds x) f₁ f) : times_cont_mdiff_at I I' n f₁ x ↔ times_cont_mdiff_at I I' n f x :=
  structure_groupoid.local_invariant_prop.lift_prop_at_congr_iff_of_eventually_eq
    (times_cont_diff_within_at_local_invariant_prop I I' n) h₁

theorem times_cont_mdiff_on.congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {s : set M} {n : with_top ℕ} (h : times_cont_mdiff_on I I' n f s) (h₁ : ∀ (y : M), y ∈ s → f₁ y = f y) : times_cont_mdiff_on I I' n f₁ s :=
  structure_groupoid.local_invariant_prop.lift_prop_on_congr (times_cont_diff_within_at_local_invariant_prop I I' n) h h₁

theorem times_cont_mdiff_on_congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {f₁ : M → M'} {s : set M} {n : with_top ℕ} (h₁ : ∀ (y : M), y ∈ s → f₁ y = f y) : times_cont_mdiff_on I I' n f₁ s ↔ times_cont_mdiff_on I I' n f s :=
  structure_groupoid.local_invariant_prop.lift_prop_on_congr_iff (times_cont_diff_within_at_local_invariant_prop I I' n)
    h₁

/-! ### Locality -/

/-- Being `C^n` is a local property. -/
theorem times_cont_mdiff_on_of_locally_times_cont_mdiff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {s : set M} {n : with_top ℕ} (h : ∀ (x : M), x ∈ s → ∃ (u : set M), is_open u ∧ x ∈ u ∧ times_cont_mdiff_on I I' n f (s ∩ u)) : times_cont_mdiff_on I I' n f s :=
  structure_groupoid.local_invariant_prop.lift_prop_on_of_locally_lift_prop_on
    (times_cont_diff_within_at_local_invariant_prop I I' n) h

theorem times_cont_mdiff_of_locally_times_cont_mdiff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {f : M → M'} {n : with_top ℕ} (h : ∀ (x : M), ∃ (u : set M), is_open u ∧ x ∈ u ∧ times_cont_mdiff_on I I' n f u) : times_cont_mdiff I I' n f :=
  structure_groupoid.local_invariant_prop.lift_prop_of_locally_lift_prop_on
    (times_cont_diff_within_at_local_invariant_prop I I' n) h

/-! ### Smoothness of the composition of smooth functions between manifolds -/

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem times_cont_mdiff_on.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {s : set M} {n : with_top ℕ} {E'' : Type u_14} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_15} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_16} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {t : set M'} {g : M' → M''} (hg : times_cont_mdiff_on I' I'' n g t) (hf : times_cont_mdiff_on I I' n f s) (st : s ⊆ f ⁻¹' t) : times_cont_mdiff_on I I'' n (g ∘ f) s := sorry

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem times_cont_mdiff_on.comp' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {s : set M} {n : with_top ℕ} {E'' : Type u_14} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_15} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_16} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {t : set M'} {g : M' → M''} (hg : times_cont_mdiff_on I' I'' n g t) (hf : times_cont_mdiff_on I I' n f s) : times_cont_mdiff_on I I'' n (g ∘ f) (s ∩ f ⁻¹' t) :=
  times_cont_mdiff_on.comp hg (times_cont_mdiff_on.mono hf (set.inter_subset_left s (f ⁻¹' t)))
    (set.inter_subset_right s (f ⁻¹' t))

/-- The composition of `C^n` functions is `C^n`. -/
theorem times_cont_mdiff.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {n : with_top ℕ} {E'' : Type u_14} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_15} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_16} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {g : M' → M''} (hg : times_cont_mdiff I' I'' n g) (hf : times_cont_mdiff I I' n f) : times_cont_mdiff I I'' n (g ∘ f) := sorry

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
theorem times_cont_mdiff_within_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {s : set M} {n : with_top ℕ} {E'' : Type u_14} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_15} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_16} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {t : set M'} {g : M' → M''} (x : M) (hg : times_cont_mdiff_within_at I' I'' n g t (f x)) (hf : times_cont_mdiff_within_at I I' n f s x) (st : s ⊆ f ⁻¹' t) : times_cont_mdiff_within_at I I'' n (g ∘ f) s x := sorry

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
theorem times_cont_mdiff_within_at.comp' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {s : set M} {n : with_top ℕ} {E'' : Type u_14} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_15} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_16} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {t : set M'} {g : M' → M''} (x : M) (hg : times_cont_mdiff_within_at I' I'' n g t (f x)) (hf : times_cont_mdiff_within_at I I' n f s x) : times_cont_mdiff_within_at I I'' n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  times_cont_mdiff_within_at.comp x hg (times_cont_mdiff_within_at.mono hf (set.inter_subset_left s (f ⁻¹' t)))
    (set.inter_subset_right s (f ⁻¹' t))

/-- The composition of `C^n` functions at points is `C^n`. -/
theorem times_cont_mdiff_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {n : with_top ℕ} {E'' : Type u_14} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_15} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_16} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {g : M' → M''} (x : M) (hg : times_cont_mdiff_at I' I'' n g (f x)) (hf : times_cont_mdiff_at I I' n f x) : times_cont_mdiff_at I I'' n (g ∘ f) x :=
  times_cont_mdiff_within_at.comp x hg hf set.subset_preimage_univ

theorem times_cont_mdiff.comp_times_cont_mdiff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {n : with_top ℕ} {E'' : Type u_14} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_15} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_16} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {f : M → M'} {g : M' → M''} {s : set M} (hg : times_cont_mdiff I' I'' n g) (hf : times_cont_mdiff_on I I' n f s) : times_cont_mdiff_on I I'' n (g ∘ f) s :=
  times_cont_mdiff_on.comp (times_cont_mdiff.times_cont_mdiff_on hg) hf set.subset_preimage_univ

theorem smooth.comp_smooth_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {E'' : Type u_14} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_15} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_16} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {f : M → M'} {g : M' → M''} {s : set M} (hg : smooth I' I'' g) (hf : smooth_on I I' f s) : smooth_on I I'' (g ∘ f) s :=
  times_cont_mdiff_on.comp (smooth.smooth_on hg) hf set.subset_preimage_univ

/-! ### Atlas members are smooth -/

/-- An atlas member is `C^n` for any `n`. -/
theorem times_cont_mdiff_on_of_mem_maximal_atlas {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {n : with_top ℕ} {e : local_homeomorph M H} (h : e ∈ smooth_manifold_with_corners.maximal_atlas I M) : times_cont_mdiff_on I I n (⇑e) (local_equiv.source (local_homeomorph.to_local_equiv e)) := sorry

/-- The inverse of an atlas member is `C^n` for any `n`. -/
theorem times_cont_mdiff_on_symm_of_mem_maximal_atlas {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {n : with_top ℕ} {e : local_homeomorph M H} (h : e ∈ smooth_manifold_with_corners.maximal_atlas I M) : times_cont_mdiff_on I I n (⇑(local_homeomorph.symm e)) (local_equiv.target (local_homeomorph.to_local_equiv e)) := sorry

theorem times_cont_mdiff_on_chart {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {x : M} {n : with_top ℕ} : times_cont_mdiff_on I I n (⇑(charted_space.chart_at H x))
  (local_equiv.source (local_homeomorph.to_local_equiv (charted_space.chart_at H x))) :=
  times_cont_mdiff_on_of_mem_maximal_atlas (structure_groupoid.chart_mem_maximal_atlas (times_cont_diff_groupoid ⊤ I) x)

theorem times_cont_mdiff_on_chart_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {x : M} {n : with_top ℕ} : times_cont_mdiff_on I I n (⇑(local_homeomorph.symm (charted_space.chart_at H x)))
  (local_equiv.target (local_homeomorph.to_local_equiv (charted_space.chart_at H x))) :=
  times_cont_mdiff_on_symm_of_mem_maximal_atlas
    (structure_groupoid.chart_mem_maximal_atlas (times_cont_diff_groupoid ⊤ I) x)

/-! ### The identity is smooth -/

theorem times_cont_mdiff_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {n : with_top ℕ} : times_cont_mdiff I I n id := sorry

theorem smooth_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] : smooth I I id :=
  times_cont_mdiff_id

theorem times_cont_mdiff_on_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {s : set M} {n : with_top ℕ} : times_cont_mdiff_on I I n id s :=
  times_cont_mdiff.times_cont_mdiff_on times_cont_mdiff_id

theorem smooth_on_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {s : set M} : smooth_on I I id s :=
  times_cont_mdiff_on_id

theorem times_cont_mdiff_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {x : M} {n : with_top ℕ} : times_cont_mdiff_at I I n id x :=
  times_cont_mdiff.times_cont_mdiff_at times_cont_mdiff_id

theorem smooth_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {x : M} : smooth_at I I id x :=
  times_cont_mdiff_at_id

theorem times_cont_mdiff_within_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {s : set M} {x : M} {n : with_top ℕ} : times_cont_mdiff_within_at I I n id s x :=
  times_cont_mdiff_at.times_cont_mdiff_within_at times_cont_mdiff_at_id

theorem smooth_within_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {s : set M} {x : M} : smooth_within_at I I id s x :=
  times_cont_mdiff_within_at_id

/-! ### Constants are smooth -/

theorem times_cont_mdiff_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {n : with_top ℕ} {c : M'} : times_cont_mdiff I I' n fun (x : M) => c := sorry

theorem smooth_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {c : M'} : smooth I I' fun (x : M) => c :=
  times_cont_mdiff_const

theorem times_cont_mdiff_on_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {s : set M} {n : with_top ℕ} {c : M'} : times_cont_mdiff_on I I' n (fun (x : M) => c) s :=
  times_cont_mdiff.times_cont_mdiff_on times_cont_mdiff_const

theorem smooth_on_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {s : set M} {c : M'} : smooth_on I I' (fun (x : M) => c) s :=
  times_cont_mdiff_on_const

theorem times_cont_mdiff_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {x : M} {n : with_top ℕ} {c : M'} : times_cont_mdiff_at I I' n (fun (x : M) => c) x :=
  times_cont_mdiff.times_cont_mdiff_at times_cont_mdiff_const

theorem smooth_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {x : M} {c : M'} : smooth_at I I' (fun (x : M) => c) x :=
  times_cont_mdiff_at_const

theorem times_cont_mdiff_within_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {s : set M} {x : M} {n : with_top ℕ} {c : M'} : times_cont_mdiff_within_at I I' n (fun (x : M) => c) s x :=
  times_cont_mdiff_at.times_cont_mdiff_within_at times_cont_mdiff_at_const

theorem smooth_within_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {s : set M} {x : M} {c : M'} : smooth_within_at I I' (fun (x : M) => c) s x :=
  times_cont_mdiff_within_at_const

/-! ### Equivalence with the basic definition for functions between vector spaces -/

theorem times_cont_mdiff_within_at_iff_times_cont_diff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} {f : E → E'} {s : set E} {x : E} : times_cont_mdiff_within_at (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f s x ↔
  times_cont_diff_within_at 𝕜 n f s x := sorry

theorem times_cont_diff_within_at.times_cont_mdiff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} {f : E → E'} {s : set E} {x : E} (hf : times_cont_diff_within_at 𝕜 n f s x) : times_cont_mdiff_within_at (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f s x :=
  iff.mpr times_cont_mdiff_within_at_iff_times_cont_diff_within_at hf

theorem times_cont_mdiff_at_iff_times_cont_diff_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} {f : E → E'} {x : E} : times_cont_mdiff_at (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f x ↔ times_cont_diff_at 𝕜 n f x := sorry

theorem times_cont_diff_at.times_cont_mdiff_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} {f : E → E'} {x : E} (hf : times_cont_diff_at 𝕜 n f x) : times_cont_mdiff_at (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f x :=
  iff.mpr times_cont_mdiff_at_iff_times_cont_diff_at hf

theorem times_cont_mdiff_on_iff_times_cont_diff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} {f : E → E'} {s : set E} : times_cont_mdiff_on (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f s ↔ times_cont_diff_on 𝕜 n f s := sorry

theorem times_cont_diff_on.times_cont_mdiff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} {f : E → E'} {s : set E} (hf : times_cont_diff_on 𝕜 n f s) : times_cont_mdiff_on (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f s :=
  iff.mpr times_cont_mdiff_on_iff_times_cont_diff_on hf

theorem times_cont_mdiff_iff_times_cont_diff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} {f : E → E'} : times_cont_mdiff (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f ↔ times_cont_diff 𝕜 n f := sorry

theorem times_cont_diff.times_cont_mdiff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} {f : E → E'} (hf : times_cont_diff 𝕜 n f) : times_cont_mdiff (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f :=
  iff.mpr times_cont_mdiff_iff_times_cont_diff hf

/-! ### The tangent map of a smooth function is smooth -/

/-- If a function is `C^n` with `1 ≤ n` on a domain with unique derivatives, then its bundled
derivative is continuous. In this auxiliary lemma, we prove this fact when the source and target
space are model spaces in models with corners. The general fact is proved in
`times_cont_mdiff_on.continuous_on_tangent_map_within`-/
theorem times_cont_mdiff_on.continuous_on_tangent_map_within_aux {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {n : with_top ℕ} {f : H → H'} {s : set H} (hf : times_cont_mdiff_on I I' n f s) (hn : 1 ≤ n) (hs : unique_mdiff_on I s) : continuous_on (tangent_map_within I I' f s) (tangent_bundle.proj I H ⁻¹' s) := sorry

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative is
`C^m` when `m+1 ≤ n`. In this auxiliary lemma, we prove this fact when the source and target space
are model spaces in models with corners. The general fact is proved in
`times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within` -/
theorem times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within_aux {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {m : with_top ℕ} {n : with_top ℕ} {f : H → H'} {s : set H} (hf : times_cont_mdiff_on I I' n f s) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) : times_cont_mdiff_on (model_with_corners.tangent I) (model_with_corners.tangent I') m (tangent_map_within I I' f s)
  (tangent_bundle.proj I H ⁻¹' s) := sorry

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative
is `C^m` when `m+1 ≤ n`. -/
theorem times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {s : set M} {m : with_top ℕ} {n : with_top ℕ} (hf : times_cont_mdiff_on I I' n f s) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) : times_cont_mdiff_on (model_with_corners.tangent I) (model_with_corners.tangent I') m (tangent_map_within I I' f s)
  (tangent_bundle.proj I M ⁻¹' s) := sorry

/-- If a function is `C^n` on a domain with unique derivatives, with `1 ≤ n`, then its bundled
derivative is continuous there. -/
theorem times_cont_mdiff_on.continuous_on_tangent_map_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {s : set M} {n : with_top ℕ} (hf : times_cont_mdiff_on I I' n f s) (hmn : 1 ≤ n) (hs : unique_mdiff_on I s) : continuous_on (tangent_map_within I I' f s) (tangent_bundle.proj I M ⁻¹' s) :=
  times_cont_mdiff_on.continuous_on (times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within hf hmn hs)

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. -/
theorem times_cont_mdiff.times_cont_mdiff_tangent_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {m : with_top ℕ} {n : with_top ℕ} (hf : times_cont_mdiff I I' n f) (hmn : m + 1 ≤ n) : times_cont_mdiff (model_with_corners.tangent I) (model_with_corners.tangent I') m (tangent_map I I' f) := sorry

/-- If a function is `C^n`, with `1 ≤ n`, then its bundled derivative is continuous. -/
theorem times_cont_mdiff.continuous_tangent_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {f : M → M'} {n : with_top ℕ} (hf : times_cont_mdiff I I' n f) (hmn : 1 ≤ n) : continuous (tangent_map I I' f) := sorry

/-! ### Smoothness of the projection in a basic smooth bundle -/

namespace basic_smooth_bundle_core


theorem times_cont_mdiff_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} (Z : basic_smooth_bundle_core I M E') : times_cont_mdiff (model_with_corners.prod I (model_with_corners_self 𝕜 E')) I n
  (topological_fiber_bundle_core.proj (to_topological_fiber_bundle_core Z)) := sorry

theorem smooth_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] (Z : basic_smooth_bundle_core I M E') : smooth (model_with_corners.prod I (model_with_corners_self 𝕜 E')) I
  (topological_fiber_bundle_core.proj (to_topological_fiber_bundle_core Z)) :=
  times_cont_mdiff_proj Z

theorem times_cont_mdiff_on_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} (Z : basic_smooth_bundle_core I M E') {s : set (topological_fiber_bundle_core.total_space (to_topological_fiber_bundle_core Z))} : times_cont_mdiff_on (model_with_corners.prod I (model_with_corners_self 𝕜 E')) I n
  (topological_fiber_bundle_core.proj (to_topological_fiber_bundle_core Z)) s :=
  times_cont_mdiff.times_cont_mdiff_on (times_cont_mdiff_proj Z)

theorem smooth_on_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] (Z : basic_smooth_bundle_core I M E') {s : set (topological_fiber_bundle_core.total_space (to_topological_fiber_bundle_core Z))} : smooth_on (model_with_corners.prod I (model_with_corners_self 𝕜 E')) I
  (topological_fiber_bundle_core.proj (to_topological_fiber_bundle_core Z)) s :=
  times_cont_mdiff_on_proj Z

theorem times_cont_mdiff_at_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} (Z : basic_smooth_bundle_core I M E') {p : topological_fiber_bundle_core.total_space (to_topological_fiber_bundle_core Z)} : times_cont_mdiff_at (model_with_corners.prod I (model_with_corners_self 𝕜 E')) I n
  (topological_fiber_bundle_core.proj (to_topological_fiber_bundle_core Z)) p :=
  times_cont_mdiff.times_cont_mdiff_at (times_cont_mdiff_proj Z)

theorem smooth_at_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] (Z : basic_smooth_bundle_core I M E') {p : topological_fiber_bundle_core.total_space (to_topological_fiber_bundle_core Z)} : smooth_at (model_with_corners.prod I (model_with_corners_self 𝕜 E')) I
  (topological_fiber_bundle_core.proj (to_topological_fiber_bundle_core Z)) p :=
  times_cont_mdiff_at_proj Z

theorem times_cont_mdiff_within_at_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {n : with_top ℕ} (Z : basic_smooth_bundle_core I M E') {s : set (topological_fiber_bundle_core.total_space (to_topological_fiber_bundle_core Z))} {p : topological_fiber_bundle_core.total_space (to_topological_fiber_bundle_core Z)} : times_cont_mdiff_within_at (model_with_corners.prod I (model_with_corners_self 𝕜 E')) I n
  (topological_fiber_bundle_core.proj (to_topological_fiber_bundle_core Z)) s p :=
  times_cont_mdiff_at.times_cont_mdiff_within_at (times_cont_mdiff_at_proj Z)

theorem smooth_within_at_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] (Z : basic_smooth_bundle_core I M E') {s : set (topological_fiber_bundle_core.total_space (to_topological_fiber_bundle_core Z))} {p : topological_fiber_bundle_core.total_space (to_topological_fiber_bundle_core Z)} : smooth_within_at (model_with_corners.prod I (model_with_corners_self 𝕜 E')) I
  (topological_fiber_bundle_core.proj (to_topological_fiber_bundle_core Z)) s p :=
  times_cont_mdiff_within_at_proj Z

/-- If an element of `E'` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is smooth. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
theorem smooth_const_section {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] (Z : basic_smooth_bundle_core I M E') (v : E') (h : ∀ (i j : ↥(charted_space.atlas H M)) (x : M),
  x ∈
      local_equiv.source (local_homeomorph.to_local_equiv (subtype.val i)) ∩
        local_equiv.source (local_homeomorph.to_local_equiv (subtype.val j)) →
    coord_change Z i j (coe_fn (subtype.val i) x) v = v) : smooth I (model_with_corners.prod I (model_with_corners_self 𝕜 E'))
  ((fun (this : M → topological_fiber_bundle_core.total_space (to_topological_fiber_bundle_core Z)) => this)
    fun (x : M) => sigma.mk x v) := sorry

end basic_smooth_bundle_core


/-! ### Smoothness of the tangent bundle projection -/

namespace tangent_bundle


theorem times_cont_mdiff_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {n : with_top ℕ} : times_cont_mdiff (model_with_corners.tangent I) I n (proj I M) :=
  basic_smooth_bundle_core.times_cont_mdiff_proj (tangent_bundle_core I M)

theorem smooth_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] : smooth (model_with_corners.tangent I) I (proj I M) :=
  basic_smooth_bundle_core.smooth_proj (tangent_bundle_core I M)

theorem times_cont_mdiff_on_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {n : with_top ℕ} {s : set (tangent_bundle I M)} : times_cont_mdiff_on (model_with_corners.tangent I) I n (proj I M) s :=
  basic_smooth_bundle_core.times_cont_mdiff_on_proj (tangent_bundle_core I M)

theorem smooth_on_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {s : set (tangent_bundle I M)} : smooth_on (model_with_corners.tangent I) I (proj I M) s :=
  basic_smooth_bundle_core.smooth_on_proj (tangent_bundle_core I M)

theorem times_cont_mdiff_at_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {n : with_top ℕ} {p : tangent_bundle I M} : times_cont_mdiff_at (model_with_corners.tangent I) I n (proj I M) p :=
  basic_smooth_bundle_core.times_cont_mdiff_at_proj (tangent_bundle_core I M)

theorem smooth_at_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {p : tangent_bundle I M} : smooth_at (model_with_corners.tangent I) I (proj I M) p :=
  basic_smooth_bundle_core.smooth_at_proj (tangent_bundle_core I M)

theorem times_cont_mdiff_within_at_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {n : with_top ℕ} {s : set (tangent_bundle I M)} {p : tangent_bundle I M} : times_cont_mdiff_within_at (model_with_corners.tangent I) I n (proj I M) s p :=
  basic_smooth_bundle_core.times_cont_mdiff_within_at_proj (tangent_bundle_core I M)

theorem smooth_within_at_proj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {s : set (tangent_bundle I M)} {p : tangent_bundle I M} : smooth_within_at (model_with_corners.tangent I) I (proj I M) s p :=
  basic_smooth_bundle_core.smooth_within_at_proj (tangent_bundle_core I M)

/-- The zero section of the tangent bundle -/
def zero_section {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) (M : Type u_4) [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] : M → tangent_bundle I M :=
  fun (x : M) => sigma.mk x 0

theorem smooth_zero_section {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] : smooth I (model_with_corners.tangent I) (zero_section I M) := sorry

/-- The derivative of the zero section of the tangent bundle maps `⟨x, v⟩` to `⟨⟨x, 0⟩, ⟨v, 0⟩⟩`.

Note that, as currently framed, this is a statement in coordinates, thus reliant on the choice
of the coordinate system we use on the tangent bundle.

However, the result itself is coordinate-dependent only to the extent that the coordinates
determine a splitting of the tangent bundle.  Moreover, there is a canonical splitting at each
point of the zero section (since there is a canonical horizontal space there, the tangent space
to the zero section, in addition to the canonical vertical space which is the kernel of the
derivative of the projection), and this canonical splitting is also the one that comes from the
coordinates on the tangent bundle in our definitions. So this statement is not as crazy as it
may seem.

TODO define splittings of vector bundles; state this result invariantly. -/
theorem tangent_map_tangent_bundle_pure {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] (p : tangent_bundle I M) : tangent_map I (model_with_corners.tangent I) (zero_section I M) p = sigma.mk (sigma.mk (sigma.fst p) 0) (sigma.snd p, 0) := sorry

end tangent_bundle


/-! ### Smoothness of standard maps associated to the product of manifolds -/

theorem times_cont_mdiff_within_at.prod_mk {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] {s : set M} {x : M} {n : with_top ℕ} {f : M → M'} {g : M → N'} (hf : times_cont_mdiff_within_at I I' n f s x) (hg : times_cont_mdiff_within_at I J' n g s x) : times_cont_mdiff_within_at I (model_with_corners.prod I' J') n (fun (x : M) => (f x, g x)) s x := sorry

theorem times_cont_mdiff_at.prod_mk {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] {x : M} {n : with_top ℕ} {f : M → M'} {g : M → N'} (hf : times_cont_mdiff_at I I' n f x) (hg : times_cont_mdiff_at I J' n g x) : times_cont_mdiff_at I (model_with_corners.prod I' J') n (fun (x : M) => (f x, g x)) x :=
  times_cont_mdiff_within_at.prod_mk hf hg

theorem times_cont_mdiff_on.prod_mk {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] {s : set M} {n : with_top ℕ} {f : M → M'} {g : M → N'} (hf : times_cont_mdiff_on I I' n f s) (hg : times_cont_mdiff_on I J' n g s) : times_cont_mdiff_on I (model_with_corners.prod I' J') n (fun (x : M) => (f x, g x)) s :=
  fun (x : M) (hx : x ∈ s) => times_cont_mdiff_within_at.prod_mk (hf x hx) (hg x hx)

theorem times_cont_mdiff.prod_mk {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] {n : with_top ℕ} {f : M → M'} {g : M → N'} (hf : times_cont_mdiff I I' n f) (hg : times_cont_mdiff I J' n g) : times_cont_mdiff I (model_with_corners.prod I' J') n fun (x : M) => (f x, g x) :=
  fun (x : M) => times_cont_mdiff_at.prod_mk (hf x) (hg x)

theorem smooth_within_at.prod_mk {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] {s : set M} {x : M} {f : M → M'} {g : M → N'} (hf : smooth_within_at I I' f s x) (hg : smooth_within_at I J' g s x) : smooth_within_at I (model_with_corners.prod I' J') (fun (x : M) => (f x, g x)) s x :=
  times_cont_mdiff_within_at.prod_mk hf hg

theorem smooth_at.prod_mk {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] {x : M} {f : M → M'} {g : M → N'} (hf : smooth_at I I' f x) (hg : smooth_at I J' g x) : smooth_at I (model_with_corners.prod I' J') (fun (x : M) => (f x, g x)) x :=
  times_cont_mdiff_at.prod_mk hf hg

theorem smooth_on.prod_mk {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] {s : set M} {f : M → M'} {g : M → N'} (hf : smooth_on I I' f s) (hg : smooth_on I J' g s) : smooth_on I (model_with_corners.prod I' J') (fun (x : M) => (f x, g x)) s :=
  times_cont_mdiff_on.prod_mk hf hg

theorem smooth.prod_mk {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] {f : M → M'} {g : M → N'} (hf : smooth I I' f) (hg : smooth I J' g) : smooth I (model_with_corners.prod I' J') fun (x : M) => (f x, g x) :=
  times_cont_mdiff.prod_mk hf hg

theorem times_cont_mdiff_within_at_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {n : with_top ℕ} {s : set (M × N)} {p : M × N} : times_cont_mdiff_within_at (model_with_corners.prod I J) I n prod.fst s p := sorry

theorem times_cont_mdiff_at_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {n : with_top ℕ} {p : M × N} : times_cont_mdiff_at (model_with_corners.prod I J) I n prod.fst p :=
  times_cont_mdiff_within_at_fst

theorem times_cont_mdiff_on_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {n : with_top ℕ} {s : set (M × N)} : times_cont_mdiff_on (model_with_corners.prod I J) I n prod.fst s :=
  fun (x : M × N) (hx : x ∈ s) => times_cont_mdiff_within_at_fst

theorem times_cont_mdiff_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {n : with_top ℕ} : times_cont_mdiff (model_with_corners.prod I J) I n prod.fst :=
  fun (x : M × N) => times_cont_mdiff_at_fst

theorem smooth_within_at_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {s : set (M × N)} {p : M × N} : smooth_within_at (model_with_corners.prod I J) I prod.fst s p :=
  times_cont_mdiff_within_at_fst

theorem smooth_at_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {p : M × N} : smooth_at (model_with_corners.prod I J) I prod.fst p :=
  times_cont_mdiff_at_fst

theorem smooth_on_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {s : set (M × N)} : smooth_on (model_with_corners.prod I J) I prod.fst s :=
  times_cont_mdiff_on_fst

theorem smooth_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] : smooth (model_with_corners.prod I J) I prod.fst :=
  times_cont_mdiff_fst

theorem times_cont_mdiff_within_at_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {n : with_top ℕ} {s : set (M × N)} {p : M × N} : times_cont_mdiff_within_at (model_with_corners.prod I J) J n prod.snd s p := sorry

theorem times_cont_mdiff_at_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {n : with_top ℕ} {p : M × N} : times_cont_mdiff_at (model_with_corners.prod I J) J n prod.snd p :=
  times_cont_mdiff_within_at_snd

theorem times_cont_mdiff_on_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {n : with_top ℕ} {s : set (M × N)} : times_cont_mdiff_on (model_with_corners.prod I J) J n prod.snd s :=
  fun (x : M × N) (hx : x ∈ s) => times_cont_mdiff_within_at_snd

theorem times_cont_mdiff_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {n : with_top ℕ} : times_cont_mdiff (model_with_corners.prod I J) J n prod.snd :=
  fun (x : M × N) => times_cont_mdiff_at_snd

theorem smooth_within_at_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {s : set (M × N)} {p : M × N} : smooth_within_at (model_with_corners.prod I J) J prod.snd s p :=
  times_cont_mdiff_within_at_snd

theorem smooth_at_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {p : M × N} : smooth_at (model_with_corners.prod I J) J prod.snd p :=
  times_cont_mdiff_at_snd

theorem smooth_on_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] {s : set (M × N)} : smooth_on (model_with_corners.prod I J) J prod.snd s :=
  times_cont_mdiff_on_snd

theorem smooth_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] : smooth (model_with_corners.prod I J) J prod.snd :=
  times_cont_mdiff_snd

theorem smooth_iff_proj_smooth {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N'] {f : M → M' × N'} : smooth I (model_with_corners.prod I' J') f ↔ smooth I I' (prod.fst ∘ f) ∧ smooth I J' (prod.snd ∘ f) := sorry

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem times_cont_mdiff_within_at.prod_map' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N'] {f : M → M'} {s : set M} {n : with_top ℕ} {g : N → N'} {r : set N} {p : M × N} (hf : times_cont_mdiff_within_at I I' n f s (prod.fst p)) (hg : times_cont_mdiff_within_at J J' n g r (prod.snd p)) : times_cont_mdiff_within_at (model_with_corners.prod I J) (model_with_corners.prod I' J') n (prod.map f g) (set.prod s r)
  p :=
  times_cont_mdiff_within_at.prod_mk
    (times_cont_mdiff_within_at.comp p hf times_cont_mdiff_within_at_fst (set.prod_subset_preimage_fst s r))
    (times_cont_mdiff_within_at.comp p hg times_cont_mdiff_within_at_snd (set.prod_subset_preimage_snd s r))

theorem times_cont_mdiff_within_at.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N'] {f : M → M'} {s : set M} {x : M} {n : with_top ℕ} {g : N → N'} {r : set N} {y : N} (hf : times_cont_mdiff_within_at I I' n f s x) (hg : times_cont_mdiff_within_at J J' n g r y) : times_cont_mdiff_within_at (model_with_corners.prod I J) (model_with_corners.prod I' J') n (prod.map f g) (set.prod s r)
  (x, y) :=
  times_cont_mdiff_within_at.prod_map' hf hg

theorem times_cont_mdiff_at.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N'] {f : M → M'} {x : M} {n : with_top ℕ} {g : N → N'} {y : N} (hf : times_cont_mdiff_at I I' n f x) (hg : times_cont_mdiff_at J J' n g y) : times_cont_mdiff_at (model_with_corners.prod I J) (model_with_corners.prod I' J') n (prod.map f g) (x, y) := sorry

theorem times_cont_mdiff_at.prod_map' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N'] {f : M → M'} {n : with_top ℕ} {g : N → N'} {p : M × N} (hf : times_cont_mdiff_at I I' n f (prod.fst p)) (hg : times_cont_mdiff_at J J' n g (prod.snd p)) : times_cont_mdiff_at (model_with_corners.prod I J) (model_with_corners.prod I' J') n (prod.map f g) p := sorry

theorem times_cont_mdiff_on.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N'] {f : M → M'} {s : set M} {n : with_top ℕ} {g : N → N'} {r : set N} (hf : times_cont_mdiff_on I I' n f s) (hg : times_cont_mdiff_on J J' n g r) : times_cont_mdiff_on (model_with_corners.prod I J) (model_with_corners.prod I' J') n (prod.map f g) (set.prod s r) :=
  times_cont_mdiff_on.prod_mk (times_cont_mdiff_on.comp hf times_cont_mdiff_on_fst (set.prod_subset_preimage_fst s r))
    (times_cont_mdiff_on.comp hg times_cont_mdiff_on_snd (set.prod_subset_preimage_snd s r))

theorem times_cont_mdiff.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N'] {f : M → M'} {n : with_top ℕ} {g : N → N'} (hf : times_cont_mdiff I I' n f) (hg : times_cont_mdiff J J' n g) : times_cont_mdiff (model_with_corners.prod I J) (model_with_corners.prod I' J') n (prod.map f g) :=
  id fun (p : M × N) => times_cont_mdiff_at.prod_map' (hf (prod.fst p)) (hg (prod.snd p))

theorem smooth_within_at.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N'] {f : M → M'} {s : set M} {x : M} {g : N → N'} {r : set N} {y : N} (hf : smooth_within_at I I' f s x) (hg : smooth_within_at J J' g r y) : smooth_within_at (model_with_corners.prod I J) (model_with_corners.prod I' J') (prod.map f g) (set.prod s r) (x, y) :=
  times_cont_mdiff_within_at.prod_map hf hg

theorem smooth_at.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N'] {f : M → M'} {x : M} {g : N → N'} {y : N} (hf : smooth_at I I' f x) (hg : smooth_at J J' g y) : smooth_at (model_with_corners.prod I J) (model_with_corners.prod I' J') (prod.map f g) (x, y) :=
  times_cont_mdiff_at.prod_map hf hg

theorem smooth_on.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N'] {f : M → M'} {s : set M} {g : N → N'} {r : set N} (hf : smooth_on I I' f s) (hg : smooth_on J J' g r) : smooth_on (model_with_corners.prod I J) (model_with_corners.prod I' J') (prod.map f g) (set.prod s r) :=
  times_cont_mdiff_on.prod_map hf hg

theorem smooth.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_4} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M' : Type u_7} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M'] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {G : Type u_9} [topological_space G] {J : model_with_corners 𝕜 F G} {N : Type u_10} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N] {F' : Type u_11} [normed_group F'] [normed_space 𝕜 F'] {G' : Type u_12} [topological_space G'] {J' : model_with_corners 𝕜 F' G'} {N' : Type u_13} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N'] {f : M → M'} {g : N → N'} (hf : smooth I I' f) (hg : smooth J J' g) : smooth (model_with_corners.prod I J) (model_with_corners.prod I' J') (prod.map f g) :=
  times_cont_mdiff.prod_map hf hg

/-! ### Linear maps between normed spaces are smooth -/

theorem continuous_linear_map.times_cont_mdiff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_8} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} (L : continuous_linear_map 𝕜 E F) : times_cont_mdiff (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 F) n ⇑L := sorry

/-! ### Smoothness of standard operations -/

/-- On any vector space, multiplication by a scalar is a smooth operation. -/
theorem smooth_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {V : Type u_14} [normed_group V] [normed_space 𝕜 V] : smooth (model_with_corners.prod (model_with_corners_self 𝕜 𝕜) (model_with_corners_self 𝕜 V))
  (model_with_corners_self 𝕜 V) fun (p : 𝕜 × V) => prod.fst p • prod.snd p := sorry

theorem smooth.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] {I : model_with_corners 𝕜 E H} {V : Type u_14} [normed_group V] [normed_space 𝕜 V] {N : Type u_4} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {f : N → 𝕜} {g : N → V} (hf : smooth I (model_with_corners_self 𝕜 𝕜) f) (hg : smooth I (model_with_corners_self 𝕜 V) g) : smooth I (model_with_corners_self 𝕜 V) fun (p : N) => f p • g p :=
  times_cont_mdiff.comp smooth_smul (smooth.prod_mk hf hg)

