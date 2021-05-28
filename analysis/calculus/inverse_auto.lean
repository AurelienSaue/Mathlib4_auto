/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.calculus.times_cont_diff
import Mathlib.topology.local_homeomorph
import Mathlib.topology.metric_space.contracting
import PostPort

universes u_1 u_2 u_3 u_6 u_7 u_8 

namespace Mathlib

/-!
# Inverse function theorem

In this file we prove the inverse function theorem. It says that if a map `f : E → F`
has an invertible strict derivative `f'` at `a`, then it is locally invertible,
and the inverse function has derivative `f' ⁻¹`.

We define `has_strict_deriv_at.to_local_homeomorph` that repacks a function `f`
with a `hf : has_strict_fderiv_at f f' a`, `f' : E ≃L[𝕜] F`, into a `local_homeomorph`.
The `to_fun` of this `local_homeomorph` is `defeq` to `f`, so one can apply theorems
about `local_homeomorph` to `hf.to_local_homeomorph f`, and get statements about `f`.

Then we define `has_strict_fderiv_at.local_inverse` to be the `inv_fun` of this `local_homeomorph`,
and prove two versions of the inverse function theorem:

* `has_strict_fderiv_at.to_local_inverse`: if `f` has an invertible derivative `f'` at `a` in the
  strict sense (`hf`), then `hf.local_inverse f f' a` has derivative `f'.symm` at `f a` in the
  strict sense;

* `has_strict_fderiv_at.to_local_left_inverse`: if `f` has an invertible derivative `f'` at `a` in
  the strict sense and `g` is locally left inverse to `f` near `a`, then `g` has derivative
  `f'.symm` at `f a` in the strict sense.

In the one-dimensional case we reformulate these theorems in terms of `has_strict_deriv_at` and
`f'⁻¹`.

We also reformulate the theorems in terms of `times_cont_diff`, to give that `C^k` (respectively,
smooth) inputs give `C^k` (smooth) inverses.  These versions require that continuous
differentiability implies strict differentiability; this is false over a general field, true over
`ℝ` or `ℂ` and implemented here assuming `is_R_or_C 𝕂`.

Some related theorems, providing the derivative and higher regularity assuming that we already know
the inverse function, are formulated in `fderiv.lean`, `deriv.lean`, and `times_cont_diff.lean`.

## Notations

In the section about `approximates_linear_on` we introduce some `local notation` to make formulas
shorter:

* by `N` we denote `∥f'⁻¹∥`;
* by `g` we denote the auxiliary contracting map `x ↦ x + f'.symm (y - f x)` used to prove that
  `{x | f x = y}` is nonempty.

## Tags

derivative, strictly differentiable, continuously differentiable, smooth, inverse function
-/

/-!
### Non-linear maps approximating close to affine maps

In this section we study a map `f` such that `∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥` on an open set
`s`, where `f' : E ≃L[𝕜] F` is a continuous linear equivalence and `c < ∥f'⁻¹∥`. Maps of this type
behave like `f a + f' (x - a)` near each `a ∈ s`.

If `E` is a complete space, we prove that the image `f '' s` is open, and `f` is a homeomorphism
between `s` and `f '' s`. More precisely, we define `approximates_linear_on.to_local_homeomorph` to
be a `local_homeomorph` with `to_fun = f`, `source = s`, and `target = f '' s`.

Maps of this type naturally appear in the proof of the inverse function theorem (see next section),
and `approximates_linear_on.to_local_homeomorph` will imply that the locally inverse function
exists.

We define this auxiliary notion to split the proof of the inverse function theorem into small
lemmas. This approach makes it possible

- to prove a lower estimate on the size of the domain of the inverse function;

- to reuse parts of the proofs in the case if a function is not strictly differentiable. E.g., for a
  function `f : E × F → G` with estimates on `f x y₁ - f x y₂` but not on `f x₁ y - f x₂ y`.
-/

/-- We say that `f` approximates a continuous linear map `f'` on `s` with constant `c`,
if `∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥` whenever `x, y ∈ s`.

This predicate is defined to facilitate the splitting of the inverse function theorem into small
lemmas. Some of these lemmas can be useful, e.g., to prove that the inverse function is defined
on a specific set. -/
def approximates_linear_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (f' : continuous_linear_map 𝕜 E F) (s : set E) (c : nnreal)  :=
  ∀ (x : E), x ∈ s → ∀ (y : E), y ∈ s → norm (f x - f y - coe_fn f' (x - y)) ≤ ↑c * norm (x - y)

namespace approximates_linear_on


/-! First we prove some properties of a function that `approximates_linear_on` a (not necessarily
invertible) continuous linear map. -/

theorem mono_num {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {s : set E} {c : nnreal} {c' : nnreal} (hc : c ≤ c') (hf : approximates_linear_on f f' s c) : approximates_linear_on f f' s c' :=
  fun (x : E) (hx : x ∈ s) (y : E) (hy : y ∈ s) =>
    le_trans (hf x hx y hy) (mul_le_mul_of_nonneg_right hc (norm_nonneg (x - y)))

theorem mono_set {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {s : set E} {t : set E} {c : nnreal} (hst : s ⊆ t) (hf : approximates_linear_on f f' t c) : approximates_linear_on f f' s c :=
  fun (x : E) (hx : x ∈ s) (y : E) (hy : y ∈ s) => hf x (hst hx) y (hst hy)

theorem lipschitz_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f f' s c) : lipschitz_with c fun (x : ↥s) => f ↑x - coe_fn f' ↑x := sorry

protected theorem lipschitz {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f f' s c) : lipschitz_with (nnnorm f' + c) (set.restrict f s) := sorry

protected theorem continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f f' s c) : continuous (set.restrict f s) :=
  lipschitz_with.continuous (approximates_linear_on.lipschitz hf)

protected theorem continuous_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f f' s c) : continuous_on f s :=
  iff.mpr continuous_on_iff_continuous_restrict (approximates_linear_on.continuous hf)

/-!
From now on we assume that `f` approximates an invertible continuous linear map `f : E ≃L[𝕜] F`.

We also assume that either `E = {0}`, or `c < ∥f'⁻¹∥⁻¹`. We use `N` as an abbreviation for `∥f'⁻¹∥`.
-/

protected theorem antilipschitz {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) : antilipschitz_with (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹ - c⁻¹) (set.restrict f s) := sorry

protected theorem injective {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) : function.injective (set.restrict f s) :=
  antilipschitz_with.injective (approximates_linear_on.antilipschitz hf hc)

protected theorem inj_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) : set.inj_on f s :=
  iff.mpr set.inj_on_iff_injective (approximates_linear_on.injective hf hc)

/-- A map approximating a linear equivalence on a set defines a local equivalence on this set.
Should not be used outside of this file, because it is superseded by `to_local_homeomorph` below.

This is a first step towards the inverse function. -/
def to_local_equiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) : local_equiv E F :=
  set.inj_on.to_local_equiv f s (approximates_linear_on.inj_on hf hc)

/-- The inverse function is continuous on `f '' s`. Use properties of `local_homeomorph` instead. -/
theorem inverse_continuous_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) : continuous_on (⇑(local_equiv.symm (to_local_equiv hf hc))) (f '' s) := sorry

/-!
Now we prove that `f '' s` is an open set. This follows from the fact that the restriction of `f`
on `s` is an open map. More precisely, we show that the image of a closed ball $$\bar B(a, ε) ⊆ s$$
under `f` includes the closed ball $$\bar B\left(f(a), \frac{ε}{∥{f'}⁻¹∥⁻¹-c}\right)$$.

In order to do this, we introduce an auxiliary map $$g_y(x) = x + {f'}⁻¹ (y - f x)$$. Provided that
$$∥y - f a∥ ≤ \frac{ε}{∥{f'}⁻¹∥⁻¹-c}$$, we prove that $$g_y$$ contracts in $$\bar B(a, ε)$$ and `f`
sends the fixed point of $$g_y$$ to `y`.
-/

/-- Iterations of this map converge to `f⁻¹ y`. The formula is very similar to the one
used in Newton's method, but we use the same `f'.symm` for all `y` instead of evaluating
the derivative at each point along the orbit. -/
def inverse_approx_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (f' : continuous_linear_equiv 𝕜 E F) (y : F) (x : E) : E :=
  x + coe_fn (continuous_linear_equiv.symm f') (y - f x)

theorem inverse_approx_map_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} (y : F) (x : E) (x' : E) : inverse_approx_map f f' y x - inverse_approx_map f f' y x' =
  x - x' - coe_fn (continuous_linear_equiv.symm f') (f x - f x') := sorry

theorem inverse_approx_map_dist_self {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} (y : F) (x : E) : dist (inverse_approx_map f f' y x) x =
  dist (coe_fn (continuous_linear_equiv.symm f') (f x)) (coe_fn (continuous_linear_equiv.symm f') y) := sorry

theorem inverse_approx_map_dist_self_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} (y : F) (x : E) : dist (inverse_approx_map f f' y x) x ≤ ↑(nnnorm ↑(continuous_linear_equiv.symm f')) * dist (f x) y := sorry

theorem inverse_approx_map_fixed_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} (y : F) {x : E} : inverse_approx_map f f' y x = x ↔ f x = y := sorry

theorem inverse_approx_map_contracts_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} (y : F) (hf : approximates_linear_on f (↑f') s c) {x : E} {x' : E} (hx : x ∈ s) (hx' : x' ∈ s) : dist (inverse_approx_map f f' y x) (inverse_approx_map f f' y x') ≤
  ↑(nnnorm ↑(continuous_linear_equiv.symm f')) * ↑c * dist x x' := sorry

theorem inverse_approx_map_maps_to {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} {y : F} {ε : ℝ} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) {b : E} (hb : b ∈ s) (hε : metric.closed_ball b ε ⊆ s) (hy : y ∈ metric.closed_ball (f b) ((↑(nnnorm ↑(continuous_linear_equiv.symm f'))⁻¹ - ↑c) * ε)) : set.maps_to (inverse_approx_map f f' y) (metric.closed_ball b ε) (metric.closed_ball b ε) := sorry

theorem surj_on_closed_ball {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} {ε : ℝ} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) {b : E} (ε0 : 0 ≤ ε) (hε : metric.closed_ball b ε ⊆ s) : set.surj_on f (metric.closed_ball b ε)
  (metric.closed_ball (f b) ((↑(nnnorm ↑(continuous_linear_equiv.symm f'))⁻¹ - ↑c) * ε)) := sorry

/-- Given a function `f` that approximates a linear equivalence on an open set `s`,
returns a local homeomorph with `to_fun = f` and `source = s`. -/
def to_local_homeomorph {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] (f : E → F) {f' : continuous_linear_equiv 𝕜 E F} (s : set E) {c : nnreal} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) (hs : is_open s) : local_homeomorph E F :=
  local_homeomorph.mk (to_local_equiv hf hc) hs sorry sorry (inverse_continuous_on hf hc)

@[simp] theorem to_local_homeomorph_coe {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) (hs : is_open s) : ⇑(to_local_homeomorph f s hf hc hs) = f :=
  rfl

@[simp] theorem to_local_homeomorph_source {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) (hs : is_open s) : local_equiv.source (local_homeomorph.to_local_equiv (to_local_homeomorph f s hf hc hs)) = s :=
  rfl

@[simp] theorem to_local_homeomorph_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) (hs : is_open s) : local_equiv.target (local_homeomorph.to_local_equiv (to_local_homeomorph f s hf hc hs)) = f '' s :=
  rfl

theorem closed_ball_subset_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {s : set E} {c : nnreal} {ε : ℝ} (hf : approximates_linear_on f (↑f') s c) (hc : subsingleton E ∨ c < (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹)) (hs : is_open s) {b : E} (ε0 : 0 ≤ ε) (hε : metric.closed_ball b ε ⊆ s) : metric.closed_ball (f b) ((↑(nnnorm ↑(continuous_linear_equiv.symm f'))⁻¹ - ↑c) * ε) ⊆
  local_equiv.target (local_homeomorph.to_local_equiv (to_local_homeomorph f s hf hc hs)) :=
  set.surj_on.mono hε
    (set.subset.refl (metric.closed_ball (f b) ((↑(nnnorm ↑(continuous_linear_equiv.symm f'))⁻¹ - ↑c) * ε)))
    (surj_on_closed_ball hf hc ε0 hε)

end approximates_linear_on


/-!
### Inverse function theorem

Now we prove the inverse function theorem. Let `f : E → F` be a map defined on a complete vector
space `E`. Assume that `f` has an invertible derivative `f' : E ≃L[𝕜] F` at `a : E` in the strict
sense. Then `f` approximates `f'` in the sense of `approximates_linear_on` on an open neighborhood
of `a`, and we can apply `approximates_linear_on.to_local_homeomorph` to construct the inverse
function. -/

namespace has_strict_fderiv_at


/-- If `f` has derivative `f'` at `a` in the strict sense and `c > 0`, then `f` approximates `f'`
with constant `c` on some neighborhood of `a`. -/
theorem approximates_deriv_on_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f f' a) {c : nnreal} (hc : subsingleton E ∨ 0 < c) : ∃ (s : set E), ∃ (H : s ∈ nhds a), approximates_linear_on f f' s c := sorry

theorem approximates_deriv_on_open_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : ∃ (s : set E),
  ∃ (hs : a ∈ s ∧ is_open s), approximates_linear_on f (↑f') s (nnnorm ↑(continuous_linear_equiv.symm f')⁻¹ / bit0 1) := sorry

/-- Given a function with an invertible strict derivative at `a`, returns a `local_homeomorph`
with `to_fun = f` and `a ∈ source`. This is a part of the inverse function theorem.
The other part `has_strict_fderiv_at.to_local_inverse` states that the inverse function
of this `local_homeomorph` has derivative `f'.symm`. -/
def to_local_homeomorph {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] (f : E → F) {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : local_homeomorph E F :=
  approximates_linear_on.to_local_homeomorph f (classical.some (approximates_deriv_on_open_nhds hf)) sorry sorry sorry

@[simp] theorem to_local_homeomorph_coe {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : ⇑(to_local_homeomorph f hf) = f :=
  rfl

theorem mem_to_local_homeomorph_source {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : a ∈ local_equiv.source (local_homeomorph.to_local_equiv (to_local_homeomorph f hf)) :=
  and.left (Exists.fst (classical.some_spec (approximates_deriv_on_open_nhds hf)))

theorem image_mem_to_local_homeomorph_target {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : f a ∈ local_equiv.target (local_homeomorph.to_local_equiv (to_local_homeomorph f hf)) :=
  local_homeomorph.map_source (to_local_homeomorph f hf) (mem_to_local_homeomorph_source hf)

theorem map_nhds_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : filter.map f (nhds a) = nhds (f a) :=
  local_homeomorph.map_nhds_eq (to_local_homeomorph f hf) (mem_to_local_homeomorph_source hf)

/-- Given a function `f` with an invertible derivative, returns a function that is locally inverse
to `f`. -/
def local_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] (f : E → F) (f' : continuous_linear_equiv 𝕜 E F) (a : E) (hf : has_strict_fderiv_at f (↑f') a) : F → E :=
  ⇑(local_homeomorph.symm (to_local_homeomorph f hf))

theorem local_inverse_def {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : local_inverse f f' a hf = ⇑(local_homeomorph.symm (to_local_homeomorph f hf)) :=
  rfl

theorem eventually_left_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : filter.eventually (fun (x : E) => local_inverse f f' a hf (f x) = x) (nhds a) :=
  local_homeomorph.eventually_left_inverse (to_local_homeomorph f hf) (mem_to_local_homeomorph_source hf)

@[simp] theorem local_inverse_apply_image {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : local_inverse f f' a hf (f a) = a :=
  filter.eventually.self_of_nhds (eventually_left_inverse hf)

theorem eventually_right_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : filter.eventually (fun (y : F) => f (local_inverse f f' a hf y) = y) (nhds (f a)) :=
  local_homeomorph.eventually_right_inverse' (to_local_homeomorph f hf) (mem_to_local_homeomorph_source hf)

theorem local_inverse_continuous_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : continuous_at (local_inverse f f' a hf) (f a) :=
  local_homeomorph.continuous_at_symm (to_local_homeomorph f hf) (image_mem_to_local_homeomorph_target hf)

theorem local_inverse_tendsto {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : filter.tendsto (local_inverse f f' a hf) (nhds (f a)) (nhds a) :=
  local_homeomorph.tendsto_symm (to_local_homeomorph f hf) (mem_to_local_homeomorph_source hf)

theorem local_inverse_unique {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) {g : F → E} (hg : filter.eventually (fun (x : E) => g (f x) = x) (nhds a)) : filter.eventually (fun (y : F) => g y = local_inverse f f' a hf y) (nhds (f a)) :=
  filter.eventually_eq_of_left_inv_of_right_inv hg (eventually_right_inverse hf)
    (local_homeomorph.tendsto_symm (to_local_homeomorph f hf) (mem_to_local_homeomorph_source hf))

/-- If `f` has an invertible derivative `f'` at `a` in the sense of strict differentiability `(hf)`,
then the inverse function `hf.local_inverse f` has derivative `f'.symm` at `f a`. -/
theorem to_local_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) : has_strict_fderiv_at (local_inverse f f' a hf) (↑(continuous_linear_equiv.symm f')) (f a) := sorry

/-- If `f : E → F` has an invertible derivative `f'` at `a` in the sense of strict differentiability
and `g (f x) = x` in a neighborhood of `a`, then `g` has derivative `f'.symm` at `f a`.

For a version assuming `f (g y) = y` and continuity of `g` at `f a` but not `[complete_space E]`
see `of_local_left_inverse`.  -/
theorem to_local_left_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [cs : complete_space E] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {a : E} (hf : has_strict_fderiv_at f (↑f') a) {g : F → E} (hg : filter.eventually (fun (x : E) => g (f x) = x) (nhds a)) : has_strict_fderiv_at g (↑(continuous_linear_equiv.symm f')) (f a) :=
  congr_of_eventually_eq (to_local_inverse hf)
    (filter.eventually.mono (local_inverse_unique hf hg) fun (_x : F) => Eq.symm)

end has_strict_fderiv_at


/-- If a function has an invertible strict derivative at all points, then it is an open map. -/
theorem open_map_of_strict_fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space E] {f : E → F} {f' : E → continuous_linear_equiv 𝕜 E F} (hf : ∀ (x : E), has_strict_fderiv_at f (↑(f' x)) x) : is_open_map f :=
  iff.mpr is_open_map_iff_nhds_le fun (x : E) => eq.ge (has_strict_fderiv_at.map_nhds_eq (hf x))

/-!
### Inverse function theorem, 1D case

In this case we prove a version of the inverse function theorem for maps `f : 𝕜 → 𝕜`.
We use `continuous_linear_equiv.units_equiv_aut` to translate `has_strict_deriv_at f f' a` and
`f' ≠ 0` into `has_strict_fderiv_at f (_ : 𝕜 ≃L[𝕜] 𝕜) a`.
-/

namespace has_strict_deriv_at


/-- A function that is inverse to `f` near `a`. -/
def local_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] [cs : complete_space 𝕜] (f : 𝕜 → 𝕜) (f' : 𝕜) (a : 𝕜) (hf : has_strict_deriv_at f f' a) (hf' : f' ≠ 0) : 𝕜 → 𝕜 :=
  has_strict_fderiv_at.local_inverse f (coe_fn (continuous_linear_equiv.units_equiv_aut 𝕜) (units.mk0 f' hf')) a
    (has_strict_fderiv_at_equiv hf hf')

theorem map_nhds_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] [cs : complete_space 𝕜] {f : 𝕜 → 𝕜} {f' : 𝕜} {a : 𝕜} (hf : has_strict_deriv_at f f' a) (hf' : f' ≠ 0) : filter.map f (nhds a) = nhds (f a) :=
  has_strict_fderiv_at.map_nhds_eq (has_strict_fderiv_at_equiv hf hf')

theorem to_local_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] [cs : complete_space 𝕜] {f : 𝕜 → 𝕜} {f' : 𝕜} {a : 𝕜} (hf : has_strict_deriv_at f f' a) (hf' : f' ≠ 0) : has_strict_deriv_at (local_inverse f f' a hf hf') (f'⁻¹) (f a) :=
  has_strict_fderiv_at.to_local_inverse (has_strict_fderiv_at_equiv hf hf')

theorem to_local_left_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] [cs : complete_space 𝕜] {f : 𝕜 → 𝕜} {f' : 𝕜} {a : 𝕜} (hf : has_strict_deriv_at f f' a) (hf' : f' ≠ 0) {g : 𝕜 → 𝕜} (hg : filter.eventually (fun (x : 𝕜) => g (f x) = x) (nhds a)) : has_strict_deriv_at g (f'⁻¹) (f a) :=
  has_strict_fderiv_at.to_local_left_inverse (has_strict_fderiv_at_equiv hf hf') hg

end has_strict_deriv_at


/-- If a function has a non-zero strict derivative at all points, then it is an open map. -/
theorem open_map_of_strict_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] [complete_space 𝕜] {f : 𝕜 → 𝕜} {f' : 𝕜 → 𝕜} (hf : ∀ (x : 𝕜), has_strict_deriv_at f (f' x) x) (h0 : ∀ (x : 𝕜), f' x ≠ 0) : is_open_map f :=
  iff.mpr is_open_map_iff_nhds_le fun (x : 𝕜) => eq.ge (has_strict_deriv_at.map_nhds_eq (hf x) (h0 x))

/-!
### Inverse function theorem, smooth case

-/

namespace times_cont_diff_at


/-- Given a `times_cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `a`, returns a `local_homeomorph` with `to_fun = f` and `a ∈ source`. -/
def to_local_homeomorph {𝕂 : Type u_6} [is_R_or_C 𝕂] {E' : Type u_7} [normed_group E'] [normed_space 𝕂 E'] {F' : Type u_8} [normed_group F'] [normed_space 𝕂 F'] [complete_space E'] (f : E' → F') {f' : continuous_linear_equiv 𝕂 E' F'} {a : E'} {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (↑f') a) (hn : 1 ≤ n) : local_homeomorph E' F' :=
  has_strict_fderiv_at.to_local_homeomorph f sorry

@[simp] theorem to_local_homeomorph_coe {𝕂 : Type u_6} [is_R_or_C 𝕂] {E' : Type u_7} [normed_group E'] [normed_space 𝕂 E'] {F' : Type u_8} [normed_group F'] [normed_space 𝕂 F'] [complete_space E'] {f : E' → F'} {f' : continuous_linear_equiv 𝕂 E' F'} {a : E'} {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (↑f') a) (hn : 1 ≤ n) : ⇑(to_local_homeomorph f hf hf' hn) = f :=
  rfl

theorem mem_to_local_homeomorph_source {𝕂 : Type u_6} [is_R_or_C 𝕂] {E' : Type u_7} [normed_group E'] [normed_space 𝕂 E'] {F' : Type u_8} [normed_group F'] [normed_space 𝕂 F'] [complete_space E'] {f : E' → F'} {f' : continuous_linear_equiv 𝕂 E' F'} {a : E'} {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (↑f') a) (hn : 1 ≤ n) : a ∈ local_equiv.source (local_homeomorph.to_local_equiv (to_local_homeomorph f hf hf' hn)) :=
  has_strict_fderiv_at.mem_to_local_homeomorph_source (has_strict_fderiv_at' hf hf' hn)

theorem image_mem_to_local_homeomorph_target {𝕂 : Type u_6} [is_R_or_C 𝕂] {E' : Type u_7} [normed_group E'] [normed_space 𝕂 E'] {F' : Type u_8} [normed_group F'] [normed_space 𝕂 F'] [complete_space E'] {f : E' → F'} {f' : continuous_linear_equiv 𝕂 E' F'} {a : E'} {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (↑f') a) (hn : 1 ≤ n) : f a ∈ local_equiv.target (local_homeomorph.to_local_equiv (to_local_homeomorph f hf hf' hn)) :=
  has_strict_fderiv_at.image_mem_to_local_homeomorph_target (has_strict_fderiv_at' hf hf' hn)

/-- Given a `times_cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, returns a function that is locally inverse to `f`. -/
def local_inverse {𝕂 : Type u_6} [is_R_or_C 𝕂] {E' : Type u_7} [normed_group E'] [normed_space 𝕂 E'] {F' : Type u_8} [normed_group F'] [normed_space 𝕂 F'] [complete_space E'] {f : E' → F'} {f' : continuous_linear_equiv 𝕂 E' F'} {a : E'} {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (↑f') a) (hn : 1 ≤ n) : F' → E' :=
  has_strict_fderiv_at.local_inverse f f' a sorry

theorem local_inverse_apply_image {𝕂 : Type u_6} [is_R_or_C 𝕂] {E' : Type u_7} [normed_group E'] [normed_space 𝕂 E'] {F' : Type u_8} [normed_group F'] [normed_space 𝕂 F'] [complete_space E'] {f : E' → F'} {f' : continuous_linear_equiv 𝕂 E' F'} {a : E'} {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (↑f') a) (hn : 1 ≤ n) : local_inverse hf hf' hn (f a) = a :=
  has_strict_fderiv_at.local_inverse_apply_image (has_strict_fderiv_at' hf hf' hn)

/-- Given a `times_cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, the inverse function (produced by `times_cont_diff.to_local_homeomorph`) is
also `times_cont_diff`. -/
theorem to_local_inverse {𝕂 : Type u_6} [is_R_or_C 𝕂] {E' : Type u_7} [normed_group E'] [normed_space 𝕂 E'] {F' : Type u_8} [normed_group F'] [normed_space 𝕂 F'] [complete_space E'] {f : E' → F'} {f' : continuous_linear_equiv 𝕂 E' F'} {a : E'} {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (↑f') a) (hn : 1 ≤ n) : times_cont_diff_at 𝕂 n (local_inverse hf hf' hn) (f a) := sorry

