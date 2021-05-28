/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.calculus.fderiv
import Mathlib.data.polynomial.derivative
import Mathlib.PostPort

universes u v u_1 w 

namespace Mathlib

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.lean). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

 - `has_deriv_at_filter f f' x L` states that the function `f` has the
    derivative `f'` at the point `x` as `x` goes along the filter `L`.

 - `has_deriv_within_at f f' s x` states that the function `f` has the
    derivative `f'` at the point `x` within the subset `s`.

 - `has_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x`.

 - `has_strict_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x` in the sense of strict differentiability, i.e.,
   `f y - f z = (y - z) • f' + o (y - z)` as `y, z → x`.

For the last two notions we also define a functional version:

  - `deriv_within f s x` is a derivative of `f` at `x` within `s`. If the
    derivative does not exist, then `deriv_within f s x` equals zero.

  - `deriv f x` is a derivative of `f` at `x`. If the derivative does not
    exist, then `deriv f x` equals zero.

The theorems `fderiv_within_deriv_within` and `fderiv_deriv` show that the
one-dimensional derivatives coincide with the general Fréchet derivatives.

We also show the existence and compute the derivatives of:
  - constants
  - the identity function
  - linear maps
  - addition
  - sum of finitely many functions
  - negation
  - subtraction
  - multiplication
  - inverse `x → x⁻¹`
  - multiplication of two functions in `𝕜 → 𝕜`
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E`
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜`
  - composition of a function in `F → E` with a function in `𝕜 → F`
  - inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)
  - division
  - polynomials

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `has_deriv_at`'s easier,
and they more frequently lead to the desired result.

We set up the simplifier so that it can compute the derivative of simple functions. For instance,
```lean
example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }
```

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

The strategy to construct simp lemmas that give the simplifier the possibility to compute
derivatives is the same as the one for differentiability statements, as explained in `fderiv.lean`.
See the explanations there.
-/

/--
`f` has the derivative `f'` at the point `x` as `x` goes along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges along the filter `L`.
-/
def has_deriv_at_filter {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (f : 𝕜 → F) (f' : F) (x : 𝕜) (L : filter 𝕜)  :=
  has_fderiv_at_filter f (continuous_linear_map.smul_right 1 f') x L

/--
`f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (f : 𝕜 → F) (f' : F) (s : set 𝕜) (x : 𝕜)  :=
  has_deriv_at_filter f f' x (nhds_within x s)

/--
`f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def has_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (f : 𝕜 → F) (f' : F) (x : 𝕜)  :=
  has_deriv_at_filter f f' x (nhds x)

/-- `f` has the derivative `f'` at the point `x` in the sense of strict differentiability.

That is, `f y - f z = (y - z) • f' + o(y - z)` as `y, z → x`. -/
def has_strict_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (f : 𝕜 → F) (f' : F) (x : 𝕜)  :=
  has_strict_fderiv_at f (continuous_linear_map.smul_right 1 f') x

/--
Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_within_at f f' s x`), then
`f x' = f x + (x' - x) • deriv_within f s x + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def deriv_within {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (f : 𝕜 → F) (s : set 𝕜) (x : 𝕜) : F :=
  coe_fn (fderiv_within 𝕜 f s x) 1

/--
Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_at f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
def deriv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (f : 𝕜 → F) (x : 𝕜) : F :=
  coe_fn (fderiv 𝕜 f x) 1

/-- Expressing `has_fderiv_at_filter f f' x L` in terms of `has_deriv_at_filter` -/
theorem has_fderiv_at_filter_iff_has_deriv_at_filter {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {L : filter 𝕜} {f' : continuous_linear_map 𝕜 𝕜 F} : has_fderiv_at_filter f f' x L ↔ has_deriv_at_filter f (coe_fn f' 1) x L := sorry

theorem has_fderiv_at_filter.has_deriv_at_filter {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {L : filter 𝕜} {f' : continuous_linear_map 𝕜 𝕜 F} : has_fderiv_at_filter f f' x L → has_deriv_at_filter f (coe_fn f' 1) x L :=
  iff.mp has_fderiv_at_filter_iff_has_deriv_at_filter

/-- Expressing `has_fderiv_within_at f f' s x` in terms of `has_deriv_within_at` -/
theorem has_fderiv_within_at_iff_has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} {f' : continuous_linear_map 𝕜 𝕜 F} : has_fderiv_within_at f f' s x ↔ has_deriv_within_at f (coe_fn f' 1) s x :=
  has_fderiv_at_filter_iff_has_deriv_at_filter

/-- Expressing `has_deriv_within_at f f' s x` in terms of `has_fderiv_within_at` -/
theorem has_deriv_within_at_iff_has_fderiv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} {f' : F} : has_deriv_within_at f f' s x ↔ has_fderiv_within_at f (continuous_linear_map.smul_right 1 f') s x :=
  iff.rfl

theorem has_fderiv_within_at.has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} {f' : continuous_linear_map 𝕜 𝕜 F} : has_fderiv_within_at f f' s x → has_deriv_within_at f (coe_fn f' 1) s x :=
  iff.mp has_fderiv_within_at_iff_has_deriv_within_at

theorem has_deriv_within_at.has_fderiv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} {f' : F} : has_deriv_within_at f f' s x → has_fderiv_within_at f (continuous_linear_map.smul_right 1 f') s x :=
  iff.mp has_deriv_within_at_iff_has_fderiv_within_at

/-- Expressing `has_fderiv_at f f' x` in terms of `has_deriv_at` -/
theorem has_fderiv_at_iff_has_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {f' : continuous_linear_map 𝕜 𝕜 F} : has_fderiv_at f f' x ↔ has_deriv_at f (coe_fn f' 1) x :=
  has_fderiv_at_filter_iff_has_deriv_at_filter

theorem has_fderiv_at.has_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {f' : continuous_linear_map 𝕜 𝕜 F} : has_fderiv_at f f' x → has_deriv_at f (coe_fn f' 1) x :=
  iff.mp has_fderiv_at_iff_has_deriv_at

theorem has_strict_fderiv_at_iff_has_strict_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {f' : continuous_linear_map 𝕜 𝕜 F} : has_strict_fderiv_at f f' x ↔ has_strict_deriv_at f (coe_fn f' 1) x := sorry

protected theorem has_strict_fderiv_at.has_strict_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {f' : continuous_linear_map 𝕜 𝕜 F} : has_strict_fderiv_at f f' x → has_strict_deriv_at f (coe_fn f' 1) x :=
  iff.mp has_strict_fderiv_at_iff_has_strict_deriv_at

/-- Expressing `has_deriv_at f f' x` in terms of `has_fderiv_at` -/
theorem has_deriv_at_iff_has_fderiv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {f' : F} : has_deriv_at f f' x ↔ has_fderiv_at f (continuous_linear_map.smul_right 1 f') x :=
  iff.rfl

theorem deriv_within_zero_of_not_differentiable_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (h : ¬differentiable_within_at 𝕜 f s x) : deriv_within f s x = 0 := sorry

theorem deriv_zero_of_not_differentiable_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} (h : ¬differentiable_at 𝕜 f x) : deriv f x = 0 := sorry

theorem unique_diff_within_at.eq_deriv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {f₁' : F} {x : 𝕜} (s : set 𝕜) (H : unique_diff_within_at 𝕜 s x) (h : has_deriv_within_at f f' s x) (h₁ : has_deriv_within_at f f₁' s x) : f' = f₁' :=
  iff.mp continuous_linear_map.smul_right_one_eq_iff (unique_diff_within_at.eq H h h₁)

theorem has_deriv_at_filter_iff_tendsto {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {L : filter 𝕜} : has_deriv_at_filter f f' x L ↔
  filter.tendsto (fun (x' : 𝕜) => norm (x' - x)⁻¹ * norm (f x' - f x - (x' - x) • f')) L (nhds 0) :=
  has_fderiv_at_filter_iff_tendsto

theorem has_deriv_within_at_iff_tendsto {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} : has_deriv_within_at f f' s x ↔
  filter.tendsto (fun (x' : 𝕜) => norm (x' - x)⁻¹ * norm (f x' - f x - (x' - x) • f')) (nhds_within x s) (nhds 0) :=
  has_fderiv_at_filter_iff_tendsto

theorem has_deriv_at_iff_tendsto {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} : has_deriv_at f f' x ↔
  filter.tendsto (fun (x' : 𝕜) => norm (x' - x)⁻¹ * norm (f x' - f x - (x' - x) • f')) (nhds x) (nhds 0) :=
  has_fderiv_at_filter_iff_tendsto

theorem has_strict_deriv_at.has_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (h : has_strict_deriv_at f f' x) : has_deriv_at f f' x :=
  has_strict_fderiv_at.has_fderiv_at h

/-- If the domain has dimension one, then Fréchet derivative is equivalent to the classical
definition with a limit. In this version we have to take the limit along the subset `-{x}`,
because for `y=x` the slope equals zero due to the convention `0⁻¹=0`. -/
theorem has_deriv_at_filter_iff_tendsto_slope {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {L : filter 𝕜} : has_deriv_at_filter f f' x L ↔
  filter.tendsto (fun (y : 𝕜) => y - x⁻¹ • (f y - f x)) (L ⊓ filter.principal (singleton xᶜ)) (nhds f') := sorry

theorem has_deriv_within_at_iff_tendsto_slope {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} : has_deriv_within_at f f' s x ↔
  filter.tendsto (fun (y : 𝕜) => y - x⁻¹ • (f y - f x)) (nhds_within x (s \ singleton x)) (nhds f') := sorry

theorem has_deriv_within_at_iff_tendsto_slope' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (hs : ¬x ∈ s) : has_deriv_within_at f f' s x ↔ filter.tendsto (fun (y : 𝕜) => y - x⁻¹ • (f y - f x)) (nhds_within x s) (nhds f') := sorry

theorem has_deriv_at_iff_tendsto_slope {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} : has_deriv_at f f' x ↔ filter.tendsto (fun (y : 𝕜) => y - x⁻¹ • (f y - f x)) (nhds_within x (singleton xᶜ)) (nhds f') :=
  has_deriv_at_filter_iff_tendsto_slope

@[simp] theorem has_deriv_within_at_diff_singleton {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} : has_deriv_within_at f f' (s \ singleton x) x ↔ has_deriv_within_at f f' s x := sorry

@[simp] theorem has_deriv_within_at_Ioi_iff_Ici {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} [partial_order 𝕜] : has_deriv_within_at f f' (set.Ioi x) x ↔ has_deriv_within_at f f' (set.Ici x) x := sorry

theorem has_deriv_within_at.Ioi_of_Ici {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} [partial_order 𝕜] : has_deriv_within_at f f' (set.Ici x) x → has_deriv_within_at f f' (set.Ioi x) x :=
  iff.mpr has_deriv_within_at_Ioi_iff_Ici

@[simp] theorem has_deriv_within_at_Iio_iff_Iic {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} [partial_order 𝕜] : has_deriv_within_at f f' (set.Iio x) x ↔ has_deriv_within_at f f' (set.Iic x) x := sorry

theorem has_deriv_within_at.Iio_of_Iic {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} [partial_order 𝕜] : has_deriv_within_at f f' (set.Iic x) x → has_deriv_within_at f f' (set.Iio x) x :=
  iff.mpr has_deriv_within_at_Iio_iff_Iic

theorem has_deriv_at_iff_is_o_nhds_zero {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} : has_deriv_at f f' x ↔ asymptotics.is_o (fun (h : 𝕜) => f (x + h) - f x - h • f') (fun (h : 𝕜) => h) (nhds 0) :=
  has_fderiv_at_iff_is_o_nhds_zero

theorem has_deriv_at_filter.mono {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {L₁ : filter 𝕜} {L₂ : filter 𝕜} (h : has_deriv_at_filter f f' x L₂) (hst : L₁ ≤ L₂) : has_deriv_at_filter f f' x L₁ :=
  has_fderiv_at_filter.mono h hst

theorem has_deriv_within_at.mono {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} {t : set 𝕜} (h : has_deriv_within_at f f' t x) (hst : s ⊆ t) : has_deriv_within_at f f' s x :=
  has_fderiv_within_at.mono h hst

theorem has_deriv_at.has_deriv_at_filter {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {L : filter 𝕜} (h : has_deriv_at f f' x) (hL : L ≤ nhds x) : has_deriv_at_filter f f' x L :=
  has_fderiv_at.has_fderiv_at_filter h hL

theorem has_deriv_at.has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (h : has_deriv_at f f' x) : has_deriv_within_at f f' s x :=
  has_fderiv_at.has_fderiv_within_at h

theorem has_deriv_within_at.differentiable_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (h : has_deriv_within_at f f' s x) : differentiable_within_at 𝕜 f s x :=
  has_fderiv_within_at.differentiable_within_at h

theorem has_deriv_at.differentiable_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (h : has_deriv_at f f' x) : differentiable_at 𝕜 f x :=
  has_fderiv_at.differentiable_at h

@[simp] theorem has_deriv_within_at_univ {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} : has_deriv_within_at f f' set.univ x ↔ has_deriv_at f f' x :=
  has_fderiv_within_at_univ

theorem has_deriv_at_unique {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f₀' : F} {f₁' : F} {x : 𝕜} (h₀ : has_deriv_at f f₀' x) (h₁ : has_deriv_at f f₁' x) : f₀' = f₁' :=
  iff.mp continuous_linear_map.smul_right_one_eq_iff (has_fderiv_at_unique h₀ h₁)

theorem has_deriv_within_at_inter' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} {t : set 𝕜} (h : t ∈ nhds_within x s) : has_deriv_within_at f f' (s ∩ t) x ↔ has_deriv_within_at f f' s x :=
  has_fderiv_within_at_inter' h

theorem has_deriv_within_at_inter {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} {t : set 𝕜} (h : t ∈ nhds x) : has_deriv_within_at f f' (s ∩ t) x ↔ has_deriv_within_at f f' s x :=
  has_fderiv_within_at_inter h

theorem has_deriv_within_at.union {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} {t : set 𝕜} (hs : has_deriv_within_at f f' s x) (ht : has_deriv_within_at f f' t x) : has_deriv_within_at f f' (s ∪ t) x := sorry

theorem has_deriv_within_at.nhds_within {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} {t : set 𝕜} (h : has_deriv_within_at f f' s x) (ht : s ∈ nhds_within x t) : has_deriv_within_at f f' t x :=
  iff.mp (has_deriv_within_at_inter' ht) (has_deriv_within_at.mono h (set.inter_subset_right t s))

theorem has_deriv_within_at.has_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (h : has_deriv_within_at f f' s x) (hs : s ∈ nhds x) : has_deriv_at f f' x :=
  has_fderiv_within_at.has_fderiv_at h hs

theorem differentiable_within_at.has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (h : differentiable_within_at 𝕜 f s x) : has_deriv_within_at f (deriv_within f s x) s x := sorry

theorem differentiable_at.has_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} (h : differentiable_at 𝕜 f x) : has_deriv_at f (deriv f x) x := sorry

theorem has_deriv_at.deriv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (h : has_deriv_at f f' x) : deriv f x = f' :=
  has_deriv_at_unique (differentiable_at.has_deriv_at (has_deriv_at.differentiable_at h)) h

theorem has_deriv_within_at.deriv_within {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (h : has_deriv_within_at f f' s x) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within f s x = f' :=
  unique_diff_within_at.eq_deriv s hxs
    (differentiable_within_at.has_deriv_within_at (has_deriv_within_at.differentiable_within_at h)) h

theorem fderiv_within_deriv_within {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} : coe_fn (fderiv_within 𝕜 f s x) 1 = deriv_within f s x :=
  rfl

theorem deriv_within_fderiv_within {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} : continuous_linear_map.smul_right 1 (deriv_within f s x) = fderiv_within 𝕜 f s x := sorry

theorem fderiv_deriv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} : coe_fn (fderiv 𝕜 f x) 1 = deriv f x :=
  rfl

theorem deriv_fderiv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} : continuous_linear_map.smul_right 1 (deriv f x) = fderiv 𝕜 f x := sorry

theorem differentiable_at.deriv_within {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (h : differentiable_at 𝕜 f x) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within f s x = deriv f x := sorry

theorem deriv_within_subset {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} {t : set 𝕜} (st : s ⊆ t) (ht : unique_diff_within_at 𝕜 s x) (h : differentiable_within_at 𝕜 f t x) : deriv_within f s x = deriv_within f t x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.mono (differentiable_within_at.has_deriv_within_at h) st) ht

@[simp] theorem deriv_within_univ {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} : deriv_within f set.univ = deriv f := sorry

theorem deriv_within_inter {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} {t : set 𝕜} (ht : t ∈ nhds x) (hs : unique_diff_within_at 𝕜 s x) : deriv_within f (s ∩ t) x = deriv_within f s x := sorry

theorem deriv_within_of_open {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (hs : is_open s) (hx : x ∈ s) : deriv_within f s x = deriv f x := sorry

/-! ### Congruence properties of derivatives -/

theorem filter.eventually_eq.has_deriv_at_filter_iff {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f₀ : 𝕜 → F} {f₁ : 𝕜 → F} {f₀' : F} {f₁' : F} {x : 𝕜} {L : filter 𝕜} (h₀ : filter.eventually_eq L f₀ f₁) (hx : f₀ x = f₁ x) (h₁ : f₀' = f₁') : has_deriv_at_filter f₀ f₀' x L ↔ has_deriv_at_filter f₁ f₁' x L := sorry

theorem has_deriv_at_filter.congr_of_eventually_eq {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {f' : F} {x : 𝕜} {L : filter 𝕜} (h : has_deriv_at_filter f f' x L) (hL : filter.eventually_eq L f₁ f) (hx : f₁ x = f x) : has_deriv_at_filter f₁ f' x L := sorry

theorem has_deriv_within_at.congr_mono {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} {t : set 𝕜} (h : has_deriv_within_at f f' s x) (ht : ∀ (x : 𝕜), x ∈ t → f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) : has_deriv_within_at f₁ f' t x :=
  has_fderiv_within_at.congr_mono h ht hx h₁

theorem has_deriv_within_at.congr {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (h : has_deriv_within_at f f' s x) (hs : ∀ (x : 𝕜), x ∈ s → f₁ x = f x) (hx : f₁ x = f x) : has_deriv_within_at f₁ f' s x :=
  has_deriv_within_at.congr_mono h hs hx (set.subset.refl s)

theorem has_deriv_within_at.congr_of_eventually_eq {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (h : has_deriv_within_at f f' s x) (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) : has_deriv_within_at f₁ f' s x :=
  has_deriv_at_filter.congr_of_eventually_eq h h₁ hx

theorem has_deriv_within_at.congr_of_eventually_eq_of_mem {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (h : has_deriv_within_at f f' s x) (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : x ∈ s) : has_deriv_within_at f₁ f' s x :=
  has_deriv_within_at.congr_of_eventually_eq h h₁ (filter.eventually_eq.eq_of_nhds_within h₁ hx)

theorem has_deriv_at.congr_of_eventually_eq {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {f' : F} {x : 𝕜} (h : has_deriv_at f f' x) (h₁ : filter.eventually_eq (nhds x) f₁ f) : has_deriv_at f₁ f' x :=
  has_deriv_at_filter.congr_of_eventually_eq h h₁ (mem_of_nhds h₁)

theorem filter.eventually_eq.deriv_within_eq {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (hs : unique_diff_within_at 𝕜 s x) (hL : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) : deriv_within f₁ s x = deriv_within f s x := sorry

theorem deriv_within_congr {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (hs : unique_diff_within_at 𝕜 s x) (hL : ∀ (y : 𝕜), y ∈ s → f₁ y = f y) (hx : f₁ x = f x) : deriv_within f₁ s x = deriv_within f s x := sorry

theorem filter.eventually_eq.deriv_eq {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {x : 𝕜} (hL : filter.eventually_eq (nhds x) f₁ f) : deriv f₁ x = deriv f x := sorry

/-! ### Derivative of the identity -/

theorem has_deriv_at_filter_id {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) (L : filter 𝕜) : has_deriv_at_filter id 1 x L :=
  has_fderiv_at_filter.has_deriv_at_filter (has_fderiv_at_filter_id x L)

theorem has_deriv_within_at_id {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) (s : set 𝕜) : has_deriv_within_at id 1 s x :=
  has_deriv_at_filter_id x (nhds_within x s)

theorem has_deriv_at_id {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) : has_deriv_at id 1 x :=
  has_deriv_at_filter_id x (nhds x)

theorem has_deriv_at_id' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) : has_deriv_at (fun (x : 𝕜) => x) 1 x :=
  has_deriv_at_filter_id x (nhds x)

theorem has_strict_deriv_at_id {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) : has_strict_deriv_at id 1 x :=
  has_strict_fderiv_at.has_strict_deriv_at (has_strict_fderiv_at_id x)

theorem deriv_id {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) : deriv id x = 1 :=
  has_deriv_at.deriv (has_deriv_at_id x)

@[simp] theorem deriv_id' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] : deriv id = fun (_x : 𝕜) => 1 :=
  funext deriv_id

@[simp] theorem deriv_id'' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) : deriv (fun (x : 𝕜) => x) x = 1 :=
  deriv_id x

theorem deriv_within_id {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) (s : set 𝕜) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within id s x = 1 :=
  has_deriv_within_at.deriv_within (has_deriv_within_at_id x s) hxs

/-! ### Derivative of constant functions -/

theorem has_deriv_at_filter_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (x : 𝕜) (L : filter 𝕜) (c : F) : has_deriv_at_filter (fun (x : 𝕜) => c) 0 x L :=
  has_fderiv_at_filter.has_deriv_at_filter (has_fderiv_at_filter_const c x L)

theorem has_strict_deriv_at_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (x : 𝕜) (c : F) : has_strict_deriv_at (fun (x : 𝕜) => c) 0 x :=
  has_strict_fderiv_at.has_strict_deriv_at (has_strict_fderiv_at_const c x)

theorem has_deriv_within_at_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (x : 𝕜) (s : set 𝕜) (c : F) : has_deriv_within_at (fun (x : 𝕜) => c) 0 s x :=
  has_deriv_at_filter_const x (nhds_within x s) c

theorem has_deriv_at_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (x : 𝕜) (c : F) : has_deriv_at (fun (x : 𝕜) => c) 0 x :=
  has_deriv_at_filter_const x (nhds x) c

theorem deriv_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (x : 𝕜) (c : F) : deriv (fun (x : 𝕜) => c) x = 0 :=
  has_deriv_at.deriv (has_deriv_at_const x c)

@[simp] theorem deriv_const' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (c : F) : (deriv fun (x : 𝕜) => c) = fun (x : 𝕜) => 0 :=
  funext fun (x : 𝕜) => deriv_const x c

theorem deriv_within_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] (x : 𝕜) (s : set 𝕜) (c : F) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (fun (x : 𝕜) => c) s x = 0 :=
  has_deriv_within_at.deriv_within (has_deriv_within_at_const x s c) hxs

/-! ### Derivative of continuous linear maps -/

theorem continuous_linear_map.has_deriv_at_filter {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {L : filter 𝕜} (e : continuous_linear_map 𝕜 𝕜 F) : has_deriv_at_filter (⇑e) (coe_fn e 1) x L :=
  has_fderiv_at_filter.has_deriv_at_filter (continuous_linear_map.has_fderiv_at_filter e)

theorem continuous_linear_map.has_strict_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} (e : continuous_linear_map 𝕜 𝕜 F) : has_strict_deriv_at (⇑e) (coe_fn e 1) x :=
  has_strict_fderiv_at.has_strict_deriv_at (continuous_linear_map.has_strict_fderiv_at e)

theorem continuous_linear_map.has_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} (e : continuous_linear_map 𝕜 𝕜 F) : has_deriv_at (⇑e) (coe_fn e 1) x :=
  continuous_linear_map.has_deriv_at_filter e

theorem continuous_linear_map.has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {s : set 𝕜} (e : continuous_linear_map 𝕜 𝕜 F) : has_deriv_within_at (⇑e) (coe_fn e 1) s x :=
  continuous_linear_map.has_deriv_at_filter e

@[simp] theorem continuous_linear_map.deriv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} (e : continuous_linear_map 𝕜 𝕜 F) : deriv (⇑e) x = coe_fn e 1 :=
  has_deriv_at.deriv (continuous_linear_map.has_deriv_at e)

theorem continuous_linear_map.deriv_within {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {s : set 𝕜} (e : continuous_linear_map 𝕜 𝕜 F) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (⇑e) s x = coe_fn e 1 :=
  has_deriv_within_at.deriv_within (continuous_linear_map.has_deriv_within_at e) hxs

/-! ### Derivative of bundled linear maps -/

theorem linear_map.has_deriv_at_filter {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {L : filter 𝕜} (e : linear_map 𝕜 𝕜 F) : has_deriv_at_filter (⇑e) (coe_fn e 1) x L :=
  continuous_linear_map.has_deriv_at_filter (linear_map.to_continuous_linear_map₁ e)

theorem linear_map.has_strict_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} (e : linear_map 𝕜 𝕜 F) : has_strict_deriv_at (⇑e) (coe_fn e 1) x :=
  continuous_linear_map.has_strict_deriv_at (linear_map.to_continuous_linear_map₁ e)

theorem linear_map.has_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} (e : linear_map 𝕜 𝕜 F) : has_deriv_at (⇑e) (coe_fn e 1) x :=
  linear_map.has_deriv_at_filter e

theorem linear_map.has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {s : set 𝕜} (e : linear_map 𝕜 𝕜 F) : has_deriv_within_at (⇑e) (coe_fn e 1) s x :=
  linear_map.has_deriv_at_filter e

@[simp] theorem linear_map.deriv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} (e : linear_map 𝕜 𝕜 F) : deriv (⇑e) x = coe_fn e 1 :=
  has_deriv_at.deriv (linear_map.has_deriv_at e)

theorem linear_map.deriv_within {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {s : set 𝕜} (e : linear_map 𝕜 𝕜 F) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (⇑e) s x = coe_fn e 1 :=
  has_deriv_within_at.deriv_within (linear_map.has_deriv_within_at e) hxs

theorem has_fpower_series_at.has_strict_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {p : formal_multilinear_series 𝕜 𝕜 F} (h : has_fpower_series_at f p x) : has_strict_deriv_at f (coe_fn (p 1) fun (_x : fin 1) => 1) x :=
  has_strict_fderiv_at.has_strict_deriv_at (has_fpower_series_at.has_strict_fderiv_at h)

theorem has_fpower_series_at.has_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {p : formal_multilinear_series 𝕜 𝕜 F} (h : has_fpower_series_at f p x) : has_deriv_at f (coe_fn (p 1) fun (_x : fin 1) => 1) x :=
  has_strict_deriv_at.has_deriv_at (has_fpower_series_at.has_strict_deriv_at h)

theorem has_fpower_series_at.deriv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {p : formal_multilinear_series 𝕜 𝕜 F} (h : has_fpower_series_at f p x) : deriv f x = coe_fn (p 1) fun (_x : fin 1) => 1 :=
  has_deriv_at.deriv (has_fpower_series_at.has_deriv_at h)

/-! ### Derivative of the sum of two functions -/

theorem has_deriv_at_filter.add {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {f' : F} {g' : F} {x : 𝕜} {L : filter 𝕜} (hf : has_deriv_at_filter f f' x L) (hg : has_deriv_at_filter g g' x L) : has_deriv_at_filter (fun (y : 𝕜) => f y + g y) (f' + g') x L := sorry

theorem has_strict_deriv_at.add {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {f' : F} {g' : F} {x : 𝕜} (hf : has_strict_deriv_at f f' x) (hg : has_strict_deriv_at g g' x) : has_strict_deriv_at (fun (y : 𝕜) => f y + g y) (f' + g') x := sorry

theorem has_deriv_within_at.add {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {f' : F} {g' : F} {x : 𝕜} {s : set 𝕜} (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) : has_deriv_within_at (fun (y : 𝕜) => f y + g y) (f' + g') s x :=
  has_deriv_at_filter.add hf hg

theorem has_deriv_at.add {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {f' : F} {g' : F} {x : 𝕜} (hf : has_deriv_at f f' x) (hg : has_deriv_at g g' x) : has_deriv_at (fun (x : 𝕜) => f x + g x) (f' + g') x :=
  has_deriv_at_filter.add hf hg

theorem deriv_within_add {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) : deriv_within (fun (y : 𝕜) => f y + g y) s x = deriv_within f s x + deriv_within g s x := sorry

@[simp] theorem deriv_add {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {x : 𝕜} (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) : deriv (fun (y : 𝕜) => f y + g y) x = deriv f x + deriv g x :=
  has_deriv_at.deriv (has_deriv_at.add (differentiable_at.has_deriv_at hf) (differentiable_at.has_deriv_at hg))

theorem has_deriv_at_filter.add_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {L : filter 𝕜} (hf : has_deriv_at_filter f f' x L) (c : F) : has_deriv_at_filter (fun (y : 𝕜) => f y + c) f' x L :=
  add_zero f' ▸ has_deriv_at_filter.add hf (has_deriv_at_filter_const x L c)

theorem has_deriv_within_at.add_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (hf : has_deriv_within_at f f' s x) (c : F) : has_deriv_within_at (fun (y : 𝕜) => f y + c) f' s x :=
  has_deriv_at_filter.add_const hf c

theorem has_deriv_at.add_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (hf : has_deriv_at f f' x) (c : F) : has_deriv_at (fun (x : 𝕜) => f x + c) f' x :=
  has_deriv_at_filter.add_const hf c

theorem deriv_within_add_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (c : F) : deriv_within (fun (y : 𝕜) => f y + c) s x = deriv_within f s x := sorry

theorem deriv_add_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} (c : F) : deriv (fun (y : 𝕜) => f y + c) x = deriv f x := sorry

theorem has_deriv_at_filter.const_add {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {L : filter 𝕜} (c : F) (hf : has_deriv_at_filter f f' x L) : has_deriv_at_filter (fun (y : 𝕜) => c + f y) f' x L :=
  zero_add f' ▸ has_deriv_at_filter.add (has_deriv_at_filter_const x L c) hf

theorem has_deriv_within_at.const_add {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (c : F) (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (y : 𝕜) => c + f y) f' s x :=
  has_deriv_at_filter.const_add c hf

theorem has_deriv_at.const_add {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (c : F) (hf : has_deriv_at f f' x) : has_deriv_at (fun (x : 𝕜) => c + f x) f' x :=
  has_deriv_at_filter.const_add c hf

theorem deriv_within_const_add {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (c : F) : deriv_within (fun (y : 𝕜) => c + f y) s x = deriv_within f s x := sorry

theorem deriv_const_add {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} (c : F) : deriv (fun (y : 𝕜) => c + f y) x = deriv f x := sorry

/-! ### Derivative of a finite sum of functions -/

theorem has_deriv_at_filter.sum {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {L : filter 𝕜} {ι : Type u_1} {u : finset ι} {A : ι → 𝕜 → F} {A' : ι → F} (h : ∀ (i : ι), i ∈ u → has_deriv_at_filter (A i) (A' i) x L) : has_deriv_at_filter (fun (y : 𝕜) => finset.sum u fun (i : ι) => A i y) (finset.sum u fun (i : ι) => A' i) x L := sorry

theorem has_strict_deriv_at.sum {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {ι : Type u_1} {u : finset ι} {A : ι → 𝕜 → F} {A' : ι → F} (h : ∀ (i : ι), i ∈ u → has_strict_deriv_at (A i) (A' i) x) : has_strict_deriv_at (fun (y : 𝕜) => finset.sum u fun (i : ι) => A i y) (finset.sum u fun (i : ι) => A' i) x := sorry

theorem has_deriv_within_at.sum {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {s : set 𝕜} {ι : Type u_1} {u : finset ι} {A : ι → 𝕜 → F} {A' : ι → F} (h : ∀ (i : ι), i ∈ u → has_deriv_within_at (A i) (A' i) s x) : has_deriv_within_at (fun (y : 𝕜) => finset.sum u fun (i : ι) => A i y) (finset.sum u fun (i : ι) => A' i) s x :=
  has_deriv_at_filter.sum h

theorem has_deriv_at.sum {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {ι : Type u_1} {u : finset ι} {A : ι → 𝕜 → F} {A' : ι → F} (h : ∀ (i : ι), i ∈ u → has_deriv_at (A i) (A' i) x) : has_deriv_at (fun (y : 𝕜) => finset.sum u fun (i : ι) => A i y) (finset.sum u fun (i : ι) => A' i) x :=
  has_deriv_at_filter.sum h

theorem deriv_within_sum {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {s : set 𝕜} {ι : Type u_1} {u : finset ι} {A : ι → 𝕜 → F} (hxs : unique_diff_within_at 𝕜 s x) (h : ∀ (i : ι), i ∈ u → differentiable_within_at 𝕜 (A i) s x) : deriv_within (fun (y : 𝕜) => finset.sum u fun (i : ι) => A i y) s x = finset.sum u fun (i : ι) => deriv_within (A i) s x :=
  has_deriv_within_at.deriv_within
    (has_deriv_within_at.sum fun (i : ι) (hi : i ∈ u) => differentiable_within_at.has_deriv_within_at (h i hi)) hxs

@[simp] theorem deriv_sum {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {ι : Type u_1} {u : finset ι} {A : ι → 𝕜 → F} (h : ∀ (i : ι), i ∈ u → differentiable_at 𝕜 (A i) x) : deriv (fun (y : 𝕜) => finset.sum u fun (i : ι) => A i y) x = finset.sum u fun (i : ι) => deriv (A i) x :=
  has_deriv_at.deriv (has_deriv_at.sum fun (i : ι) (hi : i ∈ u) => differentiable_at.has_deriv_at (h i hi))

/-! ### Derivative of the multiplication of a scalar function and a vector function -/

theorem has_deriv_within_at.smul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜} (hc : has_deriv_within_at c c' s x) (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (y : 𝕜) => c y • f y) (c x • f' + c' • f x) s x := sorry

theorem has_deriv_at.smul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜} (hc : has_deriv_at c c' x) (hf : has_deriv_at f f' x) : has_deriv_at (fun (y : 𝕜) => c y • f y) (c x • f' + c' • f x) x := sorry

theorem has_strict_deriv_at.smul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜} (hc : has_strict_deriv_at c c' x) (hf : has_strict_deriv_at f f' x) : has_strict_deriv_at (fun (y : 𝕜) => c y • f y) (c x • f' + c' • f x) x := sorry

theorem deriv_within_smul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) : deriv_within (fun (y : 𝕜) => c y • f y) s x = c x • deriv_within f s x + deriv_within c s x • f x := sorry

theorem deriv_smul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) : deriv (fun (y : 𝕜) => c y • f y) x = c x • deriv f x + deriv c x • f x :=
  has_deriv_at.deriv (has_deriv_at.smul (differentiable_at.has_deriv_at hc) (differentiable_at.has_deriv_at hf))

theorem has_deriv_within_at.smul_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜} (hc : has_deriv_within_at c c' s x) (f : F) : has_deriv_within_at (fun (y : 𝕜) => c y • f) (c' • f) s x := sorry

theorem has_deriv_at.smul_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜} (hc : has_deriv_at c c' x) (f : F) : has_deriv_at (fun (y : 𝕜) => c y • f) (c' • f) x := sorry

theorem deriv_within_smul_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (hc : differentiable_within_at 𝕜 c s x) (f : F) : deriv_within (fun (y : 𝕜) => c y • f) s x = deriv_within c s x • f :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.smul_const (differentiable_within_at.has_deriv_within_at hc) f)
    hxs

theorem deriv_smul_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {x : 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_at 𝕜 c x) (f : F) : deriv (fun (y : 𝕜) => c y • f) x = deriv c x • f :=
  has_deriv_at.deriv (has_deriv_at.smul_const (differentiable_at.has_deriv_at hc) f)

theorem has_deriv_within_at.const_smul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (c : 𝕜) (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (y : 𝕜) => c • f y) (c • f') s x := sorry

theorem has_deriv_at.const_smul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (c : 𝕜) (hf : has_deriv_at f f' x) : has_deriv_at (fun (y : 𝕜) => c • f y) (c • f') x := sorry

theorem deriv_within_const_smul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (c : 𝕜) (hf : differentiable_within_at 𝕜 f s x) : deriv_within (fun (y : 𝕜) => c • f y) s x = c • deriv_within f s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.const_smul c (differentiable_within_at.has_deriv_within_at hf))
    hxs

theorem deriv_const_smul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} (c : 𝕜) (hf : differentiable_at 𝕜 f x) : deriv (fun (y : 𝕜) => c • f y) x = c • deriv f x :=
  has_deriv_at.deriv (has_deriv_at.const_smul c (differentiable_at.has_deriv_at hf))

/-! ### Derivative of the negative of a function -/

theorem has_deriv_at_filter.neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {L : filter 𝕜} (h : has_deriv_at_filter f f' x L) : has_deriv_at_filter (fun (x : 𝕜) => -f x) (-f') x L := sorry

theorem has_deriv_within_at.neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (h : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (x : 𝕜) => -f x) (-f') s x :=
  has_deriv_at_filter.neg h

theorem has_deriv_at.neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (h : has_deriv_at f f' x) : has_deriv_at (fun (x : 𝕜) => -f x) (-f') x :=
  has_deriv_at_filter.neg h

theorem has_strict_deriv_at.neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (h : has_strict_deriv_at f f' x) : has_strict_deriv_at (fun (x : 𝕜) => -f x) (-f') x := sorry

theorem deriv_within.neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (fun (y : 𝕜) => -f y) s x = -deriv_within f s x := sorry

theorem deriv.neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} : deriv (fun (y : 𝕜) => -f y) x = -deriv f x := sorry

@[simp] theorem deriv.neg' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} : (deriv fun (y : 𝕜) => -f y) = fun (x : 𝕜) => -deriv f x :=
  funext fun (x : 𝕜) => deriv.neg

/-! ### Derivative of the negation function (i.e `has_neg.neg`) -/

theorem has_deriv_at_filter_neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) (L : filter 𝕜) : has_deriv_at_filter Neg.neg (-1) x L :=
  has_deriv_at_filter.neg (has_deriv_at_filter_id x L)

theorem has_deriv_within_at_neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) (s : set 𝕜) : has_deriv_within_at Neg.neg (-1) s x :=
  has_deriv_at_filter_neg x (nhds_within x s)

theorem has_deriv_at_neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) : has_deriv_at Neg.neg (-1) x :=
  has_deriv_at_filter_neg x (nhds x)

theorem has_deriv_at_neg' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) : has_deriv_at (fun (x : 𝕜) => -x) (-1) x :=
  has_deriv_at_filter_neg x (nhds x)

theorem has_strict_deriv_at_neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) : has_strict_deriv_at Neg.neg (-1) x :=
  has_strict_deriv_at.neg (has_strict_deriv_at_id x)

theorem deriv_neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) : deriv Neg.neg x = -1 :=
  has_deriv_at.deriv (has_deriv_at_neg x)

@[simp] theorem deriv_neg' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] : deriv Neg.neg = fun (_x : 𝕜) => -1 :=
  funext deriv_neg

@[simp] theorem deriv_neg'' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) : deriv (fun (x : 𝕜) => -x) x = -1 :=
  deriv_neg x

theorem deriv_within_neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) (s : set 𝕜) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within Neg.neg s x = -1 :=
  has_deriv_within_at.deriv_within (has_deriv_within_at_neg x s) hxs

theorem differentiable_neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] : differentiable 𝕜 Neg.neg :=
  differentiable.neg differentiable_id

theorem differentiable_on_neg {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (s : set 𝕜) : differentiable_on 𝕜 Neg.neg s :=
  differentiable_on.neg differentiable_on_id

/-! ### Derivative of the difference of two functions -/

theorem has_deriv_at_filter.sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {f' : F} {g' : F} {x : 𝕜} {L : filter 𝕜} (hf : has_deriv_at_filter f f' x L) (hg : has_deriv_at_filter g g' x L) : has_deriv_at_filter (fun (x : 𝕜) => f x - g x) (f' - g') x L := sorry

theorem has_deriv_within_at.sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {f' : F} {g' : F} {x : 𝕜} {s : set 𝕜} (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) : has_deriv_within_at (fun (x : 𝕜) => f x - g x) (f' - g') s x :=
  has_deriv_at_filter.sub hf hg

theorem has_deriv_at.sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {f' : F} {g' : F} {x : 𝕜} (hf : has_deriv_at f f' x) (hg : has_deriv_at g g' x) : has_deriv_at (fun (x : 𝕜) => f x - g x) (f' - g') x :=
  has_deriv_at_filter.sub hf hg

theorem has_strict_deriv_at.sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {f' : F} {g' : F} {x : 𝕜} (hf : has_strict_deriv_at f f' x) (hg : has_strict_deriv_at g g' x) : has_strict_deriv_at (fun (x : 𝕜) => f x - g x) (f' - g') x := sorry

theorem deriv_within_sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) : deriv_within (fun (y : 𝕜) => f y - g y) s x = deriv_within f s x - deriv_within g s x := sorry

@[simp] theorem deriv_sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {g : 𝕜 → F} {x : 𝕜} (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) : deriv (fun (y : 𝕜) => f y - g y) x = deriv f x - deriv g x :=
  has_deriv_at.deriv (has_deriv_at.sub (differentiable_at.has_deriv_at hf) (differentiable_at.has_deriv_at hg))

theorem has_deriv_at_filter.is_O_sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {L : filter 𝕜} (h : has_deriv_at_filter f f' x L) : asymptotics.is_O (fun (x' : 𝕜) => f x' - f x) (fun (x' : 𝕜) => x' - x) L :=
  has_fderiv_at_filter.is_O_sub h

theorem has_deriv_at_filter.sub_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {L : filter 𝕜} (hf : has_deriv_at_filter f f' x L) (c : F) : has_deriv_at_filter (fun (x : 𝕜) => f x - c) f' x L := sorry

theorem has_deriv_within_at.sub_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (hf : has_deriv_within_at f f' s x) (c : F) : has_deriv_within_at (fun (x : 𝕜) => f x - c) f' s x :=
  has_deriv_at_filter.sub_const hf c

theorem has_deriv_at.sub_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (hf : has_deriv_at f f' x) (c : F) : has_deriv_at (fun (x : 𝕜) => f x - c) f' x :=
  has_deriv_at_filter.sub_const hf c

theorem deriv_within_sub_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (c : F) : deriv_within (fun (y : 𝕜) => f y - c) s x = deriv_within f s x := sorry

theorem deriv_sub_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} (c : F) : deriv (fun (y : 𝕜) => f y - c) x = deriv f x := sorry

theorem has_deriv_at_filter.const_sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {L : filter 𝕜} (c : F) (hf : has_deriv_at_filter f f' x L) : has_deriv_at_filter (fun (x : 𝕜) => c - f x) (-f') x L := sorry

theorem has_deriv_within_at.const_sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (c : F) (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (x : 𝕜) => c - f x) (-f') s x :=
  has_deriv_at_filter.const_sub c hf

theorem has_deriv_at.const_sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (c : F) (hf : has_deriv_at f f' x) : has_deriv_at (fun (x : 𝕜) => c - f x) (-f') x :=
  has_deriv_at_filter.const_sub c hf

theorem deriv_within_const_sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (c : F) : deriv_within (fun (y : 𝕜) => c - f y) s x = -deriv_within f s x := sorry

theorem deriv_const_sub {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {x : 𝕜} (c : F) : deriv (fun (y : 𝕜) => c - f y) x = -deriv f x := sorry

/-! ### Continuity of a function admitting a derivative -/

theorem has_deriv_at_filter.tendsto_nhds {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {L : filter 𝕜} (hL : L ≤ nhds x) (h : has_deriv_at_filter f f' x L) : filter.tendsto f L (nhds (f x)) :=
  has_fderiv_at_filter.tendsto_nhds hL h

theorem has_deriv_within_at.continuous_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : set 𝕜} (h : has_deriv_within_at f f' s x) : continuous_within_at f s x :=
  has_deriv_at_filter.tendsto_nhds inf_le_left h

theorem has_deriv_at.continuous_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (h : has_deriv_at f f' x) : continuous_at f x :=
  has_deriv_at_filter.tendsto_nhds (le_refl (nhds x)) h

/-! ### Derivative of the cartesian product of two functions -/

theorem has_deriv_at_filter.prod {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f₁ : 𝕜 → F} {f₁' : F} {x : 𝕜} {L : filter 𝕜} {G : Type w} [normed_group G] [normed_space 𝕜 G] {f₂ : 𝕜 → G} {f₂' : G} (hf₁ : has_deriv_at_filter f₁ f₁' x L) (hf₂ : has_deriv_at_filter f₂ f₂' x L) : has_deriv_at_filter (fun (x : 𝕜) => (f₁ x, f₂ x)) (f₁', f₂') x L := sorry

theorem has_deriv_within_at.prod {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f₁ : 𝕜 → F} {f₁' : F} {x : 𝕜} {s : set 𝕜} {G : Type w} [normed_group G] [normed_space 𝕜 G] {f₂ : 𝕜 → G} {f₂' : G} (hf₁ : has_deriv_within_at f₁ f₁' s x) (hf₂ : has_deriv_within_at f₂ f₂' s x) : has_deriv_within_at (fun (x : 𝕜) => (f₁ x, f₂ x)) (f₁', f₂') s x :=
  has_deriv_at_filter.prod hf₁ hf₂

theorem has_deriv_at.prod {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f₁ : 𝕜 → F} {f₁' : F} {x : 𝕜} {G : Type w} [normed_group G] [normed_space 𝕜 G] {f₂ : 𝕜 → G} {f₂' : G} (hf₁ : has_deriv_at f₁ f₁' x) (hf₂ : has_deriv_at f₂ f₂' x) : has_deriv_at (fun (x : 𝕜) => (f₁ x, f₂ x)) (f₁', f₂') x :=
  has_deriv_at_filter.prod hf₁ hf₂

/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector valued and scalar valued functions, and `comp`
in lemmas on composition of scalar valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/

/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/

theorem has_deriv_at_filter.scomp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {g : 𝕜 → F} {g' : F} (x : 𝕜) {L : filter 𝕜} {h : 𝕜 → 𝕜} {h' : 𝕜} (hg : has_deriv_at_filter g g' (h x) (filter.map h L)) (hh : has_deriv_at_filter h h' x L) : has_deriv_at_filter (g ∘ h) (h' • g') x L := sorry

theorem has_deriv_within_at.scomp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {g : 𝕜 → F} {g' : F} (x : 𝕜) {s : set 𝕜} {h : 𝕜 → 𝕜} {h' : 𝕜} {t : set 𝕜} (hg : has_deriv_within_at g g' t (h x)) (hh : has_deriv_within_at h h' s x) (hst : s ⊆ h ⁻¹' t) : has_deriv_within_at (g ∘ h) (h' • g') s x := sorry

/-- The chain rule. -/
theorem has_deriv_at.scomp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {g : 𝕜 → F} {g' : F} (x : 𝕜) {h : 𝕜 → 𝕜} {h' : 𝕜} (hg : has_deriv_at g g' (h x)) (hh : has_deriv_at h h' x) : has_deriv_at (g ∘ h) (h' • g') x :=
  has_deriv_at_filter.scomp x (has_deriv_at_filter.mono hg (has_deriv_at.continuous_at hh)) hh

theorem has_strict_deriv_at.scomp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {g : 𝕜 → F} {g' : F} (x : 𝕜) {h : 𝕜 → 𝕜} {h' : 𝕜} (hg : has_strict_deriv_at g g' (h x)) (hh : has_strict_deriv_at h h' x) : has_strict_deriv_at (g ∘ h) (h' • g') x := sorry

theorem has_deriv_at.scomp_has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {g : 𝕜 → F} {g' : F} (x : 𝕜) {s : set 𝕜} {h : 𝕜 → 𝕜} {h' : 𝕜} (hg : has_deriv_at g g' (h x)) (hh : has_deriv_within_at h h' s x) : has_deriv_within_at (g ∘ h) (h' • g') s x :=
  has_deriv_within_at.scomp x
    (eq.mp (Eq._oldrec (Eq.refl (has_deriv_at g g' (h x))) (Eq.symm (propext has_deriv_within_at_univ))) hg) hh
    set.subset_preimage_univ

theorem deriv_within.scomp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {g : 𝕜 → F} (x : 𝕜) {s : set 𝕜} {t : set 𝕜} {h : 𝕜 → 𝕜} (hg : differentiable_within_at 𝕜 g t (h x)) (hh : differentiable_within_at 𝕜 h s x) (hs : s ⊆ h ⁻¹' t) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (g ∘ h) s x = deriv_within h s x • deriv_within g t (h x) := sorry

theorem deriv.scomp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {g : 𝕜 → F} (x : 𝕜) {h : 𝕜 → 𝕜} (hg : differentiable_at 𝕜 g (h x)) (hh : differentiable_at 𝕜 h x) : deriv (g ∘ h) x = deriv h x • deriv g (h x) :=
  has_deriv_at.deriv (has_deriv_at.scomp x (differentiable_at.has_deriv_at hg) (differentiable_at.has_deriv_at hh))

/-! ### Derivative of the composition of a scalar and vector functions -/

theorem has_deriv_at_filter.comp_has_fderiv_at_filter {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type w} [normed_group E] [normed_space 𝕜 E] {h₁ : 𝕜 → 𝕜} {h₁' : 𝕜} {f : E → 𝕜} {f' : continuous_linear_map 𝕜 E 𝕜} (x : E) {L : filter E} (hh₁ : has_deriv_at_filter h₁ h₁' (f x) (filter.map f L)) (hf : has_fderiv_at_filter f f' x L) : has_fderiv_at_filter (h₁ ∘ f) (h₁' • f') x L := sorry

theorem has_deriv_at.comp_has_fderiv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type w} [normed_group E] [normed_space 𝕜 E] {h₁ : 𝕜 → 𝕜} {h₁' : 𝕜} {f : E → 𝕜} {f' : continuous_linear_map 𝕜 E 𝕜} (x : E) (hh₁ : has_deriv_at h₁ h₁' (f x)) (hf : has_fderiv_at f f' x) : has_fderiv_at (h₁ ∘ f) (h₁' • f') x :=
  has_deriv_at_filter.comp_has_fderiv_at_filter x (has_deriv_at_filter.mono hh₁ (has_fderiv_at.continuous_at hf)) hf

theorem has_deriv_at.comp_has_fderiv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type w} [normed_group E] [normed_space 𝕜 E] {h₁ : 𝕜 → 𝕜} {h₁' : 𝕜} {f : E → 𝕜} {f' : continuous_linear_map 𝕜 E 𝕜} {s : set E} (x : E) (hh₁ : has_deriv_at h₁ h₁' (f x)) (hf : has_fderiv_within_at f f' s x) : has_fderiv_within_at (h₁ ∘ f) (h₁' • f') s x :=
  has_deriv_at_filter.comp_has_fderiv_at_filter x
    (has_deriv_at_filter.mono hh₁ (has_fderiv_within_at.continuous_within_at hf)) hf

theorem has_deriv_within_at.comp_has_fderiv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type w} [normed_group E] [normed_space 𝕜 E] {h₁ : 𝕜 → 𝕜} {h₁' : 𝕜} {f : E → 𝕜} {f' : continuous_linear_map 𝕜 E 𝕜} {s : set E} {t : set 𝕜} (x : E) (hh₁ : has_deriv_within_at h₁ h₁' t (f x)) (hf : has_fderiv_within_at f f' s x) (hst : set.maps_to f s t) : has_fderiv_within_at (h₁ ∘ f) (h₁' • f') s x := sorry

/-! ### Derivative of the composition of two scalar functions -/

theorem has_deriv_at_filter.comp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) {L : filter 𝕜} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜 → 𝕜} {h₁' : 𝕜} {h₂' : 𝕜} (hh₁ : has_deriv_at_filter h₁ h₁' (h₂ x) (filter.map h₂ L)) (hh₂ : has_deriv_at_filter h₂ h₂' x L) : has_deriv_at_filter (h₁ ∘ h₂) (h₁' * h₂') x L :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_deriv_at_filter (h₁ ∘ h₂) (h₁' * h₂') x L)) (mul_comm h₁' h₂')))
    (has_deriv_at_filter.scomp x hh₁ hh₂)

theorem has_deriv_within_at.comp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) {s : set 𝕜} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜 → 𝕜} {h₁' : 𝕜} {h₂' : 𝕜} {t : set 𝕜} (hh₁ : has_deriv_within_at h₁ h₁' t (h₂ x)) (hh₂ : has_deriv_within_at h₂ h₂' s x) (hst : s ⊆ h₂ ⁻¹' t) : has_deriv_within_at (h₁ ∘ h₂) (h₁' * h₂') s x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_deriv_within_at (h₁ ∘ h₂) (h₁' * h₂') s x)) (mul_comm h₁' h₂')))
    (has_deriv_within_at.scomp x hh₁ hh₂ hst)

/-- The chain rule. -/
theorem has_deriv_at.comp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜 → 𝕜} {h₁' : 𝕜} {h₂' : 𝕜} (hh₁ : has_deriv_at h₁ h₁' (h₂ x)) (hh₂ : has_deriv_at h₂ h₂' x) : has_deriv_at (h₁ ∘ h₂) (h₁' * h₂') x :=
  has_deriv_at_filter.comp x (has_deriv_at_filter.mono hh₁ (has_deriv_at.continuous_at hh₂)) hh₂

theorem has_strict_deriv_at.comp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜 → 𝕜} {h₁' : 𝕜} {h₂' : 𝕜} (hh₁ : has_strict_deriv_at h₁ h₁' (h₂ x)) (hh₂ : has_strict_deriv_at h₂ h₂' x) : has_strict_deriv_at (h₁ ∘ h₂) (h₁' * h₂') x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_strict_deriv_at (h₁ ∘ h₂) (h₁' * h₂') x)) (mul_comm h₁' h₂')))
    (has_strict_deriv_at.scomp x hh₁ hh₂)

theorem has_deriv_at.comp_has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) {s : set 𝕜} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜 → 𝕜} {h₁' : 𝕜} {h₂' : 𝕜} (hh₁ : has_deriv_at h₁ h₁' (h₂ x)) (hh₂ : has_deriv_within_at h₂ h₂' s x) : has_deriv_within_at (h₁ ∘ h₂) (h₁' * h₂') s x :=
  has_deriv_within_at.comp x
    (eq.mp (Eq._oldrec (Eq.refl (has_deriv_at h₁ h₁' (h₂ x))) (Eq.symm (propext has_deriv_within_at_univ))) hh₁) hh₂
    set.subset_preimage_univ

theorem deriv_within.comp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) {s : set 𝕜} {t : set 𝕜} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜 → 𝕜} (hh₁ : differentiable_within_at 𝕜 h₁ t (h₂ x)) (hh₂ : differentiable_within_at 𝕜 h₂ s x) (hs : s ⊆ h₂ ⁻¹' t) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (h₁ ∘ h₂) s x = deriv_within h₁ t (h₂ x) * deriv_within h₂ s x := sorry

theorem deriv.comp {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜 → 𝕜} (hh₁ : differentiable_at 𝕜 h₁ (h₂ x)) (hh₂ : differentiable_at 𝕜 h₂ x) : deriv (h₁ ∘ h₂) x = deriv h₁ (h₂ x) * deriv h₂ x :=
  has_deriv_at.deriv (has_deriv_at.comp x (differentiable_at.has_deriv_at hh₁) (differentiable_at.has_deriv_at hh₂))

protected theorem has_deriv_at_filter.iterate {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) {L : filter 𝕜} {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : has_deriv_at_filter f f' x L) (hL : filter.tendsto f L L) (hx : f x = x) (n : ℕ) : has_deriv_at_filter (nat.iterate f n) (f' ^ n) x L := sorry

protected theorem has_deriv_at.iterate {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : has_deriv_at f f' x) (hx : f x = x) (n : ℕ) : has_deriv_at (nat.iterate f n) (f' ^ n) x := sorry

protected theorem has_deriv_within_at.iterate {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) {s : set 𝕜} {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : has_deriv_within_at f f' s x) (hx : f x = x) (hs : set.maps_to f s s) (n : ℕ) : has_deriv_within_at (nat.iterate f n) (f' ^ n) s x := sorry

protected theorem has_strict_deriv_at.iterate {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (x : 𝕜) {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : has_strict_deriv_at f f' x) (hx : f x = x) (n : ℕ) : has_strict_deriv_at (nat.iterate f n) (f' ^ n) x := sorry

/-! ### Derivative of the composition of a function between vector spaces and of a function defined on `𝕜` -/

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem has_fderiv_within_at.comp_has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {E : Type w} [normed_group E] [normed_space 𝕜 E] {f : 𝕜 → F} {f' : F} (x : 𝕜) {s : set 𝕜} {l : F → E} {l' : continuous_linear_map 𝕜 F E} {t : set F} (hl : has_fderiv_within_at l l' t (f x)) (hf : has_deriv_within_at f f' s x) (hst : s ⊆ f ⁻¹' t) : has_deriv_within_at (l ∘ f) (coe_fn l' f') s x := sorry

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem has_fderiv_at.comp_has_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {E : Type w} [normed_group E] [normed_space 𝕜 E] {f : 𝕜 → F} {f' : F} (x : 𝕜) {l : F → E} {l' : continuous_linear_map 𝕜 F E} (hl : has_fderiv_at l l' (f x)) (hf : has_deriv_at f f' x) : has_deriv_at (l ∘ f) (coe_fn l' f') x := sorry

theorem has_fderiv_at.comp_has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {E : Type w} [normed_group E] [normed_space 𝕜 E] {f : 𝕜 → F} {f' : F} (x : 𝕜) {s : set 𝕜} {l : F → E} {l' : continuous_linear_map 𝕜 F E} (hl : has_fderiv_at l l' (f x)) (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (l ∘ f) (coe_fn l' f') s x :=
  has_fderiv_within_at.comp_has_deriv_within_at x
    (eq.mp (Eq._oldrec (Eq.refl (has_fderiv_at l l' (f x))) (Eq.symm (propext has_fderiv_within_at_univ))) hl) hf
    set.subset_preimage_univ

theorem fderiv_within.comp_deriv_within {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {E : Type w} [normed_group E] [normed_space 𝕜 E] {f : 𝕜 → F} (x : 𝕜) {s : set 𝕜} {l : F → E} {t : set F} (hl : differentiable_within_at 𝕜 l t (f x)) (hf : differentiable_within_at 𝕜 f s x) (hs : s ⊆ f ⁻¹' t) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (l ∘ f) s x = coe_fn (fderiv_within 𝕜 l t (f x)) (deriv_within f s x) := sorry

theorem fderiv.comp_deriv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {E : Type w} [normed_group E] [normed_space 𝕜 E] {f : 𝕜 → F} (x : 𝕜) {l : F → E} (hl : differentiable_at 𝕜 l (f x)) (hf : differentiable_at 𝕜 f x) : deriv (l ∘ f) x = coe_fn (fderiv 𝕜 l (f x)) (deriv f x) :=
  has_deriv_at.deriv
    (has_fderiv_at.comp_has_deriv_at x (differentiable_at.has_fderiv_at hl) (differentiable_at.has_deriv_at hf))

/-! ### Derivative of the multiplication of two scalar functions -/

theorem has_deriv_within_at.mul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} {c' : 𝕜} {d' : 𝕜} (hc : has_deriv_within_at c c' s x) (hd : has_deriv_within_at d d' s x) : has_deriv_within_at (fun (y : 𝕜) => c y * d y) (c' * d x + c x * d') s x := sorry

theorem has_deriv_at.mul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} {c' : 𝕜} {d' : 𝕜} (hc : has_deriv_at c c' x) (hd : has_deriv_at d d' x) : has_deriv_at (fun (y : 𝕜) => c y * d y) (c' * d x + c x * d') x := sorry

theorem has_strict_deriv_at.mul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} {c' : 𝕜} {d' : 𝕜} (hc : has_strict_deriv_at c c' x) (hd : has_strict_deriv_at d d' x) : has_strict_deriv_at (fun (y : 𝕜) => c y * d y) (c' * d x + c x * d') x := sorry

theorem deriv_within_mul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) : deriv_within (fun (y : 𝕜) => c y * d y) s x = deriv_within c s x * d x + c x * deriv_within d s x := sorry

@[simp] theorem deriv_mul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) : deriv (fun (y : 𝕜) => c y * d y) x = deriv c x * d x + c x * deriv d x :=
  has_deriv_at.deriv (has_deriv_at.mul (differentiable_at.has_deriv_at hc) (differentiable_at.has_deriv_at hd))

theorem has_deriv_within_at.mul_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜} (hc : has_deriv_within_at c c' s x) (d : 𝕜) : has_deriv_within_at (fun (y : 𝕜) => c y * d) (c' * d) s x := sorry

theorem has_deriv_at.mul_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜} (hc : has_deriv_at c c' x) (d : 𝕜) : has_deriv_at (fun (y : 𝕜) => c y * d) (c' * d) x := sorry

theorem deriv_within_mul_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (hc : differentiable_within_at 𝕜 c s x) (d : 𝕜) : deriv_within (fun (y : 𝕜) => c y * d) s x = deriv_within c s x * d :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.mul_const (differentiable_within_at.has_deriv_within_at hc) d) hxs

theorem deriv_mul_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_at 𝕜 c x) (d : 𝕜) : deriv (fun (y : 𝕜) => c y * d) x = deriv c x * d :=
  has_deriv_at.deriv (has_deriv_at.mul_const (differentiable_at.has_deriv_at hc) d)

theorem has_deriv_within_at.const_mul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {d : 𝕜 → 𝕜} {d' : 𝕜} (c : 𝕜) (hd : has_deriv_within_at d d' s x) : has_deriv_within_at (fun (y : 𝕜) => c * d y) (c * d') s x := sorry

theorem has_deriv_at.const_mul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {d : 𝕜 → 𝕜} {d' : 𝕜} (c : 𝕜) (hd : has_deriv_at d d' x) : has_deriv_at (fun (y : 𝕜) => c * d y) (c * d') x := sorry

theorem deriv_within_const_mul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {d : 𝕜 → 𝕜} (hxs : unique_diff_within_at 𝕜 s x) (c : 𝕜) (hd : differentiable_within_at 𝕜 d s x) : deriv_within (fun (y : 𝕜) => c * d y) s x = c * deriv_within d s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.const_mul c (differentiable_within_at.has_deriv_within_at hd)) hxs

theorem deriv_const_mul {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {d : 𝕜 → 𝕜} (c : 𝕜) (hd : differentiable_at 𝕜 d x) : deriv (fun (y : 𝕜) => c * d y) x = c * deriv d x :=
  has_deriv_at.deriv (has_deriv_at.const_mul c (differentiable_at.has_deriv_at hd))

/-! ### Derivative of `x ↦ x⁻¹` -/

theorem has_strict_deriv_at_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (hx : x ≠ 0) : has_strict_deriv_at has_inv.inv (-(x ^ bit0 1⁻¹)) x := sorry

theorem has_deriv_at_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (x_ne_zero : x ≠ 0) : has_deriv_at (fun (y : 𝕜) => y⁻¹) (-(x ^ bit0 1⁻¹)) x :=
  has_strict_deriv_at.has_deriv_at (has_strict_deriv_at_inv x_ne_zero)

theorem has_deriv_within_at_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (x_ne_zero : x ≠ 0) (s : set 𝕜) : has_deriv_within_at (fun (x : 𝕜) => x⁻¹) (-(x ^ bit0 1⁻¹)) s x :=
  has_deriv_at.has_deriv_within_at (has_deriv_at_inv x_ne_zero)

theorem differentiable_at_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (x_ne_zero : x ≠ 0) : differentiable_at 𝕜 (fun (x : 𝕜) => x⁻¹) x :=
  has_deriv_at.differentiable_at (has_deriv_at_inv x_ne_zero)

theorem differentiable_within_at_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} (x_ne_zero : x ≠ 0) : differentiable_within_at 𝕜 (fun (x : 𝕜) => x⁻¹) s x :=
  differentiable_at.differentiable_within_at (differentiable_at_inv x_ne_zero)

theorem differentiable_on_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] : differentiable_on 𝕜 (fun (x : 𝕜) => x⁻¹) (set_of fun (x : 𝕜) => x ≠ 0) :=
  fun (x : 𝕜) (hx : x ∈ set_of fun (x : 𝕜) => x ≠ 0) => differentiable_within_at_inv hx

theorem deriv_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (x_ne_zero : x ≠ 0) : deriv (fun (x : 𝕜) => x⁻¹) x = -(x ^ bit0 1⁻¹) :=
  has_deriv_at.deriv (has_deriv_at_inv x_ne_zero)

theorem deriv_within_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} (x_ne_zero : x ≠ 0) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (fun (x : 𝕜) => x⁻¹) s x = -(x ^ bit0 1⁻¹) := sorry

theorem has_fderiv_at_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (x_ne_zero : x ≠ 0) : has_fderiv_at (fun (x : 𝕜) => x⁻¹) (continuous_linear_map.smul_right 1 (-(x ^ bit0 1⁻¹))) x :=
  has_deriv_at_inv x_ne_zero

theorem has_fderiv_within_at_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} (x_ne_zero : x ≠ 0) : has_fderiv_within_at (fun (x : 𝕜) => x⁻¹) (continuous_linear_map.smul_right 1 (-(x ^ bit0 1⁻¹))) s x :=
  has_fderiv_at.has_fderiv_within_at (has_fderiv_at_inv x_ne_zero)

theorem fderiv_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (x_ne_zero : x ≠ 0) : fderiv 𝕜 (fun (x : 𝕜) => x⁻¹) x = continuous_linear_map.smul_right 1 (-(x ^ bit0 1⁻¹)) :=
  has_fderiv_at.fderiv (has_fderiv_at_inv x_ne_zero)

theorem fderiv_within_inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} (x_ne_zero : x ≠ 0) (hxs : unique_diff_within_at 𝕜 s x) : fderiv_within 𝕜 (fun (x : 𝕜) => x⁻¹) s x = continuous_linear_map.smul_right 1 (-(x ^ bit0 1⁻¹)) := sorry

theorem has_deriv_within_at.inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜} (hc : has_deriv_within_at c c' s x) (hx : c x ≠ 0) : has_deriv_within_at (fun (y : 𝕜) => c y⁻¹) (-c' / c x ^ bit0 1) s x := sorry

theorem has_deriv_at.inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜} (hc : has_deriv_at c c' x) (hx : c x ≠ 0) : has_deriv_at (fun (y : 𝕜) => c y⁻¹) (-c' / c x ^ bit0 1) x := sorry

theorem differentiable_within_at.inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_within_at 𝕜 c s x) (hx : c x ≠ 0) : differentiable_within_at 𝕜 (fun (x : 𝕜) => c x⁻¹) s x :=
  has_deriv_within_at.differentiable_within_at
    (has_deriv_within_at.inv (differentiable_within_at.has_deriv_within_at hc) hx)

@[simp] theorem differentiable_at.inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_at 𝕜 c x) (hx : c x ≠ 0) : differentiable_at 𝕜 (fun (x : 𝕜) => c x⁻¹) x :=
  has_deriv_at.differentiable_at (has_deriv_at.inv (differentiable_at.has_deriv_at hc) hx)

theorem differentiable_on.inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {s : set 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_on 𝕜 c s) (hx : ∀ (x : 𝕜), x ∈ s → c x ≠ 0) : differentiable_on 𝕜 (fun (x : 𝕜) => c x⁻¹) s :=
  fun (x : 𝕜) (h : x ∈ s) => differentiable_within_at.inv (hc x h) (hx x h)

@[simp] theorem differentiable.inv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {c : 𝕜 → 𝕜} (hc : differentiable 𝕜 c) (hx : ∀ (x : 𝕜), c x ≠ 0) : differentiable 𝕜 fun (x : 𝕜) => c x⁻¹ :=
  fun (x : 𝕜) => differentiable_at.inv (hc x) (hx x)

theorem deriv_within_inv' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_within_at 𝕜 c s x) (hx : c x ≠ 0) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (fun (x : 𝕜) => c x⁻¹) s x = -deriv_within c s x / c x ^ bit0 1 :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.inv (differentiable_within_at.has_deriv_within_at hc) hx) hxs

@[simp] theorem deriv_inv' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_at 𝕜 c x) (hx : c x ≠ 0) : deriv (fun (x : 𝕜) => c x⁻¹) x = -deriv c x / c x ^ bit0 1 :=
  has_deriv_at.deriv (has_deriv_at.inv (differentiable_at.has_deriv_at hc) hx)

/-! ### Derivative of `x ↦ c x / d x` -/

theorem has_deriv_within_at.div {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} {c' : 𝕜} {d' : 𝕜} (hc : has_deriv_within_at c c' s x) (hd : has_deriv_within_at d d' s x) (hx : d x ≠ 0) : has_deriv_within_at (fun (y : 𝕜) => c y / d y) ((c' * d x - c x * d') / d x ^ bit0 1) s x := sorry

theorem has_deriv_at.div {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} {c' : 𝕜} {d' : 𝕜} (hc : has_deriv_at c c' x) (hd : has_deriv_at d d' x) (hx : d x ≠ 0) : has_deriv_at (fun (y : 𝕜) => c y / d y) ((c' * d x - c x * d') / d x ^ bit0 1) x := sorry

theorem differentiable_within_at.div {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) (hx : d x ≠ 0) : differentiable_within_at 𝕜 (fun (x : 𝕜) => c x / d x) s x :=
  has_deriv_within_at.differentiable_within_at
    (has_deriv_within_at.div (differentiable_within_at.has_deriv_within_at hc)
      (differentiable_within_at.has_deriv_within_at hd) hx)

@[simp] theorem differentiable_at.div {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) (hx : d x ≠ 0) : differentiable_at 𝕜 (fun (x : 𝕜) => c x / d x) x :=
  has_deriv_at.differentiable_at
    (has_deriv_at.div (differentiable_at.has_deriv_at hc) (differentiable_at.has_deriv_at hd) hx)

theorem differentiable_on.div {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {s : set 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} (hc : differentiable_on 𝕜 c s) (hd : differentiable_on 𝕜 d s) (hx : ∀ (x : 𝕜), x ∈ s → d x ≠ 0) : differentiable_on 𝕜 (fun (x : 𝕜) => c x / d x) s :=
  fun (x : 𝕜) (h : x ∈ s) => differentiable_within_at.div (hc x h) (hd x h) (hx x h)

@[simp] theorem differentiable.div {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} (hc : differentiable 𝕜 c) (hd : differentiable 𝕜 d) (hx : ∀ (x : 𝕜), d x ≠ 0) : differentiable 𝕜 fun (x : 𝕜) => c x / d x :=
  fun (x : 𝕜) => differentiable_at.div (hc x) (hd x) (hx x)

theorem deriv_within_div {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) (hx : d x ≠ 0) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (fun (x : 𝕜) => c x / d x) s x = (deriv_within c s x * d x - c x * deriv_within d s x) / d x ^ bit0 1 := sorry

@[simp] theorem deriv_div {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} {d : 𝕜 → 𝕜} (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) (hx : d x ≠ 0) : deriv (fun (x : 𝕜) => c x / d x) x = (deriv c x * d x - c x * deriv d x) / d x ^ bit0 1 :=
  has_deriv_at.deriv (has_deriv_at.div (differentiable_at.has_deriv_at hc) (differentiable_at.has_deriv_at hd) hx)

theorem differentiable_within_at.div_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_within_at 𝕜 c s x) {d : 𝕜} : differentiable_within_at 𝕜 (fun (x : 𝕜) => c x / d) s x := sorry

@[simp] theorem differentiable_at.div_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_at 𝕜 c x) {d : 𝕜} : differentiable_at 𝕜 (fun (x : 𝕜) => c x / d) x :=
  has_deriv_at.differentiable_at (has_deriv_at.mul_const (differentiable_at.has_deriv_at hc) (d⁻¹))

theorem differentiable_on.div_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {s : set 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_on 𝕜 c s) {d : 𝕜} : differentiable_on 𝕜 (fun (x : 𝕜) => c x / d) s := sorry

@[simp] theorem differentiable.div_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {c : 𝕜 → 𝕜} (hc : differentiable 𝕜 c) {d : 𝕜} : differentiable 𝕜 fun (x : 𝕜) => c x / d := sorry

theorem deriv_within_div_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_within_at 𝕜 c s x) {d : 𝕜} (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (fun (x : 𝕜) => c x / d) s x = deriv_within c s x / d := sorry

@[simp] theorem deriv_div_const {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} (hc : differentiable_at 𝕜 c x) {d : 𝕜} : deriv (fun (x : 𝕜) => c x / d) x = deriv c x / d := sorry

theorem has_strict_deriv_at.has_strict_fderiv_at_equiv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {f : 𝕜 → 𝕜} {f' : 𝕜} {x : 𝕜} (hf : has_strict_deriv_at f f' x) (hf' : f' ≠ 0) : has_strict_fderiv_at f (↑(coe_fn (continuous_linear_equiv.units_equiv_aut 𝕜) (units.mk0 f' hf'))) x :=
  hf

theorem has_deriv_at.has_fderiv_at_equiv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {f : 𝕜 → 𝕜} {f' : 𝕜} {x : 𝕜} (hf : has_deriv_at f f' x) (hf' : f' ≠ 0) : has_fderiv_at f (↑(coe_fn (continuous_linear_equiv.units_equiv_aut 𝕜) (units.mk0 f' hf'))) x :=
  hf

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem has_strict_deriv_at.of_local_left_inverse {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {f : 𝕜 → 𝕜} {g : 𝕜 → 𝕜} {f' : 𝕜} {a : 𝕜} (hg : continuous_at g a) (hf : has_strict_deriv_at f f' (g a)) (hf' : f' ≠ 0) (hfg : filter.eventually (fun (y : 𝕜) => f (g y) = y) (nhds a)) : has_strict_deriv_at g (f'⁻¹) a :=
  has_strict_fderiv_at.of_local_left_inverse hg (has_strict_deriv_at.has_strict_fderiv_at_equiv hf hf') hfg

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem has_deriv_at.of_local_left_inverse {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {f : 𝕜 → 𝕜} {g : 𝕜 → 𝕜} {f' : 𝕜} {a : 𝕜} (hg : continuous_at g a) (hf : has_deriv_at f f' (g a)) (hf' : f' ≠ 0) (hfg : filter.eventually (fun (y : 𝕜) => f (g y) = y) (nhds a)) : has_deriv_at g (f'⁻¹) a :=
  has_fderiv_at.of_local_left_inverse hg (has_deriv_at.has_fderiv_at_equiv hf hf') hfg

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
nonzero derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem local_homeomorph.has_deriv_at_symm {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (f : local_homeomorph 𝕜 𝕜) {a : 𝕜} {f' : 𝕜} (ha : a ∈ local_equiv.target (local_homeomorph.to_local_equiv f)) (hf' : f' ≠ 0) (htff' : has_deriv_at (⇑f) f' (coe_fn (local_homeomorph.symm f) a)) : has_deriv_at (⇑(local_homeomorph.symm f)) (f'⁻¹) a :=
  has_deriv_at.of_local_left_inverse (local_homeomorph.continuous_at (local_homeomorph.symm f) ha) htff' hf'
    (local_homeomorph.eventually_right_inverse f ha)

theorem has_deriv_at.eventually_ne {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {F : Type v} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} (h : has_deriv_at f f' x) (hf' : f' ≠ 0) : filter.eventually (fun (z : 𝕜) => f z ≠ f x) (nhds_within x (singleton xᶜ)) := sorry

theorem not_differentiable_within_at_of_local_left_inverse_has_deriv_within_at_zero {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {f : 𝕜 → 𝕜} {g : 𝕜 → 𝕜} {a : 𝕜} {s : set 𝕜} {t : set 𝕜} (ha : a ∈ s) (hsu : unique_diff_within_at 𝕜 s a) (hf : has_deriv_within_at f 0 t (g a)) (hst : set.maps_to g s t) (hfg : filter.eventually_eq (nhds_within a s) (f ∘ g) id) : ¬differentiable_within_at 𝕜 g s a := sorry

theorem not_differentiable_at_of_local_left_inverse_has_deriv_at_zero {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {f : 𝕜 → 𝕜} {g : 𝕜 → 𝕜} {a : 𝕜} (hf : has_deriv_at f 0 (g a)) (hfg : filter.eventually_eq (nhds a) (f ∘ g) id) : ¬differentiable_at 𝕜 g a := sorry

namespace polynomial


/-! ### Derivative of a polynomial -/

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem has_strict_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (p : polynomial 𝕜) (x : 𝕜) : has_strict_deriv_at (fun (x : 𝕜) => eval x p) (eval x (coe_fn derivative p)) x := sorry

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem has_deriv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (p : polynomial 𝕜) (x : 𝕜) : has_deriv_at (fun (x : 𝕜) => eval x p) (eval x (coe_fn derivative p)) x :=
  has_strict_deriv_at.has_deriv_at (polynomial.has_strict_deriv_at p x)

protected theorem has_deriv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (p : polynomial 𝕜) (x : 𝕜) (s : set 𝕜) : has_deriv_within_at (fun (x : 𝕜) => eval x p) (eval x (coe_fn derivative p)) s x :=
  has_deriv_at.has_deriv_within_at (polynomial.has_deriv_at p x)

protected theorem differentiable_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (p : polynomial 𝕜) : differentiable_at 𝕜 (fun (x : 𝕜) => eval x p) x :=
  has_deriv_at.differentiable_at (polynomial.has_deriv_at p x)

protected theorem differentiable_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} (p : polynomial 𝕜) : differentiable_within_at 𝕜 (fun (x : 𝕜) => eval x p) s x :=
  differentiable_at.differentiable_within_at (polynomial.differentiable_at p)

protected theorem differentiable {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (p : polynomial 𝕜) : differentiable 𝕜 fun (x : 𝕜) => eval x p :=
  fun (x : 𝕜) => polynomial.differentiable_at p

protected theorem differentiable_on {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {s : set 𝕜} (p : polynomial 𝕜) : differentiable_on 𝕜 (fun (x : 𝕜) => eval x p) s :=
  differentiable.differentiable_on (polynomial.differentiable p)

@[simp] protected theorem deriv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (p : polynomial 𝕜) : deriv (fun (x : 𝕜) => eval x p) x = eval x (coe_fn derivative p) :=
  has_deriv_at.deriv (polynomial.has_deriv_at p x)

protected theorem deriv_within {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} (p : polynomial 𝕜) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (fun (x : 𝕜) => eval x p) s x = eval x (coe_fn derivative p) := sorry

protected theorem has_fderiv_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (p : polynomial 𝕜) (x : 𝕜) : has_fderiv_at (fun (x : 𝕜) => eval x p) (continuous_linear_map.smul_right 1 (eval x (coe_fn derivative p))) x := sorry

protected theorem has_fderiv_within_at {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {s : set 𝕜} (p : polynomial 𝕜) (x : 𝕜) : has_fderiv_within_at (fun (x : 𝕜) => eval x p) (continuous_linear_map.smul_right 1 (eval x (coe_fn derivative p))) s x :=
  has_fderiv_at.has_fderiv_within_at (polynomial.has_fderiv_at p x)

@[simp] protected theorem fderiv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (p : polynomial 𝕜) : fderiv 𝕜 (fun (x : 𝕜) => eval x p) x = continuous_linear_map.smul_right 1 (eval x (coe_fn derivative p)) :=
  has_fderiv_at.fderiv (polynomial.has_fderiv_at p x)

protected theorem fderiv_within {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} (p : polynomial 𝕜) (hxs : unique_diff_within_at 𝕜 s x) : fderiv_within 𝕜 (fun (x : 𝕜) => eval x p) s x = continuous_linear_map.smul_right 1 (eval x (coe_fn derivative p)) := sorry

end polynomial


/-! ### Derivative of `x ↦ x^n` for `n : ℕ` -/

theorem has_strict_deriv_at_pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (n : ℕ) (x : 𝕜) : has_strict_deriv_at (fun (x : 𝕜) => x ^ n) (↑n * x ^ (n - 1)) x := sorry

theorem has_deriv_at_pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (n : ℕ) (x : 𝕜) : has_deriv_at (fun (x : 𝕜) => x ^ n) (↑n * x ^ (n - 1)) x :=
  has_strict_deriv_at.has_deriv_at (has_strict_deriv_at_pow n x)

theorem has_deriv_within_at_pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] (n : ℕ) (x : 𝕜) (s : set 𝕜) : has_deriv_within_at (fun (x : 𝕜) => x ^ n) (↑n * x ^ (n - 1)) s x :=
  has_deriv_at.has_deriv_within_at (has_deriv_at_pow n x)

theorem differentiable_at_pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {n : ℕ} : differentiable_at 𝕜 (fun (x : 𝕜) => x ^ n) x :=
  has_deriv_at.differentiable_at (has_deriv_at_pow n x)

theorem differentiable_within_at_pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {n : ℕ} : differentiable_within_at 𝕜 (fun (x : 𝕜) => x ^ n) s x :=
  differentiable_at.differentiable_within_at differentiable_at_pow

theorem differentiable_pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {n : ℕ} : differentiable 𝕜 fun (x : 𝕜) => x ^ n :=
  fun (x : 𝕜) => differentiable_at_pow

theorem differentiable_on_pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {s : set 𝕜} {n : ℕ} : differentiable_on 𝕜 (fun (x : 𝕜) => x ^ n) s :=
  differentiable.differentiable_on differentiable_pow

theorem deriv_pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {n : ℕ} : deriv (fun (x : 𝕜) => x ^ n) x = ↑n * x ^ (n - 1) :=
  has_deriv_at.deriv (has_deriv_at_pow n x)

@[simp] theorem deriv_pow' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {n : ℕ} : (deriv fun (x : 𝕜) => x ^ n) = fun (x : 𝕜) => ↑n * x ^ (n - 1) :=
  funext fun (x : 𝕜) => deriv_pow

theorem deriv_within_pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {n : ℕ} (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (fun (x : 𝕜) => x ^ n) s x = ↑n * x ^ (n - 1) :=
  has_deriv_within_at.deriv_within (has_deriv_within_at_pow n x s) hxs

theorem iter_deriv_pow' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {n : ℕ} {k : ℕ} : (nat.iterate deriv k fun (x : 𝕜) => x ^ n) =
  fun (x : 𝕜) => ↑(finset.prod (finset.range k) fun (i : ℕ) => n - i) * x ^ (n - k) := sorry

theorem iter_deriv_pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {n : ℕ} {k : ℕ} : nat.iterate deriv k (fun (x : 𝕜) => x ^ n) x = ↑(finset.prod (finset.range k) fun (i : ℕ) => n - i) * x ^ (n - k) :=
  congr_fun iter_deriv_pow' x

theorem has_deriv_within_at.pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜} {n : ℕ} (hc : has_deriv_within_at c c' s x) : has_deriv_within_at (fun (y : 𝕜) => c y ^ n) (↑n * c x ^ (n - 1) * c') s x :=
  has_deriv_at.comp_has_deriv_within_at x (has_deriv_at_pow n (c x)) hc

theorem has_deriv_at.pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜} {n : ℕ} (hc : has_deriv_at c c' x) : has_deriv_at (fun (y : 𝕜) => c y ^ n) (↑n * c x ^ (n - 1) * c') x := sorry

theorem differentiable_within_at.pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {n : ℕ} (hc : differentiable_within_at 𝕜 c s x) : differentiable_within_at 𝕜 (fun (x : 𝕜) => c x ^ n) s x :=
  has_deriv_within_at.differentiable_within_at (has_deriv_within_at.pow (differentiable_within_at.has_deriv_within_at hc))

@[simp] theorem differentiable_at.pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} {n : ℕ} (hc : differentiable_at 𝕜 c x) : differentiable_at 𝕜 (fun (x : 𝕜) => c x ^ n) x :=
  has_deriv_at.differentiable_at (has_deriv_at.pow (differentiable_at.has_deriv_at hc))

theorem differentiable_on.pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {s : set 𝕜} {c : 𝕜 → 𝕜} {n : ℕ} (hc : differentiable_on 𝕜 c s) : differentiable_on 𝕜 (fun (x : 𝕜) => c x ^ n) s :=
  fun (x : 𝕜) (h : x ∈ s) => differentiable_within_at.pow (hc x h)

@[simp] theorem differentiable.pow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {c : 𝕜 → 𝕜} {n : ℕ} (hc : differentiable 𝕜 c) : differentiable 𝕜 fun (x : 𝕜) => c x ^ n :=
  fun (x : 𝕜) => differentiable_at.pow (hc x)

theorem deriv_within_pow' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {n : ℕ} (hc : differentiable_within_at 𝕜 c s x) (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (fun (x : 𝕜) => c x ^ n) s x = ↑n * c x ^ (n - 1) * deriv_within c s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.pow (differentiable_within_at.has_deriv_within_at hc)) hxs

@[simp] theorem deriv_pow'' {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {c : 𝕜 → 𝕜} {n : ℕ} (hc : differentiable_at 𝕜 c x) : deriv (fun (x : 𝕜) => c x ^ n) x = ↑n * c x ^ (n - 1) * deriv c x :=
  has_deriv_at.deriv (has_deriv_at.pow (differentiable_at.has_deriv_at hc))

/-! ### Derivative of `x ↦ x^m` for `m : ℤ` -/

theorem has_strict_deriv_at_fpow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (m : ℤ) (hx : x ≠ 0) : has_strict_deriv_at (fun (x : 𝕜) => x ^ m) (↑m * x ^ (m - 1)) x := sorry

theorem has_deriv_at_fpow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (m : ℤ) (hx : x ≠ 0) : has_deriv_at (fun (x : 𝕜) => x ^ m) (↑m * x ^ (m - 1)) x :=
  has_strict_deriv_at.has_deriv_at (has_strict_deriv_at_fpow m hx)

theorem has_deriv_within_at_fpow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} (m : ℤ) (hx : x ≠ 0) (s : set 𝕜) : has_deriv_within_at (fun (x : 𝕜) => x ^ m) (↑m * x ^ (m - 1)) s x :=
  has_deriv_at.has_deriv_within_at (has_deriv_at_fpow m hx)

theorem differentiable_at_fpow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {m : ℤ} (hx : x ≠ 0) : differentiable_at 𝕜 (fun (x : 𝕜) => x ^ m) x :=
  has_deriv_at.differentiable_at (has_deriv_at_fpow m hx)

theorem differentiable_within_at_fpow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {m : ℤ} (hx : x ≠ 0) : differentiable_within_at 𝕜 (fun (x : 𝕜) => x ^ m) s x :=
  differentiable_at.differentiable_within_at (differentiable_at_fpow hx)

theorem differentiable_on_fpow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {s : set 𝕜} {m : ℤ} (hs : ¬0 ∈ s) : differentiable_on 𝕜 (fun (x : 𝕜) => x ^ m) s :=
  fun (x : 𝕜) (hxs : x ∈ s) => differentiable_within_at_fpow fun (hx : x = 0) => hs (hx ▸ hxs)

-- TODO : this is true at `x=0` as well

theorem deriv_fpow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {m : ℤ} (hx : x ≠ 0) : deriv (fun (x : 𝕜) => x ^ m) x = ↑m * x ^ (m - 1) :=
  has_deriv_at.deriv (has_deriv_at_fpow m hx)

theorem deriv_within_fpow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {s : set 𝕜} {m : ℤ} (hxs : unique_diff_within_at 𝕜 s x) (hx : x ≠ 0) : deriv_within (fun (x : 𝕜) => x ^ m) s x = ↑m * x ^ (m - 1) :=
  has_deriv_within_at.deriv_within (has_deriv_within_at_fpow m hx s) hxs

theorem iter_deriv_fpow {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {x : 𝕜} {m : ℤ} {k : ℕ} (hx : x ≠ 0) : nat.iterate deriv k (fun (x : 𝕜) => x ^ m) x = ↑(finset.prod (finset.range k) fun (i : ℕ) => m - ↑i) * x ^ (m - ↑k) := sorry

/-! ### Upper estimates on liminf and limsup -/

theorem has_deriv_within_at.limsup_slope_le {f : ℝ → ℝ} {f' : ℝ} {s : set ℝ} {x : ℝ} {r : ℝ} (hf : has_deriv_within_at f f' s x) (hr : f' < r) : filter.eventually (fun (z : ℝ) => z - x⁻¹ * (f z - f x) < r) (nhds_within x (s \ singleton x)) :=
  iff.mp has_deriv_within_at_iff_tendsto_slope hf (set.Iio r) (mem_nhds_sets is_open_Iio hr)

theorem has_deriv_within_at.limsup_slope_le' {f : ℝ → ℝ} {f' : ℝ} {s : set ℝ} {x : ℝ} {r : ℝ} (hf : has_deriv_within_at f f' s x) (hs : ¬x ∈ s) (hr : f' < r) : filter.eventually (fun (z : ℝ) => z - x⁻¹ * (f z - f x) < r) (nhds_within x s) :=
  iff.mp (has_deriv_within_at_iff_tendsto_slope' hs) hf (set.Iio r) (mem_nhds_sets is_open_Iio hr)

theorem has_deriv_within_at.liminf_right_slope_le {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} {r : ℝ} (hf : has_deriv_within_at f f' (set.Ici x) x) (hr : f' < r) : filter.frequently (fun (z : ℝ) => z - x⁻¹ * (f z - f x) < r) (nhds_within x (set.Ioi x)) :=
  filter.eventually.frequently (has_deriv_within_at.limsup_slope_le' (has_deriv_within_at.Ioi_of_Ici hf) (lt_irrefl x) hr)

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ∥f'∥` the ratio
`∥f z - f x∥ / ∥z - x∥` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `∥f'∥`. -/
theorem has_deriv_within_at.limsup_norm_slope_le {E : Type u} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {f' : E} {s : set ℝ} {x : ℝ} {r : ℝ} (hf : has_deriv_within_at f f' s x) (hr : norm f' < r) : filter.eventually (fun (z : ℝ) => norm (z - x)⁻¹ * norm (f z - f x) < r) (nhds_within x s) := sorry

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ∥f'∥` the ratio
`(∥f z∥ - ∥f x∥) / ∥z - x∥` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `∥f'∥`.

This lemma is a weaker version of `has_deriv_within_at.limsup_norm_slope_le`
where `∥f z∥ - ∥f x∥` is replaced by `∥f z - f x∥`. -/
theorem has_deriv_within_at.limsup_slope_norm_le {E : Type u} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {f' : E} {s : set ℝ} {x : ℝ} {r : ℝ} (hf : has_deriv_within_at f f' s x) (hr : norm f' < r) : filter.eventually (fun (z : ℝ) => norm (z - x)⁻¹ * (norm (f z) - norm (f x)) < r) (nhds_within x s) := sorry

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ∥f'∥` the ratio
`∥f z - f x∥ / ∥z - x∥` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `∥f'∥`. See also `has_deriv_within_at.limsup_norm_slope_le`
for a stronger version using limit superior and any set `s`. -/
theorem has_deriv_within_at.liminf_right_norm_slope_le {E : Type u} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {f' : E} {x : ℝ} {r : ℝ} (hf : has_deriv_within_at f f' (set.Ici x) x) (hr : norm f' < r) : filter.frequently (fun (z : ℝ) => norm (z - x)⁻¹ * norm (f z - f x) < r) (nhds_within x (set.Ioi x)) :=
  filter.eventually.frequently (has_deriv_within_at.limsup_norm_slope_le (has_deriv_within_at.Ioi_of_Ici hf) hr)

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ∥f'∥` the ratio
`(∥f z∥ - ∥f x∥) / (z - x)` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `∥f'∥`.

See also

* `has_deriv_within_at.limsup_norm_slope_le` for a stronger version using
  limit superior and any set `s`;
* `has_deriv_within_at.liminf_right_norm_slope_le` for a stronger version using
  `∥f z - f x∥` instead of `∥f z∥ - ∥f x∥`. -/
theorem has_deriv_within_at.liminf_right_slope_norm_le {E : Type u} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {f' : E} {x : ℝ} {r : ℝ} (hf : has_deriv_within_at f f' (set.Ici x) x) (hr : norm f' < r) : filter.frequently (fun (z : ℝ) => z - x⁻¹ * (norm (f z) - norm (f x)) < r) (nhds_within x (set.Ioi x)) := sorry

