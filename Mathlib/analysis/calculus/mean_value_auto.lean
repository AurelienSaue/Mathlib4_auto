/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.calculus.local_extr
import Mathlib.analysis.convex.topology
import Mathlib.data.complex.is_R_or_C
import PostPort

universes u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# The mean value inequality and equalities

In this file we prove the following facts:

* `convex.norm_image_sub_le_of_norm_deriv_le` : if `f` is differentiable on a convex set `s`
  and the norm of its derivative is bounded by `C`, then `f` is Lipschitz continuous on `s` with
  constant `C`; also a variant in which what is bounded by `C` is the norm of the difference of the
  derivative from a fixed linear map.

* `image_le_of*`, `image_norm_le_of_*` : several similar lemmas deducing `f x ≤ B x` or
  `∥f x∥ ≤ B x` from upper estimates on `f'` or `∥f'∥`, respectively. These lemmas differ by
  their assumptions:

  * `of_liminf_*` lemmas assume that limit inferior of some ratio is less than `B' x`;
  * `of_deriv_right_*`, `of_norm_deriv_right_*` lemmas assume that the right derivative
    or its norm is less than `B' x`;
  * `of_*_lt_*` lemmas assume a strict inequality whenever `f x = B x` or `∥f x∥ = B x`;
  * `of_*_le_*` lemmas assume a non-strict inequality everywhere on `[a, b)`;
  * name of a lemma ends with `'` if (1) it assumes that `B` is continuous on `[a, b]`
    and has a right derivative at every point of `[a, b)`, and (2) the lemma has
    a counterpart assuming that `B` is differentiable everywhere on `ℝ`

* `norm_image_sub_le_*_segment` : if derivative of `f` on `[a, b]` is bounded above
  by a constant `C`, then `∥f x - f a∥ ≤ C * ∥x - a∥`; several versions deal with
  right derivative and derivative within `[a, b]` (`has_deriv_within_at` or `deriv_within`).

* `convex.is_const_of_fderiv_within_eq_zero` : if a function has derivative `0` on a convex set `s`,
  then it is a constant on `s`.

* `exists_ratio_has_deriv_at_eq_ratio_slope` and `exists_ratio_deriv_eq_ratio_slope` :
  Cauchy's Mean Value Theorem.

* `exists_has_deriv_at_eq_slope` and `exists_deriv_eq_slope` : Lagrange's Mean Value Theorem.

* `domain_mvt` : Lagrange's Mean Value Theorem, applied to a segment in a convex domain.

* `convex.image_sub_lt_mul_sub_of_deriv_lt`, `convex.mul_sub_lt_image_sub_of_lt_deriv`,
  `convex.image_sub_le_mul_sub_of_deriv_le`, `convex.mul_sub_le_image_sub_of_le_deriv`,
  if `∀ x, C (</≤/>/≥) (f' x)`, then `C * (y - x) (</≤/>/≥) (f y - f x)` whenever `x < y`.

* `convex.mono_of_deriv_nonneg`, `convex.antimono_of_deriv_nonpos`,
  `convex.strict_mono_of_deriv_pos`, `convex.strict_antimono_of_deriv_neg` :
  if the derivative of a function is non-negative/non-positive/positive/negative, then
  the function is monotone/monotonically decreasing/strictly monotone/strictly monotonically
  decreasing.

* `convex_on_of_deriv_mono`, `convex_on_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.

* `strict_fderiv_of_cont_diff` : a C^1 function over the reals is strictly differentiable.  (This
  is a corollary of the mean value inequality.)
-/

/-! ### One-dimensional fencing inequalities -/

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary' {f : ℝ → ℝ} {f' : ℝ → ℝ} {a : ℝ} {b : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ),
  x ∈ set.Ico a b →
    ∀ (r : ℝ), f' x < r → filter.frequently (fun (z : ℝ) => z - x⁻¹ * (f z - f x) < r) (nhds_within x (set.Ioi x))) {B : ℝ → ℝ} {B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (set.Icc a b)) (hB' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at B (B' x) (set.Ici x) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → f x = B x → f' x < B' x) {x : ℝ} : x ∈ set.Icc a b → f x ≤ B x := sorry

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary {f : ℝ → ℝ} {f' : ℝ → ℝ} {a : ℝ} {b : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ),
  x ∈ set.Ico a b →
    ∀ (r : ℝ), f' x < r → filter.frequently (fun (z : ℝ) => z - x⁻¹ * (f z - f x) < r) (nhds_within x (set.Ioi x))) {B : ℝ → ℝ} {B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ (x : ℝ), has_deriv_at B (B' x) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → f x = B x → f' x < B' x) {x : ℝ} : x ∈ set.Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha
    (fun (x : ℝ) (hx : x ∈ set.Icc a b) => continuous_at.continuous_within_at (has_deriv_at.continuous_at (hB x)))
    (fun (x : ℝ) (hx : x ∈ set.Ico a b) => has_deriv_at.has_deriv_within_at (hB x)) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by `B'`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_le_deriv_boundary {f : ℝ → ℝ} {a : ℝ} {b : ℝ} (hf : continuous_on f (set.Icc a b)) {B : ℝ → ℝ} {B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (set.Icc a b)) (hB' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at B (B' x) (set.Ici x) x) (bound : ∀ (x : ℝ),
  x ∈ set.Ico a b →
    ∀ (r : ℝ), B' x < r → filter.frequently (fun (z : ℝ) => z - x⁻¹ * (f z - f x) < r) (nhds_within x (set.Ioi x))) {x : ℝ} : x ∈ set.Icc a b → f x ≤ B x := sorry

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_lt_deriv_boundary' {f : ℝ → ℝ} {f' : ℝ → ℝ} {a : ℝ} {b : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f (f' x) (set.Ici x) x) {B : ℝ → ℝ} {B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (set.Icc a b)) (hB' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at B (B' x) (set.Ici x) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → f x = B x → f' x < B' x) {x : ℝ} : x ∈ set.Icc a b → f x ≤ B x := sorry

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_lt_deriv_boundary {f : ℝ → ℝ} {f' : ℝ → ℝ} {a : ℝ} {b : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f (f' x) (set.Ici x) x) {B : ℝ → ℝ} {B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ (x : ℝ), has_deriv_at B (B' x) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → f x = B x → f' x < B' x) {x : ℝ} : x ∈ set.Icc a b → f x ≤ B x :=
  image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun (x : ℝ) (hx : x ∈ set.Icc a b) => continuous_at.continuous_within_at (has_deriv_at.continuous_at (hB x)))
    (fun (x : ℝ) (hx : x ∈ set.Ico a b) => has_deriv_at.has_deriv_within_at (hB x)) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x ≤ B' x` on `[a, b)`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_le_deriv_boundary {f : ℝ → ℝ} {f' : ℝ → ℝ} {a : ℝ} {b : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f (f' x) (set.Ici x) x) {B : ℝ → ℝ} {B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (set.Icc a b)) (hB' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at B (B' x) (set.Ici x) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → f' x ≤ B' x) {x : ℝ} : x ∈ set.Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB'
    fun (x : ℝ) (hx : x ∈ set.Ico a b) (r : ℝ) (hr : B' x < r) =>
      has_deriv_within_at.liminf_right_slope_le (hf' x hx) (lt_of_le_of_lt (bound x hx) hr)

/-! ### Vector-valued functions `f : ℝ → E` -/

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `B` has right derivative at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(∥f z∥ - ∥f x∥) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. -/
theorem image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary {a : ℝ} {b : ℝ} {E : Type u_1} [normed_group E] {f : ℝ → E} {f' : ℝ → ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ),
  x ∈ set.Ico a b →
    ∀ (r : ℝ),
      f' x < r → filter.frequently (fun (z : ℝ) => z - x⁻¹ * (norm (f z) - norm (f x)) < r) (nhds_within x (set.Ioi x))) {B : ℝ → ℝ} {B' : ℝ → ℝ} (ha : norm (f a) ≤ B a) (hB : continuous_on B (set.Icc a b)) (hB' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at B (B' x) (set.Ici x) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → norm (f x) = B x → f' x < B' x) {x : ℝ} : x ∈ set.Icc a b → norm (f x) ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous.comp_continuous_on continuous_norm hf) hf' ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* the norm of `f'` is strictly less than `B'` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary' {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {a : ℝ} {b : ℝ} {f' : ℝ → E} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f (f' x) (set.Ici x) x) {B : ℝ → ℝ} {B' : ℝ → ℝ} (ha : norm (f a) ≤ B a) (hB : continuous_on B (set.Icc a b)) (hB' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at B (B' x) (set.Ici x) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → norm (f x) = B x → norm (f' x) < B' x) {x : ℝ} : x ∈ set.Icc a b → norm (f x) ≤ B x := sorry

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* the norm of `f'` is strictly less than `B'` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {a : ℝ} {b : ℝ} {f' : ℝ → E} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f (f' x) (set.Ici x) x) {B : ℝ → ℝ} {B' : ℝ → ℝ} (ha : norm (f a) ≤ B a) (hB : ∀ (x : ℝ), has_deriv_at B (B' x) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → norm (f x) = B x → norm (f' x) < B' x) {x : ℝ} : x ∈ set.Icc a b → norm (f x) ≤ B x :=
  image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun (x : ℝ) (hx : x ∈ set.Icc a b) => continuous_at.continuous_within_at (has_deriv_at.continuous_at (hB x)))
    (fun (x : ℝ) (hx : x ∈ set.Ico a b) => has_deriv_at.has_deriv_within_at (hB x)) bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* we have `∥f' x∥ ≤ B x` everywhere on `[a, b)`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary' {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {a : ℝ} {b : ℝ} {f' : ℝ → E} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f (f' x) (set.Ici x) x) {B : ℝ → ℝ} {B' : ℝ → ℝ} (ha : norm (f a) ≤ B a) (hB : continuous_on B (set.Icc a b)) (hB' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at B (B' x) (set.Ici x) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → norm (f' x) ≤ B' x) {x : ℝ} : x ∈ set.Icc a b → norm (f x) ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary (continuous.comp_continuous_on continuous_norm hf) ha hB hB'
    fun (x : ℝ) (hx : x ∈ set.Ico a b) (r : ℝ) (hr : B' x < r) =>
      has_deriv_within_at.liminf_right_slope_norm_le (hf' x hx) (lt_of_le_of_lt (bound x hx) hr)

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* we have `∥f' x∥ ≤ B x` everywhere on `[a, b)`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {a : ℝ} {b : ℝ} {f' : ℝ → E} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f (f' x) (set.Ici x) x) {B : ℝ → ℝ} {B' : ℝ → ℝ} (ha : norm (f a) ≤ B a) (hB : ∀ (x : ℝ), has_deriv_at B (B' x) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → norm (f' x) ≤ B' x) {x : ℝ} : x ∈ set.Icc a b → norm (f x) ≤ B x :=
  image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
    (fun (x : ℝ) (hx : x ∈ set.Icc a b) => continuous_at.continuous_within_at (has_deriv_at.continuous_at (hB x)))
    (fun (x : ℝ) (hx : x ∈ set.Ico a b) => has_deriv_at.has_deriv_within_at (hB x)) bound

/-- A function on `[a, b]` with the norm of the right derivative bounded by `C`
satisfies `∥f x - f a∥ ≤ C * (x - a)`. -/
theorem norm_image_sub_le_of_norm_deriv_right_le_segment {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {a : ℝ} {b : ℝ} {f' : ℝ → E} {C : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f (f' x) (set.Ici x) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → norm (f' x) ≤ C) (x : ℝ) (H : x ∈ set.Icc a b) : norm (f x - f a) ≤ C * (x - a) := sorry

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `∥f x - f a∥ ≤ C * (x - a)`, `has_deriv_within_at`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment' {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {a : ℝ} {b : ℝ} {f' : ℝ → E} {C : ℝ} (hf : ∀ (x : ℝ), x ∈ set.Icc a b → has_deriv_within_at f (f' x) (set.Icc a b) x) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → norm (f' x) ≤ C) (x : ℝ) (H : x ∈ set.Icc a b) : norm (f x - f a) ≤ C * (x - a) := sorry

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `∥f x - f a∥ ≤ C * (x - a)`, `deriv_within`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {a : ℝ} {b : ℝ} {C : ℝ} (hf : differentiable_on ℝ f (set.Icc a b)) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → norm (deriv_within f (set.Icc a b) x) ≤ C) (x : ℝ) (H : x ∈ set.Icc a b) : norm (f x - f a) ≤ C * (x - a) :=
  norm_image_sub_le_of_norm_deriv_le_segment'
    (fun (x : ℝ) (hx : x ∈ set.Icc a b) => differentiable_within_at.has_deriv_within_at (hf x hx)) bound

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `∥f 1 - f 0∥ ≤ C`, `has_deriv_within_at`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01' {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {f' : ℝ → E} {C : ℝ} (hf : ∀ (x : ℝ), x ∈ set.Icc 0 1 → has_deriv_within_at f (f' x) (set.Icc 0 1) x) (bound : ∀ (x : ℝ), x ∈ set.Ico 0 1 → norm (f' x) ≤ C) : norm (f 1 - f 0) ≤ C := sorry

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `∥f 1 - f 0∥ ≤ C`, `deriv_within` version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01 {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {C : ℝ} (hf : differentiable_on ℝ f (set.Icc 0 1)) (bound : ∀ (x : ℝ), x ∈ set.Ico 0 1 → norm (deriv_within f (set.Icc 0 1) x) ≤ C) : norm (f 1 - f 0) ≤ C := sorry

theorem constant_of_has_deriv_right_zero {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hcont : continuous_on f (set.Icc a b)) (hderiv : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f 0 (set.Ici x) x) (x : ℝ) (H : x ∈ set.Icc a b) : f x = f a := sorry

theorem constant_of_deriv_within_zero {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hdiff : differentiable_on ℝ f (set.Icc a b)) (hderiv : ∀ (x : ℝ), x ∈ set.Ico a b → deriv_within f (set.Icc a b) x = 0) (x : ℝ) (H : x ∈ set.Icc a b) : f x = f a := sorry

/-- If two continuous functions on `[a, b]` have the same right derivative and are equal at `a`,
  then they are equal everywhere on `[a, b]`. -/
theorem eq_of_has_deriv_right_eq {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {a : ℝ} {b : ℝ} {f' : ℝ → E} {g : ℝ → E} (derivf : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f (f' x) (set.Ici x) x) (derivg : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at g (f' x) (set.Ici x) x) (fcont : continuous_on f (set.Icc a b)) (gcont : continuous_on g (set.Icc a b)) (hi : f a = g a) (y : ℝ) (H : y ∈ set.Icc a b) : f y = g y := sorry

/-- If two differentiable functions on `[a, b]` have the same derivative within `[a, b]` everywhere
  on `[a, b)` and are equal at `a`, then they are equal everywhere on `[a, b]`. -/
theorem eq_of_deriv_within_eq {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {a : ℝ} {b : ℝ} {g : ℝ → E} (fdiff : differentiable_on ℝ f (set.Icc a b)) (gdiff : differentiable_on ℝ g (set.Icc a b)) (hderiv : set.eq_on (deriv_within f (set.Icc a b)) (deriv_within g (set.Icc a b)) (set.Ico a b)) (hi : f a = g a) (y : ℝ) (H : y ∈ set.Icc a b) : f y = g y := sorry

/-! ### Vector-valued functions `f : E → F` -/

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`, then
the function is `C`-Lipschitz. Version with `has_fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_has_fderiv_within_le {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F} {C : ℝ} {s : set E} {x : E} {y : E} {f' : E → continuous_linear_map ℝ E F} (hf : ∀ (x : E), x ∈ s → has_fderiv_within_at f (f' x) s x) (bound : ∀ (x : E), x ∈ s → norm (f' x) ≤ C) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : norm (f y - f x) ≤ C * norm (y - x) := sorry

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `has_fderiv_within` and
`lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_has_fderiv_within_le {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F} {C : ℝ} {s : set E} {f' : E → continuous_linear_map ℝ E F} (hf : ∀ (x : E), x ∈ s → has_fderiv_within_at f (f' x) s x) (bound : ∀ (x : E), x ∈ s → norm (f' x) ≤ C) (hs : convex s) : lipschitz_on_with (nnreal.of_real C) f s := sorry

/-- The mean value theorem on a convex set: if the derivative of a function within this set is
bounded by `C`, then the function is `C`-Lipschitz. Version with `fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_within_le {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F} {C : ℝ} {s : set E} {x : E} {y : E} (hf : differentiable_on ℝ f s) (bound : ∀ (x : E), x ∈ s → norm (fderiv_within ℝ f s x) ≤ C) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : norm (f y - f x) ≤ C * norm (y - x) :=
  convex.norm_image_sub_le_of_norm_has_fderiv_within_le
    (fun (x : E) (hx : x ∈ s) => differentiable_within_at.has_fderiv_within_at (hf x hx)) bound hs xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv_within` and
`lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_fderiv_within_le {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F} {C : ℝ} {s : set E} (hf : differentiable_on ℝ f s) (bound : ∀ (x : E), x ∈ s → norm (fderiv_within ℝ f s x) ≤ C) (hs : convex s) : lipschitz_on_with (nnreal.of_real C) f s :=
  convex.lipschitz_on_with_of_norm_has_fderiv_within_le
    (fun (x : E) (hx : x ∈ s) => differentiable_within_at.has_fderiv_within_at (hf x hx)) bound hs

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz. Version with `fderiv`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_le {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F} {C : ℝ} {s : set E} {x : E} {y : E} (hf : ∀ (x : E), x ∈ s → differentiable_at ℝ f x) (bound : ∀ (x : E), x ∈ s → norm (fderiv ℝ f x) ≤ C) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : norm (f y - f x) ≤ C * norm (y - x) :=
  convex.norm_image_sub_le_of_norm_has_fderiv_within_le
    (fun (x : E) (hx : x ∈ s) => has_fderiv_at.has_fderiv_within_at (differentiable_at.has_fderiv_at (hf x hx))) bound hs
    xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv` and `lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_fderiv_le {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F} {C : ℝ} {s : set E} (hf : ∀ (x : E), x ∈ s → differentiable_at ℝ f x) (bound : ∀ (x : E), x ∈ s → norm (fderiv ℝ f x) ≤ C) (hs : convex s) : lipschitz_on_with (nnreal.of_real C) f s :=
  convex.lipschitz_on_with_of_norm_has_fderiv_within_le
    (fun (x : E) (hx : x ∈ s) => has_fderiv_at.has_fderiv_within_at (differentiable_at.has_fderiv_at (hf x hx))) bound hs

/-- Variant of the mean value inequality on a convex set, using a bound on the difference between
the derivative and a fixed linear map, rather than a bound on the derivative itself. Version with
`has_fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_has_fderiv_within_le' {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F} {C : ℝ} {s : set E} {x : E} {y : E} {f' : E → continuous_linear_map ℝ E F} {φ : continuous_linear_map ℝ E F} (hf : ∀ (x : E), x ∈ s → has_fderiv_within_at f (f' x) s x) (bound : ∀ (x : E), x ∈ s → norm (f' x - φ) ≤ C) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : norm (f y - f x - coe_fn φ (y - x)) ≤ C * norm (y - x) := sorry

/-- Variant of the mean value inequality on a convex set. Version with `fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_within_le' {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F} {C : ℝ} {s : set E} {x : E} {y : E} {φ : continuous_linear_map ℝ E F} (hf : differentiable_on ℝ f s) (bound : ∀ (x : E), x ∈ s → norm (fderiv_within ℝ f s x - φ) ≤ C) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : norm (f y - f x - coe_fn φ (y - x)) ≤ C * norm (y - x) :=
  convex.norm_image_sub_le_of_norm_has_fderiv_within_le'
    (fun (x : E) (hx : x ∈ s) => differentiable_within_at.has_fderiv_within_at (hf x hx)) bound hs xs ys

/-- Variant of the mean value inequality on a convex set. Version with `fderiv`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_le' {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F} {C : ℝ} {s : set E} {x : E} {y : E} {φ : continuous_linear_map ℝ E F} (hf : ∀ (x : E), x ∈ s → differentiable_at ℝ f x) (bound : ∀ (x : E), x ∈ s → norm (fderiv ℝ f x - φ) ≤ C) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : norm (f y - f x - coe_fn φ (y - x)) ≤ C * norm (y - x) :=
  convex.norm_image_sub_le_of_norm_has_fderiv_within_le'
    (fun (x : E) (hx : x ∈ s) => has_fderiv_at.has_fderiv_within_at (differentiable_at.has_fderiv_at (hf x hx))) bound hs
    xs ys

/-- If a function has zero Fréchet derivative at every point of a convex set,
then it is a constant on this set. -/
theorem convex.is_const_of_fderiv_within_eq_zero {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2} [normed_group F] [normed_space ℝ F] {s : set E} (hs : convex s) {f : E → F} (hf : differentiable_on ℝ f s) (hf' : ∀ (x : E), x ∈ s → fderiv_within ℝ f s x = 0) {x : E} {y : E} (hx : x ∈ s) (hy : y ∈ s) : f x = f y := sorry

theorem is_const_of_fderiv_eq_zero {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F} (hf : differentiable ℝ f) (hf' : ∀ (x : E), fderiv ℝ f x = 0) (x : E) (y : E) : f x = f y := sorry

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `has_deriv_within`. -/
theorem convex.norm_image_sub_le_of_norm_has_deriv_within_le {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : ℝ → F} {f' : ℝ → F} {C : ℝ} {s : set ℝ} {x : ℝ} {y : ℝ} (hf : ∀ (x : ℝ), x ∈ s → has_deriv_within_at f (f' x) s x) (bound : ∀ (x : ℝ), x ∈ s → norm (f' x) ≤ C) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : norm (f y - f x) ≤ C * norm (y - x) := sorry

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `has_deriv_within` and `lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_has_deriv_within_le {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : ℝ → F} {f' : ℝ → F} {C : ℝ} {s : set ℝ} (hs : convex s) (hf : ∀ (x : ℝ), x ∈ s → has_deriv_within_at f (f' x) s x) (bound : ∀ (x : ℝ), x ∈ s → norm (f' x) ≤ C) : lipschitz_on_with (nnreal.of_real C) f s := sorry

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function within
this set is bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv_within` -/
theorem convex.norm_image_sub_le_of_norm_deriv_within_le {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : ℝ → F} {C : ℝ} {s : set ℝ} {x : ℝ} {y : ℝ} (hf : differentiable_on ℝ f s) (bound : ∀ (x : ℝ), x ∈ s → norm (deriv_within f s x) ≤ C) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : norm (f y - f x) ≤ C * norm (y - x) :=
  convex.norm_image_sub_le_of_norm_has_deriv_within_le
    (fun (x : ℝ) (hx : x ∈ s) => differentiable_within_at.has_deriv_within_at (hf x hx)) bound hs xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv_within` and `lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_deriv_within_le {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : ℝ → F} {C : ℝ} {s : set ℝ} (hs : convex s) (hf : differentiable_on ℝ f s) (bound : ∀ (x : ℝ), x ∈ s → norm (deriv_within f s x) ≤ C) : lipschitz_on_with (nnreal.of_real C) f s :=
  convex.lipschitz_on_with_of_norm_has_deriv_within_le hs
    (fun (x : ℝ) (hx : x ∈ s) => differentiable_within_at.has_deriv_within_at (hf x hx)) bound

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv`. -/
theorem convex.norm_image_sub_le_of_norm_deriv_le {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : ℝ → F} {C : ℝ} {s : set ℝ} {x : ℝ} {y : ℝ} (hf : ∀ (x : ℝ), x ∈ s → differentiable_at ℝ f x) (bound : ∀ (x : ℝ), x ∈ s → norm (deriv f x) ≤ C) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : norm (f y - f x) ≤ C * norm (y - x) :=
  convex.norm_image_sub_le_of_norm_has_deriv_within_le
    (fun (x : ℝ) (hx : x ∈ s) => has_deriv_at.has_deriv_within_at (differentiable_at.has_deriv_at (hf x hx))) bound hs xs
    ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv` and `lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_deriv_le {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : ℝ → F} {C : ℝ} {s : set ℝ} (hf : ∀ (x : ℝ), x ∈ s → differentiable_at ℝ f x) (bound : ∀ (x : ℝ), x ∈ s → norm (deriv f x) ≤ C) (hs : convex s) : lipschitz_on_with (nnreal.of_real C) f s :=
  convex.lipschitz_on_with_of_norm_has_deriv_within_le hs
    (fun (x : ℝ) (hx : x ∈ s) => has_deriv_at.has_deriv_within_at (differentiable_at.has_deriv_at (hf x hx))) bound

/-! ### Functions `[a, b] → ℝ`. -/

-- Declare all variables here to make sure they come in a correct order

/-- Cauchy's Mean Value Theorem, `has_deriv_at` version. -/
theorem exists_ratio_has_deriv_at_eq_ratio_slope (f : ℝ → ℝ) (f' : ℝ → ℝ) {a : ℝ} {b : ℝ} (hab : a < b) (hfc : continuous_on f (set.Icc a b)) (hff' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at f (f' x) x) (g : ℝ → ℝ) (g' : ℝ → ℝ) (hgc : continuous_on g (set.Icc a b)) (hgg' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at g (g' x) x) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), (g b - g a) * f' c = (f b - f a) * g' c := sorry

/-- Cauchy's Mean Value Theorem, extended `has_deriv_at` version. -/
theorem exists_ratio_has_deriv_at_eq_ratio_slope' (f : ℝ → ℝ) (f' : ℝ → ℝ) {a : ℝ} {b : ℝ} (hab : a < b) (g : ℝ → ℝ) (g' : ℝ → ℝ) {lfa : ℝ} {lga : ℝ} {lfb : ℝ} {lgb : ℝ} (hff' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at f (f' x) x) (hgg' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at g (g' x) x) (hfa : filter.tendsto f (nhds_within a (set.Ioi a)) (nhds lfa)) (hga : filter.tendsto g (nhds_within a (set.Ioi a)) (nhds lga)) (hfb : filter.tendsto f (nhds_within b (set.Iio b)) (nhds lfb)) (hgb : filter.tendsto g (nhds_within b (set.Iio b)) (nhds lgb)) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), (lgb - lga) * f' c = (lfb - lfa) * g' c := sorry

/-- Lagrange's Mean Value Theorem, `has_deriv_at` version -/
theorem exists_has_deriv_at_eq_slope (f : ℝ → ℝ) (f' : ℝ → ℝ) {a : ℝ} {b : ℝ} (hab : a < b) (hfc : continuous_on f (set.Icc a b)) (hff' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at f (f' x) x) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), f' c = (f b - f a) / (b - a) := sorry

/-- Cauchy's Mean Value Theorem, `deriv` version. -/
theorem exists_ratio_deriv_eq_ratio_slope (f : ℝ → ℝ) {a : ℝ} {b : ℝ} (hab : a < b) (hfc : continuous_on f (set.Icc a b)) (hfd : differentiable_on ℝ f (set.Ioo a b)) (g : ℝ → ℝ) (hgc : continuous_on g (set.Icc a b)) (hgd : differentiable_on ℝ g (set.Ioo a b)) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), (g b - g a) * deriv f c = (f b - f a) * deriv g c := sorry

/-- Cauchy's Mean Value Theorem, extended `deriv` version. -/
theorem exists_ratio_deriv_eq_ratio_slope' (f : ℝ → ℝ) {a : ℝ} {b : ℝ} (hab : a < b) (g : ℝ → ℝ) {lfa : ℝ} {lga : ℝ} {lfb : ℝ} {lgb : ℝ} (hdf : differentiable_on ℝ f (set.Ioo a b)) (hdg : differentiable_on ℝ g (set.Ioo a b)) (hfa : filter.tendsto f (nhds_within a (set.Ioi a)) (nhds lfa)) (hga : filter.tendsto g (nhds_within a (set.Ioi a)) (nhds lga)) (hfb : filter.tendsto f (nhds_within b (set.Iio b)) (nhds lfb)) (hgb : filter.tendsto g (nhds_within b (set.Iio b)) (nhds lgb)) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), (lgb - lga) * deriv f c = (lfb - lfa) * deriv g c := sorry

/-- Lagrange's Mean Value Theorem, `deriv` version. -/
theorem exists_deriv_eq_slope (f : ℝ → ℝ) {a : ℝ} {b : ℝ} (hab : a < b) (hfc : continuous_on f (set.Icc a b)) (hfd : differentiable_on ℝ f (set.Ioo a b)) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), deriv f c = (f b - f a) / (b - a) := sorry

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C < f'`, then
`f` grows faster than `C * x` on `D`, i.e., `C * (y - x) < f y - f x` whenever `x, y ∈ D`,
`x < y`. -/
theorem convex.mul_sub_lt_image_sub_of_lt_deriv {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) {C : ℝ} (hf'_gt : ∀ (x : ℝ), x ∈ interior D → C < deriv f x) (x : ℝ) (y : ℝ) (H : x ∈ D) : y ∈ D → x < y → C * (y - x) < f y - f x := sorry

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C < f'`, then `f` grows faster than
`C * x`, i.e., `C * (y - x) < f y - f x` whenever `x < y`. -/
theorem mul_sub_lt_image_sub_of_lt_deriv {f : ℝ → ℝ} (hf : differentiable ℝ f) {C : ℝ} (hf'_gt : ∀ (x : ℝ), C < deriv f x) {x : ℝ} {y : ℝ} (hxy : x < y) : C * (y - x) < f y - f x :=
  convex.mul_sub_lt_image_sub_of_lt_deriv convex_univ (continuous.continuous_on (differentiable.continuous hf))
    (differentiable.differentiable_on hf) (fun (x : ℝ) (_x : x ∈ interior set.univ) => hf'_gt x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C ≤ f'`, then
`f` grows at least as fast as `C * x` on `D`, i.e., `C * (y - x) ≤ f y - f x` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem convex.mul_sub_le_image_sub_of_le_deriv {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) {C : ℝ} (hf'_ge : ∀ (x : ℝ), x ∈ interior D → C ≤ deriv f x) (x : ℝ) (y : ℝ) (H : x ∈ D) : y ∈ D → x ≤ y → C * (y - x) ≤ f y - f x := sorry

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C ≤ f'`, then `f` grows at least as fast
as `C * x`, i.e., `C * (y - x) ≤ f y - f x` whenever `x ≤ y`. -/
theorem mul_sub_le_image_sub_of_le_deriv {f : ℝ → ℝ} (hf : differentiable ℝ f) {C : ℝ} (hf'_ge : ∀ (x : ℝ), C ≤ deriv f x) {x : ℝ} {y : ℝ} (hxy : x ≤ y) : C * (y - x) ≤ f y - f x :=
  convex.mul_sub_le_image_sub_of_le_deriv convex_univ (continuous.continuous_on (differentiable.continuous hf))
    (differentiable.differentiable_on hf) (fun (x : ℝ) (_x : x ∈ interior set.univ) => hf'_ge x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' < C`, then
`f` grows slower than `C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x, y ∈ D`,
`x < y`. -/
theorem convex.image_sub_lt_mul_sub_of_deriv_lt {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) {C : ℝ} (lt_hf' : ∀ (x : ℝ), x ∈ interior D → deriv f x < C) (x : ℝ) (y : ℝ) (H : x ∈ D) : y ∈ D → x < y → f y - f x < C * (y - x) := sorry

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' < C`, then `f` grows slower than
`C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x < y`. -/
theorem image_sub_lt_mul_sub_of_deriv_lt {f : ℝ → ℝ} (hf : differentiable ℝ f) {C : ℝ} (lt_hf' : ∀ (x : ℝ), deriv f x < C) {x : ℝ} {y : ℝ} (hxy : x < y) : f y - f x < C * (y - x) :=
  convex.image_sub_lt_mul_sub_of_deriv_lt convex_univ (continuous.continuous_on (differentiable.continuous hf))
    (differentiable.differentiable_on hf) (fun (x : ℝ) (_x : x ∈ interior set.univ) => lt_hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' ≤ C`, then
`f` grows at most as fast as `C * x` on `D`, i.e., `f y - f x ≤ C * (y - x)` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem convex.image_sub_le_mul_sub_of_deriv_le {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) {C : ℝ} (le_hf' : ∀ (x : ℝ), x ∈ interior D → deriv f x ≤ C) (x : ℝ) (y : ℝ) (H : x ∈ D) : y ∈ D → x ≤ y → f y - f x ≤ C * (y - x) := sorry

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' ≤ C`, then `f` grows at most as fast
as `C * x`, i.e., `f y - f x ≤ C * (y - x)` whenever `x ≤ y`. -/
theorem image_sub_le_mul_sub_of_deriv_le {f : ℝ → ℝ} (hf : differentiable ℝ f) {C : ℝ} (le_hf' : ∀ (x : ℝ), deriv f x ≤ C) {x : ℝ} {y : ℝ} (hxy : x ≤ y) : f y - f x ≤ C * (y - x) :=
  convex.image_sub_le_mul_sub_of_deriv_le convex_univ (continuous.continuous_on (differentiable.continuous hf))
    (differentiable.differentiable_on hf) (fun (x : ℝ) (_x : x ∈ interior set.univ) => le_hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is positive, then
`f` is a strictly monotonically increasing function on `D`. -/
theorem convex.strict_mono_of_deriv_pos {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) (hf'_pos : ∀ (x : ℝ), x ∈ interior D → 0 < deriv f x) (x : ℝ) (y : ℝ) (H : x ∈ D) : y ∈ D → x < y → f x < f y := sorry

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is positive, then
`f` is a strictly monotonically increasing function. -/
theorem strict_mono_of_deriv_pos {f : ℝ → ℝ} (hf : differentiable ℝ f) (hf'_pos : ∀ (x : ℝ), 0 < deriv f x) : strict_mono f := sorry

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonnegative, then
`f` is a monotonically increasing function on `D`. -/
theorem convex.mono_of_deriv_nonneg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) (hf'_nonneg : ∀ (x : ℝ), x ∈ interior D → 0 ≤ deriv f x) (x : ℝ) (y : ℝ) (H : x ∈ D) : y ∈ D → x ≤ y → f x ≤ f y := sorry

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotonically increasing function. -/
theorem mono_of_deriv_nonneg {f : ℝ → ℝ} (hf : differentiable ℝ f) (hf' : ∀ (x : ℝ), 0 ≤ deriv f x) : monotone f :=
  fun (x y : ℝ) (hxy : x ≤ y) =>
    convex.mono_of_deriv_nonneg convex_univ (continuous.continuous_on (differentiable.continuous hf))
      (differentiable.differentiable_on hf) (fun (x : ℝ) (_x : x ∈ interior set.univ) => hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is negative, then
`f` is a strictly monotonically decreasing function on `D`. -/
theorem convex.strict_antimono_of_deriv_neg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) (hf'_neg : ∀ (x : ℝ), x ∈ interior D → deriv f x < 0) (x : ℝ) (y : ℝ) (H : x ∈ D) : y ∈ D → x < y → f y < f x := sorry

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is negative, then
`f` is a strictly monotonically decreasing function. -/
theorem strict_antimono_of_deriv_neg {f : ℝ → ℝ} (hf : differentiable ℝ f) (hf' : ∀ (x : ℝ), deriv f x < 0) {x : ℝ} {y : ℝ} : x < y → f y < f x :=
  fun (hxy : x < y) =>
    convex.strict_antimono_of_deriv_neg convex_univ (continuous.continuous_on (differentiable.continuous hf))
      (differentiable.differentiable_on hf) (fun (x : ℝ) (_x : x ∈ interior set.univ) => hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonpositive, then
`f` is a monotonically decreasing function on `D`. -/
theorem convex.antimono_of_deriv_nonpos {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) (hf'_nonpos : ∀ (x : ℝ), x ∈ interior D → deriv f x ≤ 0) (x : ℝ) (y : ℝ) (H : x ∈ D) : y ∈ D → x ≤ y → f y ≤ f x := sorry

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then
`f` is a monotonically decreasing function. -/
theorem antimono_of_deriv_nonpos {f : ℝ → ℝ} (hf : differentiable ℝ f) (hf' : ∀ (x : ℝ), deriv f x ≤ 0) {x : ℝ} {y : ℝ} : x ≤ y → f y ≤ f x :=
  fun (hxy : x ≤ y) =>
    convex.antimono_of_deriv_nonpos convex_univ (continuous.continuous_on (differentiable.continuous hf))
      (differentiable.differentiable_on hf) (fun (x : ℝ) (_x : x ∈ interior set.univ) => hf' x) x y trivial trivial hxy

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is monotone on the interior, then `f` is convex on `D`. -/
theorem convex_on_of_deriv_mono {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) (hf'_mono : ∀ (x y : ℝ), x ∈ interior D → y ∈ interior D → x ≤ y → deriv f x ≤ deriv f y) : convex_on D f := sorry

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is antimonotone on the interior, then `f` is concave on `D`. -/
theorem concave_on_of_deriv_antimono {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) (hf'_mono : ∀ (x y : ℝ), x ∈ interior D → y ∈ interior D → x ≤ y → deriv f y ≤ deriv f x) : concave_on D f := sorry

/-- If a function `f` is differentiable and `f'` is monotone on `ℝ` then `f` is convex. -/
theorem convex_on_univ_of_deriv_mono {f : ℝ → ℝ} (hf : differentiable ℝ f) (hf'_mono : monotone (deriv f)) : convex_on set.univ f :=
  convex_on_of_deriv_mono convex_univ (continuous.continuous_on (differentiable.continuous hf))
    (differentiable.differentiable_on hf)
    fun (x y : ℝ) (_x : x ∈ interior set.univ) (_x : y ∈ interior set.univ) (h : x ≤ y) => hf'_mono h

/-- If a function `f` is differentiable and `f'` is antimonotone on `ℝ` then `f` is concave. -/
theorem concave_on_univ_of_deriv_antimono {f : ℝ → ℝ} (hf : differentiable ℝ f) (hf'_antimono : ∀ {a b : ℝ}, a ≤ b → deriv f b ≤ deriv f a) : concave_on set.univ f :=
  concave_on_of_deriv_antimono convex_univ (continuous.continuous_on (differentiable.continuous hf))
    (differentiable.differentiable_on hf)
    fun (x y : ℝ) (_x : x ∈ interior set.univ) (_x : y ∈ interior set.univ) (h : x ≤ y) => hf'_antimono h

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
theorem convex_on_of_deriv2_nonneg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) (hf'' : differentiable_on ℝ (deriv f) (interior D)) (hf''_nonneg : ∀ (x : ℝ), x ∈ interior D → 0 ≤ nat.iterate deriv (bit0 1) f x) : convex_on D f := sorry

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
theorem concave_on_of_deriv2_nonpos {D : set ℝ} (hD : convex D) {f : ℝ → ℝ} (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D)) (hf'' : differentiable_on ℝ (deriv f) (interior D)) (hf''_nonpos : ∀ (x : ℝ), x ∈ interior D → nat.iterate deriv (bit0 1) f x ≤ 0) : concave_on D f := sorry

/-- If a function `f` is twice differentiable on a open convex set `D ⊆ ℝ` and
`f''` is nonnegative on `D`, then `f` is convex on `D`. -/
theorem convex_on_open_of_deriv2_nonneg {D : set ℝ} (hD : convex D) (hD₂ : is_open D) {f : ℝ → ℝ} (hf' : differentiable_on ℝ f D) (hf'' : differentiable_on ℝ (deriv f) D) (hf''_nonneg : ∀ (x : ℝ), x ∈ D → 0 ≤ nat.iterate deriv (bit0 1) f x) : convex_on D f := sorry

/-- If a function `f` is twice differentiable on a open convex set `D ⊆ ℝ` and
`f''` is nonpositive on `D`, then `f` is concave on `D`. -/
theorem concave_on_open_of_deriv2_nonpos {D : set ℝ} (hD : convex D) (hD₂ : is_open D) {f : ℝ → ℝ} (hf' : differentiable_on ℝ f D) (hf'' : differentiable_on ℝ (deriv f) D) (hf''_nonpos : ∀ (x : ℝ), x ∈ D → nat.iterate deriv (bit0 1) f x ≤ 0) : concave_on D f := sorry

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonnegative on `ℝ`,
then `f` is convex on `ℝ`. -/
theorem convex_on_univ_of_deriv2_nonneg {f : ℝ → ℝ} (hf' : differentiable ℝ f) (hf'' : differentiable ℝ (deriv f)) (hf''_nonneg : ∀ (x : ℝ), 0 ≤ nat.iterate deriv (bit0 1) f x) : convex_on set.univ f :=
  convex_on_open_of_deriv2_nonneg convex_univ is_open_univ (differentiable.differentiable_on hf')
    (differentiable.differentiable_on hf'') fun (x : ℝ) (_x : x ∈ set.univ) => hf''_nonneg x

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonpositive on `ℝ`,
then `f` is concave on `ℝ`. -/
theorem concave_on_univ_of_deriv2_nonpos {f : ℝ → ℝ} (hf' : differentiable ℝ f) (hf'' : differentiable ℝ (deriv f)) (hf''_nonpos : ∀ (x : ℝ), nat.iterate deriv (bit0 1) f x ≤ 0) : concave_on set.univ f :=
  concave_on_open_of_deriv2_nonpos convex_univ is_open_univ (differentiable.differentiable_on hf')
    (differentiable.differentiable_on hf'') fun (x : ℝ) (_x : x ∈ set.univ) => hf''_nonpos x

/-! ### Functions `f : E → ℝ` -/

/-- Lagrange's Mean Value Theorem, applied to convex domains. -/
theorem domain_mvt {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} {x : E} {y : E} {f' : E → continuous_linear_map ℝ E ℝ} (hf : ∀ (x : E), x ∈ s → has_fderiv_within_at f (f' x) s x) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∃ (z : E), ∃ (H : z ∈ segment x y), f y - f x = coe_fn (f' z) (y - x) := sorry

-- parametrize segment

-- derivative of pullback of f under parametrization

-- apply 1-variable mean value theorem to pullback

-- reinterpret on domain

/-!
### Vector-valued functions `f : E → F`.  Strict differentiability.

A `C^1` function is strictly differentiable, when the field is `ℝ` or `ℂ`. This follows from the
mean value inequality on balls, which is a particular case of the above results after restricting
the scalars to `ℝ`. Note that it does not make sense to talk of a convex set over `ℂ`, but balls
make sense and are enough. Many formulations of the mean value inequality could be generalized to
balls over `ℝ` or `ℂ`. For now, we only include the ones that we need.
-/

/-- Variant of the mean value inequality over `ℝ` or `ℂ`, on a ball, using a bound on the difference
between the derivative and a fixed linear map, rather than a bound on the derivative itself.
Version with `has_fderiv_within`. -/
theorem is_R_or_C.norm_image_sub_le_of_norm_has_fderiv_within_le' {𝕜 : Type u_3} [is_R_or_C 𝕜] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {H : Type u_5} [normed_group H] [normed_space 𝕜 H] {f : G → H} {C : ℝ} {x : G} {y : G} {z : G} {r : ℝ} {f' : G → continuous_linear_map 𝕜 G H} {φ : continuous_linear_map 𝕜 G H} (hf : ∀ (x : G), x ∈ metric.ball z r → has_fderiv_within_at f (f' x) (metric.ball z r) x) (bound : ∀ (x : G), x ∈ metric.ball z r → norm (f' x - φ) ≤ C) (xs : x ∈ metric.ball z r) (ys : y ∈ metric.ball z r) : norm (f y - f x - coe_fn φ (y - x)) ≤ C * norm (y - x) := sorry

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
theorem strict_fderiv_of_cont_diff {𝕜 : Type u_3} [is_R_or_C 𝕜] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {H : Type u_5} [normed_group H] [normed_space 𝕜 H] {f : G → H} {s : set G} {x : G} {f' : G → continuous_linear_map 𝕜 G H} (hf : ∀ (x : G), x ∈ s → has_fderiv_within_at f (f' x) s x) (hcont : continuous_on f' s) (hs : s ∈ nhds x) : has_strict_fderiv_at f (f' x) x := sorry

