/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.calculus.deriv
import Mathlib.measure_theory.borel_space
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Derivative is measurable

In this file we prove that the derivative of any function with complete codomain is a measurable
function. Namely, we prove:

* `is_measurable_set_of_differentiable_at`: the set `{x | differentiable_at 𝕜 f x}` is measurable;
* `measurable_fderiv`: the function `fderiv 𝕜 f` is measurable;
* `measurable_fderiv_apply_const`: for a fixed vector `y`, the function `λ x, fderiv 𝕜 f x y`
  is measurable;
* `measurable_deriv`: the function `deriv f` is measurable (for `f : 𝕜 → F`).

## Implementation

We give a proof that avoids second-countability issues, by expressing the differentiability set
as a function of open sets in the following way. Define `A (L, r, ε)` to be the set of points
where, on a ball of radius roughly `r` around `x`, the function is uniformly approximated by the
linear map `L`, up to `ε r`. It is an open set.
Let also `B (L, r, s, ε) = A (L, r, ε) ∩ A (L, s, ε)`: we require that at two possibly different
scales `r` and `s`, the function is well approximated by the linear map `L`. It is also open.

We claim that the differentiability set of `f` is exactly
`D = ⋂ ε > 0, ⋃ δ > 0, ⋂ r, s < δ, ⋃ L, B (L, r, s, ε)`.
In other words, for any `ε > 0`, we require that there is a size `δ` such that, for any two scales
below this size, the function is well approximated by a linear map, common to the two scales.

The set `⋃ L, B (L, r, s, ε)` is open, as a union of open sets. Converting the intersections and
unions to countable ones (using real numbers of the form `2 ^ (-n)`), it follows that the
differentiability set is measurable.

To prove the claim, there are two inclusions. One is trivial: if the function is differentiable
at `x`, then `x` belongs to `D` (just take `L` to be the derivative, and use that the
differentiability exactly says that the map is well approximated by `L`). This is proved in
`mem_A_of_differentiable` and `differentiable_set_subset_D`.

For the other direction, the difficulty is that `L` in the union may depend on `ε, r, s`. The key
point is that, in fact, it doesn't depend too much on them. First, if `x` belongs both to
`A (L, r, ε)` and `A (L', r, ε)`, then `L` and `L'` have to be close on a shell, and thus
`∥L - L'∥` is bounded by `ε` (see `norm_sub_le_of_mem_A`). Assume now `x ∈ D`. If one has two maps
`L` and `L'` such that `x` belongs to `A (L, r, ε)` and to `A (L', r', ε')`, one deduces that `L` is
close to `L'` by arguing as follows. Consider another scale `s` smaller than `r` and `r'`. Take a
linear map `L₁` that approximates `f` around `x` both at scales `r` and `s` w.r.t. `ε` (it exists as
`x` belongs to `D`). Take also `L₂` that approximates `f` around `x` both at scales `r'` and `s`
w.r.t. `ε'`. Then `L₁` is close to `L` (as they are close on a shell of radius `r`), and `L₂` is
close to `L₁` (as they are close on a shell of radius `s`), and `L'` is close to `L₂` (as they are
close on a shell of radius `r'`). It follows that `L` is close to `L'`, as we claimed.

It follows that the different approximating linear maps that show up form a Cauchy sequence when
`ε` tends to `0`. When the target space is complete, this sequence converges, to a limit `f'`.
With the same kind of arguments, one checks that `f` is differentiable with derivative `f'`.

To show that the derivative itself is measurable, add in the definition of `B` and `D` a set
`K` of continuous linear maps to which `L` should belong. Then, when `K` is complete, the set `D K`
is exactly the set of points where `f` is differentiable with a derivative in `K`.

## Tags

derivative, measurable function, Borel σ-algebra
-/

namespace continuous_linear_map


protected instance measurable_space {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F] : measurable_space (continuous_linear_map 𝕜 E F) :=
  borel (continuous_linear_map 𝕜 E F)

protected instance borel_space {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F] : borel_space (continuous_linear_map 𝕜 E F) :=
  borel_space.mk rfl

theorem measurable_apply {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F] [measurable_space F] [borel_space F] (x : E) : measurable fun (f : continuous_linear_map 𝕜 E F) => coe_fn f x :=
  continuous.measurable (continuous_linear_map.continuous (apply 𝕜 F x))

theorem measurable_apply' {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F] [measurable_space E] [opens_measurable_space E] [measurable_space F] [borel_space F] : measurable fun (x : E) (f : continuous_linear_map 𝕜 E F) => coe_fn f x :=
  measurable_pi_lambda (fun (x : E) (f : continuous_linear_map 𝕜 E F) => coe_fn f x)
    fun (f : continuous_linear_map 𝕜 E F) => continuous_linear_map.measurable f

theorem measurable_apply₂ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F] [measurable_space E] [opens_measurable_space E] [topological_space.second_countable_topology E] [topological_space.second_countable_topology (continuous_linear_map 𝕜 E F)] [measurable_space F] [borel_space F] : measurable fun (p : continuous_linear_map 𝕜 E F × E) => coe_fn (prod.fst p) (prod.snd p) :=
  continuous.measurable (is_bounded_bilinear_map.continuous is_bounded_bilinear_map_apply)

theorem measurable_coe {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F] [measurable_space F] [borel_space F] : measurable fun (f : continuous_linear_map 𝕜 E F) (x : E) => coe_fn f x :=
  measurable_pi_lambda (fun (f : continuous_linear_map 𝕜 E F) (x : E) => coe_fn f x) measurable_apply

end continuous_linear_map


namespace fderiv_measurable_aux


/-- The set `A f L r ε` is the set of points `x` around which the function `f` is well approximated
at scale `r` by the linear map `L`, up to an error `ε`. We tweak the definition to make sure that
this is an open set.-/
def A {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (L : continuous_linear_map 𝕜 E F) (r : ℝ) (ε : ℝ) : set E :=
  set_of
    fun (x : E) =>
      ∃ (r' : ℝ),
        ∃ (H : r' ∈ set.Ioc (r / bit0 1) r),
          ∀ (y z : E), y ∈ metric.ball x r' → z ∈ metric.ball x r' → norm (f z - f y - coe_fn L (z - y)) ≤ ε * r

/-- The set `B f K r s ε` is the set of points `x` around which there exists a continuous linear map
`L` belonging to `K` (a given set of continuous linear maps) that approximates well the
function `f` (up to an error `ε`), simultaneously at scales `r` and `s`. -/
def B {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (K : set (continuous_linear_map 𝕜 E F)) (r : ℝ) (s : ℝ) (ε : ℝ) : set E :=
  set.Union fun (L : continuous_linear_map 𝕜 E F) => set.Union fun (H : L ∈ K) => A f L r ε ∩ A f L s ε

/-- The set `D f K` is a complicated set constructed using countable intersections and unions. Its
main use is that, when `K` is complete, it is exactly the set of points where `f` is differentiable,
with a derivative in `K`. -/
def D {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (K : set (continuous_linear_map 𝕜 E F)) : set E :=
  set.Inter
    fun (e : ℕ) =>
      set.Union
        fun (n : ℕ) =>
          set.Inter
            fun (p : ℕ) =>
              set.Inter
                fun (H : p ≥ n) =>
                  set.Inter
                    fun (q : ℕ) =>
                      set.Inter fun (H : q ≥ n) => B f K ((1 / bit0 1) ^ p) ((1 / bit0 1) ^ q) ((1 / bit0 1) ^ e)

theorem is_open_A {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (L : continuous_linear_map 𝕜 E F) (r : ℝ) (ε : ℝ) : is_open (A f L r ε) := sorry

theorem is_open_B {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {K : set (continuous_linear_map 𝕜 E F)} {r : ℝ} {s : ℝ} {ε : ℝ} : is_open (B f K r s ε) := sorry

theorem A_mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (L : continuous_linear_map 𝕜 E F) (r : ℝ) {ε : ℝ} {δ : ℝ} (h : ε ≤ δ) : A f L r ε ⊆ A f L r δ := sorry

theorem le_of_mem_A {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {r : ℝ} {ε : ℝ} {L : continuous_linear_map 𝕜 E F} {x : E} (hx : x ∈ A f L r ε) {y : E} {z : E} (hy : y ∈ metric.closed_ball x (r / bit0 1)) (hz : z ∈ metric.closed_ball x (r / bit0 1)) : norm (f z - f y - coe_fn L (z - y)) ≤ ε * r := sorry

theorem mem_A_of_differentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {ε : ℝ} (hε : 0 < ε) {x : E} (hx : differentiable_at 𝕜 f x) : ∃ (R : ℝ), ∃ (H : R > 0), ∀ (r : ℝ), r ∈ set.Ioo 0 R → x ∈ A f (fderiv 𝕜 f x) r ε := sorry

theorem norm_sub_le_of_mem_A {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {c : 𝕜} (hc : 1 < norm c) {r : ℝ} {ε : ℝ} (hε : 0 < ε) (hr : 0 < r) {x : E} {L₁ : continuous_linear_map 𝕜 E F} {L₂ : continuous_linear_map 𝕜 E F} (h₁ : x ∈ A f L₁ r ε) (h₂ : x ∈ A f L₂ r ε) : norm (L₁ - L₂) ≤ bit0 (bit0 1) * norm c * ε := sorry

/-- Easy inclusion: a differentiability point with derivative in `K` belongs to `D f K`. -/
theorem differentiable_set_subset_D {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (K : set (continuous_linear_map 𝕜 E F)) : (set_of fun (x : E) => differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ K) ⊆ D f K := sorry

/-- Harder inclusion: at a point in `D f K`, the function `f` has a derivative, in `K`. -/
