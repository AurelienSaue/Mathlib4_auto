/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.analytic.basic
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Linear functions are analytic

In this file we prove that a `continuous_linear_map` defines an analytic function with
the formal power series `f x = f a + f (x - a)`.
-/

namespace continuous_linear_map


/-- Formal power series of a continuous linear map `f : E →L[𝕜] F` at `x : E`:
`f y = f x + f (y - x)`. -/
@[simp] def fpower_series {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : continuous_linear_map 𝕜 E F) (x : E) : formal_multilinear_series 𝕜 E F :=
  sorry

@[simp] theorem fpower_series_apply_add_two {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : continuous_linear_map 𝕜 E F) (x : E) (n : ℕ) : fpower_series f x (n + bit0 1) = 0 :=
  rfl

@[simp] theorem fpower_series_radius {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : continuous_linear_map 𝕜 E F) (x : E) : formal_multilinear_series.radius (fpower_series f x) = ⊤ :=
  formal_multilinear_series.radius_eq_top_of_forall_image_add_eq_zero (fpower_series f x) (bit0 1) fun (n : ℕ) => rfl

protected theorem has_fpower_series_on_ball {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : continuous_linear_map 𝕜 E F) (x : E) : has_fpower_series_on_ball (⇑f) (fpower_series f x) x ⊤ := sorry

protected theorem has_fpower_series_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : continuous_linear_map 𝕜 E F) (x : E) : has_fpower_series_at (⇑f) (fpower_series f x) x :=
  Exists.intro ⊤ (continuous_linear_map.has_fpower_series_on_ball f x)

protected theorem analytic_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : continuous_linear_map 𝕜 E F) (x : E) : analytic_at 𝕜 (⇑f) x :=
  has_fpower_series_at.analytic_at (continuous_linear_map.has_fpower_series_at f x)

