/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.finite_dimension
import Mathlib.data.complex.module
import Mathlib.data.complex.is_R_or_C
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Normed space structure on `ℂ`.

This file gathers basic facts on complex numbers of an analytic nature.

## Main results

This file registers `ℂ` as a normed field, expresses basic properties of the norm, and gives
tools on the real vector space structure of `ℂ`. Notably, in the namespace `complex`,
it defines functions:

* `continuous_linear_map.re`
* `continuous_linear_map.im`
* `continuous_linear_map.of_real`

They are bundled versions of the real part, the imaginary part, and the embedding of `ℝ` in `ℂ`,
as continuous `ℝ`-linear maps.

We also register the fact that `ℂ` is an `is_R_or_C` field.
-/

namespace complex


protected instance has_norm : has_norm ℂ :=
  has_norm.mk abs

protected instance normed_group : normed_group ℂ :=
  normed_group.of_core ℂ sorry

protected instance normed_field : normed_field ℂ :=
  normed_field.mk sorry abs_mul

protected instance nondiscrete_normed_field : nondiscrete_normed_field ℂ :=
  nondiscrete_normed_field.mk sorry

protected instance normed_algebra_over_reals : normed_algebra ℝ ℂ :=
  normed_algebra.mk abs_of_real

@[simp] theorem norm_eq_abs (z : ℂ) : norm z = abs z :=
  rfl

theorem dist_eq (z : ℂ) (w : ℂ) : dist z w = abs (z - w) :=
  rfl

@[simp] theorem norm_real (r : ℝ) : norm ↑r = norm r :=
  abs_of_real r

@[simp] theorem norm_rat (r : ℚ) : norm ↑r = abs ↑r := sorry

@[simp] theorem norm_nat (n : ℕ) : norm ↑n = ↑n :=
  abs_of_nat n

@[simp] theorem norm_int {n : ℤ} : norm ↑n = abs ↑n := sorry

theorem norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : norm ↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (norm ↑n = ↑n)) norm_int))
    (eq.mpr (id (Eq._oldrec (Eq.refl (abs ↑n = ↑n)) (abs_of_nonneg (iff.mpr int.cast_nonneg hn)))) (Eq.refl ↑n))

/-- A complex normed vector space is also a real normed vector space. -/
protected instance normed_space.restrict_scalars_real (E : Type u_1) [normed_group E] [normed_space ℂ E] : normed_space ℝ E :=
  normed_space.restrict_scalars ℝ ℂ E

/-- The space of continuous linear maps over `ℝ`, from a real vector space to a complex vector
space, is a normed vector space over `ℂ`. -/
protected instance continuous_linear_map.real_smul_complex (E : Type u_1) [normed_group E] [normed_space ℝ E] (F : Type u_2) [normed_group F] [normed_space ℂ F] : normed_space ℂ (continuous_linear_map ℝ E F) :=
  continuous_linear_map.normed_space_extend_scalars

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def continuous_linear_map.re : continuous_linear_map ℝ ℂ ℝ :=
  linear_map.to_continuous_linear_map linear_map.re

@[simp] theorem continuous_linear_map.re_coe : ↑continuous_linear_map.re = linear_map.re :=
  rfl

@[simp] theorem continuous_linear_map.re_apply (z : ℂ) : coe_fn continuous_linear_map.re z = re z :=
  rfl

@[simp] theorem continuous_linear_map.re_norm : norm continuous_linear_map.re = 1 := sorry

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def continuous_linear_map.im : continuous_linear_map ℝ ℂ ℝ :=
  linear_map.to_continuous_linear_map linear_map.im

@[simp] theorem continuous_linear_map.im_coe : ↑continuous_linear_map.im = linear_map.im :=
  rfl

@[simp] theorem continuous_linear_map.im_apply (z : ℂ) : coe_fn continuous_linear_map.im z = im z :=
  rfl

@[simp] theorem continuous_linear_map.im_norm : norm continuous_linear_map.im = 1 := sorry

/-- Linear isometry version of the canonical embedding of `ℝ` in `ℂ`. -/
def linear_isometry.of_real : linear_isometry ℝ ℝ ℂ :=
  linear_isometry.mk linear_map.of_real sorry

/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def continuous_linear_map.of_real : continuous_linear_map ℝ ℝ ℂ :=
  linear_isometry.to_continuous_linear_map linear_isometry.of_real

theorem isometry_of_real : isometry coe :=
  linear_isometry.isometry linear_isometry.of_real

theorem continuous_of_real : continuous coe :=
  isometry.continuous isometry_of_real

@[simp] theorem continuous_linear_map.of_real_coe : ↑continuous_linear_map.of_real = linear_map.of_real :=
  rfl

@[simp] theorem continuous_linear_map.of_real_apply (x : ℝ) : coe_fn continuous_linear_map.of_real x = ↑x :=
  rfl

@[simp] theorem continuous_linear_map.of_real_norm : norm continuous_linear_map.of_real = 1 :=
  linear_isometry.norm_to_continuous_linear_map linear_isometry.of_real

protected instance is_R_or_C : is_R_or_C ℂ :=
  is_R_or_C.mk (add_monoid_hom.mk re zero_re add_re) (add_monoid_hom.mk im zero_im add_im) conj I sorry sorry sorry sorry
    sorry sorry sorry sorry sorry sorry sorry sorry sorry div_I

end complex


namespace is_R_or_C


@[simp] theorem re_to_complex {x : ℂ} : coe_fn re x = complex.re x :=
  rfl

@[simp] theorem im_to_complex {x : ℂ} : coe_fn im x = complex.im x :=
  rfl

@[simp] theorem conj_to_complex {x : ℂ} : coe_fn conj x = coe_fn complex.conj x :=
  rfl

@[simp] theorem I_to_complex : I = complex.I :=
  rfl

@[simp] theorem norm_sq_to_complex {x : ℂ} : coe_fn norm_sq x = coe_fn complex.norm_sq x := sorry

@[simp] theorem abs_to_complex {x : ℂ} : abs x = complex.abs x := sorry

