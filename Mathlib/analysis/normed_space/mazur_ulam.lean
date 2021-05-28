/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.instances.real_vector_space
import Mathlib.analysis.normed_space.add_torsor
import Mathlib.linear_algebra.affine_space.midpoint
import Mathlib.analysis.normed_space.linear_isometry
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Mazur-Ulam Theorem

Mazur-Ulam theorem states that an isometric bijection between two normed affine spaces over `ℝ` is
affine. We formalize it in three definitions:

* `isometric.to_real_linear_isometry_equiv_of_map_zero` : given `E ≃ᵢ F` sending `0` to `0`,
  returns `E ≃ₗᵢ[ℝ] F` with the same `to_fun` and `inv_fun`;
* `isometric.to_real_linear_isometry_equiv` : given `f : E ≃ᵢ F`,
  returns `g : E ≃ₗᵢ[ℝ] F` with `g x = f x - f 0`.
* `isometric.to_affine_equiv` : given `PE ≃ᵢ PF`, returns `g : PE ≃ᵃ[ℝ] PF` with the same
  `to_equiv`.

The formalization is based on [Jussi Väisälä, *A Proof of the Mazur-Ulam Theorem*][Vaisala_2003].

## Tags

isometry, affine map, linear map
-/

namespace isometric


/-- If an isometric self-homeomorphism of a normed vector space over `ℝ` fixes `x` and `y`,
then it fixes the midpoint of `[x, y]`. This is a lemma for a more general Mazur-Ulam theorem,
see below. -/
theorem midpoint_fixed {E : Type u_1} {PE : Type u_2} [normed_group E] [normed_space ℝ E] [metric_space PE] [normed_add_torsor E PE] {x : PE} {y : PE} (e : PE ≃ᵢ PE) : coe_fn e x = x → coe_fn e y = y → coe_fn e (midpoint ℝ x y) = midpoint ℝ x y := sorry

/-- A bijective isometry sends midpoints to midpoints. -/
theorem map_midpoint {E : Type u_1} {PE : Type u_2} [normed_group E] [normed_space ℝ E] [metric_space PE] [normed_add_torsor E PE] {F : Type u_3} {PF : Type u_4} [normed_group F] [normed_space ℝ F] [metric_space PF] [normed_add_torsor F PF] (f : PE ≃ᵢ PF) (x : PE) (y : PE) : coe_fn f (midpoint ℝ x y) = midpoint ℝ (coe_fn f x) (coe_fn f y) := sorry

/-!
Since `f : PE ≃ᵢ PF` sends midpoints to midpoints, it is an affine map.
We define a conversion to a `continuous_linear_equiv` first, then a conversion to an `affine_map`.
-/

/-- Mazur-Ulam Theorem: if `f` is an isometric bijection between two normed vector spaces
over `ℝ` and `f 0 = 0`, then `f` is a linear equivalence. -/
def to_real_linear_isometry_equiv_of_map_zero {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_3} [normed_group F] [normed_space ℝ F] (f : E ≃ᵢ F) (h0 : coe_fn f 0 = 0) : linear_isometry_equiv ℝ E F :=
  linear_isometry_equiv.mk
    (linear_equiv.mk
      (linear_map.to_fun
        (continuous_linear_map.to_linear_map
          (add_monoid_hom.to_real_linear_map (add_monoid_hom.of_map_midpoint ℝ ℝ (⇑f) h0 sorry) sorry)))
      sorry sorry (equiv.inv_fun (to_equiv f)) sorry sorry)
    sorry

@[simp] theorem coe_to_real_linear_equiv_of_map_zero {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_3} [normed_group F] [normed_space ℝ F] (f : E ≃ᵢ F) (h0 : coe_fn f 0 = 0) : ⇑(to_real_linear_isometry_equiv_of_map_zero f h0) = ⇑f :=
  rfl

@[simp] theorem coe_to_real_linear_equiv_of_map_zero_symm {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_3} [normed_group F] [normed_space ℝ F] (f : E ≃ᵢ F) (h0 : coe_fn f 0 = 0) : ⇑(linear_isometry_equiv.symm (to_real_linear_isometry_equiv_of_map_zero f h0)) = ⇑(isometric.symm f) :=
  rfl

/-- Mazur-Ulam Theorem: if `f` is an isometric bijection between two normed vector spaces
over `ℝ`, then `x ↦ f x - f 0` is a linear equivalence. -/
def to_real_linear_isometry_equiv {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_3} [normed_group F] [normed_space ℝ F] (f : E ≃ᵢ F) : linear_isometry_equiv ℝ E F :=
  to_real_linear_isometry_equiv_of_map_zero (isometric.trans f (isometric.symm (isometric.add_right (coe_fn f 0)))) sorry

@[simp] theorem to_real_linear_equiv_apply {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_3} [normed_group F] [normed_space ℝ F] (f : E ≃ᵢ F) (x : E) : coe_fn (to_real_linear_isometry_equiv f) x = coe_fn f x - coe_fn f 0 :=
  Eq.symm (sub_eq_add_neg (coe_fn f x) (coe_fn f 0))

@[simp] theorem to_real_linear_isometry_equiv_symm_apply {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_3} [normed_group F] [normed_space ℝ F] (f : E ≃ᵢ F) (y : F) : coe_fn (linear_isometry_equiv.symm (to_real_linear_isometry_equiv f)) y = coe_fn (isometric.symm f) (y + coe_fn f 0) :=
  rfl

/-- Convert an isometric equivalence between two affine spaces to an `affine_map`. -/
def to_affine_equiv {E : Type u_1} {PE : Type u_2} [normed_group E] [normed_space ℝ E] [metric_space PE] [normed_add_torsor E PE] {F : Type u_3} {PF : Type u_4} [normed_group F] [normed_space ℝ F] [metric_space PF] [normed_add_torsor F PF] (f : PE ≃ᵢ PF) : affine_equiv ℝ PE PF :=
  affine_equiv.mk' (to_equiv f)
    (linear_isometry_equiv.to_linear_equiv
      (to_real_linear_isometry_equiv
        (isometric.trans (vadd_const (classical.arbitrary PE))
          (isometric.trans f (isometric.symm (vadd_const (coe_fn f (classical.arbitrary PE))))))))
    (classical.arbitrary PE) sorry

@[simp] theorem coe_to_affine_equiv {E : Type u_1} {PE : Type u_2} [normed_group E] [normed_space ℝ E] [metric_space PE] [normed_add_torsor E PE] {F : Type u_3} {PF : Type u_4} [normed_group F] [normed_space ℝ F] [metric_space PF] [normed_add_torsor F PF] (f : PE ≃ᵢ PF) : ⇑(to_affine_equiv f) = ⇑f :=
  rfl

