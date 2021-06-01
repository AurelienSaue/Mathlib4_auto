/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.quaternion
import Mathlib.analysis.normed_space.inner_product
import Mathlib.PostPort

namespace Mathlib

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

## Notation

The following notation is available with `open_locale quaternion`:

* `ℍ` : quaternions

## Tags

quaternion, normed ring, normed space, normed algebra
-/

namespace quaternion


protected instance has_inner : has_inner ℝ (quaternion ℝ) :=
  has_inner.mk fun (a b : quaternion ℝ) => re (a * coe_fn conj b)

theorem inner_self (a : quaternion ℝ) : inner a a = coe_fn norm_sq a := rfl

theorem inner_def (a : quaternion ℝ) (b : quaternion ℝ) : inner a b = re (a * coe_fn conj b) := rfl

protected instance inner_product_space : inner_product_space ℝ (quaternion ℝ) :=
  inner_product_space.of_core
    (inner_product_space.core.mk inner sorry sorry sorry sorry sorry sorry)

theorem norm_sq_eq_norm_square (a : quaternion ℝ) : coe_fn norm_sq a = norm a * norm a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn norm_sq a = norm a * norm a)) (Eq.symm (inner_self a))))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (inner a a = norm a * norm a)) (real_inner_self_eq_norm_square a)))
      (Eq.refl (norm a * norm a)))

protected instance norm_one_class : norm_one_class (quaternion ℝ) :=
  norm_one_class.mk
    (eq.mpr (id (Eq._oldrec (Eq.refl (norm 1 = 1)) (norm_eq_sqrt_real_inner 1)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (real.sqrt (inner 1 1) = 1)) (inner_self 1)))
        (eq.mpr
          (id
            (Eq._oldrec (Eq.refl (real.sqrt (coe_fn norm_sq 1) = 1))
              (monoid_with_zero_hom.map_one norm_sq)))
          (eq.mpr (id (Eq._oldrec (Eq.refl (real.sqrt 1 = 1)) real.sqrt_one)) (Eq.refl 1)))))

@[simp] theorem norm_mul (a : quaternion ℝ) (b : quaternion ℝ) : norm (a * b) = norm a * norm b :=
  sorry

@[simp] theorem norm_coe (a : ℝ) : norm ↑a = norm a := sorry

protected instance normed_ring : normed_ring (quaternion ℝ) := normed_ring.mk sorry sorry

protected instance normed_algebra : normed_algebra ℝ (quaternion ℝ) := normed_algebra.mk norm_coe

protected instance has_coe : has_coe ℂ (quaternion ℝ) :=
  has_coe.mk fun (z : ℂ) => quaternion_algebra.mk (complex.re z) (complex.im z) 0 0

@[simp] theorem coe_complex_re (z : ℂ) : re ↑z = complex.re z := rfl

@[simp] theorem coe_complex_im_i (z : ℂ) : im_i ↑z = complex.im z := rfl

@[simp] theorem coe_complex_im_j (z : ℂ) : im_j ↑z = 0 := rfl

@[simp] theorem coe_complex_im_k (z : ℂ) : im_k ↑z = 0 := rfl

@[simp] theorem coe_complex_add (z : ℂ) (w : ℂ) : ↑(z + w) = ↑z + ↑w := sorry

@[simp] theorem coe_complex_mul (z : ℂ) (w : ℂ) : ↑(z * w) = ↑z * ↑w := sorry

@[simp] theorem coe_complex_zero : ↑0 = 0 := rfl

@[simp] theorem coe_complex_one : ↑1 = 1 := rfl

@[simp] theorem coe_complex_smul (r : ℝ) (z : ℂ) : ↑(r • z) = r • ↑z := sorry

@[simp] theorem coe_complex_coe (r : ℝ) : ↑↑r = ↑r := rfl

/-- Coercion `ℂ →ₐ[ℝ] ℍ` as an algebra homomorphism. -/
def of_complex : alg_hom ℝ ℂ (quaternion ℝ) :=
  alg_hom.mk coe sorry coe_complex_mul sorry coe_complex_add sorry

@[simp] theorem coe_of_complex : ⇑of_complex = coe := rfl

end Mathlib