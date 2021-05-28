/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.real.sqrt
import Mathlib.field_theory.tower
import Mathlib.analysis.normed_space.finite_dimension
import Mathlib.PostPort

universes u_1 l u_2 u_3 

namespace Mathlib

/-!
# `is_R_or_C`: a typeclass for ℝ or ℂ

This file defines the typeclass `is_R_or_C` intended to have only two instances:
ℝ and ℂ. It is meant for definitions and theorems which hold for both the real and the complex case,
and in particular when the real case follows directly from the complex case by setting `re` to `id`,
`im` to zero and so on. Its API follows closely that of ℂ.

Possible applications include defining inner products and Hilbert spaces for both the real and
complex case. One would produce the definitions and proof for an arbitrary field of this
typeclass, which basically amounts to doing the complex case, and the two cases then fall out
immediately from the two instances of the class.

The instance for `ℝ` is registered in this file.
The instance for `ℂ` is declared in `analysis.complex.basic`.

## Implementation notes

The coercion from reals into an `is_R_or_C` field is done by registering `algebra_map ℝ K` as
a `has_coe_t`. For this to work, we must proceed carefully to avoid problems involving circular
coercions in the case `K=ℝ`; in particular, we cannot use the plain `has_coe` and must set
priorities carefully. This problem was already solved for `ℕ`, and we copy the solution detailed
in `data/nat/cast`. See also Note [coercion into rings] for more details.

In addition, several lemmas need to be set at priority 900 to make sure that they do not override
their counterparts in `complex.lean` (which causes linter errors).
-/

/--
This typeclass captures properties shared by ℝ and ℂ, with an API that closely matches that of ℂ.
-/
class is_R_or_C (K : Type u_1) 
extends nondiscrete_normed_field K, normed_algebra ℝ K, complete_space K
where
  re : K →+ ℝ
  im : K →+ ℝ
  conj : K →+* K
  I : K
  I_re_ax : coe_fn re I = 0
  I_mul_I_ax : I = 0 ∨ I * I = -1
  re_add_im_ax : ∀ (z : K), coe_fn (algebra_map ℝ K) (coe_fn re z) + coe_fn (algebra_map ℝ K) (coe_fn im z) * I = z
  of_real_re_ax : ∀ (r : ℝ), coe_fn re (coe_fn (algebra_map ℝ K) r) = r
  of_real_im_ax : ∀ (r : ℝ), coe_fn im (coe_fn (algebra_map ℝ K) r) = 0
  mul_re_ax : ∀ (z w : K), coe_fn re (z * w) = coe_fn re z * coe_fn re w - coe_fn im z * coe_fn im w
  mul_im_ax : ∀ (z w : K), coe_fn im (z * w) = coe_fn re z * coe_fn im w + coe_fn im z * coe_fn re w
  conj_re_ax : ∀ (z : K), coe_fn re (coe_fn conj z) = coe_fn re z
  conj_im_ax : ∀ (z : K), coe_fn im (coe_fn conj z) = -coe_fn im z
  conj_I_ax : coe_fn conj I = -I
  norm_sq_eq_def_ax : ∀ (z : K), norm z ^ bit0 1 = coe_fn re z * coe_fn re z + coe_fn im z * coe_fn im z
  mul_im_I_ax : ∀ (z : K), coe_fn im z * coe_fn im I = coe_fn im z
  inv_def_ax : ∀ (z : K), z⁻¹ = coe_fn conj z * coe_fn (algebra_map ℝ K) (norm z ^ bit0 1⁻¹)
  div_I_ax : ∀ (z : K), z / I = -(z * I)

namespace is_R_or_C


/- The priority must be set at 900 to ensure that coercions are tried in the right order.
See Note [coercion into rings], or `data/nat/cast.lean` for more details. -/

protected instance algebra_map_coe {K : Type u_1} [is_R_or_C K] : has_coe_t ℝ K :=
  has_coe_t.mk ⇑(algebra_map ℝ K)

theorem of_real_alg {K : Type u_1} [is_R_or_C K] (x : ℝ) : ↑x = x • 1 :=
  algebra.algebra_map_eq_smul_one x

theorem algebra_map_eq_of_real {K : Type u_1} [is_R_or_C K] : ⇑(algebra_map ℝ K) = coe :=
  rfl

@[simp] theorem re_add_im {K : Type u_1} [is_R_or_C K] (z : K) : ↑(coe_fn re z) + ↑(coe_fn im z) * I = z :=
  re_add_im_ax z

@[simp] theorem of_real_re {K : Type u_1} [is_R_or_C K] (r : ℝ) : coe_fn re ↑r = r :=
  of_real_re_ax

@[simp] theorem of_real_im {K : Type u_1} [is_R_or_C K] (r : ℝ) : coe_fn im ↑r = 0 :=
  of_real_im_ax

@[simp] theorem mul_re {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : coe_fn re (z * w) = coe_fn re z * coe_fn re w - coe_fn im z * coe_fn im w :=
  mul_re_ax

@[simp] theorem mul_im {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : coe_fn im (z * w) = coe_fn re z * coe_fn im w + coe_fn im z * coe_fn re w :=
  mul_im_ax

theorem inv_def {K : Type u_1} [is_R_or_C K] (z : K) : z⁻¹ = coe_fn conj z * ↑(norm z ^ bit0 1⁻¹) :=
  inv_def_ax z

theorem ext_iff {K : Type u_1} [is_R_or_C K] {z : K} {w : K} : z = w ↔ coe_fn re z = coe_fn re w ∧ coe_fn im z = coe_fn im w := sorry

theorem ext {K : Type u_1} [is_R_or_C K] {z : K} {w : K} : coe_fn re z = coe_fn re w → coe_fn im z = coe_fn im w → z = w := sorry

@[simp] theorem of_real_zero {K : Type u_1} [is_R_or_C K] : ↑0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑0 = 0)) (of_real_alg 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 • 1 = 0)) (zero_smul ℝ 1))) (Eq.refl 0))

@[simp] theorem zero_re' {K : Type u_1} [is_R_or_C K] : coe_fn re 0 = 0 :=
  add_monoid_hom.map_zero re

@[simp] theorem of_real_one {K : Type u_1} [is_R_or_C K] : ↑1 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑1 = 1)) (of_real_alg 1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 • 1 = 1)) (one_smul ℝ 1))) (Eq.refl 1))

@[simp] theorem one_re {K : Type u_1} [is_R_or_C K] : coe_fn re 1 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn re 1 = 1)) (Eq.symm of_real_one)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn re ↑1 = 1)) (of_real_re 1))) (Eq.refl 1))

@[simp] theorem one_im {K : Type u_1} [is_R_or_C K] : coe_fn im 1 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn im 1 = 0)) (Eq.symm of_real_one)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn im ↑1 = 0)) (of_real_im 1))) (Eq.refl 0))

@[simp] theorem of_real_inj {K : Type u_1} [is_R_or_C K] {z : ℝ} {w : ℝ} : ↑z = ↑w ↔ z = w := sorry

@[simp] theorem bit0_re {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn re (bit0 z) = bit0 (coe_fn re z) := sorry

@[simp] theorem bit1_re {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn re (bit1 z) = bit1 (coe_fn re z) := sorry

@[simp] theorem bit0_im {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn im (bit0 z) = bit0 (coe_fn im z) := sorry

@[simp] theorem bit1_im {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn im (bit1 z) = bit0 (coe_fn im z) := sorry

@[simp] theorem of_real_eq_zero {K : Type u_1} [is_R_or_C K] {z : ℝ} : ↑z = 0 ↔ z = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑z = 0 ↔ z = 0)) (Eq.symm of_real_zero))) of_real_inj

@[simp] theorem of_real_add {K : Type u_1} [is_R_or_C K] {r : ℝ} {s : ℝ} : ↑(r + s) = ↑r + ↑s := sorry

@[simp] theorem of_real_bit0 {K : Type u_1} [is_R_or_C K] (r : ℝ) : ↑(bit0 r) = bit0 ↑r := sorry

@[simp] theorem of_real_bit1 {K : Type u_1} [is_R_or_C K] (r : ℝ) : ↑(bit1 r) = bit1 ↑r := sorry

/- Note: This can be proven by `norm_num` once K is proven to be of characteristic zero below. -/

theorem two_ne_zero {K : Type u_1} [is_R_or_C K] : bit0 1 ≠ 0 := sorry

@[simp] theorem of_real_neg {K : Type u_1} [is_R_or_C K] (r : ℝ) : ↑(-r) = -↑r := sorry

@[simp] theorem of_real_mul {K : Type u_1} [is_R_or_C K] (r : ℝ) (s : ℝ) : ↑(r * s) = ↑r * ↑s := sorry

theorem of_real_mul_re {K : Type u_1} [is_R_or_C K] (r : ℝ) (z : K) : coe_fn re (↑r * z) = r * coe_fn re z := sorry

theorem smul_re {K : Type u_1} [is_R_or_C K] (r : ℝ) (z : K) : coe_fn re (↑r * z) = r * coe_fn re z := sorry

theorem smul_im {K : Type u_1} [is_R_or_C K] (r : ℝ) (z : K) : coe_fn im (↑r * z) = r * coe_fn im z := sorry

theorem smul_re' {K : Type u_1} [is_R_or_C K] (r : ℝ) (z : K) : coe_fn re (r • z) = r * coe_fn re z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn re (r • z) = r * coe_fn re z)) (algebra.smul_def r z))) (smul_re r z)

theorem smul_im' {K : Type u_1} [is_R_or_C K] (r : ℝ) (z : K) : coe_fn im (r • z) = r * coe_fn im z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn im (r • z) = r * coe_fn im z)) (algebra.smul_def r z))) (smul_im r z)

/-- The real part in a `is_R_or_C` field, as a linear map. -/
def re_lm {K : Type u_1} [is_R_or_C K] : linear_map ℝ K ℝ :=
  linear_map.mk (add_monoid_hom.to_fun re) sorry smul_re'

@[simp] theorem re_lm_coe {K : Type u_1} [is_R_or_C K] : ⇑re_lm = ⇑re :=
  rfl

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
@[simp] theorem I_re {K : Type u_1} [is_R_or_C K] : coe_fn re I = 0 :=
  I_re_ax

@[simp] theorem I_im {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn im z * coe_fn im I = coe_fn im z :=
  mul_im_I_ax z

@[simp] theorem I_im' {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn im I * coe_fn im z = coe_fn im z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn im I * coe_fn im z = coe_fn im z)) (mul_comm (coe_fn im I) (coe_fn im z))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn im z * coe_fn im I = coe_fn im z)) (I_im z))) (Eq.refl (coe_fn im z)))

theorem I_mul_re {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn re (I * z) = -coe_fn im z := sorry

theorem I_mul_I {K : Type u_1} [is_R_or_C K] : I = 0 ∨ I * I = -1 :=
  I_mul_I_ax

@[simp] theorem conj_re {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn re (coe_fn conj z) = coe_fn re z :=
  conj_re_ax z

@[simp] theorem conj_im {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn im (coe_fn conj z) = -coe_fn im z :=
  conj_im_ax z

@[simp] theorem conj_of_real {K : Type u_1} [is_R_or_C K] (r : ℝ) : coe_fn conj ↑r = ↑r := sorry

@[simp] theorem conj_bit0 {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn conj (bit0 z) = bit0 (coe_fn conj z) := sorry

@[simp] theorem conj_bit1 {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn conj (bit1 z) = bit1 (coe_fn conj z) := sorry

@[simp] theorem conj_neg_I {K : Type u_1} [is_R_or_C K] : coe_fn conj (-I) = I := sorry

@[simp] theorem conj_conj {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn conj (coe_fn conj z) = z := sorry

theorem conj_involutive {K : Type u_1} [is_R_or_C K] : function.involutive ⇑conj :=
  conj_conj

theorem conj_bijective {K : Type u_1} [is_R_or_C K] : function.bijective ⇑conj :=
  function.involutive.bijective conj_involutive

theorem conj_inj {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : coe_fn conj z = coe_fn conj w ↔ z = w :=
  function.injective.eq_iff (and.left conj_bijective)

theorem conj_eq_zero {K : Type u_1} [is_R_or_C K] {z : K} : coe_fn conj z = 0 ↔ z = 0 :=
  ring_hom.map_eq_zero conj

theorem eq_conj_iff_real {K : Type u_1} [is_R_or_C K] {z : K} : coe_fn conj z = z ↔ ∃ (r : ℝ), z = ↑r := sorry

/-- Conjugation as a ring equivalence. This is used to convert the inner product into a
sesquilinear product. -/
def conj_to_ring_equiv (K : Type u_1) [is_R_or_C K] : K ≃+* (Kᵒᵖ) :=
  ring_equiv.mk (opposite.op ∘ ⇑conj) (⇑conj ∘ opposite.unop) sorry sorry sorry sorry

@[simp] theorem ring_equiv_apply {K : Type u_1} [is_R_or_C K] {x : K} : opposite.unop (coe_fn (conj_to_ring_equiv K) x) = coe_fn conj x :=
  rfl

theorem eq_conj_iff_re {K : Type u_1} [is_R_or_C K] {z : K} : coe_fn conj z = z ↔ ↑(coe_fn re z) = z := sorry

/-- The norm squared function. -/
def norm_sq {K : Type u_1} [is_R_or_C K] : monoid_with_zero_hom K ℝ :=
  monoid_with_zero_hom.mk (fun (z : K) => coe_fn re z * coe_fn re z + coe_fn im z * coe_fn im z) sorry sorry sorry

theorem norm_sq_eq_def {K : Type u_1} [is_R_or_C K] {z : K} : norm z ^ bit0 1 = coe_fn re z * coe_fn re z + coe_fn im z * coe_fn im z :=
  norm_sq_eq_def_ax z

theorem norm_sq_eq_def' {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn norm_sq z = norm z ^ bit0 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn norm_sq z = norm z ^ bit0 1)) norm_sq_eq_def)) (Eq.refl (coe_fn norm_sq z))

@[simp] theorem norm_sq_of_real {K : Type u_1} [is_R_or_C K] (r : ℝ) : norm ↑r ^ bit0 1 = r * r := sorry

theorem norm_sq_zero {K : Type u_1} [is_R_or_C K] : coe_fn norm_sq 0 = 0 :=
  monoid_with_zero_hom.map_zero norm_sq

theorem norm_sq_one {K : Type u_1} [is_R_or_C K] : coe_fn norm_sq 1 = 1 :=
  monoid_with_zero_hom.map_one norm_sq

theorem norm_sq_nonneg {K : Type u_1} [is_R_or_C K] (z : K) : 0 ≤ coe_fn norm_sq z :=
  add_nonneg (mul_self_nonneg (coe_fn re z)) (mul_self_nonneg (coe_fn im z))

@[simp] theorem norm_sq_eq_zero {K : Type u_1} [is_R_or_C K] {z : K} : coe_fn norm_sq z = 0 ↔ z = 0 := sorry

@[simp] theorem norm_sq_pos {K : Type u_1} [is_R_or_C K] {z : K} : 0 < coe_fn norm_sq z ↔ z ≠ 0 := sorry

@[simp] theorem norm_sq_neg {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn norm_sq (-z) = coe_fn norm_sq z := sorry

@[simp] theorem norm_sq_conj {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn norm_sq (coe_fn conj z) = coe_fn norm_sq z := sorry

@[simp] theorem norm_sq_mul {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : coe_fn norm_sq (z * w) = coe_fn norm_sq z * coe_fn norm_sq w :=
  monoid_with_zero_hom.map_mul norm_sq z w

theorem norm_sq_add {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : coe_fn norm_sq (z + w) = coe_fn norm_sq z + coe_fn norm_sq w + bit0 1 * coe_fn re (z * coe_fn conj w) := sorry

theorem re_sq_le_norm_sq {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn re z * coe_fn re z ≤ coe_fn norm_sq z :=
  le_add_of_nonneg_right (mul_self_nonneg (coe_fn im z))

theorem im_sq_le_norm_sq {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn im z * coe_fn im z ≤ coe_fn norm_sq z :=
  le_add_of_nonneg_left (mul_self_nonneg (coe_fn re z))

theorem mul_conj {K : Type u_1} [is_R_or_C K] (z : K) : z * coe_fn conj z = ↑(coe_fn norm_sq z) := sorry

theorem add_conj {K : Type u_1} [is_R_or_C K] (z : K) : z + coe_fn conj z = bit0 1 * ↑(coe_fn re z) := sorry

/-- The pseudo-coercion `of_real` as a `ring_hom`. -/
def of_real_hom {K : Type u_1} [is_R_or_C K] : ℝ →+* K :=
  algebra_map ℝ K

/-- The coercion from reals as a `ring_hom`. -/
def coe_hom {K : Type u_1} [is_R_or_C K] : ℝ →+* K :=
  ring_hom.mk coe of_real_one of_real_mul of_real_zero of_real_add

@[simp] theorem of_real_sub {K : Type u_1} [is_R_or_C K] (r : ℝ) (s : ℝ) : ↑(r - s) = ↑r - ↑s := sorry

@[simp] theorem of_real_pow {K : Type u_1} [is_R_or_C K] (r : ℝ) (n : ℕ) : ↑(r ^ n) = ↑r ^ n := sorry

theorem sub_conj {K : Type u_1} [is_R_or_C K] (z : K) : z - coe_fn conj z = bit0 1 * ↑(coe_fn im z) * I := sorry

theorem norm_sq_sub {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : coe_fn norm_sq (z - w) = coe_fn norm_sq z + coe_fn norm_sq w - bit0 1 * coe_fn re (z * coe_fn conj w) := sorry

theorem sqrt_norm_sq_eq_norm {K : Type u_1} [is_R_or_C K] {z : K} : real.sqrt (coe_fn norm_sq z) = norm z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (real.sqrt (coe_fn norm_sq z) = norm z)) (Eq.symm (real.sqrt_sqr (norm_nonneg z)))))
    (congr_arg real.sqrt (norm_sq_eq_def' z))

/-! ### Inversion -/

@[simp] theorem inv_re {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn re (z⁻¹) = coe_fn re z / coe_fn norm_sq z := sorry

@[simp] theorem inv_im {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn im (z⁻¹) = coe_fn im (-z) / coe_fn norm_sq z := sorry

@[simp] theorem of_real_inv {K : Type u_1} [is_R_or_C K] (r : ℝ) : ↑(r⁻¹) = (↑r⁻¹) := sorry

protected theorem inv_zero {K : Type u_1} [is_R_or_C K] : 0⁻¹ = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0⁻¹ = 0)) (Eq.symm of_real_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑0⁻¹ = ↑0)) (Eq.symm (of_real_inv 0))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑(0⁻¹) = ↑0)) inv_zero)) (Eq.refl ↑0)))

protected theorem mul_inv_cancel {K : Type u_1} [is_R_or_C K] {z : K} (h : z ≠ 0) : z * (z⁻¹) = 1 := sorry

theorem div_re {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : coe_fn re (z / w) = coe_fn re z * coe_fn re w / coe_fn norm_sq w + coe_fn im z * coe_fn im w / coe_fn norm_sq w := sorry

theorem div_im {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : coe_fn im (z / w) = coe_fn im z * coe_fn re w / coe_fn norm_sq w - coe_fn re z * coe_fn im w / coe_fn norm_sq w := sorry

@[simp] theorem of_real_div {K : Type u_1} [is_R_or_C K] (r : ℝ) (s : ℝ) : ↑(r / s) = ↑r / ↑s :=
  ring_hom.map_div coe_hom r s

theorem div_re_of_real {K : Type u_1} [is_R_or_C K] {z : K} {r : ℝ} : coe_fn re (z / ↑r) = coe_fn re z / r := sorry

@[simp] theorem of_real_fpow {K : Type u_1} [is_R_or_C K] (r : ℝ) (n : ℤ) : ↑(r ^ n) = ↑r ^ n :=
  ring_hom.map_fpow coe_hom r n

theorem I_mul_I_of_nonzero {K : Type u_1} [is_R_or_C K] : I ≠ 0 → I * I = -1 :=
  fun (ᾰ : I ≠ 0) =>
    or.dcases_on I_mul_I_ax (fun (this : I = 0) => absurd this ᾰ) fun (this : I * I = -1) => eq.mpr rfl this

@[simp] theorem div_I {K : Type u_1} [is_R_or_C K] (z : K) : z / I = -(z * I) := sorry

@[simp] theorem inv_I {K : Type u_1} [is_R_or_C K] : I⁻¹ = -I := sorry

@[simp] theorem norm_sq_inv {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn norm_sq (z⁻¹) = (coe_fn norm_sq z⁻¹) :=
  monoid_with_zero_hom.map_inv' norm_sq z

@[simp] theorem norm_sq_div {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : coe_fn norm_sq (z / w) = coe_fn norm_sq z / coe_fn norm_sq w :=
  monoid_with_zero_hom.map_div norm_sq z w

theorem norm_conj {K : Type u_1} [is_R_or_C K] {z : K} : norm (coe_fn conj z) = norm z := sorry

theorem conj_inv {K : Type u_1} [is_R_or_C K] {z : K} : coe_fn conj (z⁻¹) = (coe_fn conj z⁻¹) := sorry

theorem conj_div {K : Type u_1} [is_R_or_C K] {z : K} {w : K} : coe_fn conj (z / w) = coe_fn conj z / coe_fn conj w := sorry

/-! ### Cast lemmas -/

@[simp] theorem of_real_nat_cast {K : Type u_1} [is_R_or_C K] (n : ℕ) : ↑↑n = ↑n :=
  ring_hom.map_nat_cast of_real_hom n

@[simp] theorem nat_cast_re {K : Type u_1} [is_R_or_C K] (n : ℕ) : coe_fn re ↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn re ↑n = ↑n)) (Eq.symm (of_real_nat_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn re ↑↑n = ↑n)) (of_real_re ↑n))) (Eq.refl ↑n))

@[simp] theorem nat_cast_im {K : Type u_1} [is_R_or_C K] (n : ℕ) : coe_fn im ↑n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn im ↑n = 0)) (Eq.symm (of_real_nat_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn im ↑↑n = 0)) (of_real_im ↑n))) (Eq.refl 0))

@[simp] theorem of_real_int_cast {K : Type u_1} [is_R_or_C K] (n : ℤ) : ↑↑n = ↑n :=
  ring_hom.map_int_cast of_real_hom n

@[simp] theorem int_cast_re {K : Type u_1} [is_R_or_C K] (n : ℤ) : coe_fn re ↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn re ↑n = ↑n)) (Eq.symm (of_real_int_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn re ↑↑n = ↑n)) (of_real_re ↑n))) (Eq.refl ↑n))

@[simp] theorem int_cast_im {K : Type u_1} [is_R_or_C K] (n : ℤ) : coe_fn im ↑n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn im ↑n = 0)) (Eq.symm (of_real_int_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn im ↑↑n = 0)) (of_real_im ↑n))) (Eq.refl 0))

@[simp] theorem of_real_rat_cast {K : Type u_1} [is_R_or_C K] (n : ℚ) : ↑↑n = ↑n :=
  ring_hom.map_rat_cast of_real_hom n

@[simp] theorem rat_cast_re {K : Type u_1} [is_R_or_C K] (q : ℚ) : coe_fn re ↑q = ↑q :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn re ↑q = ↑q)) (Eq.symm (of_real_rat_cast q))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn re ↑↑q = ↑q)) (of_real_re ↑q))) (Eq.refl ↑q))

@[simp] theorem rat_cast_im {K : Type u_1} [is_R_or_C K] (q : ℚ) : coe_fn im ↑q = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn im ↑q = 0)) (Eq.symm (of_real_rat_cast q))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn im ↑↑q = 0)) (of_real_im ↑q))) (Eq.refl 0))

/-! ### Characteristic zero -/

-- TODO: I think this can be instance, because it is a `Prop`

/--
ℝ and ℂ are both of characteristic zero.

Note: This is not registered as an instance to avoid having multiple instances on ℝ and ℂ.
-/
theorem char_zero_R_or_C {K : Type u_1} [is_R_or_C K] : char_zero K := sorry

theorem re_eq_add_conj {K : Type u_1} [is_R_or_C K] (z : K) : ↑(coe_fn re z) = (z + coe_fn conj z) / bit0 1 := sorry

/-! ### Absolute value -/

/-- The complex absolute value function, defined as the square root of the norm squared. -/
def abs {K : Type u_1} [is_R_or_C K] (z : K) : ℝ :=
  real.sqrt (coe_fn norm_sq z)

@[simp] theorem abs_of_real {K : Type u_1} [is_R_or_C K] (r : ℝ) : abs ↑r = abs r := sorry

theorem norm_eq_abs {K : Type u_1} [is_R_or_C K] (z : K) : norm z = abs z := sorry

theorem abs_of_nonneg {K : Type u_1} [is_R_or_C K] {r : ℝ} (h : 0 ≤ r) : abs ↑r = r :=
  Eq.trans (abs_of_real r) (abs_of_nonneg h)

theorem abs_of_nat {K : Type u_1} [is_R_or_C K] (n : ℕ) : abs ↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs ↑n = ↑n)) (Eq.symm (of_real_nat_cast n)))) (abs_of_nonneg (nat.cast_nonneg n))

theorem mul_self_abs {K : Type u_1} [is_R_or_C K] (z : K) : abs z * abs z = coe_fn norm_sq z :=
  real.mul_self_sqrt (norm_sq_nonneg z)

@[simp] theorem abs_zero {K : Type u_1} [is_R_or_C K] : abs 0 = 0 := sorry

@[simp] theorem abs_one {K : Type u_1} [is_R_or_C K] : abs 1 = 1 := sorry

@[simp] theorem abs_two {K : Type u_1} [is_R_or_C K] : abs (bit0 1) = bit0 1 := sorry

theorem abs_nonneg {K : Type u_1} [is_R_or_C K] (z : K) : 0 ≤ abs z :=
  real.sqrt_nonneg (coe_fn norm_sq z)

@[simp] theorem abs_eq_zero {K : Type u_1} [is_R_or_C K] {z : K} : abs z = 0 ↔ z = 0 :=
  iff.trans (real.sqrt_eq_zero (norm_sq_nonneg z)) norm_sq_eq_zero

theorem abs_ne_zero {K : Type u_1} [is_R_or_C K] {z : K} : abs z ≠ 0 ↔ z ≠ 0 :=
  not_congr abs_eq_zero

@[simp] theorem abs_conj {K : Type u_1} [is_R_or_C K] (z : K) : abs (coe_fn conj z) = abs z := sorry

@[simp] theorem abs_mul {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : abs (z * w) = abs z * abs w := sorry

theorem abs_re_le_abs {K : Type u_1} [is_R_or_C K] (z : K) : abs (coe_fn re z) ≤ abs z := sorry

theorem abs_im_le_abs {K : Type u_1} [is_R_or_C K] (z : K) : abs (coe_fn im z) ≤ abs z := sorry

theorem re_le_abs {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn re z ≤ abs z :=
  and.right (iff.mp abs_le (abs_re_le_abs z))

theorem im_le_abs {K : Type u_1} [is_R_or_C K] (z : K) : coe_fn im z ≤ abs z :=
  and.right (iff.mp abs_le (abs_im_le_abs z))

theorem im_eq_zero_of_le {K : Type u_1} [is_R_or_C K] {a : K} (h : abs a ≤ coe_fn re a) : coe_fn im a = 0 := sorry

theorem re_eq_self_of_le {K : Type u_1} [is_R_or_C K] {a : K} (h : abs a ≤ coe_fn re a) : ↑(coe_fn re a) = a := sorry

theorem abs_add {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : abs (z + w) ≤ abs z + abs w := sorry

protected instance abs.is_absolute_value {K : Type u_1} [is_R_or_C K] : is_absolute_value abs :=
  is_absolute_value.mk abs_nonneg (fun (_x : K) => abs_eq_zero) abs_add abs_mul

@[simp] theorem abs_abs {K : Type u_1} [is_R_or_C K] (z : K) : abs (abs z) = abs z :=
  abs_of_nonneg (abs_nonneg z)

@[simp] theorem abs_pos {K : Type u_1} [is_R_or_C K] {z : K} : 0 < abs z ↔ z ≠ 0 :=
  is_absolute_value.abv_pos abs

@[simp] theorem abs_neg {K : Type u_1} [is_R_or_C K] (z : K) : abs (-z) = abs z :=
  is_absolute_value.abv_neg abs

theorem abs_sub {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : abs (z - w) = abs (w - z) :=
  is_absolute_value.abv_sub abs

theorem abs_sub_le {K : Type u_1} [is_R_or_C K] (a : K) (b : K) (c : K) : abs (a - c) ≤ abs (a - b) + abs (b - c) :=
  is_absolute_value.abv_sub_le abs

@[simp] theorem abs_inv {K : Type u_1} [is_R_or_C K] (z : K) : abs (z⁻¹) = (abs z⁻¹) :=
  is_absolute_value.abv_inv abs

@[simp] theorem abs_div {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : abs (z / w) = abs z / abs w :=
  is_absolute_value.abv_div abs

theorem abs_abs_sub_le_abs_sub {K : Type u_1} [is_R_or_C K] (z : K) (w : K) : abs (abs z - abs w) ≤ abs (z - w) :=
  is_absolute_value.abs_abv_sub_le_abv_sub abs

theorem abs_re_div_abs_le_one {K : Type u_1} [is_R_or_C K] (z : K) : abs (coe_fn re z / abs z) ≤ 1 := sorry

theorem abs_im_div_abs_le_one {K : Type u_1} [is_R_or_C K] (z : K) : abs (coe_fn im z / abs z) ≤ 1 := sorry

@[simp] theorem abs_cast_nat {K : Type u_1} [is_R_or_C K] (n : ℕ) : abs ↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs ↑n = ↑n)) (Eq.symm (of_real_nat_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (abs ↑↑n = ↑n)) (abs_of_nonneg (nat.cast_nonneg n)))) (Eq.refl ↑n))

theorem norm_sq_eq_abs {K : Type u_1} [is_R_or_C K] (x : K) : coe_fn norm_sq x = abs x ^ bit0 1 := sorry

theorem re_eq_abs_of_mul_conj {K : Type u_1} [is_R_or_C K] (x : K) : coe_fn re (x * coe_fn conj x) = abs (x * coe_fn conj x) := sorry

theorem abs_sqr_re_add_conj {K : Type u_1} [is_R_or_C K] (x : K) : abs (x + coe_fn conj x) ^ bit0 1 = coe_fn re (x + coe_fn conj x) ^ bit0 1 := sorry

theorem abs_sqr_re_add_conj' {K : Type u_1} [is_R_or_C K] (x : K) : abs (coe_fn conj x + x) ^ bit0 1 = coe_fn re (coe_fn conj x + x) ^ bit0 1 := sorry

theorem conj_mul_eq_norm_sq_left {K : Type u_1} [is_R_or_C K] (x : K) : coe_fn conj x * x = ↑(coe_fn norm_sq x) := sorry

/-- The real part in a `is_R_or_C` field, as a continuous linear map. -/
def re_clm {K : Type u_1} [is_R_or_C K] : continuous_linear_map ℝ K ℝ :=
  linear_map.mk_continuous re_lm 1 sorry

@[simp] theorem norm_re_clm {K : Type u_1} [is_R_or_C K] : norm re_clm = 1 := sorry

@[simp] theorem re_clm_coe {K : Type u_1} [is_R_or_C K] : ↑re_clm = re_lm :=
  rfl

@[simp] theorem re_clm_apply {K : Type u_1} [is_R_or_C K] : ⇑re_clm = ⇑re :=
  rfl

/-! ### Cauchy sequences -/

theorem is_cau_seq_re {K : Type u_1} [is_R_or_C K] (f : cau_seq K abs) : is_cau_seq abs fun (n : ℕ) => coe_fn re (coe_fn f n) := sorry

theorem is_cau_seq_im {K : Type u_1} [is_R_or_C K] (f : cau_seq K abs) : is_cau_seq abs fun (n : ℕ) => coe_fn im (coe_fn f n) := sorry

/-- The real part of a K Cauchy sequence, as a real Cauchy sequence. -/
def cau_seq_re {K : Type u_1} [is_R_or_C K] (f : cau_seq K abs) : cau_seq ℝ abs :=
  { val := fun (n : ℕ) => coe_fn re (coe_fn f n), property := is_cau_seq_re f }

/-- The imaginary part of a K Cauchy sequence, as a real Cauchy sequence. -/
def cau_seq_im {K : Type u_1} [is_R_or_C K] (f : cau_seq K abs) : cau_seq ℝ abs :=
  { val := fun (n : ℕ) => coe_fn im (coe_fn f n), property := is_cau_seq_im f }

theorem is_cau_seq_abs {K : Type u_1} [is_R_or_C K] {f : ℕ → K} (hf : is_cau_seq abs f) : is_cau_seq abs (abs ∘ f) := sorry

@[simp] theorem of_real_prod {K : Type u_1} [is_R_or_C K] {α : Type u_2} (s : finset α) (f : α → ℝ) : ↑(finset.prod s fun (i : α) => f i) = finset.prod s fun (i : α) => ↑(f i) :=
  ring_hom.map_prod (algebra_map ℝ K) (fun (i : α) => f i) s

@[simp] theorem of_real_sum {K : Type u_1} [is_R_or_C K] {α : Type u_2} (s : finset α) (f : α → ℝ) : ↑(finset.sum s fun (i : α) => f i) = finset.sum s fun (i : α) => ↑(f i) :=
  ring_hom.map_sum (algebra_map ℝ K) (fun (i : α) => f i) s

@[simp] theorem of_real_finsupp_sum {K : Type u_1} [is_R_or_C K] {α : Type u_2} {M : Type u_3} [HasZero M] (f : α →₀ M) (g : α → M → ℝ) : ↑(finsupp.sum f fun (a : α) (b : M) => g a b) = finsupp.sum f fun (a : α) (b : M) => ↑(g a b) :=
  ring_hom.map_finsupp_sum (algebra_map ℝ K) f g

@[simp] theorem of_real_finsupp_prod {K : Type u_1} [is_R_or_C K] {α : Type u_2} {M : Type u_3} [HasZero M] (f : α →₀ M) (g : α → M → ℝ) : ↑(finsupp.prod f fun (a : α) (b : M) => g a b) = finsupp.prod f fun (a : α) (b : M) => ↑(g a b) :=
  ring_hom.map_finsupp_prod (algebra_map ℝ K) f g

end is_R_or_C


namespace finite_dimensional


/-- This instance generates a type-class problem with a metavariable `?m` that should satisfy
`is_R_or_C ?m`. Since this can only be satisfied by `ℝ` or `ℂ`, this does not cause problems. -/
/-- An `is_R_or_C` field is finite-dimensional over `ℝ`, since it is spanned by `{1, I}`. -/
protected instance is_R_or_C_to_real {K : Type u_1} [is_R_or_C K] : finite_dimensional ℝ K := sorry

/-- Over an `is_R_or_C` field, we can register the properness of finite-dimensional normed spaces as
an instance. -/
protected instance proper_is_R_or_C {K : Type u_1} [is_R_or_C K] {E : Type u_2} [normed_group E] [normed_space K E] [finite_dimensional K E] : proper_space E :=
  let _inst : normed_space ℝ E := restrict_scalars.normed_space ℝ K E;
  let _inst_5 : is_scalar_tower ℝ K E := restrict_scalars.is_scalar_tower ℝ K E;
  let _inst_6 : finite_dimensional ℝ E := trans ℝ K E;
  finite_dimensional.proper_real E

end finite_dimensional


protected instance real.is_R_or_C : is_R_or_C ℝ :=
  is_R_or_C.mk (add_monoid_hom.id ℝ) 0 (ring_hom.id ℝ) 0 sorry sorry sorry sorry sorry sorry sorry sorry sorry sorry sorry
    sorry sorry sorry

namespace is_R_or_C


@[simp] theorem re_to_real {x : ℝ} : coe_fn re x = x :=
  rfl

@[simp] theorem im_to_real {x : ℝ} : coe_fn im x = 0 :=
  rfl

@[simp] theorem conj_to_real {x : ℝ} : coe_fn conj x = x :=
  rfl

@[simp] theorem I_to_real : I = 0 :=
  rfl

@[simp] theorem norm_sq_to_real {x : ℝ} : coe_fn norm_sq x = x * x := sorry

@[simp] theorem abs_to_real {x : ℝ} : abs x = abs x := sorry

@[simp] theorem coe_real_eq_id : coe = id :=
  rfl

end is_R_or_C


/- Note: one might think the following lemma belongs in `analysis.normed_space.basic`.  But it
can't be placed there, because that file is an import of `data.complex.is_R_or_C`! -/

/-- Lemma to normalize a vector in a normed space `E` over either `ℂ` or `ℝ` to unit length. -/
@[simp] theorem norm_smul_inv_norm {K : Type u_1} [is_R_or_C K] {E : Type u_2} [normed_group E] [normed_space K E] {x : E} (hx : x ≠ 0) : norm (↑(norm x)⁻¹ • x) = 1 := sorry

