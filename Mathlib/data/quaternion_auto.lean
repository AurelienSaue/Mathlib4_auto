/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.ring_exp
import Mathlib.algebra.algebra.basic
import Mathlib.algebra.opposites
import Mathlib.data.equiv.ring
import Mathlib.PostPort

universes u_1 l 

namespace Mathlib

/-!
# Quaternions

In this file we define quaternions `ℍ[R]` over a commutative ring `R`, and define some
algebraic structures on `ℍ[R]`.

## Main definitions

* `quaternion_algebra R a b`, `ℍ[R, a, b]` :
  [quaternion algebra](https://en.wikipedia.org/wiki/Quaternion_algebra) with coefficients `a`, `b`
* `quaternion R`, `ℍ[R]` : the space of quaternions, a.k.a. `quaternion_algebra R (-1) (-1)`;
* `quaternion.norm_sq` : square of the norm of a quaternion;
* `quaternion.conj` : conjugate of a quaternion;

We also define the following algebraic structures on `ℍ[R]`:

* `ring ℍ[R, a, b]` and `algebra R ℍ[R, a, b]` : for any commutative ring `R`;
* `ring ℍ[R]` and `algebra R ℍ[R]` : for any commutative ring `R`;
* `domain ℍ[R]` : for a linear ordered commutative ring `R`;
* `division_algebra ℍ[R]` : for a linear ordered field `R`.

## Notation

The following notation is available with `open_locale quaternion`.

* `ℍ[R, c₁, c₂]` : `quaternion_algebra R  c₁ c₂`
* `ℍ[R]` : quaternions over `R`.

## Implementation notes

We define quaternions over any ring `R`, not just `ℝ` to be able to deal with, e.g., integer
or rational quaternions without using real numbers. In particular, all definitions in this file
are computable.

## Tags

quaternion
-/

/-- Quaternion algebra over a type with fixed coefficients $a=i^2$ and $b=j^2$.
Implemented as a structure with four fields: `re`, `im_i`, `im_j`, and `im_k`. -/
structure quaternion_algebra (R : Type u_1) (a : R) (b : R) where
  re : R
  im_i : R
  im_j : R
  im_k : R

namespace quaternion_algebra


@[simp] theorem mk.eta {R : Type u_1} {c₁ : R} {c₂ : R} (a : quaternion_algebra R c₁ c₂) :
    mk (re a) (im_i a) (im_j a) (im_k a) = a :=
  sorry

protected instance has_coe_t {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} :
    has_coe_t R (quaternion_algebra R c₁ c₂) :=
  has_coe_t.mk fun (x : R) => mk x 0 0 0

@[simp] theorem coe_re {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (x : R) : re ↑x = x := rfl

@[simp] theorem coe_im_i {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (x : R) : im_i ↑x = 0 := rfl

@[simp] theorem coe_im_j {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (x : R) : im_j ↑x = 0 := rfl

@[simp] theorem coe_im_k {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (x : R) : im_k ↑x = 0 := rfl

theorem coe_injective {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} : function.injective coe :=
  fun (x y : R) (h : ↑x = ↑y) => congr_arg re h

@[simp] theorem coe_inj {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} {x : R} {y : R} :
    ↑x = ↑y ↔ x = y :=
  function.injective.eq_iff coe_injective

@[simp] theorem has_zero_zero_im_j {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} : im_j 0 = 0 :=
  Eq.refl (im_j 0)

@[simp] theorem coe_zero {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} : ↑0 = 0 := rfl

protected instance inhabited {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} :
    Inhabited (quaternion_algebra R c₁ c₂) :=
  { default := 0 }

@[simp] theorem has_one_one_re {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} : re 1 = 1 :=
  Eq.refl (re 1)

@[simp] theorem coe_one {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} : ↑1 = 1 := rfl

@[simp] theorem has_add_add_im_i {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) (b : quaternion_algebra R c₁ c₂) :
    im_i (a + b) = im_i a + im_i b :=
  Eq.refl (im_i (a + b))

@[simp] theorem mk_add_mk {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (a₁ : R) (a₂ : R) (a₃ : R)
    (a₄ : R) (b₁ : R) (b₂ : R) (b₃ : R) (b₄ : R) :
    mk a₁ a₂ a₃ a₄ + mk b₁ b₂ b₃ b₄ = mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) :=
  rfl

protected instance has_neg {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} :
    Neg (quaternion_algebra R c₁ c₂) :=
  { neg := fun (a : quaternion_algebra R c₁ c₂) => mk (-re a) (-im_i a) (-im_j a) (-im_k a) }

@[simp] theorem neg_mk {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (a₁ : R) (a₂ : R) (a₃ : R)
    (a₄ : R) : -mk a₁ a₂ a₃ a₄ = mk (-a₁) (-a₂) (-a₃) (-a₄) :=
  rfl

@[simp] theorem has_sub_sub_im_k {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) (b : quaternion_algebra R c₁ c₂) :
    im_k (a - b) = im_k a - im_k b :=
  Eq.refl (im_k (a - b))

@[simp] theorem mk_sub_mk {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (a₁ : R) (a₂ : R) (a₃ : R)
    (a₄ : R) (b₁ : R) (b₂ : R) (b₃ : R) (b₄ : R) :
    mk a₁ a₂ a₃ a₄ - mk b₁ b₂ b₃ b₄ = mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) :=
  rfl

/-- Multiplication is given by

* `1 * x = x * 1 = x`;
* `i * i = c₁`;
* `j * j = c₂`;
* `i * j = k`, `j * i = -k`;
* `k * k = -c₁ * c₂`;
* `i * k = c₁ * j`, `k * i = `-c₁ * j`;
* `j * k = -c₂ * i`, `k * j = c₂ * i`.  -/
@[simp] theorem has_mul_mul_im_i {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) (b : quaternion_algebra R c₁ c₂) :
    im_i (a * b) = re a * im_i b + im_i a * re b - c₂ * im_j a * im_k b + c₂ * im_k a * im_j b :=
  Eq.refl (im_i (a * b))

@[simp] theorem mk_mul_mk {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (a₁ : R) (a₂ : R) (a₃ : R)
    (a₄ : R) (b₁ : R) (b₂ : R) (b₃ : R) (b₄ : R) :
    mk a₁ a₂ a₃ a₄ * mk b₁ b₂ b₃ b₄ =
        mk (a₁ * b₁ + c₁ * a₂ * b₂ + c₂ * a₃ * b₃ - c₁ * c₂ * a₄ * b₄)
          (a₁ * b₂ + a₂ * b₁ - c₂ * a₃ * b₄ + c₂ * a₄ * b₃)
          (a₁ * b₃ + c₁ * a₂ * b₄ + a₃ * b₁ - c₁ * a₄ * b₂)
          (a₁ * b₄ + a₂ * b₃ - a₃ * b₂ + a₄ * b₁) :=
  rfl

protected instance ring {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} :
    ring (quaternion_algebra R c₁ c₂) :=
  ring.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry Mul.mul sorry 1 sorry sorry sorry
    sorry

protected instance algebra {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} :
    algebra R (quaternion_algebra R c₁ c₂) :=
  algebra.mk (ring_hom.mk coe sorry sorry sorry sorry) sorry sorry

@[simp] theorem smul_re {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (r : R)
    (a : quaternion_algebra R c₁ c₂) : re (r • a) = r • re a :=
  rfl

@[simp] theorem smul_im_i {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (r : R)
    (a : quaternion_algebra R c₁ c₂) : im_i (r • a) = r • im_i a :=
  rfl

@[simp] theorem smul_im_j {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (r : R)
    (a : quaternion_algebra R c₁ c₂) : im_j (r • a) = r • im_j a :=
  rfl

@[simp] theorem smul_im_k {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (r : R)
    (a : quaternion_algebra R c₁ c₂) : im_k (r • a) = r • im_k a :=
  rfl

@[simp] theorem coe_add {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (x : R) (y : R) :
    ↑(x + y) = ↑x + ↑y :=
  ring_hom.map_add (algebra_map R (quaternion_algebra R c₁ c₂)) x y

@[simp] theorem coe_sub {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (x : R) (y : R) :
    ↑(x - y) = ↑x - ↑y :=
  ring_hom.map_sub (algebra_map R (quaternion_algebra R c₁ c₂)) x y

@[simp] theorem coe_neg {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (x : R) : ↑(-x) = -↑x :=
  ring_hom.map_neg (algebra_map R (quaternion_algebra R c₁ c₂)) x

@[simp] theorem coe_mul {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (x : R) (y : R) :
    ↑(x * y) = ↑x * ↑y :=
  ring_hom.map_mul (algebra_map R (quaternion_algebra R c₁ c₂)) x y

theorem coe_commutes {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (r : R)
    (a : quaternion_algebra R c₁ c₂) : ↑r * a = a * ↑r :=
  algebra.commutes r a

theorem coe_commute {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (r : R)
    (a : quaternion_algebra R c₁ c₂) : commute (↑r) a :=
  coe_commutes r a

theorem coe_mul_eq_smul {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (r : R)
    (a : quaternion_algebra R c₁ c₂) : ↑r * a = r • a :=
  Eq.symm (algebra.smul_def r a)

theorem mul_coe_eq_smul {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (r : R)
    (a : quaternion_algebra R c₁ c₂) : a * ↑r = r • a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * ↑r = r • a)) (Eq.symm (coe_commutes r a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑r * a = r • a)) (coe_mul_eq_smul r a))) (Eq.refl (r • a)))

@[simp] theorem coe_algebra_map {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} :
    ⇑(algebra_map R (quaternion_algebra R c₁ c₂)) = coe :=
  rfl

theorem smul_coe {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (x : R) (y : R) :
    x • ↑y = ↑(x * y) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x • ↑y = ↑(x * y))) (coe_mul x y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x • ↑y = ↑x * ↑y)) (coe_mul_eq_smul x ↑y)))
      (Eq.refl (x • ↑y)))

/-- Quaternion conjugate. -/
def conj {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} :
    linear_equiv R (quaternion_algebra R c₁ c₂) (quaternion_algebra R c₁ c₂) :=
  linear_equiv.of_involutive
    (linear_map.mk (fun (a : quaternion_algebra R c₁ c₂) => mk (re a) (-im_i a) (-im_j a) (-im_k a))
      sorry sorry)
    sorry

@[simp] theorem re_conj {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : re (coe_fn conj a) = re a :=
  rfl

@[simp] theorem im_i_conj {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : im_i (coe_fn conj a) = -im_i a :=
  rfl

@[simp] theorem im_j_conj {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : im_j (coe_fn conj a) = -im_j a :=
  rfl

@[simp] theorem im_k_conj {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : im_k (coe_fn conj a) = -im_k a :=
  rfl

@[simp] theorem conj_conj {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : coe_fn conj (coe_fn conj a) = a :=
  ext (coe_fn conj (coe_fn conj a)) a rfl (neg_neg (im_i a)) (neg_neg (im_j a)) (neg_neg (im_k a))

theorem conj_add {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (a : quaternion_algebra R c₁ c₂)
    (b : quaternion_algebra R c₁ c₂) : coe_fn conj (a + b) = coe_fn conj a + coe_fn conj b :=
  linear_equiv.map_add conj a b

@[simp] theorem conj_mul {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) (b : quaternion_algebra R c₁ c₂) :
    coe_fn conj (a * b) = coe_fn conj b * coe_fn conj a :=
  sorry

theorem conj_conj_mul {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) (b : quaternion_algebra R c₁ c₂) :
    coe_fn conj (coe_fn conj a * b) = coe_fn conj b * a :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (coe_fn conj (coe_fn conj a * b) = coe_fn conj b * a))
        (conj_mul (coe_fn conj a) b)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (coe_fn conj b * coe_fn conj (coe_fn conj a) = coe_fn conj b * a))
          (conj_conj a)))
      (Eq.refl (coe_fn conj b * a)))

theorem conj_mul_conj {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) (b : quaternion_algebra R c₁ c₂) :
    coe_fn conj (a * coe_fn conj b) = b * coe_fn conj a :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (coe_fn conj (a * coe_fn conj b) = b * coe_fn conj a))
        (conj_mul a (coe_fn conj b))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (coe_fn conj (coe_fn conj b) * coe_fn conj a = b * coe_fn conj a))
          (conj_conj b)))
      (Eq.refl (b * coe_fn conj a)))

theorem self_add_conj' {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : a + coe_fn conj a = ↑(bit0 1 * re a) :=
  sorry

theorem self_add_conj {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : a + coe_fn conj a = bit0 1 * ↑(re a) :=
  sorry

theorem conj_add_self' {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : coe_fn conj a + a = ↑(bit0 1 * re a) :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (coe_fn conj a + a = ↑(bit0 1 * re a))) (add_comm (coe_fn conj a) a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + coe_fn conj a = ↑(bit0 1 * re a))) (self_add_conj' a)))
      (Eq.refl ↑(bit0 1 * re a)))

theorem conj_add_self {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : coe_fn conj a + a = bit0 1 * ↑(re a) :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (coe_fn conj a + a = bit0 1 * ↑(re a))) (add_comm (coe_fn conj a) a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + coe_fn conj a = bit0 1 * ↑(re a))) (self_add_conj a)))
      (Eq.refl (bit0 1 * ↑(re a))))

theorem conj_eq_two_re_sub {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : coe_fn conj a = ↑(bit0 1 * re a) - a :=
  iff.mpr eq_sub_iff_add_eq (conj_add_self' a)

theorem commute_conj_self {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : commute (coe_fn conj a) a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (commute (coe_fn conj a) a)) (conj_eq_two_re_sub a)))
    (commute.sub_left (coe_commute (bit0 1 * re a) a) (commute.refl a))

theorem commute_self_conj {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : commute a (coe_fn conj a) :=
  commute.symm (commute_conj_self a)

theorem commute_conj_conj {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    {a : quaternion_algebra R c₁ c₂} {b : quaternion_algebra R c₁ c₂} (h : commute a b) :
    commute (coe_fn conj a) (coe_fn conj b) :=
  sorry

@[simp] theorem conj_coe {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (x : R) :
    coe_fn conj ↑x = ↑x :=
  sorry

theorem conj_smul {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (r : R)
    (a : quaternion_algebra R c₁ c₂) : coe_fn conj (r • a) = r • coe_fn conj a :=
  linear_equiv.map_smul conj r a

@[simp] theorem conj_one {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} : coe_fn conj 1 = 1 :=
  conj_coe 1

theorem eq_re_of_eq_coe {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    {a : quaternion_algebra R c₁ c₂} {x : R} (h : a = ↑x) : a = ↑(re a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = ↑(re a))) h))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑x = ↑(re ↑x))) (coe_re x))) (Eq.refl ↑x))

theorem eq_re_iff_mem_range_coe {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    {a : quaternion_algebra R c₁ c₂} : a = ↑(re a) ↔ a ∈ set.range coe :=
  sorry

@[simp] theorem conj_fixed {R : Type u_1} [comm_ring R] [no_zero_divisors R] [char_zero R] {c₁ : R}
    {c₂ : R} {a : quaternion_algebra R c₁ c₂} : coe_fn conj a = a ↔ a = ↑(re a) :=
  sorry

-- Can't use `rw ← conj_fixed` in the proof without additional assumptions

theorem conj_mul_eq_coe {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : coe_fn conj a * a = ↑(re (coe_fn conj a * a)) :=
  sorry

theorem mul_conj_eq_coe {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : a * coe_fn conj a = ↑(re (a * coe_fn conj a)) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (a * coe_fn conj a = ↑(re (a * coe_fn conj a))))
        (commute.eq (commute_self_conj a))))
    (conj_mul_eq_coe a)

theorem conj_zero {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} : coe_fn conj 0 = 0 :=
  linear_equiv.map_zero conj

theorem conj_neg {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (a : quaternion_algebra R c₁ c₂) :
    coe_fn conj (-a) = -coe_fn conj a :=
  linear_equiv.map_neg conj a

theorem conj_sub {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} (a : quaternion_algebra R c₁ c₂)
    (b : quaternion_algebra R c₁ c₂) : coe_fn conj (a - b) = coe_fn conj a - coe_fn conj b :=
  linear_equiv.map_sub conj a b

protected instance star_ring {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} :
    star_ring (quaternion_algebra R c₁ c₂) :=
  star_ring.mk conj_add

@[simp] theorem star_def {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R}
    (a : quaternion_algebra R c₁ c₂) : star a = coe_fn conj a :=
  rfl

/-- Quaternion conjugate as an `alg_equiv` to the opposite ring. -/
def conj_alg_equiv {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} :
    alg_equiv R (quaternion_algebra R c₁ c₂) (quaternion_algebra R c₁ c₂ᵒᵖ) :=
  alg_equiv.mk (opposite.op ∘ ⇑conj) (⇑conj ∘ opposite.unop) sorry sorry sorry sorry sorry

@[simp] theorem coe_conj_alg_equiv {R : Type u_1} [comm_ring R] {c₁ : R} {c₂ : R} :
    ⇑conj_alg_equiv = opposite.op ∘ ⇑conj :=
  rfl

end quaternion_algebra


/-- Space of quaternions over a type. Implemented as a structure with four fields:
`re`, `im_i`, `im_j`, and `im_k`. -/
def quaternion (R : Type u_1) [HasOne R] [Neg R] := quaternion_algebra R (-1) (-1)

namespace quaternion


protected instance has_coe_t {R : Type u_1} [comm_ring R] : has_coe_t R (quaternion R) :=
  quaternion_algebra.has_coe_t

protected instance ring {R : Type u_1} [comm_ring R] : ring (quaternion R) :=
  quaternion_algebra.ring

protected instance inhabited {R : Type u_1} [comm_ring R] : Inhabited (quaternion R) :=
  quaternion_algebra.inhabited

protected instance algebra {R : Type u_1} [comm_ring R] : algebra R (quaternion R) :=
  quaternion_algebra.algebra

protected instance star_ring {R : Type u_1} [comm_ring R] : star_ring (quaternion R) :=
  quaternion_algebra.star_ring

theorem ext {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    re a = re b → im_i a = im_i b → im_j a = im_j b → im_k a = im_k b → a = b :=
  quaternion_algebra.ext a b

theorem ext_iff {R : Type u_1} [comm_ring R] {a : quaternion R} {b : quaternion R} :
    a = b ↔ re a = re b ∧ im_i a = im_i b ∧ im_j a = im_j b ∧ im_k a = im_k b :=
  quaternion_algebra.ext_iff a b

@[simp] theorem coe_re {R : Type u_1} [comm_ring R] (x : R) : re ↑x = x := rfl

@[simp] theorem coe_im_i {R : Type u_1} [comm_ring R] (x : R) : im_i ↑x = 0 := rfl

@[simp] theorem coe_im_j {R : Type u_1} [comm_ring R] (x : R) : im_j ↑x = 0 := rfl

@[simp] theorem coe_im_k {R : Type u_1} [comm_ring R] (x : R) : im_k ↑x = 0 := rfl

@[simp] theorem zero_re {R : Type u_1} [comm_ring R] : re 0 = 0 := rfl

@[simp] theorem zero_im_i {R : Type u_1} [comm_ring R] : im_i 0 = 0 := rfl

@[simp] theorem zero_im_j {R : Type u_1} [comm_ring R] : im_j 0 = 0 := rfl

@[simp] theorem zero_im_k {R : Type u_1} [comm_ring R] : im_k 0 = 0 := rfl

@[simp] theorem coe_zero {R : Type u_1} [comm_ring R] : ↑0 = 0 := rfl

@[simp] theorem one_re {R : Type u_1} [comm_ring R] : re 1 = 1 := rfl

@[simp] theorem one_im_i {R : Type u_1} [comm_ring R] : im_i 1 = 0 := rfl

@[simp] theorem one_im_j {R : Type u_1} [comm_ring R] : im_j 1 = 0 := rfl

@[simp] theorem one_im_k {R : Type u_1} [comm_ring R] : im_k 1 = 0 := rfl

@[simp] theorem coe_one {R : Type u_1} [comm_ring R] : ↑1 = 1 := rfl

@[simp] theorem add_re {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    re (a + b) = re a + re b :=
  rfl

@[simp] theorem add_im_i {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    im_i (a + b) = im_i a + im_i b :=
  rfl

@[simp] theorem add_im_j {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    im_j (a + b) = im_j a + im_j b :=
  rfl

@[simp] theorem add_im_k {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    im_k (a + b) = im_k a + im_k b :=
  rfl

@[simp] theorem coe_add {R : Type u_1} [comm_ring R] (x : R) (y : R) : ↑(x + y) = ↑x + ↑y :=
  quaternion_algebra.coe_add x y

@[simp] theorem neg_re {R : Type u_1} [comm_ring R] (a : quaternion R) : re (-a) = -re a := rfl

@[simp] theorem neg_im_i {R : Type u_1} [comm_ring R] (a : quaternion R) : im_i (-a) = -im_i a :=
  rfl

@[simp] theorem neg_im_j {R : Type u_1} [comm_ring R] (a : quaternion R) : im_j (-a) = -im_j a :=
  rfl

@[simp] theorem neg_im_k {R : Type u_1} [comm_ring R] (a : quaternion R) : im_k (-a) = -im_k a :=
  rfl

@[simp] theorem coe_neg {R : Type u_1} [comm_ring R] (x : R) : ↑(-x) = -↑x :=
  quaternion_algebra.coe_neg x

@[simp] theorem sub_re {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    re (a - b) = re a - re b :=
  rfl

@[simp] theorem sub_im_i {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    im_i (a - b) = im_i a - im_i b :=
  rfl

@[simp] theorem sub_im_j {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    im_j (a - b) = im_j a - im_j b :=
  rfl

@[simp] theorem sub_im_k {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    im_k (a - b) = im_k a - im_k b :=
  rfl

@[simp] theorem coe_sub {R : Type u_1} [comm_ring R] (x : R) (y : R) : ↑(x - y) = ↑x - ↑y :=
  quaternion_algebra.coe_sub x y

@[simp] theorem mul_re {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    re (a * b) = re a * re b - im_i a * im_i b - im_j a * im_j b - im_k a * im_k b :=
  sorry

@[simp] theorem mul_im_i {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    im_i (a * b) = re a * im_i b + im_i a * re b + im_j a * im_k b - im_k a * im_j b :=
  sorry

@[simp] theorem mul_im_j {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    im_j (a * b) = re a * im_j b - im_i a * im_k b + im_j a * re b + im_k a * im_i b :=
  sorry

@[simp] theorem mul_im_k {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    im_k (a * b) = re a * im_k b + im_i a * im_j b - im_j a * im_i b + im_k a * re b :=
  sorry

@[simp] theorem coe_mul {R : Type u_1} [comm_ring R] (x : R) (y : R) : ↑(x * y) = ↑x * ↑y :=
  quaternion_algebra.coe_mul x y

theorem coe_injective {R : Type u_1} [comm_ring R] : function.injective coe :=
  quaternion_algebra.coe_injective

@[simp] theorem coe_inj {R : Type u_1} [comm_ring R] {x : R} {y : R} : ↑x = ↑y ↔ x = y :=
  function.injective.eq_iff coe_injective

@[simp] theorem smul_re {R : Type u_1} [comm_ring R] (r : R) (a : quaternion R) :
    re (r • a) = r • re a :=
  rfl

@[simp] theorem smul_im_i {R : Type u_1} [comm_ring R] (r : R) (a : quaternion R) :
    im_i (r • a) = r • im_i a :=
  rfl

@[simp] theorem smul_im_j {R : Type u_1} [comm_ring R] (r : R) (a : quaternion R) :
    im_j (r • a) = r • im_j a :=
  rfl

@[simp] theorem smul_im_k {R : Type u_1} [comm_ring R] (r : R) (a : quaternion R) :
    im_k (r • a) = r • im_k a :=
  rfl

theorem coe_commutes {R : Type u_1} [comm_ring R] (r : R) (a : quaternion R) : ↑r * a = a * ↑r :=
  quaternion_algebra.coe_commutes r a

theorem coe_commute {R : Type u_1} [comm_ring R] (r : R) (a : quaternion R) : commute (↑r) a :=
  quaternion_algebra.coe_commute r a

theorem coe_mul_eq_smul {R : Type u_1} [comm_ring R] (r : R) (a : quaternion R) : ↑r * a = r • a :=
  quaternion_algebra.coe_mul_eq_smul r a

theorem mul_coe_eq_smul {R : Type u_1} [comm_ring R] (r : R) (a : quaternion R) : a * ↑r = r • a :=
  quaternion_algebra.mul_coe_eq_smul r a

@[simp] theorem algebra_map_def {R : Type u_1} [comm_ring R] :
    ⇑(algebra_map R (quaternion R)) = coe :=
  rfl

theorem smul_coe {R : Type u_1} [comm_ring R] (x : R) (y : R) : x • ↑y = ↑(x * y) :=
  quaternion_algebra.smul_coe x y

/-- Quaternion conjugate. -/
def conj {R : Type u_1} [comm_ring R] : linear_equiv R (quaternion R) (quaternion R) :=
  quaternion_algebra.conj

@[simp] theorem conj_re {R : Type u_1} [comm_ring R] (a : quaternion R) :
    re (coe_fn conj a) = re a :=
  rfl

@[simp] theorem conj_im_i {R : Type u_1} [comm_ring R] (a : quaternion R) :
    im_i (coe_fn conj a) = -im_i a :=
  rfl

@[simp] theorem conj_im_j {R : Type u_1} [comm_ring R] (a : quaternion R) :
    im_j (coe_fn conj a) = -im_j a :=
  rfl

@[simp] theorem conj_im_k {R : Type u_1} [comm_ring R] (a : quaternion R) :
    im_k (coe_fn conj a) = -im_k a :=
  rfl

@[simp] theorem conj_conj {R : Type u_1} [comm_ring R] (a : quaternion R) :
    coe_fn conj (coe_fn conj a) = a :=
  quaternion_algebra.conj_conj a

@[simp] theorem conj_add {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    coe_fn conj (a + b) = coe_fn conj a + coe_fn conj b :=
  quaternion_algebra.conj_add a b

@[simp] theorem conj_mul {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    coe_fn conj (a * b) = coe_fn conj b * coe_fn conj a :=
  quaternion_algebra.conj_mul a b

theorem conj_conj_mul {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    coe_fn conj (coe_fn conj a * b) = coe_fn conj b * a :=
  quaternion_algebra.conj_conj_mul a b

theorem conj_mul_conj {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    coe_fn conj (a * coe_fn conj b) = b * coe_fn conj a :=
  quaternion_algebra.conj_mul_conj a b

theorem self_add_conj' {R : Type u_1} [comm_ring R] (a : quaternion R) :
    a + coe_fn conj a = ↑(bit0 1 * re a) :=
  quaternion_algebra.self_add_conj' a

theorem self_add_conj {R : Type u_1} [comm_ring R] (a : quaternion R) :
    a + coe_fn conj a = bit0 1 * ↑(re a) :=
  quaternion_algebra.self_add_conj a

theorem conj_add_self' {R : Type u_1} [comm_ring R] (a : quaternion R) :
    coe_fn conj a + a = ↑(bit0 1 * re a) :=
  quaternion_algebra.conj_add_self' a

theorem conj_add_self {R : Type u_1} [comm_ring R] (a : quaternion R) :
    coe_fn conj a + a = bit0 1 * ↑(re a) :=
  quaternion_algebra.conj_add_self a

theorem conj_eq_two_re_sub {R : Type u_1} [comm_ring R] (a : quaternion R) :
    coe_fn conj a = ↑(bit0 1 * re a) - a :=
  quaternion_algebra.conj_eq_two_re_sub a

theorem commute_conj_self {R : Type u_1} [comm_ring R] (a : quaternion R) :
    commute (coe_fn conj a) a :=
  quaternion_algebra.commute_conj_self a

theorem commute_self_conj {R : Type u_1} [comm_ring R] (a : quaternion R) :
    commute a (coe_fn conj a) :=
  quaternion_algebra.commute_self_conj a

theorem commute_conj_conj {R : Type u_1} [comm_ring R] {a : quaternion R} {b : quaternion R}
    (h : commute a b) : commute (coe_fn conj a) (coe_fn conj b) :=
  quaternion_algebra.commute_conj_conj h

theorem Mathlib.commute.quaternion_conj {R : Type u_1} [comm_ring R] {a : quaternion R}
    {b : quaternion R} (h : commute a b) : commute (coe_fn conj a) (coe_fn conj b) :=
  commute_conj_conj

@[simp] theorem conj_coe {R : Type u_1} [comm_ring R] (x : R) : coe_fn conj ↑x = ↑x :=
  quaternion_algebra.conj_coe x

@[simp] theorem conj_smul {R : Type u_1} [comm_ring R] (r : R) (a : quaternion R) :
    coe_fn conj (r • a) = r • coe_fn conj a :=
  quaternion_algebra.conj_smul r a

@[simp] theorem conj_one {R : Type u_1} [comm_ring R] : coe_fn conj 1 = 1 := conj_coe 1

theorem eq_re_of_eq_coe {R : Type u_1} [comm_ring R] {a : quaternion R} {x : R} (h : a = ↑x) :
    a = ↑(re a) :=
  quaternion_algebra.eq_re_of_eq_coe h

theorem eq_re_iff_mem_range_coe {R : Type u_1} [comm_ring R] {a : quaternion R} :
    a = ↑(re a) ↔ a ∈ set.range coe :=
  quaternion_algebra.eq_re_iff_mem_range_coe

@[simp] theorem conj_fixed {R : Type u_1} [comm_ring R] [no_zero_divisors R] [char_zero R]
    {a : quaternion R} : coe_fn conj a = a ↔ a = ↑(re a) :=
  quaternion_algebra.conj_fixed

theorem conj_mul_eq_coe {R : Type u_1} [comm_ring R] (a : quaternion R) :
    coe_fn conj a * a = ↑(re (coe_fn conj a * a)) :=
  quaternion_algebra.conj_mul_eq_coe a

theorem mul_conj_eq_coe {R : Type u_1} [comm_ring R] (a : quaternion R) :
    a * coe_fn conj a = ↑(re (a * coe_fn conj a)) :=
  quaternion_algebra.mul_conj_eq_coe a

@[simp] theorem conj_zero {R : Type u_1} [comm_ring R] : coe_fn conj 0 = 0 :=
  quaternion_algebra.conj_zero

@[simp] theorem conj_neg {R : Type u_1} [comm_ring R] (a : quaternion R) :
    coe_fn conj (-a) = -coe_fn conj a :=
  quaternion_algebra.conj_neg a

@[simp] theorem conj_sub {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    coe_fn conj (a - b) = coe_fn conj a - coe_fn conj b :=
  quaternion_algebra.conj_sub a b

/-- Quaternion conjugate as an `alg_equiv` to the opposite ring. -/
def conj_alg_equiv {R : Type u_1} [comm_ring R] : alg_equiv R (quaternion R) (quaternion Rᵒᵖ) :=
  quaternion_algebra.conj_alg_equiv

@[simp] theorem coe_conj_alg_equiv {R : Type u_1} [comm_ring R] :
    ⇑conj_alg_equiv = opposite.op ∘ ⇑conj :=
  rfl

/-- Square of the norm. -/
def norm_sq {R : Type u_1} [comm_ring R] : monoid_with_zero_hom (quaternion R) R :=
  monoid_with_zero_hom.mk (fun (a : quaternion R) => re (a * coe_fn conj a)) sorry sorry sorry

theorem norm_sq_def {R : Type u_1} [comm_ring R] (a : quaternion R) :
    coe_fn norm_sq a = re (a * coe_fn conj a) :=
  rfl

theorem norm_sq_def' {R : Type u_1} [comm_ring R] (a : quaternion R) :
    coe_fn norm_sq a = re a ^ bit0 1 + im_i a ^ bit0 1 + im_j a ^ bit0 1 + im_k a ^ bit0 1 :=
  sorry

theorem norm_sq_coe {R : Type u_1} [comm_ring R] (x : R) : coe_fn norm_sq ↑x = x ^ bit0 1 := sorry

@[simp] theorem norm_sq_neg {R : Type u_1} [comm_ring R] (a : quaternion R) :
    coe_fn norm_sq (-a) = coe_fn norm_sq a :=
  sorry

theorem self_mul_conj {R : Type u_1} [comm_ring R] (a : quaternion R) :
    a * coe_fn conj a = ↑(coe_fn norm_sq a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * coe_fn conj a = ↑(coe_fn norm_sq a))) (mul_conj_eq_coe a)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (↑(re (a * coe_fn conj a)) = ↑(coe_fn norm_sq a))) (norm_sq_def a)))
      (Eq.refl ↑(re (a * coe_fn conj a))))

theorem conj_mul_self {R : Type u_1} [comm_ring R] (a : quaternion R) :
    coe_fn conj a * a = ↑(coe_fn norm_sq a) :=
  sorry

theorem coe_norm_sq_add {R : Type u_1} [comm_ring R] (a : quaternion R) (b : quaternion R) :
    ↑(coe_fn norm_sq (a + b)) =
        ↑(coe_fn norm_sq a) + a * coe_fn conj b + b * coe_fn conj a + ↑(coe_fn norm_sq b) :=
  sorry

end quaternion


namespace quaternion


@[simp] theorem norm_sq_eq_zero {R : Type u_1} [linear_ordered_comm_ring R] {a : quaternion R} :
    coe_fn norm_sq a = 0 ↔ a = 0 :=
  sorry

theorem norm_sq_ne_zero {R : Type u_1} [linear_ordered_comm_ring R] {a : quaternion R} :
    coe_fn norm_sq a ≠ 0 ↔ a ≠ 0 :=
  not_congr norm_sq_eq_zero

@[simp] theorem norm_sq_nonneg {R : Type u_1} [linear_ordered_comm_ring R] {a : quaternion R} :
    0 ≤ coe_fn norm_sq a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ coe_fn norm_sq a)) (norm_sq_def' a)))
    (add_nonneg
      (add_nonneg (add_nonneg (pow_two_nonneg (re a)) (pow_two_nonneg (im_i a)))
        (pow_two_nonneg (im_j a)))
      (pow_two_nonneg (im_k a)))

@[simp] theorem norm_sq_le_zero {R : Type u_1} [linear_ordered_comm_ring R] {a : quaternion R} :
    coe_fn norm_sq a ≤ 0 ↔ a = 0 :=
  sorry

protected instance domain {R : Type u_1} [linear_ordered_comm_ring R] : domain (quaternion R) :=
  domain.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry
    ring.one sorry sorry sorry sorry sorry sorry

theorem has_inv_inv {R : Type u_1} [linear_ordered_field R] (a : quaternion R) :
    a⁻¹ = coe_fn norm_sq a⁻¹ • coe_fn conj a :=
  Eq.refl (a⁻¹)

protected instance division_ring {R : Type u_1} [linear_ordered_field R] :
    division_ring (quaternion R) :=
  division_ring.mk domain.add sorry domain.zero sorry sorry domain.neg domain.sub sorry sorry
    domain.mul sorry domain.one sorry sorry sorry sorry has_inv.inv
    (div_inv_monoid.div._default domain.mul sorry domain.one sorry sorry has_inv.inv) sorry sorry
    sorry

@[simp] theorem norm_sq_inv {R : Type u_1} [linear_ordered_field R] (a : quaternion R) :
    coe_fn norm_sq (a⁻¹) = (coe_fn norm_sq a⁻¹) :=
  monoid_with_zero_hom.map_inv' norm_sq a

@[simp] theorem norm_sq_div {R : Type u_1} [linear_ordered_field R] (a : quaternion R)
    (b : quaternion R) : coe_fn norm_sq (a / b) = coe_fn norm_sq a / coe_fn norm_sq b :=
  monoid_with_zero_hom.map_div norm_sq a b

end Mathlib