/-
  Copyright (c) 2020 Anne Baanen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Anne Baanen.

  The Special Linear group $SL(n, R)$
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.matrix
import Mathlib.linear_algebra.nonsingular_inverse
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# The Special Linear group $SL(n, R)$

This file defines the elements of the Special Linear group `special_linear_group n R`,
also written `SL(n, R)` or `SLₙ(R)`, consisting of all `n` by `n` `R`-matrices with
determinant `1`.  In addition, we define the group structure on `special_linear_group n R`
and the embedding into the general linear group `general_linear_group R (n → R)`
(i.e. `GL(n, R)` or `GLₙ(R)`).

## Main definitions

 * `matrix.special_linear_group` is the type of matrices with determinant 1
 * `matrix.special_linear_group.group` gives the group structure (under multiplication)
 * `matrix.special_linear_group.embedding_GL` is the embedding `SLₙ(R) → GLₙ(R)`

## Implementation notes
The inverse operation in the `special_linear_group` is defined to be the adjugate
matrix, so that `special_linear_group n R` has a group structure for all `comm_ring R`.

We define the elements of `special_linear_group` to be matrices, since we need to
compute their determinant. This is in contrast with `general_linear_group R M`,
which consists of invertible `R`-linear maps on `M`.

## References

 * https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/

namespace matrix


/-- `special_linear_group n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1. -/
def special_linear_group (n : Type u) [DecidableEq n] [fintype n] (R : Type v) [comm_ring R]  :=
  Subtype fun (A : matrix n n R) => det A = 1

namespace special_linear_group


protected instance coe_matrix {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : has_coe (special_linear_group n R) (matrix n n R) :=
  has_coe.mk fun (A : special_linear_group n R) => subtype.val A

protected instance coe_fun {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : has_coe_to_fun (special_linear_group n R) :=
  has_coe_to_fun.mk (fun (_x : special_linear_group n R) => n → n → R) fun (A : special_linear_group n R) => subtype.val A

/--
  `to_lin' A` is matrix multiplication of vectors by `A`, as a linear map.

  After the group structure on `special_linear_group n R` is defined,
  we show in `to_linear_equiv` that this gives a linear equivalence.
-/
def to_lin' {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) : linear_map R (n → R) (n → R) :=
  coe_fn to_lin' ⇑A

theorem ext_iff {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) (B : special_linear_group n R) : A = B ↔ ∀ (i j : n), coe_fn A i j = coe_fn B i j :=
  iff.trans subtype.ext_iff_val
    { mp := fun (h : subtype.val A = subtype.val B) (i j : n) => congr_fun (congr_fun h i) j, mpr := ext }

theorem ext {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) (B : special_linear_group n R) : (∀ (i j : n), coe_fn A i j = coe_fn B i j) → A = B :=
  iff.mpr (ext_iff A B)

protected instance has_inv {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : has_inv (special_linear_group n R) :=
  has_inv.mk fun (A : special_linear_group n R) => { val := adjugate ⇑A, property := sorry }

protected instance has_mul {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : Mul (special_linear_group n R) :=
  { mul :=
      fun (A B : special_linear_group n R) => { val := matrix.mul (subtype.val A) (subtype.val B), property := sorry } }

protected instance has_one {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : HasOne (special_linear_group n R) :=
  { one := { val := 1, property := sorry } }

protected instance inhabited {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : Inhabited (special_linear_group n R) :=
  { default := 1 }

@[simp] theorem inv_val {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) : ↑(A⁻¹) = adjugate ⇑A :=
  rfl

@[simp] theorem inv_apply {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) : ⇑(A⁻¹) = adjugate ⇑A :=
  rfl

@[simp] theorem mul_val {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) (B : special_linear_group n R) : ↑(A * B) = matrix.mul ⇑A ⇑B :=
  rfl

@[simp] theorem mul_apply {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) (B : special_linear_group n R) : ⇑(A * B) = matrix.mul ⇑A ⇑B :=
  rfl

@[simp] theorem one_val {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : ↑1 = 1 :=
  rfl

@[simp] theorem one_apply {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : ⇑1 = 1 :=
  rfl

@[simp] theorem det_coe_matrix {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) : det ⇑A = 1 :=
  subtype.property A

theorem det_coe_fun {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) : det ⇑A = 1 :=
  subtype.property A

@[simp] theorem to_lin'_mul {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) (B : special_linear_group n R) : to_lin' (A * B) = linear_map.comp (to_lin' A) (to_lin' B) :=
  to_lin'_mul ⇑A ⇑B

@[simp] theorem to_lin'_one {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : to_lin' 1 = linear_map.id :=
  to_lin'_one

protected instance group {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : group (special_linear_group n R) :=
  group.mk Mul.mul sorry 1 sorry sorry has_inv.inv (div_inv_monoid.div._default Mul.mul sorry 1 sorry sorry has_inv.inv)
    sorry

/-- `to_linear_equiv A` is matrix multiplication of vectors by `A`, as a linear equivalence. -/
def to_linear_equiv {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) : linear_equiv R (n → R) (n → R) :=
  linear_equiv.mk (linear_map.to_fun (coe_fn to_lin' ⇑A)) sorry sorry ⇑(to_lin' (A⁻¹)) sorry sorry

/-- `to_GL` is the map from the special linear group to the general linear group -/
def to_GL {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) : linear_map.general_linear_group R (n → R) :=
  linear_map.general_linear_group.of_linear_equiv (to_linear_equiv A)

theorem coe_to_GL {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) : ↑(to_GL A) = to_lin' A :=
  rfl

@[simp] theorem to_GL_one {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : to_GL 1 = 1 := sorry

@[simp] theorem to_GL_mul {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (A : special_linear_group n R) (B : special_linear_group n R) : to_GL (A * B) = to_GL A * to_GL B := sorry

/-- `special_linear_group.embedding_GL` is the embedding from `special_linear_group n R`
  to `general_linear_group n R`. -/
def embedding_GL {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] : special_linear_group n R →* linear_map.general_linear_group R (n → R) :=
  monoid_hom.mk (fun (A : special_linear_group n R) => to_GL A) sorry sorry

