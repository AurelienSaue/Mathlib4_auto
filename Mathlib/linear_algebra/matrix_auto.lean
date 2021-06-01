/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Patrick Massot, Casper Putz
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.finite_dimensional
import Mathlib.linear_algebra.nonsingular_inverse
import Mathlib.linear_algebra.multilinear
import Mathlib.linear_algebra.dual
import Mathlib.PostPort

universes u_1 u_3 u_4 u_2 u_6 u_5 u_7 w v u 

namespace Mathlib

/-!
# Linear maps and matrices

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

It also defines the trace of an endomorphism, and the determinant of a family of vectors with
respect to some basis.

Some results are proved about the linear map corresponding to a
diagonal matrix (`range`, `ker` and `rank`).

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

 * `linear_map.to_matrix`: given bases `v₁ : ι → M₁` and `v₂ : κ → M₂`,
   the `R`-linear equivalence from `M₁ →ₗ[R] M₂` to `matrix κ ι R`
 * `matrix.to_lin`: the inverse of `linear_map.to_matrix`
 * `linear_map.to_matrix'`: the `R`-linear equivalence from `(n → R) →ₗ[R] (m → R)`
   to `matrix n m R` (with the standard basis on `n → R` and `m → R`)
 * `matrix.to_lin'`: the inverse of `linear_map.to_matrix'`

 * `alg_equiv_matrix`: given a basis indexed by `n`, the `R`-algebra equivalence between
   `R`-endomorphisms of `M` and `matrix n n R`
 * `matrix.trace`: the trace of a square matrix
 * `linear_map.trace`: the trace of an endomorphism
 * `is_basis.to_matrix`: the matrix whose columns are a given family of vectors in a given basis
 * `is_basis.to_matrix_equiv`: given a basis, the linear equivalence between families of vectors
   and matrices arising from `is_basis.to_matrix`
 * `is_basis.det`: the determinant of a family of vectors with respect to a basis, as a multilinear
   map

## Tags

linear_map, matrix, linear_equiv, diagonal, det, trace

-/

protected instance matrix.fintype {m : Type u_3} {n : Type u_4} [fintype m] [fintype n]
    [DecidableEq m] [DecidableEq n] (R : Type u_1) [fintype R] : fintype (matrix m n R) :=
  eq.mpr sorry pi.fintype

/-- `matrix.mul_vec M` is a linear map. -/
def matrix.mul_vec_lin {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4} [fintype m]
    [fintype n] (M : matrix m n R) : linear_map R (n → R) (m → R) :=
  linear_map.mk (matrix.mul_vec M) sorry sorry

@[simp] theorem matrix.mul_vec_lin_apply {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] (M : matrix m n R) (v : n → R) :
    coe_fn (matrix.mul_vec_lin M) v = matrix.mul_vec M v :=
  rfl

@[simp] theorem matrix.mul_vec_std_basis {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] [DecidableEq n] (M : matrix m n R) (i : m) (j : n) :
    matrix.mul_vec M (coe_fn (linear_map.std_basis R (fun (_x : n) => R) j) 1) i = M i j :=
  sorry

/-- Linear maps `(n → R) →ₗ[R] (m → R)` are linearly equivalent to `matrix m n R`. -/
def linear_map.to_matrix' {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4} [fintype m]
    [fintype n] [DecidableEq n] : linear_equiv R (linear_map R (n → R) (m → R)) (matrix m n R) :=
  linear_equiv.mk
    (fun (f : linear_map R (n → R) (m → R)) (i : m) (j : n) =>
      coe_fn f (coe_fn (linear_map.std_basis R (fun (ᾰ : n) => R) j) 1) i)
    sorry sorry matrix.mul_vec_lin sorry sorry

/-- A `matrix m n R` is linearly equivalent to a linear map `(n → R) →ₗ[R] (m → R)`. -/
def matrix.to_lin' {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4} [fintype m]
    [fintype n] [DecidableEq n] : linear_equiv R (matrix m n R) (linear_map R (n → R) (m → R)) :=
  linear_equiv.symm linear_map.to_matrix'

@[simp] theorem linear_map.to_matrix'_symm {R : Type u_1} [comm_ring R] {m : Type u_3}
    {n : Type u_4} [fintype m] [fintype n] [DecidableEq n] :
    linear_equiv.symm linear_map.to_matrix' = matrix.to_lin' :=
  rfl

@[simp] theorem matrix.to_lin'_symm {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] [DecidableEq n] :
    linear_equiv.symm matrix.to_lin' = linear_map.to_matrix' :=
  rfl

@[simp] theorem linear_map.to_matrix'_to_lin' {R : Type u_1} [comm_ring R] {m : Type u_3}
    {n : Type u_4} [fintype m] [fintype n] [DecidableEq n] (M : matrix m n R) :
    coe_fn linear_map.to_matrix' (coe_fn matrix.to_lin' M) = M :=
  linear_equiv.apply_symm_apply linear_map.to_matrix' M

@[simp] theorem matrix.to_lin'_to_matrix' {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] [DecidableEq n] (f : linear_map R (n → R) (m → R)) :
    coe_fn matrix.to_lin' (coe_fn linear_map.to_matrix' f) = f :=
  linear_equiv.apply_symm_apply matrix.to_lin' f

@[simp] theorem linear_map.to_matrix'_apply {R : Type u_1} [comm_ring R] {m : Type u_3}
    {n : Type u_4} [fintype m] [fintype n] [DecidableEq n] (f : linear_map R (n → R) (m → R))
    (i : m) (j : n) :
    coe_fn linear_map.to_matrix' f i j = coe_fn f (fun (j' : n) => ite (j' = j) 1 0) i :=
  sorry

@[simp] theorem matrix.to_lin'_apply {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] [DecidableEq n] (M : matrix m n R) (v : n → R) :
    coe_fn (coe_fn matrix.to_lin' M) v = matrix.mul_vec M v :=
  rfl

@[simp] theorem matrix.to_lin'_one {R : Type u_1} [comm_ring R] {n : Type u_4} [fintype n]
    [DecidableEq n] : coe_fn matrix.to_lin' 1 = linear_map.id :=
  sorry

@[simp] theorem linear_map.to_matrix'_id {R : Type u_1} [comm_ring R] {n : Type u_4} [fintype n]
    [DecidableEq n] : coe_fn linear_map.to_matrix' linear_map.id = 1 :=
  sorry

@[simp] theorem matrix.to_lin'_mul {R : Type u_1} [comm_ring R] {l : Type u_2} {m : Type u_3}
    {n : Type u_4} [fintype l] [fintype m] [fintype n] [DecidableEq n] [DecidableEq m]
    (M : matrix l m R) (N : matrix m n R) :
    coe_fn matrix.to_lin' (matrix.mul M N) =
        linear_map.comp (coe_fn matrix.to_lin' M) (coe_fn matrix.to_lin' N) :=
  sorry

theorem linear_map.to_matrix'_comp {R : Type u_1} [comm_ring R] {l : Type u_2} {m : Type u_3}
    {n : Type u_4} [fintype l] [fintype m] [fintype n] [DecidableEq n] [DecidableEq l]
    (f : linear_map R (n → R) (m → R)) (g : linear_map R (l → R) (n → R)) :
    coe_fn linear_map.to_matrix' (linear_map.comp f g) =
        matrix.mul (coe_fn linear_map.to_matrix' f) (coe_fn linear_map.to_matrix' g) :=
  sorry

theorem linear_map.to_matrix'_mul {R : Type u_1} [comm_ring R] {m : Type u_3} [fintype m]
    [DecidableEq m] (f : linear_map R (m → R) (m → R)) (g : linear_map R (m → R) (m → R)) :
    coe_fn linear_map.to_matrix' (f * g) =
        matrix.mul (coe_fn linear_map.to_matrix' f) (coe_fn linear_map.to_matrix' g) :=
  linear_map.to_matrix'_comp f g

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between linear maps `M₁ →ₗ M₂` and matrices over `R` indexed by the bases. -/
def linear_map.to_matrix {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4} [fintype m]
    [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁} (hv₁ : is_basis R v₁)
    {v₂ : m → M₂} (hv₂ : is_basis R v₂) : linear_equiv R (linear_map R M₁ M₂) (matrix m n R) :=
  linear_equiv.trans (linear_equiv.arrow_congr (is_basis.equiv_fun hv₁) (is_basis.equiv_fun hv₂))
    linear_map.to_matrix'

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between matrices over `R` indexed by the bases and linear maps `M₁ →ₗ M₂`. -/
def matrix.to_lin {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4} [fintype m] [fintype n]
    [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6} [add_comm_group M₁] [add_comm_group M₂]
    [module R M₁] [module R M₂] {v₁ : n → M₁} (hv₁ : is_basis R v₁) {v₂ : m → M₂}
    (hv₂ : is_basis R v₂) : linear_equiv R (matrix m n R) (linear_map R M₁ M₂) :=
  linear_equiv.symm (linear_map.to_matrix hv₁ hv₂)

@[simp] theorem linear_map.to_matrix_symm {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁} (hv₁ : is_basis R v₁)
    {v₂ : m → M₂} (hv₂ : is_basis R v₂) :
    linear_equiv.symm (linear_map.to_matrix hv₁ hv₂) = matrix.to_lin hv₁ hv₂ :=
  rfl

@[simp] theorem matrix.to_lin_symm {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁} (hv₁ : is_basis R v₁)
    {v₂ : m → M₂} (hv₂ : is_basis R v₂) :
    linear_equiv.symm (matrix.to_lin hv₁ hv₂) = linear_map.to_matrix hv₁ hv₂ :=
  rfl

@[simp] theorem matrix.to_lin_to_matrix {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁} (hv₁ : is_basis R v₁)
    {v₂ : m → M₂} (hv₂ : is_basis R v₂) (f : linear_map R M₁ M₂) :
    coe_fn (matrix.to_lin hv₁ hv₂) (coe_fn (linear_map.to_matrix hv₁ hv₂) f) = f :=
  sorry

@[simp] theorem linear_map.to_matrix_to_lin {R : Type u_1} [comm_ring R] {m : Type u_3}
    {n : Type u_4} [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6}
    [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁}
    (hv₁ : is_basis R v₁) {v₂ : m → M₂} (hv₂ : is_basis R v₂) (M : matrix m n R) :
    coe_fn (linear_map.to_matrix hv₁ hv₂) (coe_fn (matrix.to_lin hv₁ hv₂) M) = M :=
  sorry

theorem linear_map.to_matrix_apply {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁} (hv₁ : is_basis R v₁)
    {v₂ : m → M₂} (hv₂ : is_basis R v₂) (f : linear_map R M₁ M₂) (i : m) (j : n) :
    coe_fn (linear_map.to_matrix hv₁ hv₂) f i j =
        coe_fn (is_basis.equiv_fun hv₂) (coe_fn f (v₁ j)) i :=
  sorry

theorem linear_map.to_matrix_transpose_apply {R : Type u_1} [comm_ring R] {m : Type u_3}
    {n : Type u_4} [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6}
    [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁}
    (hv₁ : is_basis R v₁) {v₂ : m → M₂} (hv₂ : is_basis R v₂) (f : linear_map R M₁ M₂) (j : n) :
    matrix.transpose (coe_fn (linear_map.to_matrix hv₁ hv₂) f) j =
        coe_fn (is_basis.equiv_fun hv₂) (coe_fn f (v₁ j)) :=
  funext fun (i : m) => linear_map.to_matrix_apply hv₁ hv₂ f i j

theorem linear_map.to_matrix_apply' {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁} (hv₁ : is_basis R v₁)
    {v₂ : m → M₂} (hv₂ : is_basis R v₂) (f : linear_map R M₁ M₂) (i : m) (j : n) :
    coe_fn (linear_map.to_matrix hv₁ hv₂) f i j =
        coe_fn (coe_fn (is_basis.repr hv₂) (coe_fn f (v₁ j))) i :=
  linear_map.to_matrix_apply hv₁ hv₂ f i j

theorem linear_map.to_matrix_transpose_apply' {R : Type u_1} [comm_ring R] {m : Type u_3}
    {n : Type u_4} [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6}
    [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁}
    (hv₁ : is_basis R v₁) {v₂ : m → M₂} (hv₂ : is_basis R v₂) (f : linear_map R M₁ M₂) (j : n) :
    matrix.transpose (coe_fn (linear_map.to_matrix hv₁ hv₂) f) j =
        ⇑(coe_fn (is_basis.repr hv₂) (coe_fn f (v₁ j))) :=
  linear_map.to_matrix_transpose_apply hv₁ hv₂ f j

theorem matrix.to_lin_apply {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4} [fintype m]
    [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁} (hv₁ : is_basis R v₁)
    {v₂ : m → M₂} (hv₂ : is_basis R v₂) (M : matrix m n R) (v : M₁) :
    coe_fn (coe_fn (matrix.to_lin hv₁ hv₂) M) v =
        finset.sum finset.univ
          fun (j : m) => matrix.mul_vec M (coe_fn (is_basis.equiv_fun hv₁) v) j • v₂ j :=
  sorry

@[simp] theorem matrix.to_lin_self {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁} (hv₁ : is_basis R v₁)
    {v₂ : m → M₂} (hv₂ : is_basis R v₂) (M : matrix m n R) (i : n) :
    coe_fn (coe_fn (matrix.to_lin hv₁ hv₂) M) (v₁ i) =
        finset.sum finset.univ fun (j : m) => M j i • v₂ j :=
  sorry

@[simp] theorem linear_map.to_matrix_id {R : Type u_1} [comm_ring R] {n : Type u_4} [fintype n]
    [DecidableEq n] {M₁ : Type u_5} [add_comm_group M₁] [module R M₁] {v₁ : n → M₁}
    (hv₁ : is_basis R v₁) : coe_fn (linear_map.to_matrix hv₁ hv₁) linear_map.id = 1 :=
  sorry

@[simp] theorem matrix.to_lin_one {R : Type u_1} [comm_ring R] {n : Type u_4} [fintype n]
    [DecidableEq n] {M₁ : Type u_5} [add_comm_group M₁] [module R M₁] {v₁ : n → M₁}
    (hv₁ : is_basis R v₁) : coe_fn (matrix.to_lin hv₁ hv₁) 1 = linear_map.id :=
  sorry

theorem linear_map.to_matrix_range {R : Type u_1} [comm_ring R] {m : Type u_3} {n : Type u_4}
    [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁} (hv₁ : is_basis R v₁)
    {v₂ : m → M₂} (hv₂ : is_basis R v₂) [DecidableEq M₁] [DecidableEq M₂] (f : linear_map R M₁ M₂)
    (k : m) (i : n) :
    coe_fn (linear_map.to_matrix (is_basis.range hv₁) (is_basis.range hv₂)) f
          { val := v₂ k, property := set.mem_range_self k }
          { val := v₁ i, property := set.mem_range_self i } =
        coe_fn (linear_map.to_matrix hv₁ hv₂) f k i :=
  sorry

theorem linear_map.to_matrix_comp {R : Type u_1} [comm_ring R] {l : Type u_2} {m : Type u_3}
    {n : Type u_4} [fintype l] [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5}
    {M₂ : Type u_6} [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂]
    {v₁ : n → M₁} (hv₁ : is_basis R v₁) {v₂ : m → M₂} (hv₂ : is_basis R v₂) {M₃ : Type u_7}
    [add_comm_group M₃] [module R M₃] {v₃ : l → M₃} (hv₃ : is_basis R v₃) [DecidableEq m]
    (f : linear_map R M₂ M₃) (g : linear_map R M₁ M₂) :
    coe_fn (linear_map.to_matrix hv₁ hv₃) (linear_map.comp f g) =
        matrix.mul (coe_fn (linear_map.to_matrix hv₂ hv₃) f)
          (coe_fn (linear_map.to_matrix hv₁ hv₂) g) :=
  sorry

theorem linear_map.to_matrix_mul {R : Type u_1} [comm_ring R] {n : Type u_4} [fintype n]
    [DecidableEq n] {M₁ : Type u_5} [add_comm_group M₁] [module R M₁] {v₁ : n → M₁}
    (hv₁ : is_basis R v₁) (f : linear_map R M₁ M₁) (g : linear_map R M₁ M₁) :
    coe_fn (linear_map.to_matrix hv₁ hv₁) (f * g) =
        matrix.mul (coe_fn (linear_map.to_matrix hv₁ hv₁) f)
          (coe_fn (linear_map.to_matrix hv₁ hv₁) g) :=
  sorry

theorem matrix.to_lin_mul {R : Type u_1} [comm_ring R] {l : Type u_2} {m : Type u_3} {n : Type u_4}
    [fintype l] [fintype m] [fintype n] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6}
    [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂] {v₁ : n → M₁}
    (hv₁ : is_basis R v₁) {v₂ : m → M₂} (hv₂ : is_basis R v₂) {M₃ : Type u_7} [add_comm_group M₃]
    [module R M₃] {v₃ : l → M₃} (hv₃ : is_basis R v₃) [DecidableEq m] (A : matrix l m R)
    (B : matrix m n R) :
    coe_fn (matrix.to_lin hv₁ hv₃) (matrix.mul A B) =
        linear_map.comp (coe_fn (matrix.to_lin hv₂ hv₃) A) (coe_fn (matrix.to_lin hv₁ hv₂) B) :=
  sorry

/-- From a basis `e : ι → M` and a family of vectors `v : ι' → M`, make the matrix whose columns
are the vectors `v i` written in the basis `e`. -/
def is_basis.to_matrix {ι : Type u_1} {ι' : Type u_2} [fintype ι] [fintype ι'] {R : Type u_3}
    {M : Type u_4} [comm_ring R] [add_comm_group M] [module R M] {e : ι → M} (he : is_basis R e)
    (v : ι' → M) : matrix ι ι' R :=
  fun (i : ι) (j : ι') => coe_fn (is_basis.equiv_fun he) (v j) i

namespace is_basis


theorem to_matrix_apply {ι : Type u_1} {ι' : Type u_2} [fintype ι] [fintype ι'] {R : Type u_3}
    {M : Type u_4} [comm_ring R] [add_comm_group M] [module R M] {e : ι → M} (he : is_basis R e)
    (v : ι' → M) (i : ι) (j : ι') : to_matrix he v i j = coe_fn (equiv_fun he) (v j) i :=
  rfl

theorem to_matrix_transpose_apply {ι : Type u_1} {ι' : Type u_2} [fintype ι] [fintype ι']
    {R : Type u_3} {M : Type u_4} [comm_ring R] [add_comm_group M] [module R M] {e : ι → M}
    (he : is_basis R e) (v : ι' → M) (j : ι') :
    matrix.transpose (to_matrix he v) j = ⇑(coe_fn (repr he) (v j)) :=
  funext fun (_x : ι) => rfl

theorem to_matrix_eq_to_matrix_constr {ι : Type u_1} [fintype ι] {R : Type u_3} {M : Type u_4}
    [comm_ring R] [add_comm_group M] [module R M] {e : ι → M} (he : is_basis R e) [DecidableEq ι]
    (v : ι → M) : to_matrix he v = coe_fn (linear_map.to_matrix he he) (constr he v) :=
  sorry

@[simp] theorem to_matrix_self {ι : Type u_1} [fintype ι] {R : Type u_3} {M : Type u_4}
    [comm_ring R] [add_comm_group M] [module R M] {e : ι → M} (he : is_basis R e) [DecidableEq ι] :
    to_matrix he e = 1 :=
  sorry

theorem to_matrix_update {ι : Type u_1} {ι' : Type u_2} [fintype ι] [fintype ι'] {R : Type u_3}
    {M : Type u_4} [comm_ring R] [add_comm_group M] [module R M] {e : ι → M} (he : is_basis R e)
    (v : ι' → M) (j : ι') [DecidableEq ι'] (x : M) :
    to_matrix he (function.update v j x) =
        matrix.update_column (to_matrix he v) j ⇑(coe_fn (repr he) x) :=
  sorry

@[simp] theorem sum_to_matrix_smul_self {ι : Type u_1} {ι' : Type u_2} [fintype ι] [fintype ι']
    {R : Type u_3} {M : Type u_4} [comm_ring R] [add_comm_group M] [module R M] {e : ι → M}
    (he : is_basis R e) (v : ι' → M) (j : ι') :
    (finset.sum finset.univ fun (i : ι) => to_matrix he v i j • e i) = v j :=
  sorry

@[simp] theorem to_lin_to_matrix {ι : Type u_1} {ι' : Type u_2} [fintype ι] [fintype ι']
    {R : Type u_3} {M : Type u_4} [comm_ring R] [add_comm_group M] [module R M] {e : ι → M}
    (he : is_basis R e) (v : ι' → M) [DecidableEq ι'] (hv : is_basis R v) :
    coe_fn (matrix.to_lin hv he) (to_matrix he v) = linear_map.id :=
  sorry

/-- From a basis `e : ι → M`, build a linear equivalence between families of vectors `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in the basis `e`. -/
def to_matrix_equiv {ι : Type u_1} [fintype ι] {R : Type u_3} {M : Type u_4} [comm_ring R]
    [add_comm_group M] [module R M] {e : ι → M} (he : is_basis R e) :
    linear_equiv R (ι → M) (matrix ι ι R) :=
  linear_equiv.mk (to_matrix he) sorry sorry
    (fun (m : matrix ι ι R) (j : ι) => finset.sum finset.univ fun (i : ι) => m i j • e i) sorry
    sorry

end is_basis


@[simp] theorem is_basis_to_matrix_mul_linear_map_to_matrix {ι : Type u_1} {ι' : Type u_2}
    [fintype ι] [fintype ι'] {R : Type u_3} {M : Type u_4} [comm_ring R] [add_comm_group M]
    [module R M] {N : Type u_5} [add_comm_group N] [module R N] {b' : ι' → M} {c : ι → N}
    {c' : ι' → N} (hb' : is_basis R b') (hc : is_basis R c) (hc' : is_basis R c')
    (f : linear_map R M N) [DecidableEq ι'] :
    matrix.mul (is_basis.to_matrix hc c') (coe_fn (linear_map.to_matrix hb' hc') f) =
        coe_fn (linear_map.to_matrix hb' hc) f :=
  sorry

@[simp] theorem linear_map_to_matrix_mul_is_basis_to_matrix {ι : Type u_1} {ι' : Type u_2}
    [fintype ι] [fintype ι'] {R : Type u_3} {M : Type u_4} [comm_ring R] [add_comm_group M]
    [module R M] {N : Type u_5} [add_comm_group N] [module R N] {b : ι → M} {b' : ι' → M}
    {c' : ι' → N} (hb : is_basis R b) (hb' : is_basis R b') (hc' : is_basis R c')
    (f : linear_map R M N) [DecidableEq ι] [DecidableEq ι'] :
    matrix.mul (coe_fn (linear_map.to_matrix hb' hc') f) (is_basis.to_matrix hb' b) =
        coe_fn (linear_map.to_matrix hb hc') f :=
  sorry

theorem linear_equiv.is_unit_det {R : Type} [comm_ring R] {M : Type u_1} [add_comm_group M]
    [module R M] {M' : Type u_2} [add_comm_group M'] [module R M'] {ι : Type u_3} [DecidableEq ι]
    [fintype ι] {v : ι → M} {v' : ι → M'} (f : linear_equiv R M M') (hv : is_basis R v)
    (hv' : is_basis R v') : is_unit (matrix.det (coe_fn (linear_map.to_matrix hv hv') ↑f)) :=
  sorry

/-- Builds a linear equivalence from a linear map whose determinant in some bases is a unit. -/
def linear_equiv.of_is_unit_det {R : Type} [comm_ring R] {M : Type u_1} [add_comm_group M]
    [module R M] {M' : Type u_2} [add_comm_group M'] [module R M'] {ι : Type u_3} [DecidableEq ι]
    [fintype ι] {v : ι → M} {v' : ι → M'} {f : linear_map R M M'} {hv : is_basis R v}
    {hv' : is_basis R v'} (h : is_unit (matrix.det (coe_fn (linear_map.to_matrix hv hv') f))) :
    linear_equiv R M M' :=
  linear_equiv.mk ⇑f sorry sorry
    ⇑(coe_fn (matrix.to_lin hv' hv) (coe_fn (linear_map.to_matrix hv hv') f⁻¹)) sorry sorry

/-- The determinant of a family of vectors with respect to some basis, as an alternating
multilinear map. -/
def is_basis.det {R : Type} [comm_ring R] {M : Type u_1} [add_comm_group M] [module R M]
    {ι : Type u_3} [DecidableEq ι] [fintype ι] {e : ι → M} (he : is_basis R e) :
    alternating_map R M R ι :=
  alternating_map.mk
    (fun (v : (i : ι) → (fun (i : ι) => M) i) => matrix.det (is_basis.to_matrix he v)) sorry sorry
    sorry

theorem is_basis.det_apply {R : Type} [comm_ring R] {M : Type u_1} [add_comm_group M] [module R M]
    {ι : Type u_3} [DecidableEq ι] [fintype ι] {e : ι → M} (he : is_basis R e) (v : ι → M) :
    coe_fn (is_basis.det he) v = matrix.det (is_basis.to_matrix he v) :=
  rfl

theorem is_basis.det_self {R : Type} [comm_ring R] {M : Type u_1} [add_comm_group M] [module R M]
    {ι : Type u_3} [DecidableEq ι] [fintype ι] {e : ι → M} (he : is_basis R e) :
    coe_fn (is_basis.det he) e = 1 :=
  sorry

theorem is_basis.iff_det {R : Type} [comm_ring R] {M : Type u_1} [add_comm_group M] [module R M]
    {ι : Type u_3} [DecidableEq ι] [fintype ι] {e : ι → M} (he : is_basis R e) {v : ι → M} :
    is_basis R v ↔ is_unit (coe_fn (is_basis.det he) v) :=
  sorry

@[simp] theorem linear_map.to_matrix_transpose {K : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3}
    {ι₁ : Type u_4} {ι₂ : Type u_5} [field K] [add_comm_group V₁] [vector_space K V₁]
    [add_comm_group V₂] [vector_space K V₂] [fintype ι₁] [fintype ι₂] [DecidableEq ι₁]
    [DecidableEq ι₂] {B₁ : ι₁ → V₁} (h₁ : is_basis K B₁) {B₂ : ι₂ → V₂} (h₂ : is_basis K B₂)
    (u : linear_map K V₁ V₂) :
    coe_fn
          (linear_map.to_matrix (is_basis.dual_basis_is_basis h₂) (is_basis.dual_basis_is_basis h₁))
          (coe_fn module.dual.transpose u) =
        matrix.transpose (coe_fn (linear_map.to_matrix h₁ h₂) u) :=
  sorry

theorem linear_map.to_matrix_symm_transpose {K : Type u_1} {V₁ : Type u_2} {V₂ : Type u_3}
    {ι₁ : Type u_4} {ι₂ : Type u_5} [field K] [add_comm_group V₁] [vector_space K V₁]
    [add_comm_group V₂] [vector_space K V₂] [fintype ι₁] [fintype ι₂] [DecidableEq ι₁]
    [DecidableEq ι₂] {B₁ : ι₁ → V₁} (h₁ : is_basis K B₁) {B₂ : ι₂ → V₂} (h₂ : is_basis K B₂)
    (M : matrix ι₁ ι₂ K) :
    coe_fn
          (linear_equiv.symm
            (linear_map.to_matrix (is_basis.dual_basis_is_basis h₁)
              (is_basis.dual_basis_is_basis h₂)))
          (matrix.transpose M) =
        coe_fn module.dual.transpose (coe_fn (matrix.to_lin h₂ h₁) M) :=
  sorry

namespace matrix


/--
The diagonal of a square matrix.
-/
def diag (n : Type u_2) [fintype n] (R : Type v) (M : Type w) [semiring R] [add_comm_monoid M]
    [semimodule R M] : linear_map R (matrix n n M) (n → M) :=
  linear_map.mk (fun (A : matrix n n M) (i : n) => A i i) sorry sorry

@[simp] theorem diag_apply {n : Type u_2} [fintype n] {R : Type v} {M : Type w} [semiring R]
    [add_comm_monoid M] [semimodule R M] (A : matrix n n M) (i : n) :
    coe_fn (diag n R M) A i = A i i :=
  rfl

@[simp] theorem diag_one {n : Type u_2} [fintype n] {R : Type v} [semiring R] [DecidableEq n] :
    coe_fn (diag n R R) 1 = fun (i : n) => 1 :=
  sorry

@[simp] theorem diag_transpose {n : Type u_2} [fintype n] {R : Type v} {M : Type w} [semiring R]
    [add_comm_monoid M] [semimodule R M] (A : matrix n n M) :
    coe_fn (diag n R M) (transpose A) = coe_fn (diag n R M) A :=
  rfl

/--
The trace of a square matrix.
-/
def trace (n : Type u_2) [fintype n] (R : Type v) (M : Type w) [semiring R] [add_comm_monoid M]
    [semimodule R M] : linear_map R (matrix n n M) M :=
  linear_map.mk
    (fun (A : matrix n n M) => finset.sum finset.univ fun (i : n) => coe_fn (diag n R M) A i) sorry
    sorry

@[simp] theorem trace_diag {n : Type u_2} [fintype n] {R : Type v} {M : Type w} [semiring R]
    [add_comm_monoid M] [semimodule R M] (A : matrix n n M) :
    coe_fn (trace n R M) A = finset.sum finset.univ fun (i : n) => coe_fn (diag n R M) A i :=
  rfl

@[simp] theorem trace_one {n : Type u_2} [fintype n] {R : Type v} [semiring R] [DecidableEq n] :
    coe_fn (trace n R R) 1 = ↑(fintype.card n) :=
  sorry

@[simp] theorem trace_transpose {n : Type u_2} [fintype n] {R : Type v} {M : Type w} [semiring R]
    [add_comm_monoid M] [semimodule R M] (A : matrix n n M) :
    coe_fn (trace n R M) (transpose A) = coe_fn (trace n R M) A :=
  rfl

@[simp] theorem trace_transpose_mul {m : Type u_1} [fintype m] {n : Type u_2} [fintype n]
    {R : Type v} [semiring R] (A : matrix m n R) (B : matrix n m R) :
    coe_fn (trace n R R) (matrix.mul (transpose A) (transpose B)) =
        coe_fn (trace m R R) (matrix.mul A B) :=
  finset.sum_comm

theorem trace_mul_comm {m : Type u_1} [fintype m] {n : Type u_2} [fintype n] {S : Type v}
    [comm_ring S] (A : matrix m n S) (B : matrix n m S) :
    coe_fn (trace n S S) (matrix.mul B A) = coe_fn (trace m S S) (matrix.mul A B) :=
  sorry

theorem proj_diagonal {n : Type u_1} [fintype n] [DecidableEq n] {R : Type v} [comm_ring R] (i : n)
    (w : n → R) :
    linear_map.comp (linear_map.proj i) (coe_fn to_lin' (diagonal w)) = w i • linear_map.proj i :=
  sorry

theorem diagonal_comp_std_basis {n : Type u_1} [fintype n] [DecidableEq n] {R : Type v}
    [comm_ring R] (w : n → R) (i : n) :
    linear_map.comp (coe_fn to_lin' (diagonal w)) (linear_map.std_basis R (fun (ᾰ : n) => R) i) =
        w i • linear_map.std_basis R (fun (ᾰ : n) => R) i :=
  sorry

theorem diagonal_to_lin' {n : Type u_1} [fintype n] [DecidableEq n] {R : Type v} [comm_ring R]
    (w : n → R) :
    coe_fn to_lin' (diagonal w) = linear_map.pi fun (i : n) => w i • linear_map.proj i :=
  sorry

/-- An invertible matrix yields a linear equivalence from the free module to itself. -/
def to_linear_equiv {n : Type u_1} [fintype n] [DecidableEq n] {R : Type v} [comm_ring R]
    (P : matrix n n R) (h : is_unit P) : linear_equiv R (n → R) (n → R) :=
  (fun (h' : is_unit (det P)) =>
      linear_equiv.mk (linear_map.to_fun (coe_fn to_lin' P)) sorry sorry ⇑(coe_fn to_lin' (P⁻¹))
        sorry sorry)
    sorry

@[simp] theorem to_linear_equiv_apply {n : Type u_1} [fintype n] [DecidableEq n] {R : Type v}
    [comm_ring R] (P : matrix n n R) (h : is_unit P) : ↑(to_linear_equiv P h) = coe_fn to_lin' P :=
  rfl

@[simp] theorem to_linear_equiv_symm_apply {n : Type u_1} [fintype n] [DecidableEq n] {R : Type v}
    [comm_ring R] (P : matrix n n R) (h : is_unit P) :
    ↑(linear_equiv.symm (to_linear_equiv P h)) = coe_fn to_lin' (P⁻¹) :=
  rfl

theorem rank_vec_mul_vec {K : Type u} [field K] {m : Type u} {n : Type u} [fintype m] [fintype n]
    [DecidableEq n] (w : m → K) (v : n → K) : rank (coe_fn to_lin' (vec_mul_vec w v)) ≤ 1 :=
  sorry

theorem ker_diagonal_to_lin' {m : Type u_1} [fintype m] {K : Type u} [field K] [DecidableEq m]
    (w : m → K) :
    linear_map.ker (coe_fn to_lin' (diagonal w)) =
        supr
          fun (i : m) =>
            supr
              fun (H : i ∈ set_of fun (i : m) => w i = 0) =>
                linear_map.range (linear_map.std_basis K (fun (ᾰ : m) => K) i) :=
  sorry

theorem range_diagonal {m : Type u_1} [fintype m] {K : Type u} [field K] [DecidableEq m]
    (w : m → K) :
    linear_map.range (coe_fn to_lin' (diagonal w)) =
        supr
          fun (i : m) =>
            supr
              fun (H : i ∈ set_of fun (i : m) => w i ≠ 0) =>
                linear_map.range (linear_map.std_basis K (fun (ᾰ : m) => K) i) :=
  sorry

theorem rank_diagonal {m : Type u_1} [fintype m] {K : Type u} [field K] [DecidableEq m]
    [DecidableEq K] (w : m → K) :
    rank (coe_fn to_lin' (diagonal w)) = ↑(fintype.card (Subtype fun (i : m) => w i ≠ 0)) :=
  sorry

protected instance finite_dimensional {m : Type u_1} {n : Type u_2} [fintype m] [fintype n]
    {R : Type v} [field R] : finite_dimensional R (matrix m n R) :=
  linear_equiv.finite_dimensional (linear_equiv.symm (linear_equiv.uncurry R m n))

/--
The dimension of the space of finite dimensional matrices
is the product of the number of rows and columns.
-/
@[simp] theorem findim_matrix {m : Type u_1} {n : Type u_2} [fintype m] [fintype n] {R : Type v}
    [field R] : finite_dimensional.findim R (matrix m n R) = fintype.card m * fintype.card n :=
  sorry

/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
def reindex {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {m' : Type u_5} {n' : Type u_6}
    [fintype m'] [fintype n'] {R : Type v} (eₘ : m ≃ m') (eₙ : n ≃ n') :
    matrix m n R ≃ matrix m' n' R :=
  equiv.mk
    (fun (M : matrix m n R) (i : m') (j : n') =>
      M (coe_fn (equiv.symm eₘ) i) (coe_fn (equiv.symm eₙ) j))
    (fun (M : matrix m' n' R) (i : m) (j : n) => M (coe_fn eₘ i) (coe_fn eₙ j)) sorry sorry

@[simp] theorem reindex_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {m' : Type u_5}
    {n' : Type u_6} [fintype m'] [fintype n'] {R : Type v} (eₘ : m ≃ m') (eₙ : n ≃ n')
    (M : matrix m n R) :
    coe_fn (reindex eₘ eₙ) M =
        fun (i : m') (j : n') => M (coe_fn (equiv.symm eₘ) i) (coe_fn (equiv.symm eₙ) j) :=
  rfl

@[simp] theorem reindex_symm_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n]
    {m' : Type u_5} {n' : Type u_6} [fintype m'] [fintype n'] {R : Type v} (eₘ : m ≃ m')
    (eₙ : n ≃ n') (M : matrix m' n' R) :
    coe_fn (equiv.symm (reindex eₘ eₙ)) M = fun (i : m) (j : n) => M (coe_fn eₘ i) (coe_fn eₙ j) :=
  rfl

/-- The natural map that reindexes a matrix's rows and columns with equivalent types is a linear
equivalence. -/
def reindex_linear_equiv {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {m' : Type u_5}
    {n' : Type u_6} [fintype m'] [fintype n'] {R : Type v} [semiring R] (eₘ : m ≃ m')
    (eₙ : n ≃ n') : linear_equiv R (matrix m n R) (matrix m' n' R) :=
  linear_equiv.mk (equiv.to_fun (reindex eₘ eₙ)) sorry sorry (equiv.inv_fun (reindex eₘ eₙ)) sorry
    sorry

@[simp] theorem reindex_linear_equiv_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n]
    {m' : Type u_5} {n' : Type u_6} [fintype m'] [fintype n'] {R : Type v} [semiring R]
    (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m n R) :
    coe_fn (reindex_linear_equiv eₘ eₙ) M =
        fun (i : m') (j : n') => M (coe_fn (equiv.symm eₘ) i) (coe_fn (equiv.symm eₙ) j) :=
  rfl

@[simp] theorem reindex_linear_equiv_symm_apply {m : Type u_2} {n : Type u_3} [fintype m]
    [fintype n] {m' : Type u_5} {n' : Type u_6} [fintype m'] [fintype n'] {R : Type v} [semiring R]
    (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m' n' R) :
    coe_fn (linear_equiv.symm (reindex_linear_equiv eₘ eₙ)) M =
        fun (i : m) (j : n) => M (coe_fn eₘ i) (coe_fn eₙ j) :=
  rfl

theorem reindex_mul {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n]
    {l' : Type u_4} {m' : Type u_5} {n' : Type u_6} [fintype l'] [fintype m'] [fintype n']
    {R : Type v} [semiring R] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₗ : l ≃ l') (M : matrix m n R)
    (N : matrix n l R) :
    matrix.mul (coe_fn (reindex_linear_equiv eₘ eₙ) M) (coe_fn (reindex_linear_equiv eₙ eₗ) N) =
        coe_fn (reindex_linear_equiv eₘ eₗ) (matrix.mul M N) :=
  sorry

/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types is an equivalence of algebras. -/
def reindex_alg_equiv {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {R : Type v}
    [comm_semiring R] [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    alg_equiv R (matrix m m R) (matrix n n R) :=
  alg_equiv.mk (linear_equiv.to_fun (reindex_linear_equiv e e))
    (linear_equiv.inv_fun (reindex_linear_equiv e e)) sorry sorry sorry sorry sorry

@[simp] theorem reindex_alg_equiv_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n]
    {R : Type v} [comm_semiring R] [DecidableEq m] [DecidableEq n] (e : m ≃ n) (M : matrix m m R) :
    coe_fn (reindex_alg_equiv e) M =
        fun (i j : n) => M (coe_fn (equiv.symm e) i) (coe_fn (equiv.symm e) j) :=
  rfl

@[simp] theorem reindex_alg_equiv_symm_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n]
    {R : Type v} [comm_semiring R] [DecidableEq m] [DecidableEq n] (e : m ≃ n) (M : matrix n n R) :
    coe_fn (alg_equiv.symm (reindex_alg_equiv e)) M =
        fun (i j : m) => M (coe_fn e i) (coe_fn e j) :=
  rfl

theorem reindex_transpose {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {m' : Type u_5}
    {n' : Type u_6} [fintype m'] [fintype n'] {R : Type v} (eₘ : m ≃ m') (eₙ : n ≃ n')
    (M : matrix m n R) :
    transpose (coe_fn (reindex eₘ eₙ) M) = coe_fn (reindex eₙ eₘ) (transpose M) :=
  rfl

/-- `simp` version of `det_reindex_self`

`det_reindex_self` is not a good simp lemma because `reindex_apply` fires before.
So we have this lemma to continue from there. -/
@[simp] theorem det_reindex_self' {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {R : Type v}
    [DecidableEq m] [DecidableEq n] [comm_ring R] (e : m ≃ n) (A : matrix m m R) :
    (det fun (i j : n) => A (coe_fn (equiv.symm e) i) (coe_fn (equiv.symm e) j)) = det A :=
  sorry

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_reindex_self'`.
-/
theorem det_reindex_self {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {R : Type v}
    [DecidableEq m] [DecidableEq n] [comm_ring R] (e : m ≃ n) (A : matrix m m R) :
    det (coe_fn (reindex e e) A) = det A :=
  det_reindex_self' e A

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_reindex_self'`.
-/
theorem det_reindex_linear_equiv_self {m : Type u_2} {n : Type u_3} [fintype m] [fintype n]
    {R : Type v} [DecidableEq m] [DecidableEq n] [comm_ring R] (e : m ≃ n) (A : matrix m m R) :
    det (coe_fn (reindex_linear_equiv e e) A) = det A :=
  det_reindex_self' e A

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_reindex_self'`.
-/
theorem det_reindex_alg_equiv {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {R : Type v}
    [DecidableEq m] [DecidableEq n] [comm_ring R] (e : m ≃ n) (A : matrix m m R) :
    det (coe_fn (reindex_alg_equiv e) A) = det A :=
  det_reindex_self' e A

end matrix


namespace linear_map


/-- The trace of an endomorphism given a basis. -/
def trace_aux (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M] {ι : Type w}
    [DecidableEq ι] [fintype ι] {b : ι → M} (hb : is_basis R b) :
    linear_map R (linear_map R M M) R :=
  comp (matrix.trace ι R R) ↑(to_matrix hb hb)

@[simp] theorem trace_aux_def (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M]
    [module R M] {ι : Type w} [DecidableEq ι] [fintype ι] {b : ι → M} (hb : is_basis R b)
    (f : linear_map R M M) :
    coe_fn (trace_aux R hb) f = coe_fn (matrix.trace ι R R) (coe_fn (to_matrix hb hb) f) :=
  rfl

theorem trace_aux_eq' (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
    {ι : Type w} [DecidableEq ι] [fintype ι] {b : ι → M} (hb : is_basis R b) {κ : Type w}
    [DecidableEq κ] [fintype κ] {c : κ → M} (hc : is_basis R c) : trace_aux R hb = trace_aux R hc :=
  sorry

theorem trace_aux_range (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
    {ι : Type w} [DecidableEq ι] [fintype ι] {b : ι → M} (hb : is_basis R b) :
    trace_aux R (is_basis.range hb) = trace_aux R hb :=
  sorry

/-- where `ι` and `κ` can reside in different universes -/
theorem trace_aux_eq (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
    {ι : Type u_1} [DecidableEq ι] [fintype ι] {b : ι → M} (hb : is_basis R b) {κ : Type u_2}
    [DecidableEq κ] [fintype κ] {c : κ → M} (hc : is_basis R c) : trace_aux R hb = trace_aux R hc :=
  sorry

/-- Trace of an endomorphism independent of basis. -/
def trace (R : Type u) [comm_ring R] (M : Type v) [add_comm_group M] [module R M] :
    linear_map R (linear_map R M M) R :=
  dite (∃ (s : finset M), is_basis R fun (x : ↥↑s) => ↑x)
    (fun (H : ∃ (s : finset M), is_basis R fun (x : ↥↑s) => ↑x) => trace_aux R sorry)
    fun (H : ¬∃ (s : finset M), is_basis R fun (x : ↥↑s) => ↑x) => 0

theorem trace_eq_matrix_trace (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M]
    [module R M] {ι : Type w} [fintype ι] [DecidableEq ι] {b : ι → M} (hb : is_basis R b)
    (f : linear_map R M M) :
    coe_fn (trace R M) f = coe_fn (matrix.trace ι R R) (coe_fn (to_matrix hb hb) f) :=
  sorry

theorem trace_mul_comm (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
    (f : linear_map R M M) (g : linear_map R M M) :
    coe_fn (trace R M) (f * g) = coe_fn (trace R M) (g * f) :=
  sorry

protected instance finite_dimensional {K : Type u_1} [field K] {V : Type u_2} [add_comm_group V]
    [vector_space K V] [finite_dimensional K V] {W : Type u_3} [add_comm_group W] [vector_space K W]
    [finite_dimensional K W] : finite_dimensional K (linear_map K V W) :=
  Exists.dcases_on (finite_dimensional.exists_is_basis_finset K V)
    fun (bV : finset V) (hbV : is_basis K coe) =>
      Exists.dcases_on (finite_dimensional.exists_is_basis_finset K W)
        fun (bW : finset W) (hbW : is_basis K coe) =>
          linear_equiv.finite_dimensional (linear_equiv.symm (to_matrix hbV hbW))

/--
The dimension of the space of linear transformations is the product of the dimensions of the
domain and codomain.
-/
@[simp] theorem findim_linear_map {K : Type u_1} [field K] {V : Type u_2} [add_comm_group V]
    [vector_space K V] [finite_dimensional K V] {W : Type u_3} [add_comm_group W] [vector_space K W]
    [finite_dimensional K W] :
    finite_dimensional.findim K (linear_map K V W) =
        finite_dimensional.findim K V * finite_dimensional.findim K W :=
  sorry

end linear_map


/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the algebra structures. -/
def alg_equiv_matrix' {R : Type v} [comm_ring R] {n : Type u_1} [fintype n] [DecidableEq n] :
    alg_equiv R (module.End R (n → R)) (matrix n n R) :=
  alg_equiv.mk (linear_equiv.to_fun linear_map.to_matrix')
    (linear_equiv.inv_fun linear_map.to_matrix') sorry sorry sorry sorry sorry

/-- A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms. -/
def linear_equiv.alg_conj {R : Type v} [comm_ring R] {M₁ : Type u_1} {M₂ : Type (max u_2 u_3)}
    [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂] (e : linear_equiv R M₁ M₂) :
    alg_equiv R (module.End R M₁) (module.End R M₂) :=
  alg_equiv.mk (linear_equiv.to_fun (linear_equiv.conj e))
    (linear_equiv.inv_fun (linear_equiv.conj e)) sorry sorry sorry sorry sorry

/-- A basis of a module induces an equivalence of algebras from the endomorphisms of the module to
square matrices. -/
def alg_equiv_matrix {R : Type v} {M : Type w} {n : Type u_1} [fintype n] [comm_ring R]
    [add_comm_group M] [module R M] [DecidableEq n] {b : n → M} (h : is_basis R b) :
    alg_equiv R (module.End R M) (matrix n n R) :=
  alg_equiv.trans (linear_equiv.alg_conj (is_basis.equiv_fun h)) alg_equiv_matrix'

@[simp] theorem matrix.dot_product_std_basis_eq_mul {R : Type v} [semiring R] {n : Type w}
    [fintype n] [DecidableEq n] (v : n → R) (c : R) (i : n) :
    matrix.dot_product v (coe_fn (linear_map.std_basis R (fun (_x : n) => R) i) c) = v i * c :=
  sorry

@[simp] theorem matrix.dot_product_std_basis_one {R : Type v} [semiring R] {n : Type w} [fintype n]
    [DecidableEq n] (v : n → R) (i : n) :
    matrix.dot_product v (coe_fn (linear_map.std_basis R (fun (_x : n) => R) i) 1) = v i :=
  sorry

theorem matrix.dot_product_eq {R : Type v} [semiring R] {n : Type w} [fintype n] (v : n → R)
    (w : n → R) (h : ∀ (u : n → R), matrix.dot_product v u = matrix.dot_product w u) : v = w :=
  sorry

theorem matrix.dot_product_eq_iff {R : Type v} [semiring R] {n : Type w} [fintype n] {v : n → R}
    {w : n → R} : (∀ (u : n → R), matrix.dot_product v u = matrix.dot_product w u) ↔ v = w :=
  { mp :=
      fun (h : ∀ (u : n → R), matrix.dot_product v u = matrix.dot_product w u) =>
        matrix.dot_product_eq v w h,
    mpr := fun (h : v = w) (_x : n → R) => h ▸ rfl }

theorem matrix.dot_product_eq_zero {R : Type v} [semiring R] {n : Type w} [fintype n] (v : n → R)
    (h : ∀ (w : n → R), matrix.dot_product v w = 0) : v = 0 :=
  matrix.dot_product_eq v 0 fun (u : n → R) => Eq.symm (h u) ▸ Eq.symm (matrix.zero_dot_product u)

theorem matrix.dot_product_eq_zero_iff {R : Type v} [semiring R] {n : Type w} [fintype n]
    {v : n → R} : (∀ (w : n → R), matrix.dot_product v w = 0) ↔ v = 0 :=
  { mp := fun (h : ∀ (w : n → R), matrix.dot_product v w = 0) => matrix.dot_product_eq_zero v h,
    mpr := fun (h : v = 0) (w : n → R) => Eq.symm h ▸ matrix.zero_dot_product w }

end Mathlib