/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.tensor_product
import Mathlib.PostPort

universes u v w 

namespace Mathlib

/-!
We provide the `R`-algebra structure on `matrix n n A` when `A` is an `R`-algebra,
and show `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
-/

protected instance matrix.algebra {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] {n : Type w} [fintype n] [DecidableEq n] : algebra R (matrix n n A) :=
  algebra.mk (ring_hom.mk (ring_hom.to_fun (ring_hom.comp (matrix.scalar n) (algebra_map R A))) sorry sorry sorry sorry)
    sorry sorry

theorem algebra_map_matrix_apply {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] {n : Type w} [fintype n] [DecidableEq n] {r : R} {i : n} {j : n} : coe_fn (algebra_map R (matrix n n A)) r i j = ite (i = j) (coe_fn (algebra_map R A) r) 0 := sorry

namespace matrix_equiv_tensor


/--
(Implementation detail).
The bare function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`, on pure tensors.
-/
def to_fun (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] (a : A) (m : matrix n n R) : matrix n n A :=
  fun (i j : n) => a * coe_fn (algebra_map R A) (m i j)

/--
(Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-linear map in the second tensor factor.
-/
def to_fun_right_linear (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] (a : A) : linear_map R (matrix n n R) (matrix n n A) :=
  linear_map.mk (to_fun R A n a) sorry sorry

/--
(Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-bilinear map.
-/
def to_fun_bilinear (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] : linear_map R A (linear_map R (matrix n n R) (matrix n n A)) :=
  linear_map.mk (to_fun_right_linear R A n) sorry sorry

/--
(Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-linear map.
-/
def to_fun_linear (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] : linear_map R (tensor_product R A (matrix n n R)) (matrix n n A) :=
  tensor_product.lift (to_fun_bilinear R A n)

/--
The function `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`, as an algebra homomorphism.
-/
def to_fun_alg_hom (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] : alg_hom R (tensor_product R A (matrix n n R)) (matrix n n A) :=
  algebra.tensor_product.alg_hom_of_linear_map_tensor_product (to_fun_linear R A n) sorry sorry

@[simp] theorem to_fun_alg_hom_apply (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] (a : A) (m : matrix n n R) : coe_fn (to_fun_alg_hom R A n) (tensor_product.tmul R a m) = fun (i j : n) => a * coe_fn (algebra_map R A) (m i j) := sorry

/--
(Implementation detail.)

The bare function `matrix n n A → A ⊗[R] matrix n n R`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def inv_fun (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] (M : matrix n n A) : tensor_product R A (matrix n n R) :=
  finset.sum finset.univ
    fun (p : n × n) =>
      tensor_product.tmul R (M (prod.fst p) (prod.snd p)) (matrix.std_basis_matrix (prod.fst p) (prod.snd p) 1)

@[simp] theorem inv_fun_zero (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] : inv_fun R A n 0 = 0 := sorry

@[simp] theorem inv_fun_add (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] (M : matrix n n A) (N : matrix n n A) : inv_fun R A n (M + N) = inv_fun R A n M + inv_fun R A n N := sorry

@[simp] theorem inv_fun_smul (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] (a : A) (M : matrix n n A) : (inv_fun R A n fun (i j : n) => a * M i j) = tensor_product.tmul R a 1 * inv_fun R A n M := sorry

@[simp] theorem inv_fun_algebra_map (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] (M : matrix n n R) : (inv_fun R A n fun (i j : n) => coe_fn (algebra_map R A) (M i j)) = tensor_product.tmul R 1 M := sorry

theorem right_inv (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] (M : matrix n n A) : coe_fn (to_fun_alg_hom R A n) (inv_fun R A n M) = M := sorry

theorem left_inv (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] (M : tensor_product R A (matrix n n R)) : inv_fun R A n (coe_fn (to_fun_alg_hom R A n) M) = M := sorry

/--
(Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] matrix n n R) ≃ matrix n n A`.
-/
def equiv (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] : tensor_product R A (matrix n n R) ≃ matrix n n A :=
  equiv.mk (⇑(to_fun_alg_hom R A n)) (inv_fun R A n) sorry sorry

end matrix_equiv_tensor


/--
The `R`-algebra isomorphism `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
-/
def matrix_equiv_tensor (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] : alg_equiv R (matrix n n A) (tensor_product R A (matrix n n R)) :=
  alg_equiv.symm (alg_equiv.mk (alg_hom.to_fun sorry) (equiv.inv_fun sorry) sorry sorry sorry sorry sorry)

@[simp] theorem matrix_equiv_tensor_apply (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] (M : matrix n n A) : coe_fn (matrix_equiv_tensor R A n) M =
  finset.sum finset.univ
    fun (p : n × n) =>
      tensor_product.tmul R (M (prod.fst p) (prod.snd p)) (matrix.std_basis_matrix (prod.fst p) (prod.snd p) 1) :=
  rfl

@[simp] theorem matrix_equiv_tensor_apply_std_basis (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] (i : n) (j : n) (x : A) : coe_fn (matrix_equiv_tensor R A n) (matrix.std_basis_matrix i j x) =
  tensor_product.tmul R x (matrix.std_basis_matrix i j 1) := sorry

@[simp] theorem matrix_equiv_tensor_apply_symm (R : Type u) [comm_semiring R] (A : Type v) [semiring A] [algebra R A] (n : Type w) [fintype n] [DecidableEq n] (a : A) (M : matrix n n R) : coe_fn (alg_equiv.symm (matrix_equiv_tensor R A n)) (tensor_product.tmul R a M) =
  fun (i j : n) => a * coe_fn (algebra_map R A) (M i j) := sorry

