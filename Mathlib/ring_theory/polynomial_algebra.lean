/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.matrix_algebra
import Mathlib.data.polynomial.algebra_map
import Mathlib.PostPort

universes u_1 u_2 w 

namespace Mathlib

/-!
# Algebra isomorphism between matrices of polynomials and polynomials of matrices

Given `[comm_ring R] [ring A] [algebra R A]`
we show `polynomial A ≃ₐ[R] (A ⊗[R] polynomial R)`.
Combining this with the isomorphism `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)` proved earlier
in `ring_theory.matrix_algebra`, we obtain the algebra isomorphism
```
def mat_poly_equiv :
  matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R)
```
which is characterized by
```
coeff (mat_poly_equiv m) k i j = coeff (m i j) k
```

We will use this algebra isomorphism to prove the Cayley-Hamilton theorem.
-/

namespace poly_equiv_tensor


/--
(Implementation detail).
The bare function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`, on pure tensors.
-/
def to_fun (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (a : A) (p : polynomial R) : polynomial A :=
  finsupp.sum p fun (n : ℕ) (r : R) => coe_fn (polynomial.monomial n) (a * coe_fn (algebra_map R A) r)

/--
(Implementation detail).
The function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`,
as a linear map in the second factor.
-/
def to_fun_linear_right (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (a : A) : linear_map R (polynomial R) (polynomial A) :=
  linear_map.mk (to_fun R A a) sorry sorry

/--
(Implementation detail).
The function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`,
as a bilinear function of two arguments.
-/
def to_fun_bilinear (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] : linear_map R A (linear_map R (polynomial R) (polynomial A)) :=
  linear_map.mk (to_fun_linear_right R A) sorry sorry

/--
(Implementation detail).
The function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`,
as a linear map.
-/
def to_fun_linear (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] : linear_map R (tensor_product R A (polynomial R)) (polynomial A) :=
  tensor_product.lift (to_fun_bilinear R A)

-- We apparently need to provide the decidable instance here

-- in order to successfully rewrite by this lemma.

theorem to_fun_linear_mul_tmul_mul_aux_1 (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (p : polynomial R) (k : ℕ) (h : Decidable (¬polynomial.coeff p k = 0)) (a : A) : ite (¬polynomial.coeff p k = 0) (a * coe_fn (algebra_map R A) (polynomial.coeff p k)) 0 =
  a * coe_fn (algebra_map R A) (polynomial.coeff p k) := sorry

theorem to_fun_linear_mul_tmul_mul_aux_2 (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (k : ℕ) (a₁ : A) (a₂ : A) (p₁ : polynomial R) (p₂ : polynomial R) : a₁ * a₂ * coe_fn (algebra_map R A) (polynomial.coeff (p₁ * p₂) k) =
  finset.sum (finset.nat.antidiagonal k)
    fun (x : ℕ × ℕ) =>
      a₁ * coe_fn (algebra_map R A) (polynomial.coeff p₁ (prod.fst x)) *
        (a₂ * coe_fn (algebra_map R A) (polynomial.coeff p₂ (prod.snd x))) := sorry

theorem to_fun_linear_mul_tmul_mul (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (a₁ : A) (a₂ : A) (p₁ : polynomial R) (p₂ : polynomial R) : coe_fn (to_fun_linear R A) (tensor_product.tmul R (a₁ * a₂) (p₁ * p₂)) =
  coe_fn (to_fun_linear R A) (tensor_product.tmul R a₁ p₁) * coe_fn (to_fun_linear R A) (tensor_product.tmul R a₂ p₂) := sorry

theorem to_fun_linear_algebra_map_tmul_one (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (r : R) : coe_fn (to_fun_linear R A) (tensor_product.tmul R (coe_fn (algebra_map R A) r) 1) =
  coe_fn (algebra_map R (polynomial A)) r := sorry

/--
(Implementation detail).
The algebra homomorphism `A ⊗[R] polynomial R →ₐ[R] polynomial A`.
-/
def to_fun_alg_hom (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] : alg_hom R (tensor_product R A (polynomial R)) (polynomial A) :=
  algebra.tensor_product.alg_hom_of_linear_map_tensor_product (to_fun_linear R A) (to_fun_linear_mul_tmul_mul R A)
    (to_fun_linear_algebra_map_tmul_one R A)

@[simp] theorem to_fun_alg_hom_apply_tmul (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (a : A) (p : polynomial R) : coe_fn (to_fun_alg_hom R A) (tensor_product.tmul R a p) =
  finsupp.sum p fun (n : ℕ) (r : R) => coe_fn (polynomial.monomial n) (a * coe_fn (algebra_map R A) r) := sorry

/--
(Implementation detail.)

The bare function `polynomial A → A ⊗[R] polynomial R`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def inv_fun (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (p : polynomial A) : tensor_product R A (polynomial R) :=
  polynomial.eval₂ (↑algebra.tensor_product.include_left) (tensor_product.tmul R 1 polynomial.X) p

@[simp] theorem inv_fun_add (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] {p : polynomial A} {q : polynomial A} : inv_fun R A (p + q) = inv_fun R A p + inv_fun R A q := sorry

theorem inv_fun_monomial (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (n : ℕ) (a : A) : inv_fun R A (coe_fn (polynomial.monomial n) a) =
  coe_fn algebra.tensor_product.include_left a * tensor_product.tmul R 1 polynomial.X ^ n :=
  polynomial.eval₂_monomial (↑algebra.tensor_product.include_left) (tensor_product.tmul R 1 polynomial.X)

theorem left_inv (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (x : tensor_product R A (polynomial R)) : inv_fun R A (coe_fn (to_fun_alg_hom R A) x) = x := sorry

theorem right_inv (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (x : polynomial A) : coe_fn (to_fun_alg_hom R A) (inv_fun R A x) = x := sorry

/--
(Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] polynomial R) ≃ polynomial A`.
-/
def equiv (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] : tensor_product R A (polynomial R) ≃ polynomial A :=
  equiv.mk (⇑(to_fun_alg_hom R A)) (inv_fun R A) (left_inv R A) (right_inv R A)

end poly_equiv_tensor


/--
The `R`-algebra isomorphism `polynomial A ≃ₐ[R] (A ⊗[R] polynomial R)`.
-/
def poly_equiv_tensor (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] : alg_equiv R (polynomial A) (tensor_product R A (polynomial R)) :=
  alg_equiv.symm (alg_equiv.mk (alg_hom.to_fun sorry) (equiv.inv_fun sorry) sorry sorry sorry sorry sorry)

@[simp] theorem poly_equiv_tensor_apply (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (p : polynomial A) : coe_fn (poly_equiv_tensor R A) p =
  polynomial.eval₂ (↑algebra.tensor_product.include_left) (tensor_product.tmul R 1 polynomial.X) p :=
  rfl

@[simp] theorem poly_equiv_tensor_symm_apply_tmul (R : Type u_1) (A : Type u_2) [comm_semiring R] [semiring A] [algebra R A] (a : A) (p : polynomial R) : coe_fn (alg_equiv.symm (poly_equiv_tensor R A)) (tensor_product.tmul R a p) =
  finsupp.sum p fun (n : ℕ) (r : R) => coe_fn (polynomial.monomial n) (a * coe_fn (algebra_map R A) r) := sorry

/--
The algebra isomorphism stating "matrices of polynomials are the same as polynomials of matrices".

(You probably shouldn't attempt to use this underlying definition ---
it's an algebra equivalence, and characterised extensionally by the lemma
`mat_poly_equiv_coeff_apply` below.)
-/
def mat_poly_equiv {R : Type u_1} [comm_semiring R] {n : Type w} [DecidableEq n] [fintype n] : alg_equiv R (matrix n n (polynomial R)) (polynomial (matrix n n R)) :=
  alg_equiv.trans
    (alg_equiv.trans (matrix_equiv_tensor R (polynomial R) n)
      (algebra.tensor_product.comm R (polynomial R) (matrix n n R)))
    (alg_equiv.symm (poly_equiv_tensor R (matrix n n R)))

theorem mat_poly_equiv_coeff_apply_aux_1 {R : Type u_1} [comm_semiring R] {n : Type w} [DecidableEq n] [fintype n] (i : n) (j : n) (k : ℕ) (x : R) : coe_fn mat_poly_equiv (matrix.std_basis_matrix i j (coe_fn (polynomial.monomial k) x)) =
  coe_fn (polynomial.monomial k) (matrix.std_basis_matrix i j x) := sorry

theorem mat_poly_equiv_coeff_apply_aux_2 {R : Type u_1} [comm_semiring R] {n : Type w} [DecidableEq n] [fintype n] (i : n) (j : n) (p : polynomial R) (k : ℕ) : polynomial.coeff (coe_fn mat_poly_equiv (matrix.std_basis_matrix i j p)) k =
  matrix.std_basis_matrix i j (polynomial.coeff p k) := sorry

@[simp] theorem mat_poly_equiv_coeff_apply {R : Type u_1} [comm_semiring R] {n : Type w} [DecidableEq n] [fintype n] (m : matrix n n (polynomial R)) (k : ℕ) (i : n) (j : n) : polynomial.coeff (coe_fn mat_poly_equiv m) k i j = polynomial.coeff (m i j) k := sorry

@[simp] theorem mat_poly_equiv_symm_apply_coeff {R : Type u_1} [comm_semiring R] {n : Type w} [DecidableEq n] [fintype n] (p : polynomial (matrix n n R)) (i : n) (j : n) (k : ℕ) : polynomial.coeff (coe_fn (alg_equiv.symm mat_poly_equiv) p i j) k = polynomial.coeff p k i j := sorry

theorem mat_poly_equiv_smul_one {R : Type u_1} [comm_semiring R] {n : Type w} [DecidableEq n] [fintype n] (p : polynomial R) : coe_fn mat_poly_equiv (p • 1) = polynomial.map (algebra_map R (matrix n n R)) p := sorry

