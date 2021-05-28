/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.matrix.char_p
import Mathlib.linear_algebra.char_poly.basic
import Mathlib.linear_algebra.matrix
import Mathlib.ring_theory.polynomial.basic
import Mathlib.algebra.polynomial.big_operators
import Mathlib.group_theory.perm.cycles
import Mathlib.field_theory.finite.basic
import PostPort

universes u v u_1 

namespace Mathlib

/-!
# Characteristic polynomials

We give methods for computing coefficients of the characteristic polynomial.

## Main definitions

- `char_poly_degree_eq_dim` proves that the degree of the characteristic polynomial
  over a nonzero ring is the dimension of the matrix
- `det_eq_sign_char_poly_coeff` proves that the determinant is the constant term of the characteristic
  polynomial, up to sign.
- `trace_eq_neg_char_poly_coeff` proves that the trace is the negative of the (d-1)th coefficient of the
  characteristic polynomial, where d is the dimension of the matrix.
  For a nonzero ring, this is the second-highest coefficient.

-/

theorem char_matrix_apply_nat_degree {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] {M : matrix n n R} [nontrivial R] (i : n) (j : n) : polynomial.nat_degree (char_matrix M i j) = ite (i = j) 1 0 := sorry

theorem char_matrix_apply_nat_degree_le {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] {M : matrix n n R} (i : n) (j : n) : polynomial.nat_degree (char_matrix M i j) ≤ ite (i = j) 1 0 := sorry

theorem char_poly_sub_diagonal_degree_lt {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] (M : matrix n n R) : polynomial.degree (char_poly M - finset.prod finset.univ fun (i : n) => polynomial.X - coe_fn polynomial.C (M i i)) <
  ↑(fintype.card n - 1) := sorry

theorem char_poly_coeff_eq_prod_coeff_of_le {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] (M : matrix n n R) {k : ℕ} (h : fintype.card n - 1 ≤ k) : polynomial.coeff (char_poly M) k =
  polynomial.coeff (finset.prod finset.univ fun (i : n) => polynomial.X - coe_fn polynomial.C (M i i)) k := sorry

theorem det_of_card_zero {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] (h : fintype.card n = 0) (M : matrix n n R) : matrix.det M = 1 := sorry

theorem char_poly_degree_eq_dim {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] [nontrivial R] (M : matrix n n R) : polynomial.degree (char_poly M) = ↑(fintype.card n) := sorry

theorem char_poly_nat_degree_eq_dim {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] [nontrivial R] (M : matrix n n R) : polynomial.nat_degree (char_poly M) = fintype.card n :=
  polynomial.nat_degree_eq_of_degree_eq_some (char_poly_degree_eq_dim M)

theorem char_poly_monic {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] (M : matrix n n R) : polynomial.monic (char_poly M) := sorry

theorem trace_eq_neg_char_poly_coeff {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] [Nonempty n] (M : matrix n n R) : coe_fn (matrix.trace n R R) M = -polynomial.coeff (char_poly M) (fintype.card n - 1) := sorry

-- I feel like this should use polynomial.alg_hom_eval₂_algebra_map

theorem mat_poly_equiv_eval {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] (M : matrix n n (polynomial R)) (r : R) (i : n) (j : n) : polynomial.eval (coe_fn (matrix.scalar n) r) (coe_fn mat_poly_equiv M) i j = polynomial.eval r (M i j) := sorry

theorem eval_det {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] (M : matrix n n (polynomial R)) (r : R) : polynomial.eval r (matrix.det M) = matrix.det (polynomial.eval (coe_fn (matrix.scalar n) r) (coe_fn mat_poly_equiv M)) := sorry

theorem det_eq_sign_char_poly_coeff {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] (M : matrix n n R) : matrix.det M = (-1) ^ fintype.card n * polynomial.coeff (char_poly M) 0 := sorry

@[simp] theorem finite_field.char_poly_pow_card {n : Type v} [DecidableEq n] [fintype n] {K : Type u_1} [field K] [fintype K] (M : matrix n n K) : char_poly (M ^ fintype.card K) = char_poly M := sorry

@[simp] theorem zmod.char_poly_pow_card {n : Type v} [DecidableEq n] [fintype n] {p : ℕ} [fact (nat.prime p)] (M : matrix n n (zmod p)) : char_poly (M ^ p) = char_poly M :=
  eq.mp (Eq._oldrec (Eq.refl (char_poly (M ^ fintype.card (zmod p)) = char_poly M)) (zmod.card p))
    (finite_field.char_poly_pow_card M)

theorem finite_field.trace_pow_card {n : Type v} [DecidableEq n] [fintype n] {K : Type u_1} [field K] [fintype K] [Nonempty n] (M : matrix n n K) : coe_fn (matrix.trace n K K) (M ^ fintype.card K) = coe_fn (matrix.trace n K K) M ^ fintype.card K := sorry

theorem zmod.trace_pow_card {n : Type v} [DecidableEq n] [fintype n] {p : ℕ} [fact (nat.prime p)] [Nonempty n] (M : matrix n n (zmod p)) : coe_fn (matrix.trace n (zmod p) (zmod p)) (M ^ p) = coe_fn (matrix.trace n (zmod p) (zmod p)) M ^ p := sorry

namespace matrix


theorem is_integral {R : Type u} [comm_ring R] {n : Type v} [DecidableEq n] [fintype n] (M : matrix n n R) : is_integral R M :=
  Exists.intro (char_poly M) { left := char_poly_monic M, right := aeval_self_char_poly M }

theorem min_poly_dvd_char_poly {n : Type v} [DecidableEq n] [fintype n] {K : Type u_1} [field K] (M : matrix n n K) : minpoly K M ∣ char_poly M :=
  minpoly.dvd K M (aeval_self_char_poly M)

