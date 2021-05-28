/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.apply_fun
import Mathlib.ring_theory.matrix_algebra
import Mathlib.ring_theory.polynomial_algebra
import Mathlib.linear_algebra.nonsingular_inverse
import Mathlib.tactic.squeeze
import PostPort

universes u w 

namespace Mathlib

/-!
# Characteristic polynomials and the Cayley-Hamilton theorem

We define characteristic polynomials of matrices and
prove the Cayley–Hamilton theorem over arbitrary commutative rings.

## Main definitions

* `char_poly` is the characteristic polynomial of a matrix.

## Implementation details

We follow a nice proof from http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
-/

/--
The "characteristic matrix" of `M : matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def char_matrix {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] (M : matrix n n R) : matrix n n (polynomial R) :=
  coe_fn (matrix.scalar n) polynomial.X - coe_fn (ring_hom.map_matrix polynomial.C) M

@[simp] theorem char_matrix_apply_eq {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] (M : matrix n n R) (i : n) : char_matrix M i i = polynomial.X - coe_fn polynomial.C (M i i) := sorry

@[simp] theorem char_matrix_apply_ne {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] (M : matrix n n R) (i : n) (j : n) (h : i ≠ j) : char_matrix M i j = -coe_fn polynomial.C (M i j) := sorry

theorem mat_poly_equiv_char_matrix {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] (M : matrix n n R) : coe_fn mat_poly_equiv (char_matrix M) = polynomial.X - coe_fn polynomial.C M := sorry

/--
The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$.
-/
def char_poly {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] (M : matrix n n R) : polynomial R :=
  matrix.det (char_matrix M)

/--
The Cayley-Hamilton theorem, that the characteristic polynomial of a matrix,
applied to the matrix itself, is zero.

This holds over any commutative ring.
-/
-- This proof follows http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf

theorem aeval_self_char_poly {R : Type u} [comm_ring R] {n : Type w} [DecidableEq n] [fintype n] (M : matrix n n R) : coe_fn (polynomial.aeval M) (char_poly M) = 0 := sorry

