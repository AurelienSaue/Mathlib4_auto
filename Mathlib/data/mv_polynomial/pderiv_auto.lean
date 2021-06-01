/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.variables
import Mathlib.algebra.module.basic
import Mathlib.tactic.ring
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `mv_polynomial.pderiv i p` : the partial derivative of `p` with respect to `i`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_ring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/

namespace mv_polynomial


/-- `pderiv i p` is the partial derivative of `p` with respect to `i` -/
def pderiv {R : Type u} {σ : Type u_1} [comm_semiring R] (i : σ) :
    linear_map R (mv_polynomial σ R) (mv_polynomial σ R) :=
  linear_map.mk
    (fun (p : mv_polynomial σ R) =>
      finsupp.sum p
        fun (A : σ →₀ ℕ) (B : R) => monomial (A - finsupp.single i 1) (B * ↑(coe_fn A i)))
    sorry sorry

@[simp] theorem pderiv_monomial {R : Type u} {σ : Type u_1} {a : R} {s : σ →₀ ℕ} [comm_semiring R]
    {i : σ} :
    coe_fn (pderiv i) (monomial s a) = monomial (s - finsupp.single i 1) (a * ↑(coe_fn s i)) :=
  sorry

@[simp] theorem pderiv_C {R : Type u} {σ : Type u_1} {a : R} [comm_semiring R] {i : σ} :
    coe_fn (pderiv i) (coe_fn C a) = 0 :=
  sorry

theorem pderiv_eq_zero_of_not_mem_vars {R : Type u} {σ : Type u_1} [comm_semiring R] {i : σ}
    {f : mv_polynomial σ R} (h : ¬i ∈ vars f) : coe_fn (pderiv i) f = 0 :=
  sorry

theorem pderiv_monomial_single {R : Type u} {σ : Type u_1} {a : R} [comm_semiring R] {i : σ}
    {n : ℕ} :
    coe_fn (pderiv i) (monomial (finsupp.single i n) a) =
        monomial (finsupp.single i (n - 1)) (a * ↑n) :=
  sorry

theorem pderiv_monomial_mul {R : Type u} {σ : Type u_1} {a : R} {a' : R} {s : σ →₀ ℕ}
    [comm_semiring R] {i : σ} {s' : σ →₀ ℕ} :
    coe_fn (pderiv i) (monomial s a * monomial s' a') =
        coe_fn (pderiv i) (monomial s a) * monomial s' a' +
          monomial s a * coe_fn (pderiv i) (monomial s' a') :=
  sorry

@[simp] theorem pderiv_mul {R : Type u} {σ : Type u_1} [comm_semiring R] {i : σ}
    {f : mv_polynomial σ R} {g : mv_polynomial σ R} :
    coe_fn (pderiv i) (f * g) = coe_fn (pderiv i) f * g + f * coe_fn (pderiv i) g :=
  sorry

@[simp] theorem pderiv_C_mul {R : Type u} {σ : Type u_1} {a : R} [comm_semiring R]
    {f : mv_polynomial σ R} {i : σ} :
    coe_fn (pderiv i) (coe_fn C a * f) = coe_fn C a * coe_fn (pderiv i) f :=
  sorry

end Mathlib