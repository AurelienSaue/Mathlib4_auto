/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.invertible
import Mathlib.data.mv_polynomial.variables
import Mathlib.data.mv_polynomial.comm_ring
import Mathlib.data.mv_polynomial.expand
import Mathlib.data.zmod.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Witt polynomials

To endow `witt_vector p R` with a ring structure,
we need to study the so-called Witt polynomials.

Fix a base value `p : ℕ`.
The `p`-adic Witt polynomials are an infinite family of polynomials
indexed by a natural number `n`, taking values in an arbitrary ring `R`.
The variables of these polynomials are represented by natural numbers.
The variable set of the `n`th Witt polynomial contains at most `n+1` elements `{0, ..., n}`,
with exactly these variables when `R` has characteristic `0`.

These polynomials are used to define the addition and multiplication operators
on the type of Witt vectors. (While this type itself is not complicated,
the ring operations are what make it interesting.)

When the base `p` is invertible in `R`, the `p`-adic Witt polynomials
form a basis for `mv_polynomial ℕ R`, equivalent to the standard basis.

## Main declarations

* `witt_polynomial p R n`: the `n`-th Witt polynomial, viewed as polynomial over the ring `R`
* `X_in_terms_of_W p R n`: if `p` is invertible, the polynomial `X n` is contained in the subalgebra
  generated by the Witt polynomials. `X_in_terms_of_W p R n` is the explicit polynomial,
  which upon being bound to the Witt polynomials yields `X n`.
* `bind₁_witt_polynomial_X_in_terms_of_W`: the proof of the claim that
  `bind₁ (X_in_terms_of_W p R) (W_ R n) = X n`
* `bind₁_X_in_terms_of_W_witt_polynomial`: the converse of the above statement

## Notation

In this file we use the following notation

* `p` is a natural number, typically assumed to be prime.
* `R` and `S` are commutative rings
* `W n` (and `W_ R n` when the ring needs to be explicit) denotes the `n`th Witt polynomial

-/

/-- `witt_polynomial p R n` is the `n`-th Witt polynomial
with respect to a prime `p` with coefficients in a commutative ring `R`.
It is defined as:

`∑_{i ≤ n} p^i X_i^{p^{n-i}} ∈ R[X_0, X_1, X_2, …]`. -/
def witt_polynomial (p : ℕ) (R : Type u_1) [comm_ring R] (n : ℕ) : mv_polynomial ℕ R :=
  finset.sum (finset.range (n + 1))
    fun (i : ℕ) => mv_polynomial.monomial (finsupp.single i (p ^ (n - i))) (↑p ^ i)

theorem witt_polynomial_eq_sum_C_mul_X_pow (p : ℕ) (R : Type u_1) [comm_ring R] (n : ℕ) :
    witt_polynomial p R n =
        finset.sum (finset.range (n + 1))
          fun (i : ℕ) => coe_fn mv_polynomial.C (↑p ^ i) * mv_polynomial.X i ^ p ^ (n - i) :=
  sorry

/-! We set up notation locally to this file, to keep statements short and comprehensible.
This allows us to simply write `W n` or `W_ ℤ n`. -/

-- Notation with ring of coefficients explicit

-- Notation with ring of coefficients implicit

/- The first observation is that the Witt polynomial doesn't really depend on the coefficient ring.
If we map the coefficients through a ring homomorphism, we obtain the corresponding Witt polynomial
over the target ring. -/

@[simp] theorem map_witt_polynomial (p : ℕ) {R : Type u_1} [comm_ring R] {S : Type u_2}
    [comm_ring S] (f : R →+* S) (n : ℕ) :
    coe_fn (mv_polynomial.map f) (witt_polynomial p R n) = witt_polynomial p S n :=
  sorry

@[simp] theorem constant_coeff_witt_polynomial (p : ℕ) (R : Type u_1) [comm_ring R]
    [hp : fact (nat.prime p)] (n : ℕ) :
    coe_fn mv_polynomial.constant_coeff (witt_polynomial p R n) = 0 :=
  sorry

@[simp] theorem witt_polynomial_zero (p : ℕ) (R : Type u_1) [comm_ring R] :
    witt_polynomial p R 0 = mv_polynomial.X 0 :=
  sorry

@[simp] theorem witt_polynomial_one (p : ℕ) (R : Type u_1) [comm_ring R] :
    witt_polynomial p R 1 = coe_fn mv_polynomial.C ↑p * mv_polynomial.X 1 + mv_polynomial.X 0 ^ p :=
  sorry

theorem aeval_witt_polynomial (p : ℕ) (R : Type u_1) [comm_ring R] {A : Type u_2} [comm_ring A]
    [algebra R A] (f : ℕ → A) (n : ℕ) :
    coe_fn (mv_polynomial.aeval f) (witt_polynomial p R n) =
        finset.sum (finset.range (n + 1)) fun (i : ℕ) => ↑p ^ i * f i ^ p ^ (n - i) :=
  sorry

/--
Over the ring `zmod (p^(n+1))`, we produce the `n+1`st Witt polynomial
by expanding the `n`th witt polynomial by `p`.
-/
@[simp] theorem witt_polynomial_zmod_self (p : ℕ) (n : ℕ) :
    witt_polynomial p (zmod (p ^ (n + 1))) (n + 1) =
        coe_fn (mv_polynomial.expand p) (witt_polynomial p (zmod (p ^ (n + 1))) n) :=
  sorry

-- in fact, `0 < p` would be sufficient

theorem witt_polynomial_vars (p : ℕ) (R : Type u_1) [comm_ring R] [hp : fact (nat.prime p)]
    [char_zero R] (n : ℕ) : mv_polynomial.vars (witt_polynomial p R n) = finset.range (n + 1) :=
  sorry

theorem witt_polynomial_vars_subset (p : ℕ) (R : Type u_1) [comm_ring R] [hp : fact (nat.prime p)]
    (n : ℕ) : mv_polynomial.vars (witt_polynomial p R n) ⊆ finset.range (n + 1) :=
  sorry

/-!

## Witt polynomials as a basis of the polynomial algebra

If `p` is invertible in `R`, then the Witt polynomials form a basis
of the polynomial algebra `mv_polynomial ℕ R`.
The polynomials `X_in_terms_of_W` give the coordinate transformation in the backwards direction.
-/

/-- The `X_in_terms_of_W p R n` is the polynomial on the basis of Witt polynomials
that corresponds to the ordinary `X n`. -/
def X_in_terms_of_W (p : ℕ) (R : Type u_1) [comm_ring R] [invertible ↑p] : ℕ → mv_polynomial ℕ R :=
  sorry

theorem X_in_terms_of_W_eq (p : ℕ) (R : Type u_1) [comm_ring R] [invertible ↑p] {n : ℕ} :
    X_in_terms_of_W p R n =
        (mv_polynomial.X n -
            finset.sum (finset.range n)
              fun (i : ℕ) =>
                coe_fn mv_polynomial.C (↑p ^ i) * X_in_terms_of_W p R i ^ p ^ (n - i)) *
          coe_fn mv_polynomial.C (⅟ ^ n) :=
  sorry

@[simp] theorem constant_coeff_X_in_terms_of_W (p : ℕ) (R : Type u_1) [comm_ring R]
    [hp : fact (nat.prime p)] [invertible ↑p] (n : ℕ) :
    coe_fn mv_polynomial.constant_coeff (X_in_terms_of_W p R n) = 0 :=
  sorry

@[simp] theorem X_in_terms_of_W_zero (p : ℕ) (R : Type u_1) [comm_ring R] [invertible ↑p] :
    X_in_terms_of_W p R 0 = mv_polynomial.X 0 :=
  sorry

theorem X_in_terms_of_W_vars_aux (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) :
    n ∈ mv_polynomial.vars (X_in_terms_of_W p ℚ n) ∧
        mv_polynomial.vars (X_in_terms_of_W p ℚ n) ⊆ finset.range (n + 1) :=
  sorry

theorem X_in_terms_of_W_vars_subset (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) :
    mv_polynomial.vars (X_in_terms_of_W p ℚ n) ⊆ finset.range (n + 1) :=
  and.right (X_in_terms_of_W_vars_aux p n)

theorem X_in_terms_of_W_aux (p : ℕ) (R : Type u_1) [comm_ring R] [invertible ↑p] (n : ℕ) :
    X_in_terms_of_W p R n * coe_fn mv_polynomial.C (↑p ^ n) =
        mv_polynomial.X n -
          finset.sum (finset.range n)
            fun (i : ℕ) => coe_fn mv_polynomial.C (↑p ^ i) * X_in_terms_of_W p R i ^ p ^ (n - i) :=
  sorry

@[simp] theorem bind₁_X_in_terms_of_W_witt_polynomial (p : ℕ) (R : Type u_1) [comm_ring R]
    [invertible ↑p] (k : ℕ) :
    coe_fn (mv_polynomial.bind₁ (X_in_terms_of_W p R)) (witt_polynomial p R k) =
        mv_polynomial.X k :=
  sorry

@[simp] theorem bind₁_witt_polynomial_X_in_terms_of_W (p : ℕ) (R : Type u_1) [comm_ring R]
    [invertible ↑p] (n : ℕ) :
    coe_fn (mv_polynomial.bind₁ (witt_polynomial p R)) (X_in_terms_of_W p R n) =
        mv_polynomial.X n :=
  sorry

end Mathlib