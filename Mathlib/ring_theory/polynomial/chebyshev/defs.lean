/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.derivative
import Mathlib.tactic.ring
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Chebyshev polynomials

The Chebyshev polynomials are two families of polynomials indexed by `ℕ`,
with integral coefficients.

See the file `ring_theory.polynomial.chebyshev.basic` for more properties.

## Main definitions

* `polynomial.chebyshev₁`: the Chebyshev polynomials of the first kind.
* `polynomial.chebyshev₂`: the Chebyshev polynomials of the second kind.
* `polynomial.lambdashev`: a variant on the Chebyshev polynomials that define a Lambda structure
  on `polynomial ℤ`.

## Main statements

* The formal derivative of the Chebyshev polynomials of the first kind is a scalar multiple of the
  Chebyshev polynomials of the second kind.

## Implementation details

In this file we only give definitions and some very elementary simp-lemmas.
This way, we can import this file in `analysis.special_functions.trigonometric`,
and import that file in turn, in `ring_theory.polynomial.chebyshev.basic`.

## References

[Lionel Ponton, _Roots of the Chebyshev polynomials: A purely algebraic approach_]
[ponton2020chebyshev]

## TODO

* Redefine and/or relate the definition of Chebyshev polynomials to `linear_recurrence`.
* Add explicit formula involving square roots for Chebyshev polynomials
  `ring_theory.polynomial.chebyshev.basic`.
* Compute zeroes and extrema of Chebyshev polynomials.
* Prove that the roots of the Chebyshev polynomials (except 0) are irrational.
* Prove minimax properties of Chebyshev polynomials.
* Define a variant of Chebyshev polynomials of the second kind removing the 2
  (sometimes Dickson polynomials of the second kind) or even more general Dickson polynomials.
* Prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the adjacency
  matrices of simple connected graphs which annihilate the Dickson polynomials.
-/

namespace polynomial


/-- `chebyshev₁ n` is the `n`-th Chebyshev polynomial of the first kind -/
def chebyshev₁ (R : Type u_1) [comm_ring R] : ℕ → polynomial R :=
  sorry

@[simp] theorem chebyshev₁_zero (R : Type u_1) [comm_ring R] : chebyshev₁ R 0 = 1 :=
  rfl

@[simp] theorem chebyshev₁_one (R : Type u_1) [comm_ring R] : chebyshev₁ R 1 = X :=
  rfl

theorem chebyshev₁_two (R : Type u_1) [comm_ring R] : chebyshev₁ R (bit0 1) = bit0 1 * X ^ bit0 1 - 1 := sorry

@[simp] theorem chebyshev₁_add_two (R : Type u_1) [comm_ring R] (n : ℕ) : chebyshev₁ R (n + bit0 1) = bit0 1 * X * chebyshev₁ R (n + 1) - chebyshev₁ R n := sorry

theorem chebyshev₁_of_two_le (R : Type u_1) [comm_ring R] (n : ℕ) (h : bit0 1 ≤ n) : chebyshev₁ R n = bit0 1 * X * chebyshev₁ R (n - 1) - chebyshev₁ R (n - bit0 1) := sorry

theorem map_chebyshev₁ {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] (f : R →+* S) (n : ℕ) : map f (chebyshev₁ R n) = chebyshev₁ S n := sorry

/-- `lambdashev R n` is equal to `2 * (chebyshev₁ R n).comp (X / 2)`.
It is a family of polynomials that satisfies
`lambdashev (zmod p) p = X ^ p`, and therefore defines a Lambda structure on `polynomial ℤ`. -/
def lambdashev (R : Type u_1) [comm_ring R] : ℕ → polynomial R :=
  sorry

@[simp] theorem lambdashev_zero (R : Type u_1) [comm_ring R] : lambdashev R 0 = bit0 1 :=
  rfl

@[simp] theorem lambdashev_one (R : Type u_1) [comm_ring R] : lambdashev R 1 = X :=
  rfl

theorem lambdashev_two (R : Type u_1) [comm_ring R] : lambdashev R (bit0 1) = X ^ bit0 1 - bit0 1 := sorry

@[simp] theorem lambdashev_add_two (R : Type u_1) [comm_ring R] (n : ℕ) : lambdashev R (n + bit0 1) = X * lambdashev R (n + 1) - lambdashev R n := sorry

theorem lambdashev_eq_two_le (R : Type u_1) [comm_ring R] (n : ℕ) (h : bit0 1 ≤ n) : lambdashev R n = X * lambdashev R (n - 1) - lambdashev R (n - bit0 1) := sorry

theorem map_lambdashev {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] (f : R →+* S) (n : ℕ) : map f (lambdashev R n) = lambdashev S n := sorry

end polynomial


namespace polynomial


/-- `chebyshev₂ n` is the `n`-th Chebyshev polynomial of the second kind -/
def chebyshev₂ (R : Type u_1) [comm_ring R] : ℕ → polynomial R :=
  sorry

@[simp] theorem chebyshev₂_zero (R : Type u_1) [comm_ring R] : chebyshev₂ R 0 = 1 :=
  rfl

@[simp] theorem chebyshev₂_one (R : Type u_1) [comm_ring R] : chebyshev₂ R 1 = bit0 1 * X :=
  rfl

theorem chebyshev₂_two (R : Type u_1) [comm_ring R] : chebyshev₂ R (bit0 1) = bit0 (bit0 1) * X ^ bit0 1 - 1 := sorry

@[simp] theorem chebyshev₂_add_two (R : Type u_1) [comm_ring R] (n : ℕ) : chebyshev₂ R (n + bit0 1) = bit0 1 * X * chebyshev₂ R (n + 1) - chebyshev₂ R n := sorry

theorem chebyshev₂_of_two_le (R : Type u_1) [comm_ring R] (n : ℕ) (h : bit0 1 ≤ n) : chebyshev₂ R n = bit0 1 * X * chebyshev₂ R (n - 1) - chebyshev₂ R (n - bit0 1) := sorry

theorem chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁ (R : Type u_1) [comm_ring R] (n : ℕ) : chebyshev₂ R (n + 1) = X * chebyshev₂ R n + chebyshev₁ R (n + 1) := sorry

theorem chebyshev₁_eq_chebyshev₂_sub_X_mul_chebyshev₂ (R : Type u_1) [comm_ring R] (n : ℕ) : chebyshev₁ R (n + 1) = chebyshev₂ R (n + 1) - X * chebyshev₂ R n := sorry

theorem chebyshev₁_eq_X_mul_chebyshev₁_sub_pol_chebyshev₂ (R : Type u_1) [comm_ring R] (n : ℕ) : chebyshev₁ R (n + bit0 1) = X * chebyshev₁ R (n + 1) - (1 - X ^ bit0 1) * chebyshev₂ R n := sorry

theorem one_sub_X_pow_two_mul_chebyshev₂_eq_pol_in_chebyshev₁ (R : Type u_1) [comm_ring R] (n : ℕ) : (1 - X ^ bit0 1) * chebyshev₂ R n = X * chebyshev₁ R (n + 1) - chebyshev₁ R (n + bit0 1) := sorry

@[simp] theorem map_chebyshev₂ {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] (f : R →+* S) (n : ℕ) : map f (chebyshev₂ R n) = chebyshev₂ S n := sorry

theorem chebyshev₁_derivative_eq_chebyshev₂ {R : Type u_1} [comm_ring R] (n : ℕ) : coe_fn derivative (chebyshev₁ R (n + 1)) = (↑n + 1) * chebyshev₂ R n := sorry

theorem one_sub_X_pow_two_mul_derivative_chebyshev₁_eq_poly_in_chebyshev₁ {R : Type u_1} [comm_ring R] (n : ℕ) : (1 - X ^ bit0 1) * coe_fn derivative (chebyshev₁ R (n + 1)) = (↑n + 1) * (chebyshev₁ R n - X * chebyshev₁ R (n + 1)) := sorry

theorem add_one_mul_chebyshev₁_eq_poly_in_chebyshev₂ {R : Type u_1} [comm_ring R] (n : ℕ) : (↑n + 1) * chebyshev₁ R (n + 1) = X * chebyshev₂ R n - (1 - X ^ bit0 1) * coe_fn derivative (chebyshev₂ R n) := sorry

