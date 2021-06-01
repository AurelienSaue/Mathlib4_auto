/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.witt_vector.is_poly
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
## Multiplication by `n` in the ring of Witt vectors

In this file we show that multiplication by `n` in the ring of Witt vectors
is a polynomial function. We then use this fact to show that the composition of Frobenius
and Verschiebung is equal to multiplication by `p`.

### Main declarations

* `mul_n_is_poly`: multiplication by `n` is a polynomial function

-/

namespace witt_vector


/-- `witt_mul_n p n` is the family of polynomials that computes
the coefficients of `x * n` in terms of the coefficients of the Witt vector `x`. -/
def witt_mul_n (p : ℕ) [hp : fact (nat.prime p)] : ℕ → ℕ → mv_polynomial ℕ ℤ := sorry

theorem mul_n_coeff {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (n : ℕ)
    (x : witt_vector p R) (k : ℕ) :
    coeff (x * ↑n) k = coe_fn (mv_polynomial.aeval (coeff x)) (witt_mul_n p n k) :=
  sorry

/-- Multiplication by `n` is a polynomial function. -/
theorem mul_n_is_poly (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) :
    is_poly p fun (R : Type u_1) (_Rcr : comm_ring R) (x : witt_vector p R) => x * ↑n :=
  Exists.intro (witt_mul_n p n)
    fun (R : Type u_1) (_Rcr : comm_ring R) (x : witt_vector p R) =>
      funext fun (k : ℕ) => mul_n_coeff n x k

@[simp] theorem bind₁_witt_mul_n_witt_polynomial (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (k : ℕ) :
    coe_fn (mv_polynomial.bind₁ (witt_mul_n p n)) (witt_polynomial p ℤ k) =
        ↑n * witt_polynomial p ℤ k :=
  sorry

end Mathlib