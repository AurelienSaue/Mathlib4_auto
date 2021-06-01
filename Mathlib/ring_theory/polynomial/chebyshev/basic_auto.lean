/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.polynomial.chebyshev.defs
import Mathlib.analysis.special_functions.trigonometric
import Mathlib.ring_theory.localization
import Mathlib.data.zmod.basic
import Mathlib.algebra.invertible
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Chebyshev polynomials

The Chebyshev polynomials are two families of polynomials indexed by `ℕ`,
with integral coefficients.
In this file, we only consider Chebyshev polynomials of the first kind.

## Main declarations

* `polynomial.chebyshev₁_mul`, the `(m * n)`-th Chebyshev polynomial is the composition
  of the `m`-th and `n`-th Chebyshev polynomials.
* `polynomial.lambdashev_mul`, the `(m * n)`-th lambdashev polynomial is the composition
  of the `m`-th and `n`-th lambdashev polynomials.
* `polynomial.lambdashev_char_p`, for a prime number `p`, the `p`-th lambdashev polynomial
  is congruent to `X ^ p` modulo `p`.

## Implementation details

Since Chebyshev polynomials have interesting behaviour over the complex numbers and modulo `p`,
we define them to have coefficients in an arbitrary commutative ring, even though
technically `ℤ` would suffice.
The benefit of allowing arbitrary coefficient rings, is that the statements afterwards are clean,
and do not have `map (int.cast_ring_hom R)` interfering all the time.


-/

namespace polynomial


/-- The `(m * n)`-th Chebyshev polynomial is the composition of the `m`-th and `n`-th -/
theorem chebyshev₁_mul (R : Type u_1) [comm_ring R] (m : ℕ) (n : ℕ) :
    chebyshev₁ R (m * n) = comp (chebyshev₁ R m) (chebyshev₁ R n) :=
  sorry

/-!

### A Lambda structure on `polynomial ℤ`

Mathlib doesn't currently know what a Lambda ring is.
But once it does, we can endow `polynomial ℤ` with a Lambda structure
in terms of the `lambdashev` polynomials defined below.
There is exactly one other Lambda structure on `polynomial ℤ` in terms of binomial polynomials.

-/

theorem lambdashev_eval_add_inv {R : Type u_1} [comm_ring R] (x : R) (y : R) (h : x * y = 1)
    (n : ℕ) : eval (x + y) (lambdashev R n) = x ^ n + y ^ n :=
  sorry

theorem lambdashev_eq_chebyshev₁ (R : Type u_1) [comm_ring R] [invertible (bit0 1)] (n : ℕ) :
    lambdashev R n = bit0 1 * comp (chebyshev₁ R n) (coe_fn C ⅟ * X) :=
  sorry

theorem chebyshev₁_eq_lambdashev (R : Type u_1) [comm_ring R] [invertible (bit0 1)] (n : ℕ) :
    chebyshev₁ R n = coe_fn C ⅟ * comp (lambdashev R n) (bit0 1 * X) :=
  sorry

/-- the `(m * n)`-th lambdashev polynomial is the composition of the `m`-th and `n`-th -/
theorem lambdashev_mul (R : Type u_1) [comm_ring R] (m : ℕ) (n : ℕ) :
    lambdashev R (m * n) = comp (lambdashev R m) (lambdashev R n) :=
  sorry

theorem lambdashev_comp_comm (R : Type u_1) [comm_ring R] (m : ℕ) (n : ℕ) :
    comp (lambdashev R m) (lambdashev R n) = comp (lambdashev R n) (lambdashev R m) :=
  sorry

theorem lambdashev_zmod_p (p : ℕ) [fact (nat.prime p)] : lambdashev (zmod p) p = X ^ p := sorry

theorem lambdashev_char_p (R : Type u_1) [comm_ring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] :
    lambdashev R p = X ^ p :=
  sorry

end Mathlib