/-
Copyright (c) 2020 Johan Commelin and Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin and Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.basic
import Mathlib.ring_theory.algebra_tower
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Invertible polynomials

This file is a stub containing some basic facts about invertible elements in the ring of polynomials.
-/

protected instance mv_polynomial.invertible_C (σ : Type u_1) {R : Type u_2} [comm_semiring R]
    (r : R) [invertible r] : invertible (coe_fn mv_polynomial.C r) :=
  invertible.map (ring_hom.to_monoid_hom mv_polynomial.C) r

/-- A natural number that is invertible when coerced to a commutative semiring `R` is also invertible
when coerced to any polynomial ring with rational coefficients.

Short-cut for typeclass resolution. -/
protected instance mv_polynomial.invertible_coe_nat (σ : Type u_1) (R : Type u_2) (p : ℕ)
    [comm_semiring R] [invertible ↑p] : invertible ↑p :=
  is_scalar_tower.invertible_algebra_coe_nat R (mv_polynomial σ R) p

end Mathlib