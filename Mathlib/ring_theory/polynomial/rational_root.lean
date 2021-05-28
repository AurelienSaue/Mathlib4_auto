/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.polynomial.scale_roots
import Mathlib.ring_theory.localization
import Mathlib.PostPort

universes u_1 u_4 u_2 

namespace Mathlib

/-!
# Rational root theorem and integral root theorem

This file contains the rational root theorem and integral root theorem.
The rational root theorem for a unique factorization domain `A`
with localization `S`, states that the roots of `p : polynomial A` in `A`'s
field of fractions are of the form `x / y` with `x y : A`, `x ∣ p.coeff 0` and
`y ∣ p.leading_coeff`.
The corollary is the integral root theorem `is_integer_of_is_root_of_monic`:
if `p` is monic, its roots must be integers.
Finally, we use this to show unique factorization domains are integrally closed.

## References

 * https://en.wikipedia.org/wiki/Rational_root_theorem
-/

theorem scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero {A : Type u_1} {S : Type u_4} [integral_domain A] [comm_ring S] {M : submonoid A} {f : localization_map M S} {p : polynomial A} {r : A} {s : ↥M} (hr : coe_fn (polynomial.aeval (localization_map.mk' f r s)) p = 0) : coe_fn (polynomial.aeval (coe_fn (localization_map.to_map f) r)) (scale_roots p ↑s) = 0 := sorry

theorem num_is_root_scale_roots_of_aeval_eq_zero {A : Type u_1} {K : Type u_2} [integral_domain A] [field K] [unique_factorization_monoid A] (g : fraction_map A K) {p : polynomial A} {x : localization_map.codomain g} (hr : coe_fn (polynomial.aeval x) p = 0) : polynomial.is_root (scale_roots p ↑(fraction_map.denom g x)) (fraction_map.num g x) := sorry

/-- Rational root theorem part 1:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the numerator of `r` divides the constant coefficient -/
theorem num_dvd_of_is_root {A : Type u_1} {K : Type u_2} [integral_domain A] [unique_factorization_monoid A] [field K] {f : fraction_map A K} {p : polynomial A} {r : localization_map.codomain f} (hr : coe_fn (polynomial.aeval r) p = 0) : fraction_map.num f r ∣ polynomial.coeff p 0 := sorry

/-- Rational root theorem part 2:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the denominator of `r` divides the leading coefficient -/
theorem denom_dvd_of_is_root {A : Type u_1} {K : Type u_2} [integral_domain A] [unique_factorization_monoid A] [field K] {f : fraction_map A K} {p : polynomial A} {r : localization_map.codomain f} (hr : coe_fn (polynomial.aeval r) p = 0) : ↑(fraction_map.denom f r) ∣ polynomial.leading_coeff p := sorry

/-- Integral root theorem:
if `r : f.codomain` is a root of a monic polynomial over the ufd `A`,
then `r` is an integer -/
theorem is_integer_of_is_root_of_monic {A : Type u_1} {K : Type u_2} [integral_domain A] [unique_factorization_monoid A] [field K] {f : fraction_map A K} {p : polynomial A} (hp : polynomial.monic p) {r : localization_map.codomain f} (hr : coe_fn (polynomial.aeval r) p = 0) : localization_map.is_integer f r :=
  fraction_map.is_integer_of_is_unit_denom f
    (is_unit_of_dvd_one (↑(fraction_map.denom f r)) (hp ▸ denom_dvd_of_is_root hr))

namespace unique_factorization_monoid


theorem integer_of_integral {A : Type u_1} {K : Type u_2} [integral_domain A] [unique_factorization_monoid A] [field K] {f : fraction_map A K} {x : localization_map.codomain f} : is_integral A x → localization_map.is_integer f x := sorry

theorem integrally_closed {A : Type u_1} {K : Type u_2} [integral_domain A] [unique_factorization_monoid A] [field K] {f : fraction_map A K} : integral_closure A (localization_map.codomain f) = ⊥ :=
  iff.mpr eq_bot_iff
    fun (x : localization_map.codomain f) (hx : x ∈ ↑(integral_closure A (localization_map.codomain f))) =>
      iff.mpr algebra.mem_bot (integer_of_integral hx)

