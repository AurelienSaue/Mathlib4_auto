/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.ideal.operations
import Mathlib.data.polynomial.ring_division
import Mathlib.tactic.apply_fun
import Mathlib.ring_theory.prime
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Eisenstein's criterion

A proof of a slight generalisation of Eisenstein's criterion for the irreducibility of
a polynomial over an integral domain.
-/

namespace polynomial


namespace eisenstein_criterion_aux


/- Section for auxiliary lemmas used in the proof of `irreducible_of_eisenstein_criterion`-/

theorem map_eq_C_mul_X_pow_of_forall_coeff_mem {R : Type u_1} [integral_domain R] {f : polynomial R}
    {P : ideal R} (hfP : ∀ (n : ℕ), ↑n < degree f → coeff f n ∈ P) (hf0 : f ≠ 0) :
    map (ideal.quotient.mk P) f =
        coe_fn C (coe_fn (ideal.quotient.mk P) (leading_coeff f)) * X ^ nat_degree f :=
  sorry

theorem le_nat_degree_of_map_eq_mul_X_pow {R : Type u_1} [integral_domain R] {n : ℕ} {P : ideal R}
    (hP : ideal.is_prime P) {q : polynomial R} {c : polynomial (ideal.quotient P)}
    (hq : map (ideal.quotient.mk P) q = c * X ^ n) (hc0 : degree c = 0) : n ≤ nat_degree q :=
  sorry

theorem eval_zero_mem_ideal_of_eq_mul_X_pow {R : Type u_1} [integral_domain R] {n : ℕ} {P : ideal R}
    {q : polynomial R} {c : polynomial (ideal.quotient P)}
    (hq : map (ideal.quotient.mk P) q = c * X ^ n) (hn0 : 0 < n) : eval 0 q ∈ P :=
  sorry

theorem is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit {R : Type u_1} [integral_domain R]
    {p : polynomial R} {q : polynomial R} (hu : ∀ (x : R), coe_fn C x ∣ p * q → is_unit x)
    (hpm : nat_degree p = 0) : is_unit p :=
  sorry

end eisenstein_criterion_aux


/-- If `f` is a non constant polynomial with coefficients in `R`, and `P` is a prime ideal in `R`,
then if every coefficient in `R` except the leading coefficient is in `P`, and
the trailing coefficient is not in `P^2` and no non units in `R` divide `f`, then `f` is
irreducible. -/
theorem irreducible_of_eisenstein_criterion {R : Type u_1} [integral_domain R] {f : polynomial R}
    {P : ideal R} (hP : ideal.is_prime P) (hfl : ¬leading_coeff f ∈ P)
    (hfP : ∀ (n : ℕ), ↑n < degree f → coeff f n ∈ P) (hfd0 : 0 < degree f)
    (h0 : ¬coeff f 0 ∈ P ^ bit0 1) (hu : ∀ (x : R), coe_fn C x ∣ f → is_unit x) : irreducible f :=
  sorry

end Mathlib