/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.discrete_valuation_ring
import Mathlib.ring_theory.fractional_ideal
import Mathlib.ring_theory.ideal.over
import Mathlib.PostPort

universes u_1 u_2 l u_3 u_4 u_5 

namespace Mathlib

/-!
# Dedekind domains

This file defines the notion of a Dedekind domain (or Dedekind ring),
giving three equivalent definitions (TODO: and shows that they are equivalent).

## Main definitions

 - `is_dedekind_domain` defines a Dedekind domain as a commutative ring that is not a field,
   Noetherian, integrally closed in its field of fractions and has Krull dimension exactly one.
   `is_dedekind_domain_iff` shows that this does not depend on the choice of field of fractions.
 - `is_dedekind_domain_dvr` alternatively defines a Dedekind domain as an integral domain that
   is not a field, Noetherian, and the localization at every nonzero prime ideal is a DVR.
 - `is_dedekind_domain_inv` alternatively defines a Dedekind domain as an integral domain that
   is not a field, and every nonzero fractional ideal is invertible.
 - `is_dedekind_domain_inv_iff` shows that this does note depend on the choice of field of fractions.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags

dedekind domain, dedekind ring
-/

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def ring.dimension_le_one (R : Type u_1) [comm_ring R] :=
  ∀ (p : ideal R), p ≠ ⊥ → ideal.is_prime p → ideal.is_maximal p

namespace ring


theorem dimension_le_one.principal_ideal_ring (A : Type u_2) [integral_domain A] [is_principal_ideal_ring A] : dimension_le_one A :=
  fun (p : ideal A) (nonzero : p ≠ ⊥) (prime : ideal.is_prime p) => is_prime.to_maximal_ideal nonzero

theorem dimension_le_one.integral_closure (R : Type u_1) (A : Type u_2) [comm_ring R] [integral_domain A] [nontrivial R] [algebra R A] (h : dimension_le_one R) : dimension_le_one ↥(integral_closure R A) := sorry

end ring


/--
A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension exactly one (`not_is_field` and `dimension_le_one`).

The integral closure condition is independent of the choice of field of fractions:
use `is_dedekind_domain_iff` to prove `is_dedekind_domain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class is_dedekind_domain (A : Type u_2) [integral_domain A] 
where
  not_is_field : ¬is_field A
  is_noetherian_ring : is_noetherian_ring A
  dimension_le_one : ring.dimension_le_one A
  is_integrally_closed : integral_closure A (fraction_ring A) = ⊥

/-- An integral domain is a Dedekind domain iff and only if it is not a field, is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
theorem is_dedekind_domain_iff (A : Type u_2) (K : Type u_3) [integral_domain A] [field K] (f : fraction_map A K) : is_dedekind_domain A ↔
  ¬is_field A ∧ is_noetherian_ring A ∧ ring.dimension_le_one A ∧ integral_closure A (localization_map.codomain f) = ⊥ := sorry

/--
A Dedekind domain is an integral domain that is not a field, is Noetherian, and the
localization at every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_dvr (A : Type u_2) [integral_domain A] 
where
  not_is_field : ¬is_field A
  is_noetherian_ring : is_noetherian_ring A
  is_dvr_at_nonzero_prime : ∀ (P : ideal A), P ≠ ⊥ → ideal.is_prime P → discrete_valuation_ring (localization.at_prime P)

protected instance ring.fractional_ideal.has_inv (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} : has_inv (ring.fractional_ideal g) :=
  has_inv.mk fun (I : ring.fractional_ideal g) => 1 / I

theorem inv_eq (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} {I : ring.fractional_ideal g} : I⁻¹ = 1 / I :=
  rfl

theorem inv_zero' (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} : 0⁻¹ = 0 :=
  ring.fractional_ideal.div_zero

theorem inv_nonzero (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} {J : ring.fractional_ideal g} (h : J ≠ 0) : J⁻¹ = { val := ↑1 / ↑J, property := ring.fractional_ideal.fractional_div_of_nonzero h } :=
  ring.fractional_ideal.div_nonzero h

theorem coe_inv_of_nonzero (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} {J : ring.fractional_ideal g} (h : J ≠ 0) : ↑(J⁻¹) = localization_map.coe_submodule g 1 / ↑J :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(J⁻¹) = localization_map.coe_submodule g 1 / ↑J)) (inv_nonzero K h)))
    (Eq.refl ↑{ val := ↑1 / ↑J, property := ring.fractional_ideal.fractional_div_of_nonzero h })

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} (I : ring.fractional_ideal g) (J : ring.fractional_ideal g) (h : I * J = 1) : J = (I⁻¹) :=
  congr_arg units.inv (units.ext rfl)

theorem mul_inv_cancel_iff (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} {I : ring.fractional_ideal g} : I * (I⁻¹) = 1 ↔ ∃ (J : ring.fractional_ideal g), I * J = 1 := sorry

@[simp] theorem map_inv (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} {K' : Type u_5} [field K'] {g' : fraction_map R₁ K'} (I : ring.fractional_ideal g) (h : alg_equiv R₁ (localization_map.codomain g) (localization_map.codomain g')) : ring.fractional_ideal.map (↑h) (I⁻¹) = (ring.fractional_ideal.map (↑h) I⁻¹) := sorry

@[simp] theorem span_singleton_inv (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} (x : localization_map.codomain g) : ring.fractional_ideal.span_singleton x⁻¹ = ring.fractional_ideal.span_singleton (x⁻¹) :=
  ring.fractional_ideal.one_div_span_singleton x

theorem mul_generator_self_inv (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} (I : ring.fractional_ideal g) [submodule.is_principal ↑I] (h : I ≠ 0) : I * ring.fractional_ideal.span_singleton (submodule.is_principal.generator ↑I⁻¹) = 1 := sorry

theorem invertible_of_principal (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} (I : ring.fractional_ideal g) [submodule.is_principal ↑I] (h : I ≠ 0) : I * (I⁻¹) = 1 :=
  iff.mpr ring.fractional_ideal.mul_div_self_cancel_iff
    (Exists.intro (ring.fractional_ideal.span_singleton (submodule.is_principal.generator ↑I⁻¹))
      (mul_generator_self_inv K I h))

theorem invertible_iff_generator_nonzero (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} (I : ring.fractional_ideal g) [submodule.is_principal ↑I] : I * (I⁻¹) = 1 ↔ submodule.is_principal.generator ↑I ≠ 0 := sorry

theorem is_principal_inv (K : Type u_3) [field K] {R₁ : Type u_4} [integral_domain R₁] {g : fraction_map R₁ K} (I : ring.fractional_ideal g) [submodule.is_principal ↑I] (h : I ≠ 0) : submodule.is_principal (subtype.val (I⁻¹)) := sorry

/--
A Dedekind domain is an integral domain that is not a field such that every fractional ideal
has an inverse.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_inv (A : Type u_2) [integral_domain A] 
where
  not_is_field : ¬is_field A
  mul_inv_cancel : ∀ (I : ring.fractional_ideal (fraction_ring.of A)), I ≠ ⊥ → I * (1 / I) = 1

theorem is_dedekind_domain_inv_iff (A : Type u_2) (K : Type u_3) [integral_domain A] [field K] (f : fraction_map A K) : is_dedekind_domain_inv A ↔ ¬is_field A ∧ ∀ (I : ring.fractional_ideal f), I ≠ ⊥ → I * (I⁻¹) = 1 := sorry

