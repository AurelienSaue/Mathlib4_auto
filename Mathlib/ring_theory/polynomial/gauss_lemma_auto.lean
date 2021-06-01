/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.localization
import Mathlib.ring_theory.int.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Gauss's Lemma

Gauss's Lemma is one of a few results pertaining to irreducibility of primitive polynomials.

## Main Results
 - `polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map`:
  A primitive polynomial is irreducible iff it is irreducible in a fraction field.
 - `polynomial.is_primitive.int.irreducible_iff_irreducible_map_cast`:
  A primitive polynomial over `ℤ` is irreducible iff it is irreducible over `ℚ`.
 - `polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map`:
  Two primitive polynomials divide each other iff they do in a fraction field.
 - `polynomial.is_primitive.int.dvd_iff_map_cast_dvd_map_cast`:
  Two primitive polynomials over `ℤ` divide each other if they do in `ℚ`.

-/

namespace polynomial


theorem is_primitive.is_unit_iff_is_unit_map_of_injective {R : Type u_1} [integral_domain R]
    [gcd_monoid R] {S : Type u_2} [integral_domain S] {φ : R →+* S} (hinj : function.injective ⇑φ)
    {f : polynomial R} (hf : is_primitive f) : is_unit f ↔ is_unit (map φ f) :=
  sorry

theorem is_primitive.irreducible_of_irreducible_map_of_injective {R : Type u_1} [integral_domain R]
    [gcd_monoid R] {S : Type u_2} [integral_domain S] {φ : R →+* S} (hinj : function.injective ⇑φ)
    {f : polynomial R} (hf : is_primitive f) (h_irr : irreducible (map φ f)) : irreducible f :=
  sorry

theorem is_primitive.is_unit_iff_is_unit_map {R : Type u_1} [integral_domain R] [gcd_monoid R]
    {K : Type u_2} [field K] (f : fraction_map R K) {p : polynomial R} (hp : is_primitive p) :
    is_unit p ↔ is_unit (map (localization_map.to_map f) p) :=
  is_primitive.is_unit_iff_is_unit_map_of_injective (fraction_map.injective f) hp

theorem is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part {R : Type u_1}
    [integral_domain R] [gcd_monoid R] {K : Type u_2} [field K] (f : fraction_map R K)
    {p : polynomial K} (h0 : p ≠ 0)
    (h : is_unit (prim_part (localization_map.integer_normalization f p))) : is_unit p :=
  sorry

/-- Gauss's Lemma states that a primitive polynomial is irreducible iff it is irreducible in the
  fraction field. -/
theorem is_primitive.irreducible_iff_irreducible_map_fraction_map {R : Type u_1} [integral_domain R]
    [gcd_monoid R] {K : Type u_2} [field K] (f : fraction_map R K) {p : polynomial R}
    (hp : is_primitive p) : irreducible p ↔ irreducible (map (localization_map.to_map f) p) :=
  sorry

theorem is_primitive.dvd_of_fraction_map_dvd_fraction_map {R : Type u_1} [integral_domain R]
    [gcd_monoid R] {K : Type u_2} [field K] (f : fraction_map R K) {p : polynomial R}
    {q : polynomial R} (hp : is_primitive p) (hq : is_primitive q)
    (h_dvd : map (localization_map.to_map f) p ∣ map (localization_map.to_map f) q) : p ∣ q :=
  sorry

theorem is_primitive.dvd_iff_fraction_map_dvd_fraction_map {R : Type u_1} [integral_domain R]
    [gcd_monoid R] {K : Type u_2} [field K] (f : fraction_map R K) {p : polynomial R}
    {q : polynomial R} (hp : is_primitive p) (hq : is_primitive q) :
    p ∣ q ↔ map (localization_map.to_map f) p ∣ map (localization_map.to_map f) q :=
  sorry

/-- Gauss's Lemma for `ℤ` states that a primitive integer polynomial is irreducible iff it is
  irreducible over `ℚ`. -/
theorem is_primitive.int.irreducible_iff_irreducible_map_cast {p : polynomial ℤ}
    (hp : is_primitive p) : irreducible p ↔ irreducible (map (int.cast_ring_hom ℚ) p) :=
  is_primitive.irreducible_iff_irreducible_map_fraction_map fraction_map.int.fraction_map hp

theorem is_primitive.int.dvd_iff_map_cast_dvd_map_cast (p : polynomial ℤ) (q : polynomial ℤ)
    (hp : is_primitive p) (hq : is_primitive q) :
    p ∣ q ↔ map (int.cast_ring_hom ℚ) p ∣ map (int.cast_ring_hom ℚ) q :=
  is_primitive.dvd_iff_fraction_map_dvd_fraction_map fraction_map.int.fraction_map hp hq

end Mathlib