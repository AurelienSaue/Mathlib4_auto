/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebraic_geometry.prime_spectrum
import Mathlib.ring_theory.polynomial.basic
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
The morphism `Spec R[x] --> Spec R` induced by the natural inclusion `R --> R[x]` is an open map.
-/

namespace algebraic_geometry


namespace polynomial


/-- Given a polynomial `f ∈ R[x]`, `image_of_Df` is the subset of `Spec R` where at least one
of the coefficients of `f` does not vanish.  Lemma `image_of_Df_eq_comap_C_compl_zero_locus`
proves that `image_of_Df` is the image of `(zero_locus {f})ᶜ` under the morphism
`comap C : Spec R[x] → Spec R`. -/
def image_of_Df {R : Type u_1} [comm_ring R] (f : polynomial R) : set (prime_spectrum R) :=
  set_of fun (p : prime_spectrum R) => ∃ (i : ℕ), ¬polynomial.coeff f i ∈ prime_spectrum.as_ideal p

theorem is_open_image_of_Df {R : Type u_1} [comm_ring R] {f : polynomial R} : is_open (image_of_Df f) := sorry

/-- If a point of `Spec R[x]` is not contained in the vanishing set of `f`, then its image in
`Spec R` is contained in the open set where at least one of the coefficients of `f` is non-zero.
This lemma is a reformulation of `exists_coeff_not_mem_C_inverse`. -/
theorem comap_C_mem_image_of_Df {R : Type u_1} [comm_ring R] {f : polynomial R} {I : prime_spectrum (polynomial R)} (H : I ∈ (prime_spectrum.zero_locus (singleton f)ᶜ)) : prime_spectrum.comap polynomial.C I ∈ image_of_Df f :=
  polynomial.exists_coeff_not_mem_C_inverse (iff.mp prime_spectrum.mem_compl_zero_locus_iff_not_mem H)

/-- The open set `image_of_Df f` coincides with the image of `basic_open f` under the
morphism `C⁺ : Spec R[x] → Spec R`. -/
theorem image_of_Df_eq_comap_C_compl_zero_locus {R : Type u_1} [comm_ring R] {f : polynomial R} : image_of_Df f = prime_spectrum.comap polynomial.C '' (prime_spectrum.zero_locus (singleton f)ᶜ) := sorry

/--  The morphism `C⁺ : Spec R[x] → Spec R` is open. -/
theorem is_open_map_comap_C {R : Type u_1} [comm_ring R] : is_open_map (prime_spectrum.comap polynomial.C) := sorry

