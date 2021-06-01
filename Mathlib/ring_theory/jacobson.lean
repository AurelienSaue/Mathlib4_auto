/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.default
import Mathlib.ring_theory.ideal.over
import Mathlib.ring_theory.jacobson_ideal
import Mathlib.ring_theory.localization
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Jacobson Rings
The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its Jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its Jacobson radical
Any ring satisfying any of these equivalent conditions is said to be Jacobson.
Some particular examples of Jacobson rings are also proven.
`is_jacobson_quotient` says that the quotient of a Jacobson ring is Jacobson.
`is_jacobson_localization` says the localization of a Jacobson ring to a single element is Jacobson.
`is_jacobson_polynomial_iff_is_jacobson` says polynomials over a Jacobson ring form a Jacobson ring.
## Main definitions
Let `R` be a commutative ring. Jacobson Rings are defined using the first of the above conditions
* `is_jacobson R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.radical = I` implies `I.jacobson = I`.

## Main statements
* `is_jacobson_iff_prime_eq` is the equivalence between conditions 1 and 3 above.
* `is_jacobson_iff_Inf_maximal` is the equivalence between conditions 1 and 2 above.
* `is_jacobson_of_surjective` says that if `R` is a Jacobson ring and `f : R →+* S` is surjective,
  then `S` is also a Jacobson ring
* `is_jacobson_mv_polynomial` says that multi-variate polynomials over a Jacobson ring are Jacobson.
## Tags
Jacobson, Jacobson Ring
-/

namespace ideal


/-!
The following two lemmas are independent of Jacobson.  I extracted them from the
original proof of `quotient_mk_comp_C_is_integral_of_jacobson` to speed up processing.
Honestly, I did not spend time to unwind their "meaning", hence the names are likely inappropriate.

TODO: clean up, move elsewhere
-/

theorem injective_quotient_le_comap_map {R : Type u_1} [comm_ring R] (P : ideal (polynomial R)) : function.injective
  ⇑(quotient_map (map (polynomial.map_ring_hom (quotient.mk (comap polynomial.C P))) P)
      (polynomial.map_ring_hom (quotient.mk (comap polynomial.C P))) le_comap_map) := sorry

/-- The identity in this lemma is used in the proof of `quotient_mk_comp_C_is_integral_of_jacobson`.
It is isolated, since it speeds up the processing, avoiding a deterministic timeout. -/
theorem quotient_mk_maps_eq {R : Type u_1} [comm_ring R] (P : ideal (polynomial R)) : ring_hom.comp
    (ring_hom.comp (quotient.mk (map (polynomial.map_ring_hom (quotient.mk (comap polynomial.C P))) P)) polynomial.C)
    (quotient.mk (comap polynomial.C P)) =
  ring_hom.comp
    (quotient_map (map (polynomial.map_ring_hom (quotient.mk (comap polynomial.C P))) P)
      (polynomial.map_ring_hom (quotient.mk (comap polynomial.C P))) le_comap_map)
    (ring_hom.comp (quotient.mk P) polynomial.C) := sorry

/-- A ring is a Jacobson ring if for every radical ideal `I`,
 the Jacobson radical of `I` is equal to `I`.
 See `is_jacobson_iff_prime_eq` and `is_jacobson_iff_Inf_maximal` for equivalent definitions. -/
def is_jacobson (R : Type u_1) [comm_ring R] :=
  ∀ (I : ideal R), radical I = I → jacobson I = I

/--  A ring is a Jacobson ring if and only if for all prime ideals `P`,
 the Jacobson radical of `P` is equal to `P`. -/
theorem is_jacobson_iff_prime_eq {R : Type u_1} [comm_ring R] : is_jacobson R ↔ ∀ (P : ideal R), is_prime P → jacobson P = P := sorry

/-- A ring `R` is Jacobson if and only if for every prime ideal `I`,
 `I` can be written as the infimum of some collection of maximal ideals.
 Allowing ⊤ in the set `M` of maximal ideals is equivalent, but makes some proofs cleaner. -/
theorem is_jacobson_iff_Inf_maximal {R : Type u_1} [comm_ring R] : is_jacobson R ↔
  ∀ {I : ideal R}, is_prime I → ∃ (M : set (ideal R)), (∀ (J : ideal R), J ∈ M → is_maximal J ∨ J = ⊤) ∧ I = Inf M := sorry

theorem is_jacobson_iff_Inf_maximal' {R : Type u_1} [comm_ring R] : is_jacobson R ↔
  ∀ {I : ideal R},
    is_prime I → ∃ (M : set (ideal R)), (∀ (J : ideal R), J ∈ M → ∀ (K : ideal R), J < K → K = ⊤) ∧ I = Inf M := sorry

theorem radical_eq_jacobson {R : Type u_1} [comm_ring R] [H : is_jacobson R] (I : ideal R) : radical I = jacobson I := sorry

/-- Fields have only two ideals, and the condition holds for both of them.  -/
protected instance is_jacobson_field {K : Type u_1} [field K] : is_jacobson K :=
  fun (I : ideal K) (hI : radical I = I) =>
    or.rec_on (eq_bot_or_top I)
      (fun (h : I = ⊥) =>
        le_antisymm (Inf_le { left := le_of_eq rfl, right := Eq.symm h ▸ bot_is_maximal }) (Eq.symm h ▸ bot_le))
      fun (h : I = ⊤) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (jacobson I = I)) h))
          (eq.mpr (id (Eq._oldrec (Eq.refl (jacobson ⊤ = ⊤)) (propext jacobson_eq_top_iff))) (Eq.refl ⊤))

theorem is_jacobson_of_surjective {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] [H : is_jacobson R] : (∃ (f : R →+* S), function.surjective ⇑f) → is_jacobson S := sorry

protected instance is_jacobson_quotient {R : Type u_1} [comm_ring R] {I : ideal R} [is_jacobson R] : is_jacobson (quotient I) :=
  is_jacobson_of_surjective
    (Exists.intro (quotient.mk I)
      (id
        fun (b : quotient I) =>
          quot.induction_on b fun (x : R) => Exists.intro x (id (Eq.refl (coe_fn (quotient.mk I) x)))))

theorem is_jacobson_iso {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] (e : R ≃+* S) : is_jacobson R ↔ is_jacobson S := sorry

theorem is_jacobson_of_is_integral {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] [algebra R S] (hRS : algebra.is_integral R S) (hR : is_jacobson R) : is_jacobson S := sorry

theorem is_jacobson_of_is_integral' {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] (f : R →+* S) (hf : ring_hom.is_integral f) (hR : is_jacobson R) : is_jacobson S :=
  is_jacobson_of_is_integral hf hR

theorem disjoint_powers_iff_not_mem {R : Type u_1} [comm_ring R] {I : ideal R} {y : R} (hI : radical I = I) : disjoint ↑(submonoid.powers y) ↑I ↔ ¬y ∈ submodule.carrier I := sorry

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its comap.
See `le_rel_iso_of_maximal` for the more general relation isomorphism -/
theorem is_maximal_iff_is_maximal_disjoint {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] {y : R} (f : localization_map.away_map y S) [H : is_jacobson R] (J : ideal S) : is_maximal J ↔ is_maximal (comap (localization_map.to_map f) J) ∧ ¬y ∈ comap (localization_map.to_map f) J := sorry

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its map.
See `le_rel_iso_of_maximal` for the more general statement, and the reverse of this implication -/
theorem is_maximal_of_is_maximal_disjoint {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] {y : R} (f : localization_map.away_map y S) [is_jacobson R] (I : ideal R) (hI : is_maximal I) (hy : ¬y ∈ I) : is_maximal (map (localization_map.to_map f) I) := sorry

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y` -/
def order_iso_of_maximal {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] {y : R} (f : localization_map.away_map y S) [is_jacobson R] : (Subtype fun (p : ideal S) => is_maximal p) ≃o Subtype fun (p : ideal R) => is_maximal p ∧ ¬y ∈ p :=
  rel_iso.mk
    (equiv.mk
      (fun (p : Subtype fun (p : ideal S) => is_maximal p) =>
        { val := comap (localization_map.to_map f) (subtype.val p), property := sorry })
      (fun (p : Subtype fun (p : ideal R) => is_maximal p ∧ ¬y ∈ p) =>
        { val := map (localization_map.to_map f) (subtype.val p), property := sorry })
      sorry sorry)
    sorry

/-- If `S` is the localization of the Jacobson ring `R` at the submonoid generated by `y : R`, then `S` is Jacobson. -/
theorem is_jacobson_localization {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] {y : R} [H : is_jacobson R] (f : localization_map.away_map y S) : is_jacobson S := sorry

namespace polynomial


/-- If `I` is a prime ideal of `polynomial R` and `pX ∈ I` is a non-constant polynomial,
  then the map `R →+* R[x]/I` descends to an integral map when localizing at `pX.leading_coeff`.
  In particular `X` is integral because it satisfies `pX`, and constants are trivially integral,
  so integrality of the entire extension follows by closure under addition and multiplication. -/
theorem is_integral_localization_map_polynomial_quotient {R : Type u_1} [comm_ring R] {Rₘ : Type u_3} {Sₘ : Type u_4} [comm_ring Rₘ] [comm_ring Sₘ] (P : ideal (polynomial R)) [is_prime P] (pX : polynomial R) (hpX : pX ∈ P) (ϕ : localization_map (submonoid.powers (polynomial.leading_coeff (polynomial.map (quotient.mk (comap polynomial.C P)) pX)))
  Rₘ) (ϕ' : localization_map
  (submonoid.map (↑(quotient_map P polynomial.C le_rfl))
    (submonoid.powers (polynomial.leading_coeff (polynomial.map (quotient.mk (comap polynomial.C P)) pX))))
  Sₘ) : ring_hom.is_integral
  (localization_map.map ϕ
    (submonoid.mem_map_of_mem
      (submonoid.powers (polynomial.leading_coeff (polynomial.map (quotient.mk (comap polynomial.C P)) pX)))
      ↑(quotient_map P polynomial.C le_rfl))
    ϕ') := sorry

/-- If `f : R → S` descends to an integral map in the localization at `x`,
  and `R` is a Jacobson ring, then the intersection of all maximal ideals in `S` is trivial -/
theorem jacobson_bot_of_integral_localization {S : Type u_2} [integral_domain S] {Rₘ : Type u_3} {Sₘ : Type u_4} [comm_ring Rₘ] [comm_ring Sₘ] {R : Type u_1} [integral_domain R] [is_jacobson R] (φ : R →+* S) (hφ : function.injective ⇑φ) (x : R) (hx : x ≠ 0) (ϕ : localization_map (submonoid.powers x) Rₘ) (ϕ' : localization_map (submonoid.map (↑φ) (submonoid.powers x)) Sₘ) (hφ' : ring_hom.is_integral (localization_map.map ϕ (submonoid.mem_map_of_mem (submonoid.powers x) ↑φ) ϕ')) : jacobson ⊥ = ⊥ := sorry

/-- Used to bootstrap the proof of `is_jacobson_polynomial_iff_is_jacobson`.
  That theorem is more general and should be used instead of this one. -/
theorem is_jacobson_polynomial_of_is_jacobson {R : Type u_1} [comm_ring R] (hR : is_jacobson R) : is_jacobson (polynomial R) := sorry

theorem is_jacobson_polynomial_iff_is_jacobson {R : Type u_1} [comm_ring R] : is_jacobson (polynomial R) ↔ is_jacobson R := sorry

protected instance polynomial.ideal.is_jacobson {R : Type u_1} [comm_ring R] [is_jacobson R] : is_jacobson (polynomial R) :=
  iff.mpr is_jacobson_polynomial_iff_is_jacobson _inst_5

theorem is_maximal_comap_C_of_is_maximal {R : Type u_1} [integral_domain R] [is_jacobson R] (P : ideal (polynomial R)) [hP : is_maximal P] (hP' : ∀ (x : R), coe_fn polynomial.C x ∈ P → x = 0) : is_maximal (comap polynomial.C P) := sorry

/-- Used to bootstrap the more general `quotient_mk_comp_C_is_integral_of_jacobson` -/
/-- If `R` is a Jacobson ring, and `P` is a maximal ideal of `polynomial R`,
  then `R → (polynomial R)/P` is an integral map. -/
theorem quotient_mk_comp_C_is_integral_of_jacobson {R : Type u_1} [integral_domain R] [is_jacobson R] (P : ideal (polynomial R)) [hP : is_maximal P] : ring_hom.is_integral (ring_hom.comp (quotient.mk P) polynomial.C) := sorry

theorem is_maximal_comap_C_of_is_jacobson {R : Type u_1} [integral_domain R] [is_jacobson R] (P : ideal (polynomial R)) [hP : is_maximal P] : is_maximal (comap polynomial.C P) := sorry

theorem comp_C_integral_of_surjective_of_jacobson {R : Type u_1} [integral_domain R] [is_jacobson R] {S : Type u_2} [field S] (f : polynomial R →+* S) (hf : function.surjective ⇑f) : ring_hom.is_integral (ring_hom.comp f polynomial.C) := sorry

end polynomial


namespace mv_polynomial


theorem is_jacobson_mv_polynomial_fin {R : Type u_1} [comm_ring R] [H : is_jacobson R] (n : ℕ) : is_jacobson (mv_polynomial (fin n) R) := sorry

/-- General form of the nullstellensatz for Jacobson rings, since in a Jacobson ring we have
  `Inf {P maximal | P ≥ I} = Inf {P prime | P ≥ I} = I.radical`. Fields are always Jacobson,
  and in that special case this is (most of) the classical Nullstellensatz,
  since `I(V(I))` is the intersection of maximal ideals containing `I`, which is then `I.radical` -/
protected instance mv_polynomial.ideal.is_jacobson {R : Type u_1} [comm_ring R] {ι : Type u_2} [fintype ι] [is_jacobson R] : is_jacobson (mv_polynomial ι R) :=
  quot.induction_on (fintype.equiv_fin ι)
    fun (e : ι ≃ fin (fintype.card ι)) =>
      eq.mpr
        (id
          (Eq._oldrec (Eq.refl (is_jacobson (mv_polynomial ι R)))
            (propext (is_jacobson_iso (mv_polynomial.ring_equiv_of_equiv R e)))))
        (is_jacobson_mv_polynomial_fin (fintype.card ι))

theorem quotient_mk_comp_C_is_integral_of_jacobson {n : ℕ} {R : Type u_1} [integral_domain R] [is_jacobson R] (P : ideal (mv_polynomial (fin n) R)) [is_maximal P] : ring_hom.is_integral (ring_hom.comp (quotient.mk P) mv_polynomial.C) := sorry

theorem comp_C_integral_of_surjective_of_jacobson {R : Type u_1} [integral_domain R] [is_jacobson R] {σ : Type u_2} [fintype σ] {S : Type u_3} [field S] (f : mv_polynomial σ R →+* S) (hf : function.surjective ⇑f) : ring_hom.is_integral (ring_hom.comp f mv_polynomial.C) := sorry

