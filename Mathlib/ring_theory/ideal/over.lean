/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.algebraic
import Mathlib.ring_theory.localization
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Ideals over/under ideals

This file concerns ideals lying over other ideals.
Let `f : R →+* S` be a ring homomorphism (typically a ring extension), `I` an ideal of `R` and
`J` an ideal of `S`. We say `J` lies over `I` (and `I` under `J`) if `I` is the `f`-preimage of `J`.
This is expressed here by writing `I = J.comap f`.

## Implementation notes

The proofs of the `comap_ne_bot` and `comap_lt_comap` families use an approach
specific for their situation: we construct an element in `I.comap f` from the
coefficients of a minimal polynomial.
Once mathlib has more material on the localization at a prime ideal, the results
can be proven using more general going-up/going-down theory.
-/

namespace ideal


theorem coeff_zero_mem_comap_of_root_mem_of_eval_mem {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] {f : R →+* S} {I : ideal S} {r : S} (hr : r ∈ I) {p : polynomial R} (hp : polynomial.eval₂ f r p ∈ I) : polynomial.coeff p 0 ∈ comap f I := sorry

theorem coeff_zero_mem_comap_of_root_mem {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] {f : R →+* S} {I : ideal S} {r : S} (hr : r ∈ I) {p : polynomial R} (hp : polynomial.eval₂ f r p = 0) : polynomial.coeff p 0 ∈ comap f I :=
  coeff_zero_mem_comap_of_root_mem_of_eval_mem hr (Eq.symm hp ▸ ideal.zero_mem I)

theorem exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] {f : R →+* S} {I : ideal S} {r : S} (r_non_zero_divisor : ∀ {x : S}, x * r = 0 → x = 0) (hr : r ∈ I) {p : polynomial R} (p_ne_zero : p ≠ 0) (hp : polynomial.eval₂ f r p = 0) : ∃ (i : ℕ), polynomial.coeff p i ≠ 0 ∧ polynomial.coeff p i ∈ comap f I := sorry

theorem exists_coeff_ne_zero_mem_comap_of_root_mem {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] {f : R →+* S} {I : ideal S} {r : S} (r_ne_zero : r ≠ 0) (hr : r ∈ I) {p : polynomial R} (p_ne_zero : p ≠ 0) (hp : polynomial.eval₂ f r p = 0) : ∃ (i : ℕ), polynomial.coeff p i ≠ 0 ∧ polynomial.coeff p i ∈ comap f I :=
  exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
    (fun (_x : S) (h : _x * r = 0) => or.resolve_right (iff.mp mul_eq_zero h) r_ne_zero) hr

theorem exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] {f : R →+* S} {I : ideal S} {J : ideal S} [is_prime I] (hIJ : I ≤ J) {r : S} (hr : r ∈ ↑J \ ↑I) {p : polynomial R} (p_ne_zero : polynomial.map (quotient.mk (comap f I)) p ≠ 0) (hpI : polynomial.eval₂ f r p ∈ I) : ∃ (i : ℕ), polynomial.coeff p i ∈ ↑(comap f J) \ ↑(comap f I) := sorry

theorem comap_ne_bot_of_root_mem {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] {f : R →+* S} {I : ideal S} {r : S} (r_ne_zero : r ≠ 0) (hr : r ∈ I) {p : polynomial R} (p_ne_zero : p ≠ 0) (hp : polynomial.eval₂ f r p = 0) : comap f I ≠ ⊥ := sorry

theorem comap_lt_comap_of_root_mem_sdiff {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] {f : R →+* S} {I : ideal S} {J : ideal S} [is_prime I] (hIJ : I ≤ J) {r : S} (hr : r ∈ ↑J \ ↑I) {p : polynomial R} (p_ne_zero : polynomial.map (quotient.mk (comap f I)) p ≠ 0) (hp : polynomial.eval₂ f r p ∈ I) : comap f I < comap f J := sorry

theorem comap_ne_bot_of_algebraic_mem {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] {I : ideal S} [algebra R S] {x : S} (x_ne_zero : x ≠ 0) (x_mem : x ∈ I) (hx : is_algebraic R x) : comap (algebra_map R S) I ≠ ⊥ := sorry

theorem comap_ne_bot_of_integral_mem {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] {I : ideal S} [algebra R S] [nontrivial R] {x : S} (x_ne_zero : x ≠ 0) (x_mem : x ∈ I) (hx : is_integral R x) : comap (algebra_map R S) I ≠ ⊥ :=
  comap_ne_bot_of_algebraic_mem x_ne_zero x_mem (is_integral.is_algebraic R hx)

theorem eq_bot_of_comap_eq_bot {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] {I : ideal S} [algebra R S] [nontrivial R] (hRS : algebra.is_integral R S) (hI : comap (algebra_map R S) I = ⊥) : I = ⊥ := sorry

theorem mem_of_one_mem {S : Type u_2} [integral_domain S] {I : ideal S} (h : 1 ∈ I) (x : S) : x ∈ I :=
  Eq.symm (iff.mpr (eq_top_iff_one I) h) ▸ submodule.mem_top

theorem comap_lt_comap_of_integral_mem_sdiff {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] {I : ideal S} {J : ideal S} [algebra R S] [hI : is_prime I] (hIJ : I ≤ J) {x : S} (mem : x ∈ ↑J \ ↑I) (integral : is_integral R x) : comap (algebra_map R S) I < comap (algebra_map R S) J := sorry

theorem is_maximal_of_is_integral_of_is_maximal_comap {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] [algebra R S] (hRS : algebra.is_integral R S) (I : ideal S) [is_prime I] (hI : is_maximal (comap (algebra_map R S) I)) : is_maximal I := sorry

theorem is_maximal_of_is_integral_of_is_maximal_comap' {R : Type u_1} {S : Type u_2} [comm_ring R] [integral_domain S] (f : R →+* S) (hf : ring_hom.is_integral f) (I : ideal S) [hI' : is_prime I] (hI : is_maximal (comap f I)) : is_maximal I :=
  is_maximal_of_is_integral_of_is_maximal_comap hf I hI

theorem is_maximal_comap_of_is_integral_of_is_maximal {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] [algebra R S] (hRS : algebra.is_integral R S) (I : ideal S) [hI : is_maximal I] : is_maximal (comap (algebra_map R S) I) := sorry

theorem is_maximal_comap_of_is_integral_of_is_maximal' {R : Type u_1} {S : Type u_2} [comm_ring R] [integral_domain S] (f : R →+* S) (hf : ring_hom.is_integral f) (I : ideal S) (hI : is_maximal I) : is_maximal (comap f I) :=
  is_maximal_comap_of_is_integral_of_is_maximal hf I

theorem integral_closure.comap_ne_bot {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] [algebra R S] [nontrivial R] {I : ideal ↥(integral_closure R S)} (I_ne_bot : I ≠ ⊥) : comap (algebra_map R ↥(integral_closure R S)) I ≠ ⊥ := sorry

theorem integral_closure.eq_bot_of_comap_eq_bot {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] [algebra R S] [nontrivial R] {I : ideal ↥(integral_closure R S)} : comap (algebra_map R ↥(integral_closure R S)) I = ⊥ → I = ⊥ :=
  imp_of_not_imp_not (comap (algebra_map R ↥(integral_closure R S)) I = ⊥) (I = ⊥) integral_closure.comap_ne_bot

theorem integral_closure.comap_lt_comap {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] [algebra R S] {I : ideal ↥(integral_closure R S)} {J : ideal ↥(integral_closure R S)} [is_prime I] (I_lt_J : I < J) : comap (algebra_map R ↥(integral_closure R S)) I < comap (algebra_map R ↥(integral_closure R S)) J := sorry

theorem integral_closure.is_maximal_of_is_maximal_comap {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] [algebra R S] (I : ideal ↥(integral_closure R S)) [is_prime I] (hI : is_maximal (comap (algebra_map R ↥(integral_closure R S)) I)) : is_maximal I :=
  is_maximal_of_is_integral_of_is_maximal_comap (fun (x : ↥(integral_closure R S)) => integral_closure.is_integral x) I hI

/-- `comap (algebra_map R S)` is a surjection from the prime spec of `R` to prime spec of `S`.
`hP : (algebra_map R S).ker ≤ P` is a slight generalization of the extension being injective -/
theorem exists_ideal_over_prime_of_is_integral' {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] [algebra R S] (H : algebra.is_integral R S) (P : ideal R) [is_prime P] (hP : ring_hom.ker (algebra_map R S) ≤ P) : ∃ (Q : ideal S), is_prime Q ∧ comap (algebra_map R S) Q = P := sorry

/-- More general going-up theorem than `exists_ideal_over_prime_of_is_integral'`.
TODO: Version of going-up theorem with arbitrary length chains (by induction on this)?
  Not sure how best to write an ascending chain in Lean -/
theorem exists_ideal_over_prime_of_is_integral {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] [algebra R S] (H : algebra.is_integral R S) (P : ideal R) [is_prime P] (I : ideal S) [is_prime I] (hIP : comap (algebra_map R S) I ≤ P) : ∃ (Q : ideal S), ∃ (H : Q ≥ I), is_prime Q ∧ comap (algebra_map R S) Q = P := sorry

/-- `comap (algebra_map R S)` is a surjection from the max spec of `S` to max spec of `R`.
`hP : (algebra_map R S).ker ≤ P` is a slight generalization of the extension being injective -/
theorem exists_ideal_over_maximal_of_is_integral {R : Type u_1} [comm_ring R] {S : Type u_2} [integral_domain S] [algebra R S] (H : algebra.is_integral R S) (P : ideal R) [P_max : is_maximal P] (hP : ring_hom.ker (algebra_map R S) ≤ P) : ∃ (Q : ideal S), is_maximal Q ∧ comap (algebra_map R S) Q = P := sorry

