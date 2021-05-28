/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.ideal.operations
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Ideals in product rings

For commutative rings `R` and `S` and ideals `I ≤ R`, `J ≤ S`, we define `ideal.prod I J` as the
product `I × J`, viewed as an ideal of `R × S`. In `ideal_prod_eq` we show that every ideal of
`R × S` is of this form.  Furthermore, we show that every prime ideal of `R × S` is of the form
`p × S` or `R × p`, where `p` is a prime ideal.
-/

namespace ideal


/-- `I × J` as an ideal of `R × S`. -/
def prod {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (I : ideal R) (J : ideal S) : ideal (R × S) :=
  submodule.mk (set_of fun (x : R × S) => prod.fst x ∈ I ∧ prod.snd x ∈ J) sorry sorry sorry

@[simp] theorem mem_prod {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (I : ideal R) (J : ideal S) {r : R} {s : S} : (r, s) ∈ prod I J ↔ r ∈ I ∧ s ∈ J :=
  iff.rfl

@[simp] theorem prod_top_top {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] : prod ⊤ ⊤ = ⊤ := sorry

/-- Every ideal of the product ring is of the form `I × J`, where `I` and `J` can be explicitly
    given as the image under the projection maps. -/
theorem ideal_prod_eq {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (I : ideal (R × S)) : I = prod (map (ring_hom.fst R S) I) (map (ring_hom.snd R S) I) := sorry

@[simp] theorem map_fst_prod {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (I : ideal R) (J : ideal S) : map (ring_hom.fst R S) (prod I J) = I := sorry

@[simp] theorem map_snd_prod {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (I : ideal R) (J : ideal S) : map (ring_hom.snd R S) (prod I J) = J := sorry

@[simp] theorem map_prod_comm_prod {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (I : ideal R) (J : ideal S) : map (↑ring_equiv.prod_comm) (prod I J) = prod J I := sorry

/-- Ideals of `R × S` are in one-to-one correspondence with pairs of ideals of `R` and ideals of
    `S`. -/
def ideal_prod_equiv {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] : ideal (R × S) ≃ ideal R × ideal S :=
  equiv.mk (fun (I : ideal (R × S)) => (map (ring_hom.fst R S) I, map (ring_hom.snd R S) I))
    (fun (I : ideal R × ideal S) => prod (prod.fst I) (prod.snd I)) sorry sorry

@[simp] theorem ideal_prod_equiv_symm_apply {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (I : ideal R) (J : ideal S) : coe_fn (equiv.symm ideal_prod_equiv) (I, J) = prod I J :=
  rfl

theorem prod.ext_iff {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {I : ideal R} {I' : ideal R} {J : ideal S} {J' : ideal S} : prod I J = prod I' J' ↔ I = I' ∧ J = J' := sorry

theorem is_prime_of_is_prime_prod_top {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {I : ideal R} (h : is_prime (prod I ⊤)) : is_prime I := sorry

theorem is_prime_of_is_prime_prod_top' {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {I : ideal S} (h : is_prime (prod ⊤ I)) : is_prime I :=
  is_prime_of_is_prime_prod_top
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_prime (prod I ⊤))) (Eq.symm (map_prod_comm_prod ⊤ I))))
      (map_is_prime_of_equiv ring_equiv.prod_comm))

theorem is_prime_ideal_prod_top {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {I : ideal R} [h : is_prime I] : is_prime (prod I ⊤) := sorry

theorem is_prime_ideal_prod_top' {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {I : ideal S} [h : is_prime I] : is_prime (prod ⊤ I) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_prime (prod ⊤ I))) (Eq.symm (map_prod_comm_prod I ⊤))))
    (map_is_prime_of_equiv ring_equiv.prod_comm)

theorem ideal_prod_prime_aux {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] {I : ideal R} {J : ideal S} : is_prime (prod I J) → I = ⊤ ∨ J = ⊤ := sorry

/-- Classification of prime ideals in product rings: the prime ideals of `R × S` are precisely the
    ideals of the form `p × S` or `R × p`, where `p` is a prime ideal of `R` or `S`. -/
theorem ideal_prod_prime {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (I : ideal (R × S)) : is_prime I ↔ (∃ (p : ideal R), is_prime p ∧ I = prod p ⊤) ∨ ∃ (p : ideal S), is_prime p ∧ I = prod ⊤ p := sorry

/-- The prime ideals of `R × S` are in bijection with the disjoint union of the prime ideals
    of `R` and the prime ideals of `S`. -/
def prime_ideals_equiv (R : Type u) (S : Type v) [comm_ring R] [comm_ring S] : (Subtype fun (K : ideal (R × S)) => is_prime K) ≃
  (Subtype fun (I : ideal R) => is_prime I) ⊕ Subtype fun (J : ideal S) => is_prime J :=
  equiv.symm (equiv.of_bijective prime_ideals_equiv_impl sorry)

@[simp] theorem prime_ideals_equiv_symm_inl {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (I : ideal R) (h : is_prime I) : coe_fn (equiv.symm (prime_ideals_equiv R S)) (sum.inl { val := I, property := h }) =
  { val := prod I ⊤, property := is_prime_ideal_prod_top } :=
  rfl

@[simp] theorem prime_ideals_equiv_symm_inr {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (J : ideal S) (h : is_prime J) : coe_fn (equiv.symm (prime_ideals_equiv R S)) (sum.inr { val := J, property := h }) =
  { val := prod ⊤ J, property := is_prime_ideal_prod_top' } :=
  rfl

