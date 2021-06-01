/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Multivariate functions of the form `α^n → α` are isomorphic to multivariate polynomials in
`n` variables.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.ideal.operations
import Mathlib.linear_algebra.finsupp_vector_space
import Mathlib.algebra.char_p.basic
import Mathlib.PostPort

universes u v u_1 u_2 

namespace Mathlib

namespace mv_polynomial


theorem quotient_mk_comp_C_injective (σ : Type u) (α : Type v) [field α]
    (I : ideal (mv_polynomial σ α)) (hI : I ≠ ⊤) :
    function.injective ⇑(ring_hom.comp (ideal.quotient.mk I) C) :=
  sorry

def restrict_total_degree (σ : Type u) (α : Type v) [field α] (m : ℕ) :
    submodule α (mv_polynomial σ α) :=
  finsupp.supported α α (set_of fun (n : σ →₀ ℕ) => (finsupp.sum n fun (n : σ) (e : ℕ) => e) ≤ m)

theorem mem_restrict_total_degree (σ : Type u) (α : Type v) [field α] (m : ℕ)
    (p : mv_polynomial σ α) : p ∈ restrict_total_degree σ α m ↔ total_degree p ≤ m :=
  sorry

def restrict_degree (σ : Type u) (α : Type v) (m : ℕ) [field α] : submodule α (mv_polynomial σ α) :=
  finsupp.supported α α (set_of fun (n : σ →₀ ℕ) => ∀ (i : σ), coe_fn n i ≤ m)

theorem mem_restrict_degree {σ : Type u} {α : Type v} [field α] (p : mv_polynomial σ α) (n : ℕ) :
    p ∈ restrict_degree σ α n ↔ ∀ (s : σ →₀ ℕ), s ∈ finsupp.support p → ∀ (i : σ), coe_fn s i ≤ n :=
  sorry

theorem mem_restrict_degree_iff_sup {σ : Type u} {α : Type v} [field α] (p : mv_polynomial σ α)
    (n : ℕ) : p ∈ restrict_degree σ α n ↔ ∀ (i : σ), multiset.count i (degrees p) ≤ n :=
  sorry

theorem map_range_eq_map {σ : Type u} {α : Type v} {β : Type u_1} [comm_ring α] [comm_ring β]
    (p : mv_polynomial σ α) (f : α →+* β) :
    finsupp.map_range (⇑f) (ring_hom.map_zero f) p = coe_fn (map f) p :=
  sorry

theorem is_basis_monomials (σ : Type u) (α : Type v) [field α] :
    is_basis α fun (s : σ →₀ ℕ) => monomial s 1 :=
  sorry

end mv_polynomial


namespace mv_polynomial


theorem dim_mv_polynomial (σ : Type u) (α : Type u) [field α] :
    vector_space.dim α (mv_polynomial σ α) = cardinal.mk (σ →₀ ℕ) :=
  sorry

end mv_polynomial


namespace mv_polynomial


protected instance char_p (σ : Type u_1) (R : Type u_2) [comm_ring R] (p : ℕ) [char_p R p] :
    char_p (mv_polynomial σ R) p :=
  char_p.mk
    fun (n : ℕ) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (↑n = 0 ↔ p ∣ n)) (Eq.symm (C_eq_coe_nat n))))
        (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn C ↑n = 0 ↔ p ∣ n)) (Eq.symm C_0)))
          (eq.mpr
            (id
              (Eq._oldrec (Eq.refl (coe_fn C ↑n = coe_fn C 0 ↔ p ∣ n)) (propext (C_inj R (↑n) 0))))
            (eq.mpr
              (id (Eq._oldrec (Eq.refl (↑n = 0 ↔ p ∣ n)) (propext (char_p.cast_eq_zero_iff R p n))))
              (iff.refl (p ∣ n)))))

end Mathlib