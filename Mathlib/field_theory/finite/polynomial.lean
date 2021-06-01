/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.field_theory.finite.basic
import Mathlib.field_theory.mv_polynomial
import Mathlib.data.mv_polynomial.expand
import Mathlib.linear_algebra.basic
import Mathlib.PostPort

universes u_1 u_2 u 

namespace Mathlib

/-!
## Polynomials over finite fields
-/

namespace mv_polynomial


/-- A polynomial over the integers is divisible by `n : ℕ`
if and only if it is zero over `zmod n`. -/
theorem C_dvd_iff_zmod {σ : Type u_1} (n : ℕ) (φ : mv_polynomial σ ℤ) : coe_fn C ↑n ∣ φ ↔ coe_fn (map (int.cast_ring_hom (zmod n))) φ = 0 :=
  C_dvd_iff_map_hom_eq_zero (int.cast_ring_hom (zmod n)) (↑n) (char_p.int_cast_eq_zero_iff (zmod n) n) φ

theorem frobenius_zmod {σ : Type u_1} {p : ℕ} [fact (nat.prime p)] (f : mv_polynomial σ (zmod p)) : coe_fn (frobenius (mv_polynomial σ (zmod p)) p) f = coe_fn (expand p) f := sorry

theorem expand_zmod {σ : Type u_1} {p : ℕ} [fact (nat.prime p)] (f : mv_polynomial σ (zmod p)) : coe_fn (expand p) f = f ^ p :=
  Eq.symm (frobenius_zmod f)

end mv_polynomial


namespace mv_polynomial


def indicator {K : Type u_1} {σ : Type u_2} [field K] [fintype K] [fintype σ] (a : σ → K) : mv_polynomial σ K :=
  finset.prod finset.univ fun (n : σ) => 1 - (X n - coe_fn C (a n)) ^ (fintype.card K - 1)

theorem eval_indicator_apply_eq_one {K : Type u_1} {σ : Type u_2} [field K] [fintype K] [fintype σ] (a : σ → K) : coe_fn (eval a) (indicator a) = 1 := sorry

theorem eval_indicator_apply_eq_zero {K : Type u_1} {σ : Type u_2} [field K] [fintype K] [fintype σ] (a : σ → K) (b : σ → K) (h : a ≠ b) : coe_fn (eval a) (indicator b) = 0 := sorry

theorem degrees_indicator {K : Type u_1} {σ : Type u_2} [field K] [fintype K] [fintype σ] (c : σ → K) : degrees (indicator c) ≤ finset.sum finset.univ fun (s : σ) => (fintype.card K - 1) •ℕ singleton s := sorry

theorem indicator_mem_restrict_degree {K : Type u_1} {σ : Type u_2} [field K] [fintype K] [fintype σ] (c : σ → K) : indicator c ∈ restrict_degree σ K (fintype.card K - 1) := sorry

def evalₗ (K : Type u_1) (σ : Type u_2) [field K] [fintype K] [fintype σ] : linear_map K (mv_polynomial σ K) ((σ → K) → K) :=
  linear_map.mk (fun (p : mv_polynomial σ K) (e : σ → K) => coe_fn (eval e) p) sorry sorry

theorem evalₗ_apply {K : Type u_1} {σ : Type u_2} [field K] [fintype K] [fintype σ] (p : mv_polynomial σ K) (e : σ → K) : coe_fn (evalₗ K σ) p e = coe_fn (eval e) p :=
  rfl

theorem map_restrict_dom_evalₗ {K : Type u_1} {σ : Type u_2} [field K] [fintype K] [fintype σ] : submodule.map (evalₗ K σ) (restrict_degree σ K (fintype.card K - 1)) = ⊤ := sorry

end mv_polynomial


namespace mv_polynomial


def R (σ : Type u) (K : Type u) [fintype σ] [field K] [fintype K] :=
  ↥(restrict_degree σ K (fintype.card K - 1))

protected instance decidable_restrict_degree (σ : Type u) [fintype σ] (m : ℕ) : decidable_pred fun (n : σ →₀ ℕ) => n ∈ set_of fun (n : σ →₀ ℕ) => ∀ (i : σ), coe_fn n i ≤ m :=
  eq.mpr sorry fun (a : σ →₀ ℕ) => fintype.decidable_forall_fintype

theorem dim_R (σ : Type u) (K : Type u) [fintype σ] [field K] [fintype K] : vector_space.dim K (R σ K) = ↑(fintype.card (σ → K)) := sorry

def evalᵢ (σ : Type u) (K : Type u) [fintype σ] [field K] [fintype K] : linear_map K (R σ K) ((σ → K) → K) :=
  linear_map.comp (evalₗ K σ) (submodule.subtype (restrict_degree σ K (fintype.card K - 1)))

theorem range_evalᵢ (σ : Type u) (K : Type u) [fintype σ] [field K] [fintype K] : linear_map.range (evalᵢ σ K) = ⊤ := sorry

theorem ker_evalₗ (σ : Type u) (K : Type u) [fintype σ] [field K] [fintype K] : linear_map.ker (evalᵢ σ K) = ⊥ := sorry

theorem eq_zero_of_eval_eq_zero (σ : Type u) (K : Type u) [fintype σ] [field K] [fintype K] (p : mv_polynomial σ K) (h : ∀ (v : σ → K), coe_fn (eval v) p = 0) (hp : p ∈ restrict_degree σ K (fintype.card K - 1)) : p = 0 := sorry

