/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Linear structures on function with finite support `ι →₀ β`.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.mv_polynomial.default
import Mathlib.linear_algebra.dimension
import Mathlib.linear_algebra.direct_sum.finsupp
import PostPort

universes u_1 u_2 u_3 u_4 u_5 u v w 

namespace Mathlib

namespace finsupp


theorem linear_independent_single {R : Type u_1} {M : Type u_2} {ι : Type u_3} [ring R] [add_comm_group M] [module R M] {φ : ι → Type u_4} {f : (ι : ι) → φ ι → M} (hf : ∀ (i : ι), linear_independent R (f i)) : linear_independent R fun (ix : sigma fun (i : ι) => φ i) => single (sigma.fst ix) (f (sigma.fst ix) (sigma.snd ix)) := sorry

theorem is_basis_single {R : Type u_1} {M : Type u_2} {ι : Type u_3} [ring R] [add_comm_group M] [module R M] {φ : ι → Type u_4} (f : (ι : ι) → φ ι → M) (hf : ∀ (i : ι), is_basis R (f i)) : is_basis R fun (ix : sigma fun (i : ι) => φ i) => single (sigma.fst ix) (f (sigma.fst ix) (sigma.snd ix)) := sorry

theorem is_basis_single_one {R : Type u_1} {ι : Type u_3} [ring R] : is_basis R fun (i : ι) => single i 1 := sorry

/-- If b : ι → M and c : κ → N are bases then so is λ i, b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N. -/
theorem is_basis.tensor_product {R : Type u_1} {M : Type u_2} {N : Type u_3} {ι : Type u_4} {κ : Type u_5} [comm_ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N] {b : ι → M} (hb : is_basis R b) {c : κ → N} (hc : is_basis R c) : is_basis R fun (i : ι × κ) => tensor_product.tmul R (b (prod.fst i)) (c (prod.snd i)) := sorry

theorem dim_eq {K : Type u} {V : Type v} {ι : Type v} [field K] [add_comm_group V] [vector_space K V] : vector_space.dim K (ι →₀ V) = cardinal.mk ι * vector_space.dim K V := sorry

end finsupp


/- We use `universe variables` instead of `universes` here because universes introduced by the
   `universes` keyword do not get replaced by metavariables once a lemma has been proven. So if you
   prove a lemma using universe `u`, you can only apply it to universe `u` in other lemmas of the
   same section. -/

theorem equiv_of_dim_eq_lift_dim {K : Type u} {V : Type v} {V' : Type w} [field K] [add_comm_group V] [vector_space K V] [add_comm_group V'] [vector_space K V'] (h : cardinal.lift (vector_space.dim K V) = cardinal.lift (vector_space.dim K V')) : Nonempty (linear_equiv K V V') := sorry

/-- Two `K`-vector spaces are equivalent if their dimension is the same. -/
def equiv_of_dim_eq_dim {K : Type u} {V₁ : Type v} {V₂ : Type v} [field K] [add_comm_group V₁] [vector_space K V₁] [add_comm_group V₂] [vector_space K V₂] (h : vector_space.dim K V₁ = vector_space.dim K V₂) : linear_equiv K V₁ V₂ :=
  Classical.choice sorry

/-- An `n`-dimensional `K`-vector space is equivalent to `fin n → K`. -/
def fin_dim_vectorspace_equiv {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (n : ℕ) (hn : vector_space.dim K V = ↑n) : linear_equiv K V (fin n → K) :=
  Classical.choice sorry

theorem eq_bot_iff_dim_eq_zero {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (p : submodule K V) (h : vector_space.dim K ↥p = 0) : p = ⊥ :=
  let e : linear_equiv K ↥p ↥⊥ :=
    equiv_of_dim_eq_dim (eq.mpr (id (Eq._oldrec (Eq.refl (vector_space.dim K ↥p = vector_space.dim K ↥⊥)) dim_bot)) h);
  linear_equiv.eq_bot_of_equiv p e

theorem injective_of_surjective {K : Type u} {V₁ : Type v} {V₂ : Type v} [field K] [add_comm_group V₁] [vector_space K V₁] [add_comm_group V₂] [vector_space K V₂] (f : linear_map K V₁ V₂) (hV₁ : vector_space.dim K V₁ < cardinal.omega) (heq : vector_space.dim K V₂ = vector_space.dim K V₁) (hf : linear_map.range f = ⊤) : linear_map.ker f = ⊥ := sorry

theorem cardinal_mk_eq_cardinal_mk_field_pow_dim {K : Type u} {V : Type u} [field K] [add_comm_group V] [vector_space K V] (h : vector_space.dim K V < cardinal.omega) : cardinal.mk V = cardinal.mk K ^ vector_space.dim K V := sorry

theorem cardinal_lt_omega_of_dim_lt_omega {K : Type u} {V : Type u} [field K] [add_comm_group V] [vector_space K V] [fintype K] (h : vector_space.dim K V < cardinal.omega) : cardinal.mk V < cardinal.omega :=
  eq.mpr (id (Eq._oldrec (Eq.refl (cardinal.mk V < cardinal.omega)) (cardinal_mk_eq_cardinal_mk_field_pow_dim h)))
    (cardinal.power_lt_omega (iff.mpr cardinal.lt_omega_iff_fintype (Nonempty.intro infer_instance)) h)

