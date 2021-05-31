/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.default
import Mathlib.data.mv_polynomial.rename
import Mathlib.data.mv_polynomial.comm_ring
import Mathlib.PostPort

universes u_1 u_2 u_4 u_3 

namespace Mathlib

/-!
# Symmetric Polynomials and Elementary Symmetric Polynomials

This file defines symmetric `mv_polynomial`s and elementary symmetric `mv_polynomial`s.
We also prove some basic facts about them.

## Main declarations

* `mv_polynomial.is_symmetric`

* `mv_polynomial.esymm`

## Notation

+ `esymm σ R n`, is the `n`th elementary symmetric polynomial in `mv_polynomial σ R`.

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R S : Type*` `[comm_semiring R]` `[comm_semiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `φ ψ : mv_polynomial σ R`

-/

namespace mv_polynomial


/-- A mv_polynomial φ is symmetric if it is invariant under
permutations of its variables by the  `rename` operation -/
def is_symmetric {σ : Type u_1} {R : Type u_2} [comm_semiring R] (φ : mv_polynomial σ R) :=
  ∀ (e : equiv.perm σ), coe_fn (rename ⇑e) φ = φ

namespace is_symmetric


@[simp] theorem C {σ : Type u_1} {R : Type u_2} [comm_semiring R] (r : R) : is_symmetric (coe_fn C r) :=
  fun (e : equiv.perm σ) => rename_C (⇑e) r

@[simp] theorem zero {σ : Type u_1} {R : Type u_2} [comm_semiring R] : is_symmetric 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_symmetric 0)) (Eq.symm C_0))) (C 0)

@[simp] theorem one {σ : Type u_1} {R : Type u_2} [comm_semiring R] : is_symmetric 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_symmetric 1)) (Eq.symm C_1))) (C 1)

theorem add {σ : Type u_1} {R : Type u_2} [comm_semiring R] {φ : mv_polynomial σ R} {ψ : mv_polynomial σ R} (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ + ψ) := sorry

theorem mul {σ : Type u_1} {R : Type u_2} [comm_semiring R] {φ : mv_polynomial σ R} {ψ : mv_polynomial σ R} (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ * ψ) := sorry

theorem smul {σ : Type u_1} {R : Type u_2} [comm_semiring R] {φ : mv_polynomial σ R} (r : R) (hφ : is_symmetric φ) : is_symmetric (r • φ) :=
  fun (e : equiv.perm σ) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (rename ⇑e) (r • φ) = r • φ)) (alg_hom.map_smul (rename ⇑e) r φ)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (r • coe_fn (rename ⇑e) φ = r • φ)) (hφ e))) (Eq.refl (r • φ)))

@[simp] theorem map {σ : Type u_1} {R : Type u_2} {S : Type u_4} [comm_semiring R] [comm_semiring S] {φ : mv_polynomial σ R} (hφ : is_symmetric φ) (f : R →+* S) : is_symmetric (coe_fn (map f) φ) := sorry

theorem neg {σ : Type u_1} {R : Type u_2} [comm_ring R] {φ : mv_polynomial σ R} (hφ : is_symmetric φ) : is_symmetric (-φ) :=
  fun (e : equiv.perm σ) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (rename ⇑e) (-φ) = -φ)) (alg_hom.map_neg (rename ⇑e) φ)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (-coe_fn (rename ⇑e) φ = -φ)) (hφ e))) (Eq.refl (-φ)))

theorem sub {σ : Type u_1} {R : Type u_2} [comm_ring R] {φ : mv_polynomial σ R} {ψ : mv_polynomial σ R} (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ - ψ) := sorry

end is_symmetric


/-- The `n`th elementary symmetric `mv_polynomial σ R`. -/
def esymm (σ : Type u_1) (R : Type u_2) [comm_semiring R] [fintype σ] (n : ℕ) : mv_polynomial σ R :=
  finset.sum (finset.powerset_len n finset.univ) fun (t : finset σ) => finset.prod t fun (i : σ) => X i

/-- We can define `esymm σ R n` by summing over a subtype instead of over `powerset_len`. -/
theorem esymm_eq_sum_subtype (σ : Type u_1) (R : Type u_2) [comm_semiring R] [fintype σ] (n : ℕ) : esymm σ R n =
  finset.sum finset.univ fun (t : Subtype fun (s : finset σ) => finset.card s = n) => finset.prod ↑t fun (i : σ) => X i := sorry

/-- We can define `esymm σ R n` as a sum over explicit monomials -/
theorem esymm_eq_sum_monomial (σ : Type u_1) (R : Type u_2) [comm_semiring R] [fintype σ] (n : ℕ) : esymm σ R n =
  finset.sum (finset.powerset_len n finset.univ)
    fun (t : finset σ) => monomial (finset.sum t fun (i : σ) => finsupp.single i 1) 1 := sorry

@[simp] theorem esymm_zero (σ : Type u_1) (R : Type u_2) [comm_semiring R] [fintype σ] : esymm σ R 0 = 1 := sorry

theorem map_esymm (σ : Type u_1) (R : Type u_2) {S : Type u_4} [comm_semiring R] [comm_semiring S] [fintype σ] (n : ℕ) (f : R →+* S) : coe_fn (map f) (esymm σ R n) = esymm σ S n := sorry

theorem rename_esymm (σ : Type u_1) (R : Type u_2) {τ : Type u_3} [comm_semiring R] [fintype σ] [fintype τ] (n : ℕ) (e : σ ≃ τ) : coe_fn (rename ⇑e) (esymm σ R n) = esymm τ R n := sorry

theorem esymm_is_symmetric (σ : Type u_1) (R : Type u_2) [comm_semiring R] [fintype σ] (n : ℕ) : is_symmetric (esymm σ R n) := sorry

