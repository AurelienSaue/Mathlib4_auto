/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.mv_polynomial.basic
import PostPort

universes u_1 u_2 u_4 u_5 u_3 

namespace Mathlib

/-!
# Renaming variables of polynomials

This file establishes the `rename` operation on multivariate polynomials,
which modifies the set of variables.

## Main declarations

* `mv_polynomial.rename`

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ α : Type*` (indexing the variables)

+ `R S : Type*` `[comm_semiring R]` `[comm_semiring S]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ α`

-/

namespace mv_polynomial


/-- Rename all the variables in a multivariable polynomial. -/
def rename {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (f : σ → τ) : alg_hom R (mv_polynomial σ R) (mv_polynomial τ R) :=
  aeval (X ∘ f)

@[simp] theorem rename_C {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (f : σ → τ) (r : R) : coe_fn (rename f) (coe_fn C r) = coe_fn C r :=
  eval₂_C (algebra_map R (mv_polynomial τ R)) (fun (n : σ) => function.comp X f n) r

@[simp] theorem rename_X {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (f : σ → τ) (i : σ) : coe_fn (rename f) (X i) = X (f i) :=
  eval₂_X (algebra_map R (mv_polynomial τ R)) (fun (n : σ) => function.comp X f n) i

theorem map_rename {σ : Type u_1} {τ : Type u_2} {R : Type u_4} {S : Type u_5} [comm_semiring R] [comm_semiring S] (f : R →+* S) (g : σ → τ) (p : mv_polynomial σ R) : coe_fn (map f) (coe_fn (rename g) p) = coe_fn (rename g) (coe_fn (map f) p) := sorry

@[simp] theorem rename_rename {σ : Type u_1} {τ : Type u_2} {α : Type u_3} {R : Type u_4} [comm_semiring R] (f : σ → τ) (g : τ → α) (p : mv_polynomial σ R) : coe_fn (rename g) (coe_fn (rename f) p) = coe_fn (rename (g ∘ f)) p := sorry

@[simp] theorem rename_id {σ : Type u_1} {R : Type u_4} [comm_semiring R] (p : mv_polynomial σ R) : coe_fn (rename id) p = p :=
  eval₂_eta p

theorem rename_monomial {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (f : σ → τ) (d : σ →₀ ℕ) (r : R) : coe_fn (rename f) (monomial d r) = monomial (finsupp.map_domain f d) r := sorry

theorem rename_eq {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (f : σ → τ) (p : mv_polynomial σ R) : coe_fn (rename f) p = finsupp.map_domain (finsupp.map_domain f) p := sorry

theorem rename_injective {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (f : σ → τ) (hf : function.injective f) : function.injective ⇑(rename f) := sorry

theorem eval₂_rename {σ : Type u_1} {τ : Type u_2} {R : Type u_4} {S : Type u_5} [comm_semiring R] [comm_semiring S] (f : R →+* S) (k : σ → τ) (g : τ → S) (p : mv_polynomial σ R) : eval₂ f g (coe_fn (rename k) p) = eval₂ f (g ∘ k) p := sorry

theorem eval₂_hom_rename {σ : Type u_1} {τ : Type u_2} {R : Type u_4} {S : Type u_5} [comm_semiring R] [comm_semiring S] (f : R →+* S) (k : σ → τ) (g : τ → S) (p : mv_polynomial σ R) : coe_fn (eval₂_hom f g) (coe_fn (rename k) p) = coe_fn (eval₂_hom f (g ∘ k)) p :=
  eval₂_rename f k (fun (n : τ) => g n) p

theorem aeval_rename {σ : Type u_1} {τ : Type u_2} {R : Type u_4} {S : Type u_5} [comm_semiring R] [comm_semiring S] (k : σ → τ) (g : τ → S) (p : mv_polynomial σ R) [algebra R S] : coe_fn (aeval g) (coe_fn (rename k) p) = coe_fn (aeval (g ∘ k)) p :=
  eval₂_hom_rename (algebra_map R S) k (fun (n : τ) => g n) p

theorem rename_eval₂ {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (k : σ → τ) (p : mv_polynomial σ R) (g : τ → mv_polynomial σ R) : coe_fn (rename k) (eval₂ C (g ∘ k) p) = eval₂ C (⇑(rename k) ∘ g) (coe_fn (rename k) p) := sorry

theorem rename_prodmk_eval₂ {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (p : mv_polynomial σ R) (j : τ) (g : σ → mv_polynomial σ R) : coe_fn (rename (Prod.mk j)) (eval₂ C g p) = eval₂ C (fun (x : σ) => coe_fn (rename (Prod.mk j)) (g x)) p := sorry

theorem eval₂_rename_prodmk {σ : Type u_1} {τ : Type u_2} {R : Type u_4} {S : Type u_5} [comm_semiring R] [comm_semiring S] (f : R →+* S) (g : σ × τ → S) (i : σ) (p : mv_polynomial τ R) : eval₂ f g (coe_fn (rename (Prod.mk i)) p) = eval₂ f (fun (j : τ) => g (i, j)) p := sorry

theorem eval_rename_prodmk {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (g : σ × τ → R) (i : σ) (p : mv_polynomial τ R) : coe_fn (eval g) (coe_fn (rename (Prod.mk i)) p) = coe_fn (eval fun (j : τ) => g (i, j)) p :=
  eval₂_rename_prodmk (ring_hom.id R) (fun (n : σ × τ) => g n) i p

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_finset_rename {σ : Type u_1} {R : Type u_4} [comm_semiring R] (p : mv_polynomial σ R) : ∃ (s : finset σ), ∃ (q : mv_polynomial (Subtype fun (x : σ) => x ∈ s) R), p = coe_fn (rename coe) q := sorry

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_fin_rename {σ : Type u_1} {R : Type u_4} [comm_semiring R] (p : mv_polynomial σ R) : ∃ (n : ℕ), ∃ (f : fin n → σ), ∃ (hf : function.injective f), ∃ (q : mv_polynomial (fin n) R), p = coe_fn (rename f) q := sorry

theorem eval₂_cast_comp {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (f : σ → τ) (c : ℤ →+* R) (g : τ → R) (p : mv_polynomial σ ℤ) : eval₂ c (g ∘ f) p = eval₂ c g (coe_fn (rename f) p) := sorry

@[simp] theorem coeff_rename_map_domain {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (f : σ → τ) (hf : function.injective f) (φ : mv_polynomial σ R) (d : σ →₀ ℕ) : coeff (finsupp.map_domain f d) (coe_fn (rename f) φ) = coeff d φ := sorry

theorem coeff_rename_eq_zero {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (f : σ → τ) (φ : mv_polynomial σ R) (d : τ →₀ ℕ) (h : ∀ (u : σ →₀ ℕ), finsupp.map_domain f u = d → coeff u φ = 0) : coeff d (coe_fn (rename f) φ) = 0 := sorry

theorem coeff_rename_ne_zero {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (f : σ → τ) (φ : mv_polynomial σ R) (d : τ →₀ ℕ) (h : coeff d (coe_fn (rename f) φ) ≠ 0) : ∃ (u : σ →₀ ℕ), finsupp.map_domain f u = d ∧ coeff u φ ≠ 0 := sorry

@[simp] theorem constant_coeff_rename {σ : Type u_1} {R : Type u_4} [comm_semiring R] {τ : Type u_2} (f : σ → τ) (φ : mv_polynomial σ R) : coe_fn constant_coeff (coe_fn (rename f) φ) = coe_fn constant_coeff φ := sorry

