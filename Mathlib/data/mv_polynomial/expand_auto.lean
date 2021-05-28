/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.mv_polynomial.monad
import PostPort

universes u_1 u_3 u_2 u_4 

namespace Mathlib

/-!
## Expand multivariate polynomials

Given a multivariate polynomial `φ`, one may replace every occurence of `X i` by `X i ^ n`,
for some natural number `n`.
This operation is called `mv_polynomial.expand` and it is an algebra homomorphism.

### Main declaration

* `mv_polynomial.expand`: expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

namespace mv_polynomial


/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `polynomial.expand`. -/
def expand {σ : Type u_1} {R : Type u_3} [comm_semiring R] (p : ℕ) : alg_hom R (mv_polynomial σ R) (mv_polynomial σ R) :=
  alg_hom.mk (ring_hom.to_fun (eval₂_hom C fun (i : σ) => X i ^ p)) sorry sorry sorry sorry sorry

@[simp] theorem expand_C {σ : Type u_1} {R : Type u_3} [comm_semiring R] (p : ℕ) (r : R) : coe_fn (expand p) (coe_fn C r) = coe_fn C r :=
  eval₂_hom_C C (fun (n : σ) => (fun (i : σ) => X i ^ p) n) r

@[simp] theorem expand_X {σ : Type u_1} {R : Type u_3} [comm_semiring R] (p : ℕ) (i : σ) : coe_fn (expand p) (X i) = X i ^ p :=
  eval₂_hom_X' C (fun (n : σ) => (fun (i : σ) => X i ^ p) n) i

@[simp] theorem expand_monomial {σ : Type u_1} {R : Type u_3} [comm_semiring R] (p : ℕ) (d : σ →₀ ℕ) (r : R) : coe_fn (expand p) (monomial d r) = coe_fn C r * finset.prod (finsupp.support d) fun (i : σ) => (X i ^ p) ^ coe_fn d i :=
  bind₁_monomial (fun (i : σ) => X i ^ p) d r

theorem expand_one_apply {σ : Type u_1} {R : Type u_3} [comm_semiring R] (f : mv_polynomial σ R) : coe_fn (expand 1) f = f := sorry

@[simp] theorem expand_one {σ : Type u_1} {R : Type u_3} [comm_semiring R] : expand 1 = alg_hom.id R (mv_polynomial σ R) := sorry

theorem expand_comp_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R] (p : ℕ) (f : σ → mv_polynomial τ R) : alg_hom.comp (expand p) (bind₁ f) = bind₁ fun (i : σ) => coe_fn (expand p) (f i) := sorry

theorem expand_bind₁ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R] (p : ℕ) (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) : coe_fn (expand p) (coe_fn (bind₁ f) φ) = coe_fn (bind₁ fun (i : σ) => coe_fn (expand p) (f i)) φ := sorry

@[simp] theorem map_expand {σ : Type u_1} {R : Type u_3} {S : Type u_4} [comm_semiring R] [comm_semiring S] (f : R →+* S) (p : ℕ) (φ : mv_polynomial σ R) : coe_fn (map f) (coe_fn (expand p) φ) = coe_fn (expand p) (coe_fn (map f) φ) := sorry

@[simp] theorem rename_expand {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R] (f : σ → τ) (p : ℕ) (φ : mv_polynomial σ R) : coe_fn (rename f) (coe_fn (expand p) φ) = coe_fn (expand p) (coe_fn (rename f) φ) := sorry

@[simp] theorem rename_comp_expand {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [comm_semiring R] (f : σ → τ) (p : ℕ) : alg_hom.comp (rename f) (expand p) = alg_hom.comp (expand p) (rename f) := sorry

