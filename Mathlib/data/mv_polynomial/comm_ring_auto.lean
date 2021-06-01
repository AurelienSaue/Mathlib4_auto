/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.variables
import Mathlib.PostPort

universes u u_1 v 

namespace Mathlib

/-!
# Multivariate polynomials over a ring

Many results about polynomials hold when the coefficient ring is a commutative semiring.
Some stronger results can be derived when we assume this semiring is a ring.

This file does not define any new operations, but proves some of these stronger results.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_ring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/

namespace mv_polynomial


protected instance comm_ring {R : Type u} {σ : Type u_1} [comm_ring R] :
    comm_ring (mv_polynomial σ R) :=
  add_monoid_algebra.comm_ring

protected instance C.is_ring_hom {R : Type u} {σ : Type u_1} [comm_ring R] : is_ring_hom ⇑C :=
  is_ring_hom.of_semiring ⇑C

@[simp] theorem C_sub {R : Type u} (σ : Type u_1) (a : R) (a' : R) [comm_ring R] :
    coe_fn C (a - a') = coe_fn C a - coe_fn C a' :=
  is_ring_hom.map_sub ⇑C

@[simp] theorem C_neg {R : Type u} (σ : Type u_1) (a : R) [comm_ring R] :
    coe_fn C (-a) = -coe_fn C a :=
  is_ring_hom.map_neg ⇑C

@[simp] theorem coeff_neg {R : Type u} (σ : Type u_1) [comm_ring R] (m : σ →₀ ℕ)
    (p : mv_polynomial σ R) : coeff m (-p) = -coeff m p :=
  finsupp.neg_apply

@[simp] theorem coeff_sub {R : Type u} (σ : Type u_1) [comm_ring R] (m : σ →₀ ℕ)
    (p : mv_polynomial σ R) (q : mv_polynomial σ R) : coeff m (p - q) = coeff m p - coeff m q :=
  finsupp.sub_apply

protected instance coeff.is_add_group_hom {R : Type u} (σ : Type u_1) [comm_ring R] (m : σ →₀ ℕ) :
    is_add_group_hom (coeff m) :=
  is_add_group_hom.mk

theorem degrees_neg {R : Type u} {σ : Type u_1} [comm_ring R] (p : mv_polynomial σ R) :
    degrees (-p) = degrees p :=
  sorry

theorem degrees_sub {R : Type u} {σ : Type u_1} [comm_ring R] (p : mv_polynomial σ R)
    (q : mv_polynomial σ R) : degrees (p - q) ≤ degrees p ⊔ degrees q :=
  sorry

@[simp] theorem vars_neg {R : Type u} {σ : Type u_1} [comm_ring R] (p : mv_polynomial σ R) :
    vars (-p) = vars p :=
  sorry

theorem vars_sub_subset {R : Type u} {σ : Type u_1} [comm_ring R] (p : mv_polynomial σ R)
    (q : mv_polynomial σ R) : vars (p - q) ⊆ vars p ∪ vars q :=
  sorry

@[simp] theorem vars_sub_of_disjoint {R : Type u} {σ : Type u_1} [comm_ring R]
    {p : mv_polynomial σ R} {q : mv_polynomial σ R} (hpq : disjoint (vars p) (vars q)) :
    vars (p - q) = vars p ∪ vars q :=
  sorry

@[simp] theorem eval₂_sub {R : Type u} {S : Type v} {σ : Type u_1} [comm_ring R]
    (p : mv_polynomial σ R) {q : mv_polynomial σ R} [comm_ring S] (f : R →+* S) (g : σ → S) :
    eval₂ f g (p - q) = eval₂ f g p - eval₂ f g q :=
  ring_hom.map_sub (eval₂_hom f g) p q

@[simp] theorem eval₂_neg {R : Type u} {S : Type v} {σ : Type u_1} [comm_ring R]
    (p : mv_polynomial σ R) [comm_ring S] (f : R →+* S) (g : σ → S) :
    eval₂ f g (-p) = -eval₂ f g p :=
  ring_hom.map_neg (eval₂_hom f g) p

theorem hom_C {S : Type v} {σ : Type u_1} [comm_ring S] (f : mv_polynomial σ ℤ → S) [is_ring_hom f]
    (n : ℤ) : f (coe_fn C n) = ↑n :=
  ring_hom.eq_int_cast (ring_hom.comp (ring_hom.of f) (ring_hom.of ⇑C)) n

/-- A ring homomorphism f : Z[X_1, X_2, ...] → R
is determined by the evaluations f(X_1), f(X_2), ... -/
@[simp] theorem eval₂_hom_X {S : Type v} [comm_ring S] {R : Type u} (c : ℤ →+* S)
    (f : mv_polynomial R ℤ →+* S) (x : mv_polynomial R ℤ) : eval₂ c (⇑f ∘ X) x = coe_fn f x :=
  sorry

/-- Ring homomorphisms out of integer polynomials on a type `σ` are the same as
functions out of the type `σ`, -/
def hom_equiv {S : Type v} {σ : Type u_1} [comm_ring S] : (mv_polynomial σ ℤ →+* S) ≃ (σ → S) :=
  equiv.mk (fun (f : mv_polynomial σ ℤ →+* S) => ⇑f ∘ X)
    (fun (f : σ → S) => eval₂_hom (int.cast_ring_hom S) f) sorry sorry

@[simp] theorem total_degree_neg {R : Type u} {σ : Type u_1} [comm_ring R] (a : mv_polynomial σ R) :
    total_degree (-a) = total_degree a :=
  sorry

theorem total_degree_sub {R : Type u} {σ : Type u_1} [comm_ring R] (a : mv_polynomial σ R)
    (b : mv_polynomial σ R) : total_degree (a - b) ≤ max (total_degree a) (total_degree b) :=
  sorry

end Mathlib