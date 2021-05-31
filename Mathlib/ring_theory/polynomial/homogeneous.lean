/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.default
import Mathlib.data.fintype.card
import Mathlib.PostPort

universes u_1 u_3 u_2 

namespace Mathlib

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`.

## Main definitions/lemmas

* `is_homogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneous_component n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneous_component`: every polynomial is the sum of its homogeneous components

-/

namespace mv_polynomial


/-
TODO
* create definition for `∑ i in d.support, d i`
* define graded rings, and show that mv_polynomial is an example
-/

/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`. -/
def is_homogeneous {σ : Type u_1} {R : Type u_3} [comm_semiring R] (φ : mv_polynomial σ R) (n : ℕ) :=
  ∀ {d : σ →₀ ℕ}, coeff d φ ≠ 0 → (finset.sum (finsupp.support d) fun (i : σ) => coe_fn d i) = n

theorem is_homogeneous_monomial {σ : Type u_1} {R : Type u_3} [comm_semiring R] (d : σ →₀ ℕ) (r : R) (n : ℕ) (hn : (finset.sum (finsupp.support d) fun (i : σ) => coe_fn d i) = n) : is_homogeneous (monomial d r) n := sorry

theorem is_homogeneous_C (σ : Type u_1) {R : Type u_3} [comm_semiring R] (r : R) : is_homogeneous (coe_fn C r) 0 := sorry

theorem is_homogeneous_zero (σ : Type u_1) (R : Type u_3) [comm_semiring R] (n : ℕ) : is_homogeneous 0 n :=
  fun (d : σ →₀ ℕ) (hd : coeff d 0 ≠ 0) => false.elim (hd (coeff_zero d))

theorem is_homogeneous_one (σ : Type u_1) (R : Type u_3) [comm_semiring R] : is_homogeneous 1 0 :=
  is_homogeneous_C σ 1

theorem is_homogeneous_X {σ : Type u_1} (R : Type u_3) [comm_semiring R] (i : σ) : is_homogeneous (X i) 1 := sorry

namespace is_homogeneous


theorem coeff_eq_zero {σ : Type u_1} {R : Type u_3} [comm_semiring R] {φ : mv_polynomial σ R} {n : ℕ} (hφ : is_homogeneous φ n) (d : σ →₀ ℕ) (hd : (finset.sum (finsupp.support d) fun (i : σ) => coe_fn d i) ≠ n) : coeff d φ = 0 :=
  eq.mp (Eq._oldrec (Eq.refl (¬coeff d φ ≠ 0)) (propext not_not)) (mt hφ hd)

theorem inj_right {σ : Type u_1} {R : Type u_3} [comm_semiring R] {φ : mv_polynomial σ R} {m : ℕ} {n : ℕ} (hm : is_homogeneous φ m) (hn : is_homogeneous φ n) (hφ : φ ≠ 0) : m = n := sorry

theorem add {σ : Type u_1} {R : Type u_3} [comm_semiring R] {φ : mv_polynomial σ R} {ψ : mv_polynomial σ R} {n : ℕ} (hφ : is_homogeneous φ n) (hψ : is_homogeneous ψ n) : is_homogeneous (φ + ψ) n := sorry

theorem sum {σ : Type u_1} {R : Type u_3} [comm_semiring R] {ι : Type u_2} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ℕ) (h : ∀ (i : ι), i ∈ s → is_homogeneous (φ i) n) : is_homogeneous (finset.sum s fun (i : ι) => φ i) n := sorry

theorem mul {σ : Type u_1} {R : Type u_3} [comm_semiring R] {φ : mv_polynomial σ R} {ψ : mv_polynomial σ R} {m : ℕ} {n : ℕ} (hφ : is_homogeneous φ m) (hψ : is_homogeneous ψ n) : is_homogeneous (φ * ψ) (m + n) := sorry

theorem prod {σ : Type u_1} {R : Type u_3} [comm_semiring R] {ι : Type u_2} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ι → ℕ) (h : ∀ (i : ι), i ∈ s → is_homogeneous (φ i) (n i)) : is_homogeneous (finset.prod s fun (i : ι) => φ i) (finset.sum s fun (i : ι) => n i) := sorry

theorem total_degree {σ : Type u_1} {R : Type u_3} [comm_semiring R] {φ : mv_polynomial σ R} {n : ℕ} (hφ : is_homogeneous φ n) (h : φ ≠ 0) : total_degree φ = n := sorry

end is_homogeneous


/-- `homogeneous_component n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneous_component` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneous_component {σ : Type u_1} {R : Type u_3} [comm_semiring R] (n : ℕ) : linear_map R (mv_polynomial σ R) (mv_polynomial σ R) :=
  linear_map.comp
    (submodule.subtype
      (finsupp.supported R R (set_of fun (d : σ →₀ ℕ) => (finset.sum (finsupp.support d) fun (i : σ) => coe_fn d i) = n)))
    (finsupp.restrict_dom R R (set_of fun (d : σ →₀ ℕ) => (finset.sum (finsupp.support d) fun (i : σ) => coe_fn d i) = n))

theorem coeff_homogeneous_component {σ : Type u_1} {R : Type u_3} [comm_semiring R] (n : ℕ) (φ : mv_polynomial σ R) (d : σ →₀ ℕ) : coeff d (coe_fn (homogeneous_component n) φ) =
  ite ((finset.sum (finsupp.support d) fun (i : σ) => coe_fn d i) = n) (coeff d φ) 0 := sorry

theorem homogeneous_component_apply {σ : Type u_1} {R : Type u_3} [comm_semiring R] (n : ℕ) (φ : mv_polynomial σ R) : coe_fn (homogeneous_component n) φ =
  finset.sum
    (finset.filter (fun (d : σ →₀ ℕ) => (finset.sum (finsupp.support d) fun (i : σ) => coe_fn d i) = n)
      (finsupp.support φ))
    fun (d : σ →₀ ℕ) => monomial d (coeff d φ) := sorry

theorem homogeneous_component_is_homogeneous {σ : Type u_1} {R : Type u_3} [comm_semiring R] (n : ℕ) (φ : mv_polynomial σ R) : is_homogeneous (coe_fn (homogeneous_component n) φ) n := sorry

theorem homogeneous_component_zero {σ : Type u_1} {R : Type u_3} [comm_semiring R] (φ : mv_polynomial σ R) : coe_fn (homogeneous_component 0) φ = coe_fn C (coeff 0 φ) := sorry

theorem homogeneous_component_eq_zero' {σ : Type u_1} {R : Type u_3} [comm_semiring R] (n : ℕ) (φ : mv_polynomial σ R) (h : ∀ (d : σ →₀ ℕ), d ∈ finsupp.support φ → (finset.sum (finsupp.support d) fun (i : σ) => coe_fn d i) ≠ n) : coe_fn (homogeneous_component n) φ = 0 := sorry

theorem homogeneous_component_eq_zero {σ : Type u_1} {R : Type u_3} [comm_semiring R] (n : ℕ) (φ : mv_polynomial σ R) (h : total_degree φ < n) : coe_fn (homogeneous_component n) φ = 0 := sorry

theorem sum_homogeneous_component {σ : Type u_1} {R : Type u_3} [comm_semiring R] (φ : mv_polynomial σ R) : (finset.sum (finset.range (total_degree φ + 1)) fun (i : ℕ) => coe_fn (homogeneous_component i) φ) = φ := sorry

