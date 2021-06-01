/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.monad
import Mathlib.data.set.disjointed
import Mathlib.PostPort

universes u u_1 u_2 v u_3 

namespace Mathlib

/-!
# Degrees and variables of polynomials

This file establishes many results about the degree and variable sets of a multivariate polynomial.

The *variable set* of a polynomial $P \in R[X]$ is a `finset` containing each $x \in X$
that appears in a monomial in $P$.

The *degree set* of a polynomial $P \in R[X]$ is a `multiset` containing, for each $x$ in the
variable set, $n$ copies of $x$, where $n$ is the maximum number of copies of $x$ appearing in a
monomial of $P$.

## Main declarations

* `mv_polynomial.degrees p` : the multiset of variables representing the union of the multisets corresponding
  to each non-zero monomial in `p`. For example if `7 ≠ 0` in `R` and `p = x²y+7y³` then
  `degrees p = {x, x, y, y, y}`

* `mv_polynomial.vars p` : the finset of variables occurring in `p`. For example if `p = x⁴y+yz` then
  `vars p = {x, y, z}`

* `mv_polynomial.degree_of n p : ℕ` -- the total degree of `p` with respect to the variable `n`. For example
  if `p = x⁴y+yz` then `degree_of y p = 1`.

* `mv_polynomial.total_degree p : ℕ` -- the max of the sizes of the multisets `s` whose monomials `X^s` occur
  in `p`. For example if `p = x⁴y+yz` then `total_degree p = 5`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `r : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/

namespace mv_polynomial


/-! ### `degrees` -/

/--
The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset.

(For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
-/
def degrees {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) : multiset σ :=
  finset.sup (finsupp.support p) fun (s : σ →₀ ℕ) => coe_fn finsupp.to_multiset s

theorem degrees_monomial {R : Type u} {σ : Type u_1} [comm_semiring R] (s : σ →₀ ℕ) (a : R) :
    degrees (monomial s a) ≤ coe_fn finsupp.to_multiset s :=
  sorry

theorem degrees_monomial_eq {R : Type u} {σ : Type u_1} [comm_semiring R] (s : σ →₀ ℕ) (a : R)
    (ha : a ≠ 0) : degrees (monomial s a) = coe_fn finsupp.to_multiset s :=
  sorry

theorem degrees_C {R : Type u} {σ : Type u_1} [comm_semiring R] (a : R) :
    degrees (coe_fn C a) = 0 :=
  iff.mp multiset.le_zero (degrees_monomial 0 a)

theorem degrees_X' {R : Type u} {σ : Type u_1} [comm_semiring R] (n : σ) :
    degrees (X n) ≤ singleton n :=
  le_trans (degrees_monomial (finsupp.single n 1) 1) (le_of_eq (finsupp.to_multiset_single n 1))

@[simp] theorem degrees_X {R : Type u} {σ : Type u_1} [comm_semiring R] [nontrivial R] (n : σ) :
    degrees (X n) = singleton n :=
  Eq.trans (degrees_monomial_eq (finsupp.single n 1) 1 one_ne_zero) (finsupp.to_multiset_single n 1)

@[simp] theorem degrees_zero {R : Type u} {σ : Type u_1} [comm_semiring R] : degrees 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (degrees 0 = 0)) (Eq.symm C_0))) (degrees_C 0)

@[simp] theorem degrees_one {R : Type u} {σ : Type u_1} [comm_semiring R] : degrees 1 = 0 :=
  degrees_C 1

theorem degrees_add {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R)
    (q : mv_polynomial σ R) : degrees (p + q) ≤ degrees p ⊔ degrees q :=
  sorry

theorem degrees_sum {R : Type u} {σ : Type u_1} [comm_semiring R] {ι : Type u_2} (s : finset ι)
    (f : ι → mv_polynomial σ R) :
    degrees (finset.sum s fun (i : ι) => f i) ≤ finset.sup s fun (i : ι) => degrees (f i) :=
  sorry

theorem degrees_mul {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R)
    (q : mv_polynomial σ R) : degrees (p * q) ≤ degrees p + degrees q :=
  sorry

theorem degrees_prod {R : Type u} {σ : Type u_1} [comm_semiring R] {ι : Type u_2} (s : finset ι)
    (f : ι → mv_polynomial σ R) :
    degrees (finset.prod s fun (i : ι) => f i) ≤ finset.sum s fun (i : ι) => degrees (f i) :=
  sorry

theorem degrees_pow {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) (n : ℕ) :
    degrees (p ^ n) ≤ n •ℕ degrees p :=
  sorry

theorem mem_degrees {R : Type u} {σ : Type u_1} [comm_semiring R] {p : mv_polynomial σ R} {i : σ} :
    i ∈ degrees p ↔ ∃ (d : σ →₀ ℕ), coeff d p ≠ 0 ∧ i ∈ finsupp.support d :=
  sorry

theorem le_degrees_add {R : Type u} {σ : Type u_1} [comm_semiring R] {p : mv_polynomial σ R}
    {q : mv_polynomial σ R} (h : multiset.disjoint (degrees p) (degrees q)) :
    degrees p ≤ degrees (p + q) :=
  sorry

theorem degrees_add_of_disjoint {R : Type u} {σ : Type u_1} [comm_semiring R]
    {p : mv_polynomial σ R} {q : mv_polynomial σ R}
    (h : multiset.disjoint (degrees p) (degrees q)) : degrees (p + q) = degrees p ∪ degrees q :=
  sorry

theorem degrees_map {R : Type u} {S : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S]
    (p : mv_polynomial σ R) (f : R →+* S) : degrees (coe_fn (map f) p) ⊆ degrees p :=
  sorry

theorem degrees_rename {R : Type u} {σ : Type u_1} {τ : Type u_2} [comm_semiring R] (f : σ → τ)
    (φ : mv_polynomial σ R) : degrees (coe_fn (rename f) φ) ⊆ multiset.map f (degrees φ) :=
  sorry

theorem degrees_map_of_injective {R : Type u} {S : Type v} {σ : Type u_1} [comm_semiring R]
    [comm_semiring S] (p : mv_polynomial σ R) {f : R →+* S} (hf : function.injective ⇑f) :
    degrees (coe_fn (map f) p) = degrees p :=
  sorry

/-! ### `vars` -/

/-- `vars p` is the set of variables appearing in the polynomial `p` -/
def vars {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) : finset σ :=
  multiset.to_finset (degrees p)

@[simp] theorem vars_0 {R : Type u} {σ : Type u_1} [comm_semiring R] : vars 0 = ∅ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (vars 0 = ∅)) (vars.equations._eqn_1 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (multiset.to_finset (degrees 0) = ∅)) degrees_zero))
      (eq.mpr (id (Eq._oldrec (Eq.refl (multiset.to_finset 0 = ∅)) multiset.to_finset_zero))
        (Eq.refl ∅)))

@[simp] theorem vars_monomial {R : Type u} {σ : Type u_1} {r : R} {s : σ →₀ ℕ} [comm_semiring R]
    (h : r ≠ 0) : vars (monomial s r) = finsupp.support s :=
  sorry

@[simp] theorem vars_C {R : Type u} {σ : Type u_1} {r : R} [comm_semiring R] :
    vars (coe_fn C r) = ∅ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (vars (coe_fn C r) = ∅)) (vars.equations._eqn_1 (coe_fn C r))))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (multiset.to_finset (degrees (coe_fn C r)) = ∅)) (degrees_C r)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (multiset.to_finset 0 = ∅)) multiset.to_finset_zero))
        (Eq.refl ∅)))

@[simp] theorem vars_X {R : Type u} {σ : Type u_1} {n : σ} [comm_semiring R] [nontrivial R] :
    vars (X n) = singleton n :=
  sorry

theorem mem_vars {R : Type u} {σ : Type u_1} [comm_semiring R] {p : mv_polynomial σ R} (i : σ) :
    i ∈ vars p ↔ ∃ (d : σ →₀ ℕ), ∃ (H : d ∈ finsupp.support p), i ∈ finsupp.support d :=
  sorry

theorem mem_support_not_mem_vars_zero {R : Type u} {σ : Type u_1} [comm_semiring R]
    {f : mv_polynomial σ R} {x : σ →₀ ℕ} (H : x ∈ finsupp.support f) {v : σ} (h : ¬v ∈ vars f) :
    coe_fn x v = 0 :=
  sorry

theorem vars_add_subset {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R)
    (q : mv_polynomial σ R) : vars (p + q) ⊆ vars p ∪ vars q :=
  sorry

theorem vars_add_of_disjoint {R : Type u} {σ : Type u_1} [comm_semiring R] {p : mv_polynomial σ R}
    {q : mv_polynomial σ R} (h : disjoint (vars p) (vars q)) : vars (p + q) = vars p ∪ vars q :=
  sorry

theorem vars_mul {R : Type u} {σ : Type u_1} [comm_semiring R] (φ : mv_polynomial σ R)
    (ψ : mv_polynomial σ R) : vars (φ * ψ) ⊆ vars φ ∪ vars ψ :=
  sorry

@[simp] theorem vars_one {R : Type u} {σ : Type u_1} [comm_semiring R] : vars 1 = ∅ := vars_C

theorem vars_pow {R : Type u} {σ : Type u_1} [comm_semiring R] (φ : mv_polynomial σ R) (n : ℕ) :
    vars (φ ^ n) ⊆ vars φ :=
  sorry

/--
The variables of the product of a family of polynomials
are a subset of the union of the sets of variables of each polynomial.
-/
theorem vars_prod {R : Type u} {σ : Type u_1} [comm_semiring R] {ι : Type u_2} {s : finset ι}
    (f : ι → mv_polynomial σ R) :
    vars (finset.prod s fun (i : ι) => f i) ⊆ finset.bUnion s fun (i : ι) => vars (f i) :=
  sorry

theorem vars_C_mul {σ : Type u_1} {A : Type u_3} [integral_domain A] (a : A) (ha : a ≠ 0)
    (φ : mv_polynomial σ A) : vars (coe_fn C a * φ) = vars φ :=
  sorry

theorem vars_sum_subset {R : Type u} {σ : Type u_1} [comm_semiring R] {ι : Type u_3} (t : finset ι)
    (φ : ι → mv_polynomial σ R) :
    vars (finset.sum t fun (i : ι) => φ i) ⊆ finset.bUnion t fun (i : ι) => vars (φ i) :=
  sorry

theorem vars_sum_of_disjoint {R : Type u} {σ : Type u_1} [comm_semiring R] {ι : Type u_3}
    (t : finset ι) (φ : ι → mv_polynomial σ R)
    (h : pairwise (disjoint on fun (i : ι) => vars (φ i))) :
    vars (finset.sum t fun (i : ι) => φ i) = finset.bUnion t fun (i : ι) => vars (φ i) :=
  sorry

theorem vars_map {R : Type u} {S : Type v} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R)
    [comm_semiring S] (f : R →+* S) : vars (coe_fn (map f) p) ⊆ vars p :=
  sorry

theorem vars_map_of_injective {R : Type u} {S : Type v} {σ : Type u_1} [comm_semiring R]
    (p : mv_polynomial σ R) [comm_semiring S] {f : R →+* S} (hf : function.injective ⇑f) :
    vars (coe_fn (map f) p) = vars p :=
  sorry

theorem vars_monomial_single {R : Type u} {σ : Type u_1} [comm_semiring R] (i : σ) {e : ℕ} {r : R}
    (he : e ≠ 0) (hr : r ≠ 0) : vars (monomial (finsupp.single i e) r) = singleton i :=
  sorry

theorem vars_eq_support_bUnion_support {R : Type u} {σ : Type u_1} [comm_semiring R]
    (p : mv_polynomial σ R) : vars p = finset.bUnion (finsupp.support p) finsupp.support :=
  sorry

/-! ### `degree_of` -/

/-- `degree_of n p` gives the highest power of X_n that appears in `p` -/
def degree_of {R : Type u} {σ : Type u_1} [comm_semiring R] (n : σ) (p : mv_polynomial σ R) : ℕ :=
  multiset.count n (degrees p)

/-! ### `total_degree` -/

/-- `total_degree p` gives the maximum |s| over the monomials X^s in `p` -/
def total_degree {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) : ℕ :=
  finset.sup (finsupp.support p) fun (s : σ →₀ ℕ) => finsupp.sum s fun (n : σ) (e : ℕ) => e

theorem total_degree_eq {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) :
    total_degree p =
        finset.sup (finsupp.support p)
          fun (m : σ →₀ ℕ) => coe_fn multiset.card (coe_fn finsupp.to_multiset m) :=
  sorry

theorem total_degree_le_degrees_card {R : Type u} {σ : Type u_1} [comm_semiring R]
    (p : mv_polynomial σ R) : total_degree p ≤ coe_fn multiset.card (degrees p) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (total_degree p ≤ coe_fn multiset.card (degrees p)))
        (total_degree_eq p)))
    (finset.sup_le
      fun (s : σ →₀ ℕ) (hs : s ∈ finsupp.support p) => multiset.card_le_of_le (finset.le_sup hs))

@[simp] theorem total_degree_C {R : Type u} {σ : Type u_1} [comm_semiring R] (a : R) :
    total_degree (coe_fn C a) = 0 :=
  sorry

@[simp] theorem total_degree_zero {R : Type u} {σ : Type u_1} [comm_semiring R] :
    total_degree 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (total_degree 0 = 0)) (Eq.symm C_0))) (total_degree_C 0)

@[simp] theorem total_degree_one {R : Type u} {σ : Type u_1} [comm_semiring R] :
    total_degree 1 = 0 :=
  total_degree_C 1

@[simp] theorem total_degree_X {σ : Type u_1} {R : Type u_2} [comm_semiring R] [nontrivial R]
    (s : σ) : total_degree (X s) = 1 :=
  sorry

theorem total_degree_add {R : Type u} {σ : Type u_1} [comm_semiring R] (a : mv_polynomial σ R)
    (b : mv_polynomial σ R) : total_degree (a + b) ≤ max (total_degree a) (total_degree b) :=
  sorry

theorem total_degree_mul {R : Type u} {σ : Type u_1} [comm_semiring R] (a : mv_polynomial σ R)
    (b : mv_polynomial σ R) : total_degree (a * b) ≤ total_degree a + total_degree b :=
  sorry

theorem total_degree_pow {R : Type u} {σ : Type u_1} [comm_semiring R] (a : mv_polynomial σ R)
    (n : ℕ) : total_degree (a ^ n) ≤ n * total_degree a :=
  sorry

theorem total_degree_list_prod {R : Type u} {σ : Type u_1} [comm_semiring R]
    (s : List (mv_polynomial σ R)) :
    total_degree (list.prod s) ≤ list.sum (list.map total_degree s) :=
  sorry

theorem total_degree_multiset_prod {R : Type u} {σ : Type u_1} [comm_semiring R]
    (s : multiset (mv_polynomial σ R)) :
    total_degree (multiset.prod s) ≤ multiset.sum (multiset.map total_degree s) :=
  sorry

theorem total_degree_finset_prod {R : Type u} {σ : Type u_1} [comm_semiring R] {ι : Type u_2}
    (s : finset ι) (f : ι → mv_polynomial σ R) :
    total_degree (finset.prod s f) ≤ finset.sum s fun (i : ι) => total_degree (f i) :=
  sorry

theorem exists_degree_lt {R : Type u} {σ : Type u_1} [comm_semiring R] [fintype σ]
    (f : mv_polynomial σ R) (n : ℕ) (h : total_degree f < n * fintype.card σ) {d : σ →₀ ℕ}
    (hd : d ∈ finsupp.support f) : ∃ (i : σ), coe_fn d i < n :=
  sorry

theorem coeff_eq_zero_of_total_degree_lt {R : Type u} {σ : Type u_1} [comm_semiring R]
    {f : mv_polynomial σ R} {d : σ →₀ ℕ}
    (h : total_degree f < finset.sum (finsupp.support d) fun (i : σ) => coe_fn d i) :
    coeff d f = 0 :=
  sorry

theorem total_degree_rename_le {R : Type u} {σ : Type u_1} {τ : Type u_2} [comm_semiring R]
    (f : σ → τ) (p : mv_polynomial σ R) : total_degree (coe_fn (rename f) p) ≤ total_degree p :=
  sorry

/-! ### `vars` and `eval` -/

theorem eval₂_hom_eq_constant_coeff_of_vars {R : Type u} {S : Type v} {σ : Type u_1}
    [comm_semiring R] [comm_semiring S] (f : R →+* S) {g : σ → S} {p : mv_polynomial σ R}
    (hp : ∀ (i : σ), i ∈ vars p → g i = 0) :
    coe_fn (eval₂_hom f g) p = coe_fn f (coe_fn constant_coeff p) :=
  sorry

theorem aeval_eq_constant_coeff_of_vars {R : Type u} {S : Type v} {σ : Type u_1} [comm_semiring R]
    [comm_semiring S] [algebra R S] {g : σ → S} {p : mv_polynomial σ R}
    (hp : ∀ (i : σ), i ∈ vars p → g i = 0) :
    coe_fn (aeval g) p = coe_fn (algebra_map R S) (coe_fn constant_coeff p) :=
  eval₂_hom_eq_constant_coeff_of_vars (algebra_map R S) hp

theorem eval₂_hom_congr' {R : Type u} {S : Type v} {σ : Type u_1} [comm_semiring R]
    [comm_semiring S] {f₁ : R →+* S} {f₂ : R →+* S} {g₁ : σ → S} {g₂ : σ → S}
    {p₁ : mv_polynomial σ R} {p₂ : mv_polynomial σ R} :
    f₁ = f₂ →
        (∀ (i : σ), i ∈ vars p₁ → i ∈ vars p₂ → g₁ i = g₂ i) →
          p₁ = p₂ → coe_fn (eval₂_hom f₁ g₁) p₁ = coe_fn (eval₂_hom f₂ g₂) p₂ :=
  sorry

theorem vars_bind₁ {R : Type u} {σ : Type u_1} {τ : Type u_2} [comm_semiring R]
    (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
    vars (coe_fn (bind₁ f) φ) ⊆ finset.bUnion (vars φ) fun (i : σ) => vars (f i) :=
  sorry

theorem mem_vars_bind₁ {R : Type u} {σ : Type u_1} {τ : Type u_2} [comm_semiring R]
    (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) {j : τ}
    (h : j ∈ vars (coe_fn (bind₁ f) φ)) : ∃ (i : σ), i ∈ vars φ ∧ j ∈ vars (f i) :=
  sorry

theorem vars_rename {R : Type u} {σ : Type u_1} {τ : Type u_2} [comm_semiring R] (f : σ → τ)
    (φ : mv_polynomial σ R) : vars (coe_fn (rename f) φ) ⊆ finset.image f (vars φ) :=
  sorry

theorem mem_vars_rename {R : Type u} {σ : Type u_1} {τ : Type u_2} [comm_semiring R] (f : σ → τ)
    (φ : mv_polynomial σ R) {j : τ} (h : j ∈ vars (coe_fn (rename f) φ)) :
    ∃ (i : σ), i ∈ vars φ ∧ f i = j :=
  sorry

end Mathlib