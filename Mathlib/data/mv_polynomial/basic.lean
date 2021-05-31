/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.eval
import Mathlib.PostPort

universes u_1 u_2 u w v x 

namespace Mathlib

/-!
# Multivariate polynomials

This file defines polynomial rings over a base ring (or even semiring),
with variables from a general type `σ` (which could be infinite).

## Important definitions

Let `R` be a commutative ring (or a semiring) and let `σ` be an arbitrary
type. This file creates the type `mv_polynomial σ R`, which mathematicians
might denote $R[X_i : i \in σ]$. It is the type of multivariate
(a.k.a. multivariable) polynomials, with variables
corresponding to the terms in `σ`, and coefficients in `R`.

### Notation

In the definitions below, we use the following notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

### Definitions

* `mv_polynomial σ R` : the type of polynomials with variables of type `σ` and coefficients
  in the commutative semiring `R`

* `monomial s a` : the monomial which mathematically would be denoted `a * X^s`

* `C a` : the constant polynomial with value `a`

* `X i` : the degree one monomial corresponding to i; mathematically this might be denoted `Xᵢ`.

* `coeff s p` : the coefficient of `s` in `p`.

* `eval₂ (f : R → S₁) (g : σ → S₁) p` : given a semiring homomorphism from `R` to another
  semiring `S₁`, and a map `σ → S₁`, evaluates `p` at this valuation, returning a term of type `S₁`.
  Note that `eval₂` can be made using `eval` and `map` (see below), and it has been suggested
  that sticking to `eval` and `map` might make the code less brittle.

* `eval (g : σ → R) p` : given a map `σ → R`, evaluates `p` at this valuation,
  returning a term of type `R`

* `map (f : R → S₁) p` : returns the multivariate polynomial obtained from `p` by the change of
  coefficient semiring corresponding to `f`

## Implementation notes

Recall that if `Y` has a zero, then `X →₀ Y` is the type of functions from `X` to `Y` with finite
support, i.e. such that only finitely many elements of `X` get sent to non-zero terms in `Y`.
The definition of `mv_polynomial σ R` is `(σ →₀ ℕ) →₀ R` ; here `σ →₀ ℕ` denotes the space of all
monomials in the variables, and the function to `R` sends a monomial to its coefficient in
the polynomial being represented.

## Tags

polynomial, multivariate polynomial, multivariable polynomial

-/

/-- Multivariate polynomial, where `σ` is the index set of the variables and
  `R` is the coefficient ring -/
def mv_polynomial (σ : Type u_1) (R : Type u_2) [comm_semiring R] :=
  add_monoid_algebra R (σ →₀ ℕ)

namespace mv_polynomial


protected instance decidable_eq_mv_polynomial {R : Type u} {σ : Type u_1} [comm_semiring R] [DecidableEq σ] [DecidableEq R] : DecidableEq (mv_polynomial σ R) :=
  finsupp.finsupp.decidable_eq

protected instance comm_semiring {R : Type u} {σ : Type u_1} [comm_semiring R] : comm_semiring (mv_polynomial σ R) :=
  add_monoid_algebra.comm_semiring

protected instance inhabited {R : Type u} {σ : Type u_1} [comm_semiring R] : Inhabited (mv_polynomial σ R) :=
  { default := 0 }

protected instance has_scalar {R : Type u} {σ : Type u_1} [comm_semiring R] : has_scalar R (mv_polynomial σ R) :=
  add_monoid_algebra.has_scalar

protected instance semimodule {R : Type u} {σ : Type u_1} [comm_semiring R] : semimodule R (mv_polynomial σ R) :=
  add_monoid_algebra.semimodule

protected instance algebra {R : Type u} {σ : Type u_1} [comm_semiring R] : algebra R (mv_polynomial σ R) :=
  add_monoid_algebra.algebra

/-- The coercion turning an `mv_polynomial` into the function which reports the coefficient
of a given monomial. -/
def coeff_coe_to_fun {R : Type u} {σ : Type u_1} [comm_semiring R] : has_coe_to_fun (mv_polynomial σ R) :=
  finsupp.has_coe_to_fun

/-- `monomial s a` is the monomial with coefficient `a` and exponents given by `s`  -/
def monomial {R : Type u} {σ : Type u_1} [comm_semiring R] (s : σ →₀ ℕ) (a : R) : mv_polynomial σ R :=
  finsupp.single s a

theorem single_eq_monomial {R : Type u} {σ : Type u_1} [comm_semiring R] (s : σ →₀ ℕ) (a : R) : finsupp.single s a = monomial s a :=
  rfl

/-- `C a` is the constant polynomial with value `a` -/
def C {R : Type u} {σ : Type u_1} [comm_semiring R] : R →+* mv_polynomial σ R :=
  ring_hom.mk (monomial 0) sorry sorry sorry sorry

theorem algebra_map_eq (R : Type u) (σ : Type u_1) [comm_semiring R] : algebra_map R (mv_polynomial σ R) = C :=
  rfl

/-- `X n` is the degree `1` monomial $X_n$. -/
def X {R : Type u} {σ : Type u_1} [comm_semiring R] (n : σ) : mv_polynomial σ R :=
  monomial (finsupp.single n 1) 1

@[simp] theorem C_0 {R : Type u} {σ : Type u_1} [comm_semiring R] : coe_fn C 0 = 0 := sorry

@[simp] theorem C_1 {R : Type u} {σ : Type u_1} [comm_semiring R] : coe_fn C 1 = 1 :=
  rfl

theorem C_mul_monomial {R : Type u} {σ : Type u_1} {a : R} {a' : R} {s : σ →₀ ℕ} [comm_semiring R] : coe_fn C a * monomial s a' = monomial s (a * a') := sorry

@[simp] theorem C_add {R : Type u} {σ : Type u_1} {a : R} {a' : R} [comm_semiring R] : coe_fn C (a + a') = coe_fn C a + coe_fn C a' :=
  finsupp.single_add

@[simp] theorem C_mul {R : Type u} {σ : Type u_1} {a : R} {a' : R} [comm_semiring R] : coe_fn C (a * a') = coe_fn C a * coe_fn C a' :=
  Eq.symm C_mul_monomial

@[simp] theorem C_pow {R : Type u} {σ : Type u_1} [comm_semiring R] (a : R) (n : ℕ) : coe_fn C (a ^ n) = coe_fn C a ^ n := sorry

theorem C_injective (σ : Type u_1) (R : Type u_2) [comm_semiring R] : function.injective ⇑C :=
  finsupp.single_injective 0

theorem C_surjective {R : Type u_1} [comm_semiring R] (σ : Type u_2) (hσ : ¬Nonempty σ) : function.surjective ⇑C := sorry

theorem C_surjective_fin_0 {R : Type u_1} [comm_ring R] : function.surjective ⇑C := sorry

@[simp] theorem C_inj {σ : Type u_1} (R : Type u_2) [comm_semiring R] (r : R) (s : R) : coe_fn C r = coe_fn C s ↔ r = s :=
  function.injective.eq_iff (C_injective σ R)

protected instance infinite_of_infinite (σ : Type u_1) (R : Type u_2) [comm_semiring R] [infinite R] : infinite (mv_polynomial σ R) :=
  infinite.of_injective (⇑C) (C_injective σ R)

protected instance infinite_of_nonempty (σ : Type u_1) (R : Type u_2) [Nonempty σ] [comm_semiring R] [nontrivial R] : infinite (mv_polynomial σ R) := sorry

theorem C_eq_coe_nat {R : Type u} {σ : Type u_1} [comm_semiring R] (n : ℕ) : coe_fn C ↑n = ↑n := sorry

theorem C_mul' {R : Type u} {σ : Type u_1} {a : R} [comm_semiring R] {p : mv_polynomial σ R} : coe_fn C a * p = a • p := sorry

theorem smul_eq_C_mul {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) (a : R) : a • p = coe_fn C a * p :=
  Eq.symm C_mul'

theorem X_pow_eq_single {R : Type u} {σ : Type u_1} {e : ℕ} {n : σ} [comm_semiring R] : X n ^ e = monomial (finsupp.single n e) 1 := sorry

theorem monomial_add_single {R : Type u} {σ : Type u_1} {a : R} {e : ℕ} {n : σ} {s : σ →₀ ℕ} [comm_semiring R] : monomial (s + finsupp.single n e) a = monomial s a * X n ^ e := sorry

theorem monomial_single_add {R : Type u} {σ : Type u_1} {a : R} {e : ℕ} {n : σ} {s : σ →₀ ℕ} [comm_semiring R] : monomial (finsupp.single n e + s) a = X n ^ e * monomial s a := sorry

theorem single_eq_C_mul_X {R : Type u} {σ : Type u_1} [comm_semiring R] {s : σ} {a : R} {n : ℕ} : monomial (finsupp.single s n) a = coe_fn C a * X s ^ n := sorry

@[simp] theorem monomial_add {R : Type u} {σ : Type u_1} [comm_semiring R] {s : σ →₀ ℕ} {a : R} {b : R} : monomial s a + monomial s b = monomial s (a + b) := sorry

@[simp] theorem monomial_mul {R : Type u} {σ : Type u_1} [comm_semiring R] {s : σ →₀ ℕ} {s' : σ →₀ ℕ} {a : R} {b : R} : monomial s a * monomial s' b = monomial (s + s') (a * b) := sorry

@[simp] theorem monomial_zero {R : Type u} {σ : Type u_1} [comm_semiring R] {s : σ →₀ ℕ} : monomial s 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (monomial s 0 = 0)) (monomial.equations._eqn_1 s 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (finsupp.single s 0 = 0)) finsupp.single_zero)) (Eq.refl 0))

@[simp] theorem sum_monomial {R : Type u} {σ : Type u_1} [comm_semiring R] {A : Type u_2} [add_comm_monoid A] {u : σ →₀ ℕ} {r : R} {b : (σ →₀ ℕ) → R → A} (w : b u 0 = 0) : finsupp.sum (monomial u r) b = b u r :=
  finsupp.sum_single_index w

theorem monomial_eq {R : Type u} {σ : Type u_1} {a : R} {s : σ →₀ ℕ} [comm_semiring R] : monomial s a = coe_fn C a * finsupp.prod s fun (n : σ) (e : ℕ) => X n ^ e := sorry

theorem induction_on {R : Type u} {σ : Type u_1} [comm_semiring R] {M : mv_polynomial σ R → Prop} (p : mv_polynomial σ R) (h_C : ∀ (a : R), M (coe_fn C a)) (h_add : ∀ (p q : mv_polynomial σ R), M p → M q → M (p + q)) (h_X : ∀ (p : mv_polynomial σ R) (n : σ), M p → M (p * X n)) : M p := sorry

theorem induction_on' {R : Type u} {σ : Type u_1} [comm_semiring R] {P : mv_polynomial σ R → Prop} (p : mv_polynomial σ R) (h1 : ∀ (u : σ →₀ ℕ) (a : R), P (monomial u a)) (h2 : ∀ (p q : mv_polynomial σ R), P p → P q → P (p + q)) : P p := sorry

theorem ring_hom_ext {R : Type u} {σ : Type u_1} [comm_semiring R] {A : Type u_2} [semiring A] {f : mv_polynomial σ R →+* A} {g : mv_polynomial σ R →+* A} (hC : ∀ (r : R), coe_fn f (coe_fn C r) = coe_fn g (coe_fn C r)) (hX : ∀ (i : σ), coe_fn f (X i) = coe_fn g (X i)) : f = g :=
  add_monoid_algebra.ring_hom_ext' (ring_hom.ext fun (x : R) => hC x)
    (finsupp.mul_hom_ext' fun (x : σ) => monoid_hom.ext_mnat (hX x))

theorem hom_eq_hom {R : Type u} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [semiring S₂] (f : mv_polynomial σ R →+* S₂) (g : mv_polynomial σ R →+* S₂) (hC : ∀ (a : R), coe_fn f (coe_fn C a) = coe_fn g (coe_fn C a)) (hX : ∀ (n : σ), coe_fn f (X n) = coe_fn g (X n)) (p : mv_polynomial σ R) : coe_fn f p = coe_fn g p :=
  ring_hom.congr_fun (ring_hom_ext hC hX) p

theorem is_id {R : Type u} {σ : Type u_1} [comm_semiring R] (f : mv_polynomial σ R →+* mv_polynomial σ R) (hC : ∀ (a : R), coe_fn f (coe_fn C a) = coe_fn C a) (hX : ∀ (n : σ), coe_fn f (X n) = X n) (p : mv_polynomial σ R) : coe_fn f p = p :=
  hom_eq_hom f (ring_hom.id (mv_polynomial σ R)) hC hX p

theorem alg_hom_ext {R : Type u} {σ : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {f : alg_hom R (mv_polynomial σ R) A} {g : alg_hom R (mv_polynomial σ R) A} (hf : ∀ (i : σ), coe_fn f (X i) = coe_fn g (X i)) : f = g :=
  add_monoid_algebra.alg_hom_ext' (finsupp.mul_hom_ext' fun (x : σ) => monoid_hom.ext_mnat (hf x))

@[simp] theorem alg_hom_C {R : Type u} {σ : Type u_1} [comm_semiring R] (f : alg_hom R (mv_polynomial σ R) (mv_polynomial σ R)) (r : R) : coe_fn f (coe_fn C r) = coe_fn C r :=
  alg_hom.commutes f r

-- While setting up `coeff`, we make `mv_polynomial` reducible so we can treat it as a function.

/-- The coefficient of the monomial `m` in the multi-variable polynomial `p`. -/
def coeff {R : Type u} {σ : Type u_1} [comm_semiring R] (m : σ →₀ ℕ) (p : mv_polynomial σ R) : R :=
  coe_fn p m

theorem ext {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) (q : mv_polynomial σ R) : (∀ (m : σ →₀ ℕ), coeff m p = coeff m q) → p = q :=
  finsupp.ext

theorem ext_iff {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) (q : mv_polynomial σ R) : p = q ↔ ∀ (m : σ →₀ ℕ), coeff m p = coeff m q :=
  { mp :=
      fun (h : p = q) (m : σ →₀ ℕ) => eq.mpr (id (Eq._oldrec (Eq.refl (coeff m p = coeff m q)) h)) (Eq.refl (coeff m q)),
    mpr := ext p q }

@[simp] theorem coeff_add {R : Type u} {σ : Type u_1} [comm_semiring R] (m : σ →₀ ℕ) (p : mv_polynomial σ R) (q : mv_polynomial σ R) : coeff m (p + q) = coeff m p + coeff m q :=
  finsupp.add_apply

@[simp] theorem coeff_zero {R : Type u} {σ : Type u_1} [comm_semiring R] (m : σ →₀ ℕ) : coeff m 0 = 0 :=
  rfl

@[simp] theorem coeff_zero_X {R : Type u} {σ : Type u_1} [comm_semiring R] (i : σ) : coeff 0 (X i) = 0 := sorry

protected instance coeff.is_add_monoid_hom {R : Type u} {σ : Type u_1} [comm_semiring R] (m : σ →₀ ℕ) : is_add_monoid_hom (coeff m) :=
  is_add_monoid_hom.mk (coeff_zero m)

theorem coeff_sum {R : Type u} {σ : Type u_1} [comm_semiring R] {X : Type u_2} (s : finset X) (f : X → mv_polynomial σ R) (m : σ →₀ ℕ) : coeff m (finset.sum s fun (x : X) => f x) = finset.sum s fun (x : X) => coeff m (f x) :=
  Eq.symm (finset.sum_hom s (coeff m))

theorem monic_monomial_eq {R : Type u} {σ : Type u_1} [comm_semiring R] (m : σ →₀ ℕ) : monomial m 1 = finsupp.prod m fun (n : σ) (e : ℕ) => X n ^ e := sorry

@[simp] theorem coeff_monomial {R : Type u} {σ : Type u_1} [comm_semiring R] (m : σ →₀ ℕ) (n : σ →₀ ℕ) (a : R) : coeff m (monomial n a) = ite (n = m) a 0 := sorry

@[simp] theorem coeff_C {R : Type u} {σ : Type u_1} [comm_semiring R] (m : σ →₀ ℕ) (a : R) : coeff m (coe_fn C a) = ite (0 = m) a 0 := sorry

theorem coeff_X_pow {R : Type u} {σ : Type u_1} [comm_semiring R] (i : σ) (m : σ →₀ ℕ) (k : ℕ) : coeff m (X i ^ k) = ite (finsupp.single i k = m) 1 0 := sorry

theorem coeff_X' {R : Type u} {σ : Type u_1} [comm_semiring R] (i : σ) (m : σ →₀ ℕ) : coeff m (X i) = ite (finsupp.single i 1 = m) 1 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coeff m (X i) = ite (finsupp.single i 1 = m) 1 0)) (Eq.symm (coeff_X_pow i m 1))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coeff m (X i) = coeff m (X i ^ 1))) (pow_one (X i)))) (Eq.refl (coeff m (X i))))

@[simp] theorem coeff_X {R : Type u} {σ : Type u_1} [comm_semiring R] (i : σ) : coeff (finsupp.single i 1) (X i) = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coeff (finsupp.single i 1) (X i) = 1)) (coeff_X' i (finsupp.single i 1))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ite (finsupp.single i 1 = finsupp.single i 1) 1 0 = 1)) (if_pos rfl))) (Eq.refl 1))

@[simp] theorem coeff_C_mul {R : Type u} {σ : Type u_1} [comm_semiring R] (m : σ →₀ ℕ) (a : R) (p : mv_polynomial σ R) : coeff m (coe_fn C a * p) = a * coeff m p := sorry

theorem coeff_mul {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) (q : mv_polynomial σ R) (n : σ →₀ ℕ) : coeff n (p * q) =
  finset.sum (finsupp.support (finsupp.antidiagonal n))
    fun (x : (σ →₀ ℕ) × (σ →₀ ℕ)) => coeff (prod.fst x) p * coeff (prod.snd x) q := sorry

@[simp] theorem coeff_mul_X {R : Type u} {σ : Type u_1} [comm_semiring R] (m : σ →₀ ℕ) (s : σ) (p : mv_polynomial σ R) : coeff (m + finsupp.single s 1) (p * X s) = coeff m p := sorry

theorem coeff_mul_X' {R : Type u} {σ : Type u_1} [comm_semiring R] (m : σ →₀ ℕ) (s : σ) (p : mv_polynomial σ R) : coeff m (p * X s) = ite (s ∈ finsupp.support m) (coeff (m - finsupp.single s 1) p) 0 := sorry

theorem eq_zero_iff {R : Type u} {σ : Type u_1} [comm_semiring R] {p : mv_polynomial σ R} : p = 0 ↔ ∀ (d : σ →₀ ℕ), coeff d p = 0 := sorry

theorem ne_zero_iff {R : Type u} {σ : Type u_1} [comm_semiring R] {p : mv_polynomial σ R} : p ≠ 0 ↔ ∃ (d : σ →₀ ℕ), coeff d p ≠ 0 := sorry

theorem exists_coeff_ne_zero {R : Type u} {σ : Type u_1} [comm_semiring R] {p : mv_polynomial σ R} (h : p ≠ 0) : ∃ (d : σ →₀ ℕ), coeff d p ≠ 0 :=
  iff.mp ne_zero_iff h

theorem C_dvd_iff_dvd_coeff {R : Type u} {σ : Type u_1} [comm_semiring R] (r : R) (φ : mv_polynomial σ R) : coe_fn C r ∣ φ ↔ ∀ (i : σ →₀ ℕ), r ∣ coeff i φ := sorry

/--
`constant_coeff p` returns the constant term of the polynomial `p`, defined as `coeff 0 p`.
This is a ring homomorphism.
-/
def constant_coeff {R : Type u} {σ : Type u_1} [comm_semiring R] : mv_polynomial σ R →+* R :=
  ring_hom.mk (coeff 0) sorry sorry sorry sorry

theorem constant_coeff_eq {R : Type u} {σ : Type u_1} [comm_semiring R] : ⇑constant_coeff = coeff 0 :=
  rfl

@[simp] theorem constant_coeff_C {R : Type u} {σ : Type u_1} [comm_semiring R] (r : R) : coe_fn constant_coeff (coe_fn C r) = r := sorry

@[simp] theorem constant_coeff_X {R : Type u} {σ : Type u_1} [comm_semiring R] (i : σ) : coe_fn constant_coeff (X i) = 0 := sorry

theorem constant_coeff_monomial {R : Type u} {σ : Type u_1} [comm_semiring R] (d : σ →₀ ℕ) (r : R) : coe_fn constant_coeff (monomial d r) = ite (d = 0) r 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn constant_coeff (monomial d r) = ite (d = 0) r 0)) constant_coeff_eq))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coeff 0 (monomial d r) = ite (d = 0) r 0)) (coeff_monomial 0 d r)))
      (Eq.refl (ite (d = 0) r 0)))

@[simp] theorem constant_coeff_comp_C (R : Type u) (σ : Type u_1) [comm_semiring R] : ring_hom.comp constant_coeff C = ring_hom.id R :=
  ring_hom.ext fun (x : R) => constant_coeff_C x

@[simp] theorem constant_coeff_comp_algebra_map (R : Type u) (σ : Type u_1) [comm_semiring R] : ring_hom.comp constant_coeff (algebra_map R (mv_polynomial σ R)) = ring_hom.id R :=
  constant_coeff_comp_C R σ

@[simp] theorem support_sum_monomial_coeff {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) : (finset.sum (finsupp.support p) fun (v : σ →₀ ℕ) => monomial v (coeff v p)) = p :=
  finsupp.sum_single p

theorem as_sum {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) : p = finset.sum (finsupp.support p) fun (v : σ →₀ ℕ) => monomial v (coeff v p) :=
  Eq.symm (support_sum_monomial_coeff p)

/-- Evaluate a polynomial `p` given a valuation `g` of all the variables
  and a ring hom `f` from the scalar ring to the target -/
def eval₂ {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) (p : mv_polynomial σ R) : S₁ :=
  finsupp.sum p fun (s : σ →₀ ℕ) (a : R) => coe_fn f a * finsupp.prod s fun (n : σ) (e : ℕ) => g n ^ e

theorem eval₂_eq {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (g : R →+* S₁) (x : σ → S₁) (f : mv_polynomial σ R) : eval₂ g x f =
  finset.sum (finsupp.support f)
    fun (d : σ →₀ ℕ) => coe_fn g (coeff d f) * finset.prod (finsupp.support d) fun (i : σ) => x i ^ coe_fn d i :=
  rfl

theorem eval₂_eq' {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] [fintype σ] (g : R →+* S₁) (x : σ → S₁) (f : mv_polynomial σ R) : eval₂ g x f =
  finset.sum (finsupp.support f)
    fun (d : σ →₀ ℕ) => coe_fn g (coeff d f) * finset.prod finset.univ fun (i : σ) => x i ^ coe_fn d i := sorry

@[simp] theorem eval₂_zero {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) : eval₂ f g 0 = 0 :=
  finsupp.sum_zero_index

@[simp] theorem eval₂_add {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] {p : mv_polynomial σ R} {q : mv_polynomial σ R} [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) : eval₂ f g (p + q) = eval₂ f g p + eval₂ f g q := sorry

@[simp] theorem eval₂_monomial {R : Type u} {S₁ : Type v} {σ : Type u_1} {a : R} {s : σ →₀ ℕ} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) : eval₂ f g (monomial s a) = coe_fn f a * finsupp.prod s fun (n : σ) (e : ℕ) => g n ^ e := sorry

@[simp] theorem eval₂_C {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) (a : R) : eval₂ f g (coe_fn C a) = coe_fn f a := sorry

@[simp] theorem eval₂_one {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) : eval₂ f g 1 = 1 :=
  Eq.trans (eval₂_C f g 1) (is_semiring_hom.map_one ⇑f)

@[simp] theorem eval₂_X {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) (n : σ) : eval₂ f g (X n) = g n := sorry

theorem eval₂_mul_monomial {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] {p : mv_polynomial σ R} [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) {s : σ →₀ ℕ} {a : R} : eval₂ f g (p * monomial s a) = eval₂ f g p * coe_fn f a * finsupp.prod s fun (n : σ) (e : ℕ) => g n ^ e := sorry

@[simp] theorem eval₂_mul {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] {q : mv_polynomial σ R} [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) {p : mv_polynomial σ R} : eval₂ f g (p * q) = eval₂ f g p * eval₂ f g q := sorry

@[simp] theorem eval₂_pow {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) {p : mv_polynomial σ R} {n : ℕ} : eval₂ f g (p ^ n) = eval₂ f g p ^ n := sorry

protected instance eval₂.is_semiring_hom {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) : is_semiring_hom (eval₂ f g) :=
  is_semiring_hom.mk (eval₂_zero f g) (eval₂_one f g) (fun (p q : mv_polynomial σ R) => eval₂_add f g)
    fun (p q : mv_polynomial σ R) => eval₂_mul f g

/-- `mv_polynomial.eval₂` as a `ring_hom`. -/
def eval₂_hom {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) : mv_polynomial σ R →+* S₁ :=
  ring_hom.of (eval₂ f g)

@[simp] theorem coe_eval₂_hom {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) : ⇑(eval₂_hom f g) = eval₂ f g :=
  rfl

theorem eval₂_hom_congr {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] {f₁ : R →+* S₁} {f₂ : R →+* S₁} {g₁ : σ → S₁} {g₂ : σ → S₁} {p₁ : mv_polynomial σ R} {p₂ : mv_polynomial σ R} : f₁ = f₂ → g₁ = g₂ → p₁ = p₂ → coe_fn (eval₂_hom f₁ g₁) p₁ = coe_fn (eval₂_hom f₂ g₂) p₂ :=
  fun (ᾰ : f₁ = f₂) (ᾰ_1 : g₁ = g₂) (ᾰ_2 : p₁ = p₂) =>
    Eq._oldrec (Eq._oldrec (Eq._oldrec (Eq.refl (coe_fn (eval₂_hom f₁ g₁) p₁)) ᾰ_2) ᾰ_1) ᾰ

@[simp] theorem eval₂_hom_C {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) (r : R) : coe_fn (eval₂_hom f g) (coe_fn C r) = coe_fn f r :=
  eval₂_C f g r

@[simp] theorem eval₂_hom_X' {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) (i : σ) : coe_fn (eval₂_hom f g) (X i) = g i :=
  eval₂_X f g i

@[simp] theorem comp_eval₂_hom {R : Type u} {S₁ : Type v} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] [comm_semiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂) : ring_hom.comp φ (eval₂_hom f g) = eval₂_hom (ring_hom.comp φ f) fun (i : σ) => coe_fn φ (g i) := sorry

theorem map_eval₂_hom {R : Type u} {S₁ : Type v} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] [comm_semiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂) (p : mv_polynomial σ R) : coe_fn φ (coe_fn (eval₂_hom f g) p) = coe_fn (eval₂_hom (ring_hom.comp φ f) fun (i : σ) => coe_fn φ (g i)) p := sorry

theorem eval₂_hom_monomial {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) (d : σ →₀ ℕ) (r : R) : coe_fn (eval₂_hom f g) (monomial d r) = coe_fn f r * finsupp.prod d fun (i : σ) (k : ℕ) => g i ^ k := sorry

theorem eval₂_comp_left {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] {S₂ : Type u_2} [comm_semiring S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p : mv_polynomial σ R) : coe_fn k (eval₂ f g p) = eval₂ (ring_hom.comp k f) (⇑k ∘ g) p := sorry

@[simp] theorem eval₂_eta {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) : eval₂ C X p = p := sorry

theorem eval₂_congr {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] {p : mv_polynomial σ R} [comm_semiring S₁] (f : R →+* S₁) (g₁ : σ → S₁) (g₂ : σ → S₁) (h : ∀ {i : σ} {c : σ →₀ ℕ}, i ∈ finsupp.support c → coeff c p ≠ 0 → g₁ i = g₂ i) : eval₂ f g₁ p = eval₂ f g₂ p := sorry

@[simp] theorem eval₂_prod {R : Type u} {S₁ : Type v} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) (s : finset S₂) (p : S₂ → mv_polynomial σ R) : eval₂ f g (finset.prod s fun (x : S₂) => p x) = finset.prod s fun (x : S₂) => eval₂ f g (p x) :=
  Eq.symm (finset.prod_hom s (eval₂ f g))

@[simp] theorem eval₂_sum {R : Type u} {S₁ : Type v} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) (s : finset S₂) (p : S₂ → mv_polynomial σ R) : eval₂ f g (finset.sum s fun (x : S₂) => p x) = finset.sum s fun (x : S₂) => eval₂ f g (p x) :=
  Eq.symm (finset.sum_hom s (eval₂ f g))

theorem eval₂_assoc {R : Type u} {S₁ : Type v} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) (q : S₂ → mv_polynomial σ R) (p : mv_polynomial S₂ R) : eval₂ f (fun (t : S₂) => eval₂ f g (q t)) p = eval₂ f g (eval₂ C q p) := sorry

/-- Evaluate a polynomial `p` given a valuation `f` of all the variables -/
def eval {R : Type u} {σ : Type u_1} [comm_semiring R] (f : σ → R) : mv_polynomial σ R →+* R :=
  eval₂_hom (ring_hom.id R) f

theorem eval_eq {R : Type u} {σ : Type u_1} [comm_semiring R] (x : σ → R) (f : mv_polynomial σ R) : coe_fn (eval x) f =
  finset.sum (finsupp.support f)
    fun (d : σ →₀ ℕ) => coeff d f * finset.prod (finsupp.support d) fun (i : σ) => x i ^ coe_fn d i :=
  rfl

theorem eval_eq' {R : Type u} {σ : Type u_1} [comm_semiring R] [fintype σ] (x : σ → R) (f : mv_polynomial σ R) : coe_fn (eval x) f =
  finset.sum (finsupp.support f) fun (d : σ →₀ ℕ) => coeff d f * finset.prod finset.univ fun (i : σ) => x i ^ coe_fn d i :=
  eval₂_eq' (ring_hom.id R) x f

theorem eval_monomial {R : Type u} {σ : Type u_1} {a : R} {s : σ →₀ ℕ} [comm_semiring R] {f : σ → R} : coe_fn (eval f) (monomial s a) = a * finsupp.prod s fun (n : σ) (e : ℕ) => f n ^ e :=
  eval₂_monomial (ring_hom.id R) fun (n : σ) => f n

@[simp] theorem eval_C {R : Type u} {σ : Type u_1} [comm_semiring R] {f : σ → R} (a : R) : coe_fn (eval f) (coe_fn C a) = a :=
  eval₂_C (ring_hom.id R) fun (n : σ) => f n

@[simp] theorem eval_X {R : Type u} {σ : Type u_1} [comm_semiring R] {f : σ → R} (n : σ) : coe_fn (eval f) (X n) = f n :=
  eval₂_X (ring_hom.id R) fun (n : σ) => f n

@[simp] theorem smul_eval {R : Type u} {σ : Type u_1} [comm_semiring R] (x : σ → R) (p : mv_polynomial σ R) (s : R) : coe_fn (eval x) (s • p) = s * coe_fn (eval x) p := sorry

theorem eval_sum {R : Type u} {σ : Type u_1} [comm_semiring R] {ι : Type u_2} (s : finset ι) (f : ι → mv_polynomial σ R) (g : σ → R) : coe_fn (eval g) (finset.sum s fun (i : ι) => f i) = finset.sum s fun (i : ι) => coe_fn (eval g) (f i) :=
  ring_hom.map_sum (eval g) (fun (i : ι) => f i) s

theorem eval_prod {R : Type u} {σ : Type u_1} [comm_semiring R] {ι : Type u_2} (s : finset ι) (f : ι → mv_polynomial σ R) (g : σ → R) : coe_fn (eval g) (finset.prod s fun (i : ι) => f i) = finset.prod s fun (i : ι) => coe_fn (eval g) (f i) :=
  ring_hom.map_prod (eval g) (fun (i : ι) => f i) s

theorem eval_assoc {R : Type u} {σ : Type u_1} [comm_semiring R] {τ : Type u_2} (f : σ → mv_polynomial τ R) (g : τ → R) (p : mv_polynomial σ R) : coe_fn (eval (⇑(eval g) ∘ f)) p = coe_fn (eval g) (eval₂ C f p) := sorry

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) : mv_polynomial σ R →+* mv_polynomial σ S₁ :=
  eval₂_hom (ring_hom.comp C f) X

@[simp] theorem map_monomial {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (s : σ →₀ ℕ) (a : R) : coe_fn (map f) (monomial s a) = monomial s (coe_fn f a) :=
  Eq.trans (eval₂_monomial (ring_hom.comp C f) fun (n : σ) => X n) (Eq.symm monomial_eq)

@[simp] theorem map_C {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (a : R) : coe_fn (map f) (coe_fn C a) = coe_fn C (coe_fn f a) :=
  map_monomial f 0

@[simp] theorem map_X {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (n : σ) : coe_fn (map f) (X n) = X n :=
  eval₂_X (ring_hom.comp C f) fun (n : σ) => X n

theorem map_id {R : Type u} {σ : Type u_1} [comm_semiring R] (p : mv_polynomial σ R) : coe_fn (map (ring_hom.id R)) p = p :=
  eval₂_eta

theorem map_map {R : Type u} {S₁ : Type v} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) [comm_semiring S₂] (g : S₁ →+* S₂) (p : mv_polynomial σ R) : coe_fn (map g) (coe_fn (map f) p) = coe_fn (map (ring_hom.comp g f)) p := sorry

theorem eval₂_eq_eval_map {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) (p : mv_polynomial σ R) : eval₂ f g p = coe_fn (eval g) (coe_fn (map f) p) := sorry

theorem eval₂_comp_right {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] {S₂ : Type u_2} [comm_semiring S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p : mv_polynomial σ R) : coe_fn k (eval₂ f g p) = eval₂ k (⇑k ∘ g) (coe_fn (map f) p) := sorry

theorem map_eval₂ {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : S₂ → mv_polynomial S₃ R) (p : mv_polynomial S₂ R) : coe_fn (map f) (eval₂ C g p) = eval₂ C (⇑(map f) ∘ g) (coe_fn (map f) p) := sorry

theorem coeff_map {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (p : mv_polynomial σ R) (m : σ →₀ ℕ) : coeff m (coe_fn (map f) p) = coe_fn f (coeff m p) := sorry

theorem map_injective {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (hf : function.injective ⇑f) : function.injective ⇑(map f) := sorry

@[simp] theorem eval_map {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : σ → S₁) (p : mv_polynomial σ R) : coe_fn (eval g) (coe_fn (map f) p) = eval₂ f g p := sorry

@[simp] theorem eval₂_map {R : Type u} {S₁ : Type v} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] [comm_semiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂) (p : mv_polynomial σ R) : eval₂ φ g (coe_fn (map f) p) = eval₂ (ring_hom.comp φ f) g p := sorry

@[simp] theorem eval₂_hom_map_hom {R : Type u} {S₁ : Type v} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] [comm_semiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂) (p : mv_polynomial σ R) : coe_fn (eval₂_hom φ g) (coe_fn (map f) p) = coe_fn (eval₂_hom (ring_hom.comp φ f) g) p :=
  eval₂_map f g φ p

@[simp] theorem constant_coeff_map {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (φ : mv_polynomial σ R) : coe_fn constant_coeff (coe_fn (map f) φ) = coe_fn f (coe_fn constant_coeff φ) :=
  coeff_map f φ 0

theorem constant_coeff_comp_map {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) : ring_hom.comp constant_coeff (map f) = ring_hom.comp f constant_coeff := sorry

theorem support_map_subset {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (p : mv_polynomial σ R) : finsupp.support (coe_fn (map f) p) ⊆ finsupp.support p := sorry

theorem support_map_of_injective {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (p : mv_polynomial σ R) {f : R →+* S₁} (hf : function.injective ⇑f) : finsupp.support (coe_fn (map f) p) = finsupp.support p := sorry

theorem C_dvd_iff_map_hom_eq_zero {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (q : R →+* S₁) (r : R) (hr : ∀ (r' : R), coe_fn q r' = 0 ↔ r ∣ r') (φ : mv_polynomial σ R) : coe_fn C r ∣ φ ↔ coe_fn (map q) φ = 0 := sorry

theorem map_map_range_eq_iff {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] (f : R →+* S₁) (g : S₁ → R) (hg : g 0 = 0) (φ : mv_polynomial σ S₁) : coe_fn (map f) (finsupp.map_range g hg φ) = φ ↔ ∀ (d : σ →₀ ℕ), coe_fn f (g (coeff d φ)) = coeff d φ := sorry

/-! ### The algebra of multivariate polynomials -/

/-- A map `σ → S₁` where `S₁` is an algebra over `R` generates an `R`-algebra homomorphism
from multivariate polynomials over `σ` to `S₁`. -/
def aeval {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] (f : σ → S₁) [comm_semiring S₁] [algebra R S₁] : alg_hom R (mv_polynomial σ R) S₁ :=
  alg_hom.mk (ring_hom.to_fun (eval₂_hom (algebra_map R S₁) f)) sorry sorry sorry sorry sorry

theorem aeval_def {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] (f : σ → S₁) [comm_semiring S₁] [algebra R S₁] (p : mv_polynomial σ R) : coe_fn (aeval f) p = eval₂ (algebra_map R S₁) f p :=
  rfl

theorem aeval_eq_eval₂_hom {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] (f : σ → S₁) [comm_semiring S₁] [algebra R S₁] (p : mv_polynomial σ R) : coe_fn (aeval f) p = coe_fn (eval₂_hom (algebra_map R S₁) f) p :=
  rfl

@[simp] theorem aeval_X {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] (f : σ → S₁) [comm_semiring S₁] [algebra R S₁] (s : σ) : coe_fn (aeval f) (X s) = f s :=
  eval₂_X (algebra_map R S₁) (fun (n : σ) => f n) s

@[simp] theorem aeval_C {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] (f : σ → S₁) [comm_semiring S₁] [algebra R S₁] (r : R) : coe_fn (aeval f) (coe_fn C r) = coe_fn (algebra_map R S₁) r :=
  eval₂_C (algebra_map R S₁) (fun (n : σ) => f n) r

theorem aeval_unique {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] [algebra R S₁] (φ : alg_hom R (mv_polynomial σ R) S₁) : φ = aeval (⇑φ ∘ X) := sorry

theorem comp_aeval {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] (f : σ → S₁) [comm_semiring S₁] [algebra R S₁] {B : Type u_2} [comm_semiring B] [algebra R B] (φ : alg_hom R S₁ B) : alg_hom.comp φ (aeval f) = aeval fun (i : σ) => coe_fn φ (f i) := sorry

@[simp] theorem map_aeval {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] [algebra R S₁] {B : Type u_2} [comm_semiring B] (g : σ → S₁) (φ : S₁ →+* B) (p : mv_polynomial σ R) : coe_fn φ (coe_fn (aeval g) p) = coe_fn (eval₂_hom (ring_hom.comp φ (algebra_map R S₁)) fun (i : σ) => coe_fn φ (g i)) p := sorry

@[simp] theorem eval₂_hom_zero {R : Type u} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₂] (f : R →+* S₂) (p : mv_polynomial σ R) : coe_fn (eval₂_hom f 0) p = coe_fn f (coe_fn constant_coeff p) := sorry

@[simp] theorem eval₂_hom_zero' {R : Type u} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₂] (f : R →+* S₂) (p : mv_polynomial σ R) : coe_fn (eval₂_hom f fun (_x : σ) => 0) p = coe_fn f (coe_fn constant_coeff p) :=
  eval₂_hom_zero f p

@[simp] theorem aeval_zero {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] [algebra R S₁] (p : mv_polynomial σ R) : coe_fn (aeval 0) p = coe_fn (algebra_map R S₁) (coe_fn constant_coeff p) :=
  eval₂_hom_zero (algebra_map R S₁) p

@[simp] theorem aeval_zero' {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] [algebra R S₁] (p : mv_polynomial σ R) : coe_fn (aeval fun (_x : σ) => 0) p = coe_fn (algebra_map R S₁) (coe_fn constant_coeff p) :=
  aeval_zero p

theorem aeval_monomial {R : Type u} {S₁ : Type v} {σ : Type u_1} [comm_semiring R] [comm_semiring S₁] [algebra R S₁] (g : σ → S₁) (d : σ →₀ ℕ) (r : R) : coe_fn (aeval g) (monomial d r) = coe_fn (algebra_map R S₁) r * finsupp.prod d fun (i : σ) (k : ℕ) => g i ^ k :=
  eval₂_hom_monomial (algebra_map R S₁) (fun (n : σ) => g n) d r

theorem eval₂_hom_eq_zero {R : Type u} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₂] (f : R →+* S₂) (g : σ → S₂) (φ : mv_polynomial σ R) (h : ∀ (d : σ →₀ ℕ), coeff d φ ≠ 0 → ∃ (i : σ), ∃ (H : i ∈ finsupp.support d), g i = 0) : coe_fn (eval₂_hom f g) φ = 0 := sorry

theorem aeval_eq_zero {R : Type u} {S₂ : Type w} {σ : Type u_1} [comm_semiring R] [comm_semiring S₂] [algebra R S₂] (f : σ → S₂) (φ : mv_polynomial σ R) (h : ∀ (d : σ →₀ ℕ), coeff d φ ≠ 0 → ∃ (i : σ), ∃ (H : i ∈ finsupp.support d), f i = 0) : coe_fn (aeval f) φ = 0 :=
  eval₂_hom_eq_zero (algebra_map R S₂) (fun (n : σ) => f n) φ h

