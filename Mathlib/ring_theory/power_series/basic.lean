/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.default
import Mathlib.ring_theory.ideal.operations
import Mathlib.ring_theory.multiplicity
import Mathlib.ring_theory.algebra_tower
import Mathlib.tactic.linarith.default
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Formal power series

This file defines (multivariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

We provide the natural inclusion from polynomials to formal power series.

## Generalities

The file starts with setting up the (semi)ring structure on multivariate power series.

`trunc n φ` truncates a formal power series to the polynomial
that has the same coefficients as `φ`, for all `m ≤ n`, and `0` otherwise.

If the constant coefficient of a formal power series is invertible,
then this formal power series is invertible.

Formal power series over a local ring form a local ring.

## Formal power series in one variable

We prove that if the ring of coefficients is an integral domain,
then formal power series in one variable form an integral domain.

The `order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `order` is a valuation
(`order_mul`, `le_order_add`).

## Implementation notes

In this file we define multivariate formal power series with
variables indexed by `σ` and coefficients in `R` as
`mv_power_series σ R := (σ →₀ ℕ) → R`.
Unfortunately there is not yet enough API to show that they are the completion
of the ring of multivariate polynomials. However, we provide most of the infrastructure
that is needed to do this. Once I-adic completion (topological or algebraic) is available
it should not be hard to fill in the details.

Formal power series in one variable are defined as
`power_series R := mv_power_series unit R`.

This allows us to port a lot of proofs and properties
from the multivariate case to the single variable case.
However, it means that formal power series are indexed by `unit →₀ ℕ`,
which is of course canonically isomorphic to `ℕ`.
We then build some glue to treat formal power series as if they are indexed by `ℕ`.
Occasionally this leads to proofs that are uglier than expected.
-/

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring.-/
def mv_power_series (σ : Type u_1) (R : Type u_2)  :=
  (σ →₀ ℕ) → R

namespace mv_power_series


protected instance inhabited {σ : Type u_1} {R : Type u_2} [Inhabited R] : Inhabited (mv_power_series σ R) :=
  { default := fun (_x : σ →₀ ℕ) => Inhabited.default }

protected instance has_zero {σ : Type u_1} {R : Type u_2} [HasZero R] : HasZero (mv_power_series σ R) :=
  pi.has_zero

protected instance add_monoid {σ : Type u_1} {R : Type u_2} [add_monoid R] : add_monoid (mv_power_series σ R) :=
  pi.add_monoid

protected instance add_group {σ : Type u_1} {R : Type u_2} [add_group R] : add_group (mv_power_series σ R) :=
  pi.add_group

protected instance add_comm_monoid {σ : Type u_1} {R : Type u_2} [add_comm_monoid R] : add_comm_monoid (mv_power_series σ R) :=
  pi.add_comm_monoid

protected instance add_comm_group {σ : Type u_1} {R : Type u_2} [add_comm_group R] : add_comm_group (mv_power_series σ R) :=
  pi.add_comm_group

protected instance nontrivial {σ : Type u_1} {R : Type u_2} [nontrivial R] : nontrivial (mv_power_series σ R) :=
  function.nontrivial

protected instance semimodule {σ : Type u_1} {R : Type u_2} {A : Type u_3} [semiring R] [add_comm_monoid A] [semimodule R A] : semimodule R (mv_power_series σ A) :=
  pi.semimodule (σ →₀ ℕ) (fun (ᾰ : σ →₀ ℕ) => A) R

protected instance is_scalar_tower {σ : Type u_1} {R : Type u_2} {A : Type u_3} {S : Type u_4} [semiring R] [semiring S] [add_comm_monoid A] [semimodule R A] [semimodule S A] [has_scalar R S] [is_scalar_tower R S A] : is_scalar_tower R S (mv_power_series σ A) :=
  pi.is_scalar_tower

/-- The `n`th monomial with coefficient `a` as multivariate formal power series.-/
def monomial {σ : Type u_1} (R : Type u_2) [semiring R] (n : σ →₀ ℕ) : linear_map R R (mv_power_series σ R) :=
  linear_map.std_basis R (fun (n : σ →₀ ℕ) => R) n

/-- The `n`th coefficient of a multivariate formal power series.-/
def coeff {σ : Type u_1} (R : Type u_2) [semiring R] (n : σ →₀ ℕ) : linear_map R (mv_power_series σ R) R :=
  linear_map.proj n

/-- Two multivariate formal power series are equal if all their coefficients are equal.-/
theorem ext {σ : Type u_1} {R : Type u_2} [semiring R] {φ : mv_power_series σ R} {ψ : mv_power_series σ R} (h : ∀ (n : σ →₀ ℕ), coe_fn (coeff R n) φ = coe_fn (coeff R n) ψ) : φ = ψ :=
  funext h

/-- Two multivariate formal power series are equal
 if and only if all their coefficients are equal.-/
theorem ext_iff {σ : Type u_1} {R : Type u_2} [semiring R] {φ : mv_power_series σ R} {ψ : mv_power_series σ R} : φ = ψ ↔ ∀ (n : σ →₀ ℕ), coe_fn (coeff R n) φ = coe_fn (coeff R n) ψ :=
  function.funext_iff

theorem coeff_monomial {σ : Type u_1} {R : Type u_2} [semiring R] (m : σ →₀ ℕ) (n : σ →₀ ℕ) (a : R) : coe_fn (coeff R m) (coe_fn (monomial R n) a) = ite (m = n) a 0 := sorry

@[simp] theorem coeff_monomial_same {σ : Type u_1} {R : Type u_2} [semiring R] (n : σ →₀ ℕ) (a : R) : coe_fn (coeff R n) (coe_fn (monomial R n) a) = a :=
  linear_map.std_basis_same R (fun (n : σ →₀ ℕ) => R) n a

theorem coeff_monomial_ne {σ : Type u_1} {R : Type u_2} [semiring R] {m : σ →₀ ℕ} {n : σ →₀ ℕ} (h : m ≠ n) (a : R) : coe_fn (coeff R m) (coe_fn (monomial R n) a) = 0 :=
  linear_map.std_basis_ne R (fun (n : σ →₀ ℕ) => R) n m h a

theorem eq_of_coeff_monomial_ne_zero {σ : Type u_1} {R : Type u_2} [semiring R] {m : σ →₀ ℕ} {n : σ →₀ ℕ} {a : R} (h : coe_fn (coeff R m) (coe_fn (monomial R n) a) ≠ 0) : m = n :=
  by_contra fun (h' : ¬m = n) => h (coeff_monomial_ne h' a)

@[simp] theorem coeff_comp_monomial {σ : Type u_1} {R : Type u_2} [semiring R] (n : σ →₀ ℕ) : linear_map.comp (coeff R n) (monomial R n) = linear_map.id :=
  linear_map.ext (coeff_monomial_same n)

@[simp] theorem coeff_zero {σ : Type u_1} {R : Type u_2} [semiring R] (n : σ →₀ ℕ) : coe_fn (coeff R n) 0 = 0 :=
  rfl

protected instance has_one {σ : Type u_1} {R : Type u_2} [semiring R] : HasOne (mv_power_series σ R) :=
  { one := coe_fn (monomial R 0) 1 }

theorem coeff_one {σ : Type u_1} {R : Type u_2} [semiring R] (n : σ →₀ ℕ) : coe_fn (coeff R n) 1 = ite (n = 0) 1 0 :=
  coeff_monomial n 0 1

theorem coeff_zero_one {σ : Type u_1} {R : Type u_2} [semiring R] : coe_fn (coeff R 0) 1 = 1 :=
  coeff_monomial_same 0 1

theorem monomial_zero_one {σ : Type u_1} {R : Type u_2} [semiring R] : coe_fn (monomial R 0) 1 = 1 :=
  rfl

protected instance has_mul {σ : Type u_1} {R : Type u_2} [semiring R] : Mul (mv_power_series σ R) :=
  { mul :=
      fun (φ ψ : mv_power_series σ R) (n : σ →₀ ℕ) =>
        finset.sum (finsupp.support (finsupp.antidiagonal n))
          fun (p : (σ →₀ ℕ) × (σ →₀ ℕ)) => coe_fn (coeff R (prod.fst p)) φ * coe_fn (coeff R (prod.snd p)) ψ }

theorem coeff_mul {σ : Type u_1} {R : Type u_2} [semiring R] (n : σ →₀ ℕ) (φ : mv_power_series σ R) (ψ : mv_power_series σ R) : coe_fn (coeff R n) (φ * ψ) =
  finset.sum (finsupp.support (finsupp.antidiagonal n))
    fun (p : (σ →₀ ℕ) × (σ →₀ ℕ)) => coe_fn (coeff R (prod.fst p)) φ * coe_fn (coeff R (prod.snd p)) ψ :=
  rfl

protected theorem zero_mul {σ : Type u_1} {R : Type u_2} [semiring R] (φ : mv_power_series σ R) : 0 * φ = 0 := sorry

protected theorem mul_zero {σ : Type u_1} {R : Type u_2} [semiring R] (φ : mv_power_series σ R) : φ * 0 = 0 := sorry

theorem coeff_monomial_mul {σ : Type u_1} {R : Type u_2} [semiring R] (m : σ →₀ ℕ) (n : σ →₀ ℕ) (φ : mv_power_series σ R) (a : R) : coe_fn (coeff R m) (coe_fn (monomial R n) a * φ) = ite (n ≤ m) (a * coe_fn (coeff R (m - n)) φ) 0 := sorry

theorem coeff_mul_monomial {σ : Type u_1} {R : Type u_2} [semiring R] (m : σ →₀ ℕ) (n : σ →₀ ℕ) (φ : mv_power_series σ R) (a : R) : coe_fn (coeff R m) (φ * coe_fn (monomial R n) a) = ite (n ≤ m) (coe_fn (coeff R (m - n)) φ * a) 0 := sorry

theorem coeff_add_monomial_mul {σ : Type u_1} {R : Type u_2} [semiring R] (m : σ →₀ ℕ) (n : σ →₀ ℕ) (φ : mv_power_series σ R) (a : R) : coe_fn (coeff R (m + n)) (coe_fn (monomial R m) a * φ) = a * coe_fn (coeff R n) φ := sorry

theorem coeff_add_mul_monomial {σ : Type u_1} {R : Type u_2} [semiring R] (m : σ →₀ ℕ) (n : σ →₀ ℕ) (φ : mv_power_series σ R) (a : R) : coe_fn (coeff R (m + n)) (φ * coe_fn (monomial R n) a) = coe_fn (coeff R m) φ * a := sorry

protected theorem one_mul {σ : Type u_1} {R : Type u_2} [semiring R] (φ : mv_power_series σ R) : 1 * φ = φ := sorry

protected theorem mul_one {σ : Type u_1} {R : Type u_2} [semiring R] (φ : mv_power_series σ R) : φ * 1 = φ := sorry

protected theorem mul_add {σ : Type u_1} {R : Type u_2} [semiring R] (φ₁ : mv_power_series σ R) (φ₂ : mv_power_series σ R) (φ₃ : mv_power_series σ R) : φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ := sorry

protected theorem add_mul {σ : Type u_1} {R : Type u_2} [semiring R] (φ₁ : mv_power_series σ R) (φ₂ : mv_power_series σ R) (φ₃ : mv_power_series σ R) : (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ := sorry

protected theorem mul_assoc {σ : Type u_1} {R : Type u_2} [semiring R] (φ₁ : mv_power_series σ R) (φ₂ : mv_power_series σ R) (φ₃ : mv_power_series σ R) : φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃) := sorry

protected instance semiring {σ : Type u_1} {R : Type u_2} [semiring R] : semiring (mv_power_series σ R) :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry Mul.mul mv_power_series.mul_assoc 1
    mv_power_series.one_mul mv_power_series.mul_one mv_power_series.zero_mul mv_power_series.mul_zero
    mv_power_series.mul_add mv_power_series.add_mul

protected instance comm_semiring {σ : Type u_1} {R : Type u_2} [comm_semiring R] : comm_semiring (mv_power_series σ R) :=
  comm_semiring.mk semiring.add sorry semiring.zero sorry sorry sorry semiring.mul sorry semiring.one sorry sorry sorry
    sorry sorry sorry sorry

protected instance ring {σ : Type u_1} {R : Type u_2} [ring R] : ring (mv_power_series σ R) :=
  ring.mk semiring.add sorry semiring.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry semiring.mul
    sorry semiring.one sorry sorry sorry sorry

protected instance comm_ring {σ : Type u_1} {R : Type u_2} [comm_ring R] : comm_ring (mv_power_series σ R) :=
  comm_ring.mk comm_semiring.add sorry comm_semiring.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    comm_semiring.mul sorry comm_semiring.one sorry sorry sorry sorry sorry

theorem monomial_mul_monomial {σ : Type u_1} {R : Type u_2} [semiring R] (m : σ →₀ ℕ) (n : σ →₀ ℕ) (a : R) (b : R) : coe_fn (monomial R m) a * coe_fn (monomial R n) b = coe_fn (monomial R (m + n)) (a * b) := sorry

/-- The constant multivariate formal power series.-/
def C (σ : Type u_1) (R : Type u_2) [semiring R] : R →+* mv_power_series σ R :=
  ring_hom.mk (linear_map.to_fun (monomial R 0)) sorry sorry sorry sorry

@[simp] theorem monomial_zero_eq_C {σ : Type u_1} {R : Type u_2} [semiring R] : ⇑(monomial R 0) = ⇑(C σ R) :=
  rfl

theorem monomial_zero_eq_C_apply {σ : Type u_1} {R : Type u_2} [semiring R] (a : R) : coe_fn (monomial R 0) a = coe_fn (C σ R) a :=
  rfl

theorem coeff_C {σ : Type u_1} {R : Type u_2} [semiring R] (n : σ →₀ ℕ) (a : R) : coe_fn (coeff R n) (coe_fn (C σ R) a) = ite (n = 0) a 0 :=
  coeff_monomial n 0 a

theorem coeff_zero_C {σ : Type u_1} {R : Type u_2} [semiring R] (a : R) : coe_fn (coeff R 0) (coe_fn (C σ R) a) = a :=
  coeff_monomial_same 0 a

/-- The variables of the multivariate formal power series ring.-/
def X {σ : Type u_1} {R : Type u_2} [semiring R] (s : σ) : mv_power_series σ R :=
  coe_fn (monomial R (finsupp.single s 1)) 1

theorem coeff_X {σ : Type u_1} {R : Type u_2} [semiring R] (n : σ →₀ ℕ) (s : σ) : coe_fn (coeff R n) (X s) = ite (n = finsupp.single s 1) 1 0 :=
  coeff_monomial n (finsupp.single s 1) 1

theorem coeff_index_single_X {σ : Type u_1} {R : Type u_2} [semiring R] (s : σ) (t : σ) : coe_fn (coeff R (finsupp.single t 1)) (X s) = ite (t = s) 1 0 := sorry

@[simp] theorem coeff_index_single_self_X {σ : Type u_1} {R : Type u_2} [semiring R] (s : σ) : coe_fn (coeff R (finsupp.single s 1)) (X s) = 1 :=
  coeff_monomial_same (finsupp.single s 1) 1

theorem coeff_zero_X {σ : Type u_1} {R : Type u_2} [semiring R] (s : σ) : coe_fn (coeff R 0) (X s) = 0 := sorry

theorem X_def {σ : Type u_1} {R : Type u_2} [semiring R] (s : σ) : X s = coe_fn (monomial R (finsupp.single s 1)) 1 :=
  rfl

theorem X_pow_eq {σ : Type u_1} {R : Type u_2} [semiring R] (s : σ) (n : ℕ) : X s ^ n = coe_fn (monomial R (finsupp.single s n)) 1 := sorry

theorem coeff_X_pow {σ : Type u_1} {R : Type u_2} [semiring R] (m : σ →₀ ℕ) (s : σ) (n : ℕ) : coe_fn (coeff R m) (X s ^ n) = ite (m = finsupp.single s n) 1 0 := sorry

@[simp] theorem coeff_mul_C {σ : Type u_1} {R : Type u_2} [semiring R] (n : σ →₀ ℕ) (φ : mv_power_series σ R) (a : R) : coe_fn (coeff R n) (φ * coe_fn (C σ R) a) = coe_fn (coeff R n) φ * a := sorry

@[simp] theorem coeff_C_mul {σ : Type u_1} {R : Type u_2} [semiring R] (n : σ →₀ ℕ) (φ : mv_power_series σ R) (a : R) : coe_fn (coeff R n) (coe_fn (C σ R) a * φ) = a * coe_fn (coeff R n) φ := sorry

theorem coeff_zero_mul_X {σ : Type u_1} {R : Type u_2} [semiring R] (φ : mv_power_series σ R) (s : σ) : coe_fn (coeff R 0) (φ * X s) = 0 := sorry

/-- The constant coefficient of a formal power series.-/
def constant_coeff (σ : Type u_1) (R : Type u_2) [semiring R] : mv_power_series σ R →+* R :=
  ring_hom.mk (⇑(coeff R 0)) coeff_zero_one sorry sorry sorry

@[simp] theorem coeff_zero_eq_constant_coeff {σ : Type u_1} {R : Type u_2} [semiring R] : ⇑(coeff R 0) = ⇑(constant_coeff σ R) :=
  rfl

theorem coeff_zero_eq_constant_coeff_apply {σ : Type u_1} {R : Type u_2} [semiring R] (φ : mv_power_series σ R) : coe_fn (coeff R 0) φ = coe_fn (constant_coeff σ R) φ :=
  rfl

@[simp] theorem constant_coeff_C {σ : Type u_1} {R : Type u_2} [semiring R] (a : R) : coe_fn (constant_coeff σ R) (coe_fn (C σ R) a) = a :=
  rfl

@[simp] theorem constant_coeff_comp_C {σ : Type u_1} {R : Type u_2} [semiring R] : ring_hom.comp (constant_coeff σ R) (C σ R) = ring_hom.id R :=
  rfl

@[simp] theorem constant_coeff_zero {σ : Type u_1} {R : Type u_2} [semiring R] : coe_fn (constant_coeff σ R) 0 = 0 :=
  rfl

@[simp] theorem constant_coeff_one {σ : Type u_1} {R : Type u_2} [semiring R] : coe_fn (constant_coeff σ R) 1 = 1 :=
  rfl

@[simp] theorem constant_coeff_X {σ : Type u_1} {R : Type u_2} [semiring R] (s : σ) : coe_fn (constant_coeff σ R) (X s) = 0 :=
  coeff_zero_X s

/-- If a multivariate formal power series is invertible,
 then so is its constant coefficient.-/
theorem is_unit_constant_coeff {σ : Type u_1} {R : Type u_2} [semiring R] (φ : mv_power_series σ R) (h : is_unit φ) : is_unit (coe_fn (constant_coeff σ R) φ) :=
  is_unit.map' (⇑(constant_coeff σ R)) h

@[simp] theorem coeff_smul {σ : Type u_1} {R : Type u_2} [semiring R] (f : mv_power_series σ R) (n : σ →₀ ℕ) (a : R) : coe_fn (coeff R n) (a • f) = a * coe_fn (coeff R n) f :=
  rfl

theorem X_inj {σ : Type u_1} {R : Type u_2} [semiring R] [nontrivial R] {s : σ} {t : σ} : X s = X t ↔ s = t := sorry

/-- The map between multivariate formal power series induced by a map on the coefficients.-/
def map (σ : Type u_1) {R : Type u_2} {S : Type u_3} [semiring R] [semiring S] (f : R →+* S) : mv_power_series σ R →+* mv_power_series σ S :=
  ring_hom.mk (fun (φ : mv_power_series σ R) (n : σ →₀ ℕ) => coe_fn f (coe_fn (coeff R n) φ)) sorry sorry sorry sorry

@[simp] theorem map_id {σ : Type u_1} {R : Type u_2} [semiring R] : map σ (ring_hom.id R) = ring_hom.id (mv_power_series σ R) :=
  rfl

theorem map_comp {σ : Type u_1} {R : Type u_2} {S : Type u_3} {T : Type u_4} [semiring R] [semiring S] [semiring T] (f : R →+* S) (g : S →+* T) : map σ (ring_hom.comp g f) = ring_hom.comp (map σ g) (map σ f) :=
  rfl

@[simp] theorem coeff_map {σ : Type u_1} {R : Type u_2} {S : Type u_3} [semiring R] [semiring S] (f : R →+* S) (n : σ →₀ ℕ) (φ : mv_power_series σ R) : coe_fn (coeff S n) (coe_fn (map σ f) φ) = coe_fn f (coe_fn (coeff R n) φ) :=
  rfl

@[simp] theorem constant_coeff_map {σ : Type u_1} {R : Type u_2} {S : Type u_3} [semiring R] [semiring S] (f : R →+* S) (φ : mv_power_series σ R) : coe_fn (constant_coeff σ S) (coe_fn (map σ f) φ) = coe_fn f (coe_fn (constant_coeff σ R) φ) :=
  rfl

@[simp] theorem map_monomial {σ : Type u_1} {R : Type u_2} {S : Type u_3} [semiring R] [semiring S] (f : R →+* S) (n : σ →₀ ℕ) (a : R) : coe_fn (map σ f) (coe_fn (monomial R n) a) = coe_fn (monomial S n) (coe_fn f a) := sorry

@[simp] theorem map_C {σ : Type u_1} {R : Type u_2} {S : Type u_3} [semiring R] [semiring S] (f : R →+* S) (a : R) : coe_fn (map σ f) (coe_fn (C σ R) a) = coe_fn (C σ S) (coe_fn f a) :=
  map_monomial f 0 a

@[simp] theorem map_X {σ : Type u_1} {R : Type u_2} {S : Type u_3} [semiring R] [semiring S] (f : R →+* S) (s : σ) : coe_fn (map σ f) (X s) = X s := sorry

protected instance algebra {σ : Type u_1} {R : Type u_2} {A : Type u_3} [comm_semiring R] [semiring A] [algebra R A] : algebra R (mv_power_series σ A) :=
  algebra.mk (ring_hom.comp (map σ (algebra_map R A)) (C σ R)) sorry sorry

/-- Auxiliary definition for the truncation function. -/
def trunc_fun {σ : Type u_1} {R : Type u_2} [comm_semiring R] (n : σ →₀ ℕ) (φ : mv_power_series σ R) : mv_polynomial σ R :=
  finsupp.mk
    (finset.filter (fun (m : σ →₀ ℕ) => coe_fn (coeff R m) φ ≠ 0)
      (finset.image prod.fst (finsupp.support (finsupp.antidiagonal n))))
    (fun (m : σ →₀ ℕ) => ite (m ≤ n) (coe_fn (coeff R m) φ) 0) sorry

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial -/
def trunc {σ : Type u_1} (R : Type u_2) [comm_semiring R] (n : σ →₀ ℕ) : mv_power_series σ R →+ mv_polynomial σ R :=
  add_monoid_hom.mk (trunc_fun n) sorry sorry

theorem coeff_trunc {σ : Type u_1} {R : Type u_2} [comm_semiring R] (n : σ →₀ ℕ) (m : σ →₀ ℕ) (φ : mv_power_series σ R) : mv_polynomial.coeff m (coe_fn (trunc R n) φ) = ite (m ≤ n) (coe_fn (coeff R m) φ) 0 :=
  rfl

@[simp] theorem trunc_one {σ : Type u_1} {R : Type u_2} [comm_semiring R] (n : σ →₀ ℕ) : coe_fn (trunc R n) 1 = 1 := sorry

@[simp] theorem trunc_C {σ : Type u_1} {R : Type u_2} [comm_semiring R] (n : σ →₀ ℕ) (a : R) : coe_fn (trunc R n) (coe_fn (C σ R) a) = coe_fn mv_polynomial.C a := sorry

theorem X_pow_dvd_iff {σ : Type u_1} {R : Type u_2} [comm_semiring R] {s : σ} {n : ℕ} {φ : mv_power_series σ R} : X s ^ n ∣ φ ↔ ∀ (m : σ →₀ ℕ), coe_fn m s < n → coe_fn (coeff R m) φ = 0 := sorry

theorem X_dvd_iff {σ : Type u_1} {R : Type u_2} [comm_semiring R] {s : σ} {φ : mv_power_series σ R} : X s ∣ φ ↔ ∀ (m : σ →₀ ℕ), coe_fn m s = 0 → coe_fn (coeff R m) φ = 0 := sorry

/-
The inverse of a multivariate formal power series is defined by
well-founded recursion on the coeffients of the inverse.
-/

/-- Auxiliary definition that unifies
 the totalised inverse formal power series `(_)⁻¹` and
 the inverse formal power series that depends on
 an inverse of the constant coefficient `inv_of_unit`.-/
protected def inv.aux {σ : Type u_1} {R : Type u_2} [ring R] (a : R) (φ : mv_power_series σ R) : mv_power_series σ R :=
  sorry

theorem coeff_inv_aux {σ : Type u_1} {R : Type u_2} [ring R] (n : σ →₀ ℕ) (a : R) (φ : mv_power_series σ R) : coe_fn (coeff R n) (inv.aux a φ) =
  ite (n = 0) a
    (-a *
      finset.sum (finsupp.support (finsupp.antidiagonal n))
        fun (x : (σ →₀ ℕ) × (σ →₀ ℕ)) =>
          ite (prod.snd x < n) (coe_fn (coeff R (prod.fst x)) φ * coe_fn (coeff R (prod.snd x)) (inv.aux a φ)) 0) := sorry

/-- A multivariate formal power series is invertible if the constant coefficient is invertible.-/
def inv_of_unit {σ : Type u_1} {R : Type u_2} [ring R] (φ : mv_power_series σ R) (u : units R) : mv_power_series σ R :=
  inv.aux (↑(u⁻¹)) φ

theorem coeff_inv_of_unit {σ : Type u_1} {R : Type u_2} [ring R] (n : σ →₀ ℕ) (φ : mv_power_series σ R) (u : units R) : coe_fn (coeff R n) (inv_of_unit φ u) =
  ite (n = 0) (↑(u⁻¹))
    (-↑(u⁻¹) *
      finset.sum (finsupp.support (finsupp.antidiagonal n))
        fun (x : (σ →₀ ℕ) × (σ →₀ ℕ)) =>
          ite (prod.snd x < n) (coe_fn (coeff R (prod.fst x)) φ * coe_fn (coeff R (prod.snd x)) (inv_of_unit φ u)) 0) :=
  coeff_inv_aux n (↑(u⁻¹)) φ

@[simp] theorem constant_coeff_inv_of_unit {σ : Type u_1} {R : Type u_2} [ring R] (φ : mv_power_series σ R) (u : units R) : coe_fn (constant_coeff σ R) (inv_of_unit φ u) = ↑(u⁻¹) := sorry

theorem mul_inv_of_unit {σ : Type u_1} {R : Type u_2} [ring R] (φ : mv_power_series σ R) (u : units R) (h : coe_fn (constant_coeff σ R) φ = ↑u) : φ * inv_of_unit φ u = 1 := sorry

/-- Multivariate formal power series over a local ring form a local ring. -/
protected instance is_local_ring {σ : Type u_1} {R : Type u_2} [comm_ring R] [local_ring R] : local_ring (mv_power_series σ R) := sorry

-- TODO(jmc): once adic topology lands, show that this is complete

-- Thanks to the linter for informing us that  this instance does

-- not actually need R and S to be local rings!

/-- The map `A[[X]] → B[[X]]` induced by a local ring hom `A → B` is local -/
protected instance map.is_local_ring_hom {σ : Type u_1} {R : Type u_2} {S : Type u_3} [comm_ring R] [comm_ring S] (f : R →+* S) [is_local_ring_hom f] : is_local_ring_hom (map σ f) :=
  is_local_ring_hom.mk
    fun (φ : mv_power_series σ R) (ᾰ : is_unit (coe_fn (map σ f) φ)) =>
      Exists.dcases_on ᾰ
        fun (ψ : units (mv_power_series σ S)) (h : ↑ψ = coe_fn (map σ f) φ) =>
          Exists.dcases_on
            (is_unit_of_map_unit f (coe_fn (constant_coeff σ R) φ)
              (eq.mp
                (Eq._oldrec (Eq.refl (is_unit (coe_fn (constant_coeff σ S) ↑ψ)))
                  (eq.mp
                    (Eq._oldrec
                      (Eq.refl (coe_fn (constant_coeff σ S) ↑ψ = coe_fn (constant_coeff σ S) (coe_fn (map σ f) φ)))
                      (constant_coeff_map f φ))
                    (congr_arg (⇑(constant_coeff σ S)) h)))
                (is_unit_constant_coeff (↑ψ) (is_unit_unit ψ))))
            fun (c : units R) (hc : ↑c = coe_fn (constant_coeff σ R) φ) =>
              is_unit_of_mul_eq_one φ (inv_of_unit φ c) (mul_inv_of_unit φ c (Eq.symm hc))

protected instance local_ring {σ : Type u_1} {R : Type u_2} [comm_ring R] [local_ring R] : local_ring (mv_power_series σ R) :=
  local_ring.mk local_ring.is_local

/-- The inverse `1/f` of a multivariable power series `f` over a field -/
protected def inv {σ : Type u_1} {k : Type u_3} [field k] (φ : mv_power_series σ k) : mv_power_series σ k :=
  sorry

protected instance has_inv {σ : Type u_1} {k : Type u_3} [field k] : has_inv (mv_power_series σ k) :=
  has_inv.mk mv_power_series.inv

theorem coeff_inv {σ : Type u_1} {k : Type u_3} [field k] (n : σ →₀ ℕ) (φ : mv_power_series σ k) : coe_fn (coeff k n) (φ⁻¹) =
  ite (n = 0) (coe_fn (constant_coeff σ k) φ⁻¹)
    (-(coe_fn (constant_coeff σ k) φ⁻¹) *
      finset.sum (finsupp.support (finsupp.antidiagonal n))
        fun (x : (σ →₀ ℕ) × (σ →₀ ℕ)) =>
          ite (prod.snd x < n) (coe_fn (coeff k (prod.fst x)) φ * coe_fn (coeff k (prod.snd x)) (φ⁻¹)) 0) :=
  coeff_inv_aux n (coe_fn (constant_coeff σ k) φ⁻¹) φ

@[simp] theorem constant_coeff_inv {σ : Type u_1} {k : Type u_3} [field k] (φ : mv_power_series σ k) : coe_fn (constant_coeff σ k) (φ⁻¹) = (coe_fn (constant_coeff σ k) φ⁻¹) := sorry

theorem inv_eq_zero {σ : Type u_1} {k : Type u_3} [field k] {φ : mv_power_series σ k} : φ⁻¹ = 0 ↔ coe_fn (constant_coeff σ k) φ = 0 := sorry

@[simp] theorem inv_of_unit_eq {σ : Type u_1} {k : Type u_3} [field k] (φ : mv_power_series σ k) (h : coe_fn (constant_coeff σ k) φ ≠ 0) : inv_of_unit φ (units.mk0 (coe_fn (constant_coeff σ k) φ) h) = (φ⁻¹) :=
  rfl

@[simp] theorem inv_of_unit_eq' {σ : Type u_1} {k : Type u_3} [field k] (φ : mv_power_series σ k) (u : units k) (h : coe_fn (constant_coeff σ k) φ = ↑u) : inv_of_unit φ u = (φ⁻¹) := sorry

@[simp] protected theorem mul_inv {σ : Type u_1} {k : Type u_3} [field k] (φ : mv_power_series σ k) (h : coe_fn (constant_coeff σ k) φ ≠ 0) : φ * (φ⁻¹) = 1 := sorry

@[simp] protected theorem inv_mul {σ : Type u_1} {k : Type u_3} [field k] (φ : mv_power_series σ k) (h : coe_fn (constant_coeff σ k) φ ≠ 0) : φ⁻¹ * φ = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (φ⁻¹ * φ = 1)) (mul_comm (φ⁻¹) φ)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (φ * (φ⁻¹) = 1)) (mv_power_series.mul_inv φ h))) (Eq.refl 1))

protected theorem eq_mul_inv_iff_mul_eq {σ : Type u_1} {k : Type u_3} [field k] {φ₁ : mv_power_series σ k} {φ₂ : mv_power_series σ k} {φ₃ : mv_power_series σ k} (h : coe_fn (constant_coeff σ k) φ₃ ≠ 0) : φ₁ = φ₂ * (φ₃⁻¹) ↔ φ₁ * φ₃ = φ₂ := sorry

protected theorem eq_inv_iff_mul_eq_one {σ : Type u_1} {k : Type u_3} [field k] {φ : mv_power_series σ k} {ψ : mv_power_series σ k} (h : coe_fn (constant_coeff σ k) ψ ≠ 0) : φ = (ψ⁻¹) ↔ φ * ψ = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (φ = (ψ⁻¹) ↔ φ * ψ = 1)) (Eq.symm (propext (mv_power_series.eq_mul_inv_iff_mul_eq h)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (φ = (ψ⁻¹) ↔ φ = 1 * (ψ⁻¹))) (one_mul (ψ⁻¹)))) (iff.refl (φ = (ψ⁻¹))))

protected theorem inv_eq_iff_mul_eq_one {σ : Type u_1} {k : Type u_3} [field k] {φ : mv_power_series σ k} {ψ : mv_power_series σ k} (h : coe_fn (constant_coeff σ k) ψ ≠ 0) : ψ⁻¹ = φ ↔ φ * ψ = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ψ⁻¹ = φ ↔ φ * ψ = 1)) (propext eq_comm)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (φ = (ψ⁻¹) ↔ φ * ψ = 1)) (propext (mv_power_series.eq_inv_iff_mul_eq_one h))))
      (iff.refl (φ * ψ = 1)))

end mv_power_series


namespace mv_polynomial


/-- The natural inclusion from multivariate polynomials into multivariate formal power series.-/
protected instance coe_to_mv_power_series {σ : Type u_1} {R : Type u_2} [comm_semiring R] : has_coe (mv_polynomial σ R) (mv_power_series σ R) :=
  has_coe.mk fun (φ : mv_polynomial σ R) (n : σ →₀ ℕ) => coeff n φ

@[simp] theorem coeff_coe {σ : Type u_1} {R : Type u_2} [comm_semiring R] (φ : mv_polynomial σ R) (n : σ →₀ ℕ) : coe_fn (mv_power_series.coeff R n) ↑φ = coeff n φ :=
  rfl

@[simp] theorem coe_monomial {σ : Type u_1} {R : Type u_2} [comm_semiring R] (n : σ →₀ ℕ) (a : R) : ↑(monomial n a) = coe_fn (mv_power_series.monomial R n) a := sorry

@[simp] theorem coe_zero {σ : Type u_1} {R : Type u_2} [comm_semiring R] : ↑0 = 0 :=
  rfl

@[simp] theorem coe_one {σ : Type u_1} {R : Type u_2} [comm_semiring R] : ↑1 = 1 :=
  coe_monomial 0 1

@[simp] theorem coe_add {σ : Type u_1} {R : Type u_2} [comm_semiring R] (φ : mv_polynomial σ R) (ψ : mv_polynomial σ R) : ↑(φ + ψ) = ↑φ + ↑ψ :=
  rfl

@[simp] theorem coe_mul {σ : Type u_1} {R : Type u_2} [comm_semiring R] (φ : mv_polynomial σ R) (ψ : mv_polynomial σ R) : ↑(φ * ψ) = ↑φ * ↑ψ := sorry

@[simp] theorem coe_C {σ : Type u_1} {R : Type u_2} [comm_semiring R] (a : R) : ↑(coe_fn C a) = coe_fn (mv_power_series.C σ R) a :=
  coe_monomial 0 a

@[simp] theorem coe_X {σ : Type u_1} {R : Type u_2} [comm_semiring R] (s : σ) : ↑(X s) = mv_power_series.X s :=
  coe_monomial (finsupp.single s 1) 1

/--
The coercion from multivariable polynomials to multivariable power series
as a ring homomorphism.
-/
-- TODO as an algebra homomorphism?

def coe_to_mv_power_series.ring_hom {σ : Type u_1} {R : Type u_2} [comm_semiring R] : mv_polynomial σ R →+* mv_power_series σ R :=
  ring_hom.mk coe coe_one coe_mul coe_zero coe_add

end mv_polynomial


/-- Formal power series over the coefficient ring `R`.-/
def power_series (R : Type u_1)  :=
  mv_power_series Unit R

namespace power_series


protected instance inhabited {R : Type u_1} [Inhabited R] : Inhabited (power_series R) :=
  mv_power_series.inhabited

protected instance add_monoid {R : Type u_1} [add_monoid R] : add_monoid (power_series R) :=
  mv_power_series.add_monoid

protected instance add_group {R : Type u_1} [add_group R] : add_group (power_series R) :=
  mv_power_series.add_group

protected instance add_comm_monoid {R : Type u_1} [add_comm_monoid R] : add_comm_monoid (power_series R) :=
  mv_power_series.add_comm_monoid

protected instance add_comm_group {R : Type u_1} [add_comm_group R] : add_comm_group (power_series R) :=
  mv_power_series.add_comm_group

protected instance semiring {R : Type u_1} [semiring R] : semiring (power_series R) :=
  mv_power_series.semiring

protected instance comm_semiring {R : Type u_1} [comm_semiring R] : comm_semiring (power_series R) :=
  mv_power_series.comm_semiring

protected instance ring {R : Type u_1} [ring R] : ring (power_series R) :=
  mv_power_series.ring

protected instance comm_ring {R : Type u_1} [comm_ring R] : comm_ring (power_series R) :=
  mv_power_series.comm_ring

protected instance nontrivial {R : Type u_1} [nontrivial R] : nontrivial (power_series R) :=
  mv_power_series.nontrivial

protected instance semimodule {R : Type u_1} {A : Type u_2} [semiring R] [add_comm_monoid A] [semimodule R A] : semimodule R (power_series A) :=
  mv_power_series.semimodule

protected instance is_scalar_tower {R : Type u_1} {A : Type u_2} {S : Type u_3} [semiring R] [semiring S] [add_comm_monoid A] [semimodule R A] [semimodule S A] [has_scalar R S] [is_scalar_tower R S A] : is_scalar_tower R S (power_series A) :=
  pi.is_scalar_tower

protected instance algebra {R : Type u_1} [comm_ring R] : algebra R (power_series R) :=
  mv_power_series.algebra

/-- The `n`th coefficient of a formal power series.-/
def coeff (R : Type u_1) [semiring R] (n : ℕ) : linear_map R (power_series R) R :=
  mv_power_series.coeff R (finsupp.single Unit.unit n)

/-- The `n`th monomial with coefficient `a` as formal power series.-/
def monomial (R : Type u_1) [semiring R] (n : ℕ) : linear_map R R (power_series R) :=
  mv_power_series.monomial R (finsupp.single Unit.unit n)

theorem coeff_def {R : Type u_1} [semiring R] {s : Unit →₀ ℕ} {n : ℕ} (h : coe_fn s Unit.unit = n) : coeff R n = mv_power_series.coeff R s := sorry

/-- Two formal power series are equal if all their coefficients are equal.-/
theorem ext {R : Type u_1} [semiring R] {φ : power_series R} {ψ : power_series R} (h : ∀ (n : ℕ), coe_fn (coeff R n) φ = coe_fn (coeff R n) ψ) : φ = ψ := sorry

/-- Two formal power series are equal if all their coefficients are equal.-/
theorem ext_iff {R : Type u_1} [semiring R] {φ : power_series R} {ψ : power_series R} : φ = ψ ↔ ∀ (n : ℕ), coe_fn (coeff R n) φ = coe_fn (coeff R n) ψ :=
  { mp := fun (h : φ = ψ) (n : ℕ) => congr_arg (⇑(coeff R n)) h, mpr := ext }

/-- Constructor for formal power series.-/
def mk {R : Type u_1} (f : ℕ → R) : power_series R :=
  fun (s : Unit →₀ ℕ) => f (coe_fn s Unit.unit)

@[simp] theorem coeff_mk {R : Type u_1} [semiring R] (n : ℕ) (f : ℕ → R) : coe_fn (coeff R n) (mk f) = f n :=
  congr_arg f finsupp.single_eq_same

theorem coeff_monomial {R : Type u_1} [semiring R] (m : ℕ) (n : ℕ) (a : R) : coe_fn (coeff R m) (coe_fn (monomial R n) a) = ite (m = n) a 0 := sorry

theorem monomial_eq_mk {R : Type u_1} [semiring R] (n : ℕ) (a : R) : coe_fn (monomial R n) a = mk fun (m : ℕ) => ite (m = n) a 0 := sorry

@[simp] theorem coeff_monomial_same {R : Type u_1} [semiring R] (n : ℕ) (a : R) : coe_fn (coeff R n) (coe_fn (monomial R n) a) = a :=
  mv_power_series.coeff_monomial_same (finsupp.single Unit.unit n) a

@[simp] theorem coeff_comp_monomial {R : Type u_1} [semiring R] (n : ℕ) : linear_map.comp (coeff R n) (monomial R n) = linear_map.id :=
  linear_map.ext (coeff_monomial_same n)

/--The constant coefficient of a formal power series. -/
def constant_coeff (R : Type u_1) [semiring R] : power_series R →+* R :=
  mv_power_series.constant_coeff Unit R

/-- The constant formal power series.-/
def C (R : Type u_1) [semiring R] : R →+* power_series R :=
  mv_power_series.C Unit R

/-- The variable of the formal power series ring.-/
def X {R : Type u_1} [semiring R] : power_series R :=
  mv_power_series.X Unit.unit

@[simp] theorem coeff_zero_eq_constant_coeff {R : Type u_1} [semiring R] : ⇑(coeff R 0) = ⇑(constant_coeff R) := sorry

theorem coeff_zero_eq_constant_coeff_apply {R : Type u_1} [semiring R] (φ : power_series R) : coe_fn (coeff R 0) φ = coe_fn (constant_coeff R) φ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (coeff R 0) φ = coe_fn (constant_coeff R) φ)) coeff_zero_eq_constant_coeff))
    (Eq.refl (coe_fn (constant_coeff R) φ))

@[simp] theorem monomial_zero_eq_C {R : Type u_1} [semiring R] : ⇑(monomial R 0) = ⇑(C R) := sorry

theorem monomial_zero_eq_C_apply {R : Type u_1} [semiring R] (a : R) : coe_fn (monomial R 0) a = coe_fn (C R) a := sorry

theorem coeff_C {R : Type u_1} [semiring R] (n : ℕ) (a : R) : coe_fn (coeff R n) (coe_fn (C R) a) = ite (n = 0) a 0 := sorry

theorem coeff_zero_C {R : Type u_1} [semiring R] (a : R) : coe_fn (coeff R 0) (coe_fn (C R) a) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (coeff R 0) (coe_fn (C R) a) = a)) (Eq.symm (monomial_zero_eq_C_apply a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (coeff R 0) (coe_fn (monomial R 0) a) = a)) (coeff_monomial_same 0 a)))
      (Eq.refl a))

theorem X_eq {R : Type u_1} [semiring R] : X = coe_fn (monomial R 1) 1 :=
  rfl

theorem coeff_X {R : Type u_1} [semiring R] (n : ℕ) : coe_fn (coeff R n) X = ite (n = 1) 1 0 := sorry

theorem coeff_zero_X {R : Type u_1} [semiring R] : coe_fn (coeff R 0) X = 0 := sorry

@[simp] theorem coeff_one_X {R : Type u_1} [semiring R] : coe_fn (coeff R 1) X = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (coeff R 1) X = 1)) (coeff_X 1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ite (1 = 1) 1 0 = 1)) (if_pos rfl))) (Eq.refl 1))

theorem X_pow_eq {R : Type u_1} [semiring R] (n : ℕ) : X ^ n = coe_fn (monomial R n) 1 :=
  mv_power_series.X_pow_eq Unit.unit n

theorem coeff_X_pow {R : Type u_1} [semiring R] (m : ℕ) (n : ℕ) : coe_fn (coeff R m) (X ^ n) = ite (m = n) 1 0 := sorry

@[simp] theorem coeff_X_pow_self {R : Type u_1} [semiring R] (n : ℕ) : coe_fn (coeff R n) (X ^ n) = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (coeff R n) (X ^ n) = 1)) (coeff_X_pow n n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ite (n = n) 1 0 = 1)) (if_pos rfl))) (Eq.refl 1))

@[simp] theorem coeff_one {R : Type u_1} [semiring R] (n : ℕ) : coe_fn (coeff R n) 1 = ite (n = 0) 1 0 := sorry

theorem coeff_zero_one {R : Type u_1} [semiring R] : coe_fn (coeff R 0) 1 = 1 :=
  coeff_zero_C 1

theorem coeff_mul {R : Type u_1} [semiring R] (n : ℕ) (φ : power_series R) (ψ : power_series R) : coe_fn (coeff R n) (φ * ψ) =
  finset.sum (finset.nat.antidiagonal n)
    fun (p : ℕ × ℕ) => coe_fn (coeff R (prod.fst p)) φ * coe_fn (coeff R (prod.snd p)) ψ := sorry

@[simp] theorem coeff_mul_C {R : Type u_1} [semiring R] (n : ℕ) (φ : power_series R) (a : R) : coe_fn (coeff R n) (φ * coe_fn (C R) a) = coe_fn (coeff R n) φ * a :=
  mv_power_series.coeff_mul_C (finsupp.single Unit.unit n) φ a

@[simp] theorem coeff_C_mul {R : Type u_1} [semiring R] (n : ℕ) (φ : power_series R) (a : R) : coe_fn (coeff R n) (coe_fn (C R) a * φ) = a * coe_fn (coeff R n) φ :=
  mv_power_series.coeff_C_mul (finsupp.single Unit.unit n) φ a

@[simp] theorem coeff_smul {R : Type u_1} [semiring R] (n : ℕ) (φ : power_series R) (a : R) : coe_fn (coeff R n) (a • φ) = a * coe_fn (coeff R n) φ :=
  rfl

@[simp] theorem coeff_succ_mul_X {R : Type u_1} [semiring R] (n : ℕ) (φ : power_series R) : coe_fn (coeff R (n + 1)) (φ * X) = coe_fn (coeff R n) φ := sorry

@[simp] theorem constant_coeff_C {R : Type u_1} [semiring R] (a : R) : coe_fn (constant_coeff R) (coe_fn (C R) a) = a :=
  rfl

@[simp] theorem constant_coeff_comp_C {R : Type u_1} [semiring R] : ring_hom.comp (constant_coeff R) (C R) = ring_hom.id R :=
  rfl

@[simp] theorem constant_coeff_zero {R : Type u_1} [semiring R] : coe_fn (constant_coeff R) 0 = 0 :=
  rfl

@[simp] theorem constant_coeff_one {R : Type u_1} [semiring R] : coe_fn (constant_coeff R) 1 = 1 :=
  rfl

@[simp] theorem constant_coeff_X {R : Type u_1} [semiring R] : coe_fn (constant_coeff R) X = 0 :=
  mv_power_series.coeff_zero_X Unit.unit

theorem coeff_zero_mul_X {R : Type u_1} [semiring R] (φ : power_series R) : coe_fn (coeff R 0) (φ * X) = 0 := sorry

/-- If a formal power series is invertible, then so is its constant coefficient.-/
theorem is_unit_constant_coeff {R : Type u_1} [semiring R] (φ : power_series R) (h : is_unit φ) : is_unit (coe_fn (constant_coeff R) φ) :=
  mv_power_series.is_unit_constant_coeff φ h

/-- The map between formal power series induced by a map on the coefficients.-/
def map {R : Type u_1} [semiring R] {S : Type u_2} [semiring S] (f : R →+* S) : power_series R →+* power_series S :=
  mv_power_series.map Unit f

@[simp] theorem map_id {R : Type u_1} [semiring R] : ⇑(map (ring_hom.id R)) = id :=
  rfl

theorem map_comp {R : Type u_1} [semiring R] {S : Type u_2} {T : Type u_3} [semiring S] [semiring T] (f : R →+* S) (g : S →+* T) : map (ring_hom.comp g f) = ring_hom.comp (map g) (map f) :=
  rfl

@[simp] theorem coeff_map {R : Type u_1} [semiring R] {S : Type u_2} [semiring S] (f : R →+* S) (n : ℕ) (φ : power_series R) : coe_fn (coeff S n) (coe_fn (map f) φ) = coe_fn f (coe_fn (coeff R n) φ) :=
  rfl

theorem X_pow_dvd_iff {R : Type u_1} [comm_semiring R] {n : ℕ} {φ : power_series R} : X ^ n ∣ φ ↔ ∀ (m : ℕ), m < n → coe_fn (coeff R m) φ = 0 := sorry

theorem X_dvd_iff {R : Type u_1} [comm_semiring R] {φ : power_series R} : X ∣ φ ↔ coe_fn (constant_coeff R) φ = 0 := sorry

/-- The `n`th truncation of a formal power series to a polynomial -/
def trunc {R : Type u_1} [comm_semiring R] (n : ℕ) (φ : power_series R) : polynomial R :=
  finsupp.mk (finset.filter (fun (m : ℕ) => coe_fn (coeff R m) φ ≠ 0) (finset.image prod.fst (finset.nat.antidiagonal n)))
    (fun (m : ℕ) => ite (m ≤ n) (coe_fn (coeff R m) φ) 0) sorry

theorem coeff_trunc {R : Type u_1} [comm_semiring R] (m : ℕ) (n : ℕ) (φ : power_series R) : polynomial.coeff (trunc n φ) m = ite (m ≤ n) (coe_fn (coeff R m) φ) 0 :=
  rfl

@[simp] theorem trunc_zero {R : Type u_1} [comm_semiring R] (n : ℕ) : trunc n 0 = 0 := sorry

@[simp] theorem trunc_one {R : Type u_1} [comm_semiring R] (n : ℕ) : trunc n 1 = 1 := sorry

@[simp] theorem trunc_C {R : Type u_1} [comm_semiring R] (n : ℕ) (a : R) : trunc n (coe_fn (C R) a) = coe_fn polynomial.C a := sorry

@[simp] theorem trunc_add {R : Type u_1} [comm_semiring R] (n : ℕ) (φ : power_series R) (ψ : power_series R) : trunc n (φ + ψ) = trunc n φ + trunc n ψ := sorry

/-- Auxiliary function used for computing inverse of a power series -/
protected def inv.aux {R : Type u_1} [ring R] : R → power_series R → power_series R :=
  mv_power_series.inv.aux

theorem coeff_inv_aux {R : Type u_1} [ring R] (n : ℕ) (a : R) (φ : power_series R) : coe_fn (coeff R n) (inv.aux a φ) =
  ite (n = 0) a
    (-a *
      finset.sum (finset.nat.antidiagonal n)
        fun (x : ℕ × ℕ) =>
          ite (prod.snd x < n) (coe_fn (coeff R (prod.fst x)) φ * coe_fn (coeff R (prod.snd x)) (inv.aux a φ)) 0) := sorry

/-- A formal power series is invertible if the constant coefficient is invertible.-/
def inv_of_unit {R : Type u_1} [ring R] (φ : power_series R) (u : units R) : power_series R :=
  mv_power_series.inv_of_unit φ u

theorem coeff_inv_of_unit {R : Type u_1} [ring R] (n : ℕ) (φ : power_series R) (u : units R) : coe_fn (coeff R n) (inv_of_unit φ u) =
  ite (n = 0) (↑(u⁻¹))
    (-↑(u⁻¹) *
      finset.sum (finset.nat.antidiagonal n)
        fun (x : ℕ × ℕ) =>
          ite (prod.snd x < n) (coe_fn (coeff R (prod.fst x)) φ * coe_fn (coeff R (prod.snd x)) (inv_of_unit φ u)) 0) :=
  coeff_inv_aux n (↑(u⁻¹)) φ

@[simp] theorem constant_coeff_inv_of_unit {R : Type u_1} [ring R] (φ : power_series R) (u : units R) : coe_fn (constant_coeff R) (inv_of_unit φ u) = ↑(u⁻¹) := sorry

theorem mul_inv_of_unit {R : Type u_1} [ring R] (φ : power_series R) (u : units R) (h : coe_fn (constant_coeff R) φ = ↑u) : φ * inv_of_unit φ u = 1 :=
  mv_power_series.mul_inv_of_unit φ u h

theorem eq_zero_or_eq_zero_of_mul_eq_zero {R : Type u_1} [integral_domain R] (φ : power_series R) (ψ : power_series R) (h : φ * ψ = 0) : φ = 0 ∨ ψ = 0 := sorry

protected instance integral_domain {R : Type u_1} [integral_domain R] : integral_domain (power_series R) :=
  integral_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul
    sorry comm_ring.one sorry sorry sorry sorry sorry sorry eq_zero_or_eq_zero_of_mul_eq_zero

/-- The ideal spanned by the variable in the power series ring
 over an integral domain is a prime ideal.-/
theorem span_X_is_prime {R : Type u_1} [integral_domain R] : ideal.is_prime (ideal.span (singleton X)) := sorry

/-- The variable of the power series ring over an integral domain is prime.-/
theorem X_prime {R : Type u_1} [integral_domain R] : prime X := sorry

protected instance map.is_local_ring_hom {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] (f : R →+* S) [is_local_ring_hom f] : is_local_ring_hom (map f) :=
  mv_power_series.map.is_local_ring_hom f

protected instance local_ring {R : Type u_1} [comm_ring R] [local_ring R] : local_ring (power_series R) :=
  mv_power_series.local_ring

/-- The inverse 1/f of a power series f defined over a field -/
protected def inv {k : Type u_2} [field k] : power_series k → power_series k :=
  mv_power_series.inv

protected instance has_inv {k : Type u_2} [field k] : has_inv (power_series k) :=
  has_inv.mk power_series.inv

theorem inv_eq_inv_aux {k : Type u_2} [field k] (φ : power_series k) : φ⁻¹ = inv.aux (coe_fn (constant_coeff k) φ⁻¹) φ :=
  rfl

theorem coeff_inv {k : Type u_2} [field k] (n : ℕ) (φ : power_series k) : coe_fn (coeff k n) (φ⁻¹) =
  ite (n = 0) (coe_fn (constant_coeff k) φ⁻¹)
    (-(coe_fn (constant_coeff k) φ⁻¹) *
      finset.sum (finset.nat.antidiagonal n)
        fun (x : ℕ × ℕ) =>
          ite (prod.snd x < n) (coe_fn (coeff k (prod.fst x)) φ * coe_fn (coeff k (prod.snd x)) (φ⁻¹)) 0) := sorry

@[simp] theorem constant_coeff_inv {k : Type u_2} [field k] (φ : power_series k) : coe_fn (constant_coeff k) (φ⁻¹) = (coe_fn (constant_coeff k) φ⁻¹) :=
  mv_power_series.constant_coeff_inv φ

theorem inv_eq_zero {k : Type u_2} [field k] {φ : power_series k} : φ⁻¹ = 0 ↔ coe_fn (constant_coeff k) φ = 0 :=
  mv_power_series.inv_eq_zero

@[simp] theorem inv_of_unit_eq {k : Type u_2} [field k] (φ : power_series k) (h : coe_fn (constant_coeff k) φ ≠ 0) : inv_of_unit φ (units.mk0 (coe_fn (constant_coeff k) φ) h) = (φ⁻¹) :=
  mv_power_series.inv_of_unit_eq φ h

@[simp] theorem inv_of_unit_eq' {k : Type u_2} [field k] (φ : power_series k) (u : units k) (h : coe_fn (constant_coeff k) φ = ↑u) : inv_of_unit φ u = (φ⁻¹) :=
  mv_power_series.inv_of_unit_eq' φ u h

@[simp] protected theorem mul_inv {k : Type u_2} [field k] (φ : power_series k) (h : coe_fn (constant_coeff k) φ ≠ 0) : φ * (φ⁻¹) = 1 :=
  mv_power_series.mul_inv φ h

@[simp] protected theorem inv_mul {k : Type u_2} [field k] (φ : power_series k) (h : coe_fn (constant_coeff k) φ ≠ 0) : φ⁻¹ * φ = 1 :=
  mv_power_series.inv_mul φ h

theorem eq_mul_inv_iff_mul_eq {k : Type u_2} [field k] {φ₁ : power_series k} {φ₂ : power_series k} {φ₃ : power_series k} (h : coe_fn (constant_coeff k) φ₃ ≠ 0) : φ₁ = φ₂ * (φ₃⁻¹) ↔ φ₁ * φ₃ = φ₂ :=
  mv_power_series.eq_mul_inv_iff_mul_eq h

theorem eq_inv_iff_mul_eq_one {k : Type u_2} [field k] {φ : power_series k} {ψ : power_series k} (h : coe_fn (constant_coeff k) ψ ≠ 0) : φ = (ψ⁻¹) ↔ φ * ψ = 1 :=
  mv_power_series.eq_inv_iff_mul_eq_one h

theorem inv_eq_iff_mul_eq_one {k : Type u_2} [field k] {φ : power_series k} {ψ : power_series k} (h : coe_fn (constant_coeff k) ψ ≠ 0) : ψ⁻¹ = φ ↔ φ * ψ = 1 :=
  mv_power_series.inv_eq_iff_mul_eq_one h

end power_series


namespace power_series


/-- The order of a formal power series `φ` is the greatest `n : enat`
such that `X^n` divides `φ`. The order is `⊤` if and only if `φ = 0`. -/
def order {R : Type u_1} [comm_semiring R] (φ : power_series R) : enat :=
  multiplicity X φ

theorem order_finite_of_coeff_ne_zero {R : Type u_1} [comm_semiring R] (φ : power_series R) (h : ∃ (n : ℕ), coe_fn (coeff R n) φ ≠ 0) : roption.dom (order φ) := sorry

/-- If the order of a formal power series is finite,
then the coefficient indexed by the order is nonzero.-/
theorem coeff_order {R : Type u_1} [comm_semiring R] (φ : power_series R) (h : roption.dom (order φ)) : coe_fn (coeff R (roption.get (order φ) h)) φ ≠ 0 := sorry

/-- If the `n`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `n`.-/
theorem order_le {R : Type u_1} [comm_semiring R] (φ : power_series R) (n : ℕ) (h : coe_fn (coeff R n) φ ≠ 0) : order φ ≤ ↑n := sorry

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
theorem coeff_of_lt_order {R : Type u_1} [comm_semiring R] (φ : power_series R) (n : ℕ) (h : ↑n < order φ) : coe_fn (coeff R n) φ = 0 := sorry

/-- The order of the `0` power series is infinite.-/
@[simp] theorem order_zero {R : Type u_1} [comm_semiring R] : order 0 = ⊤ :=
  multiplicity.zero X

/-- The `0` power series is the unique power series with infinite order.-/
@[simp] theorem order_eq_top {R : Type u_1} [comm_semiring R] {φ : power_series R} : order φ = ⊤ ↔ φ = 0 := sorry

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
theorem nat_le_order {R : Type u_1} [comm_semiring R] (φ : power_series R) (n : ℕ) (h : ∀ (i : ℕ), i < n → coe_fn (coeff R i) φ = 0) : ↑n ≤ order φ := sorry

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
theorem le_order {R : Type u_1} [comm_semiring R] (φ : power_series R) (n : enat) (h : ∀ (i : ℕ), ↑i < n → coe_fn (coeff R i) φ = 0) : n ≤ order φ := sorry

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
theorem order_eq_nat {R : Type u_1} [comm_semiring R] {φ : power_series R} {n : ℕ} : order φ = ↑n ↔ coe_fn (coeff R n) φ ≠ 0 ∧ ∀ (i : ℕ), i < n → coe_fn (coeff R i) φ = 0 := sorry

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
theorem order_eq {R : Type u_1} [comm_semiring R] {φ : power_series R} {n : enat} : order φ = n ↔ (∀ (i : ℕ), ↑i = n → coe_fn (coeff R i) φ ≠ 0) ∧ ∀ (i : ℕ), ↑i < n → coe_fn (coeff R i) φ = 0 := sorry

/-- The order of the sum of two formal power series
 is at least the minimum of their orders.-/
theorem le_order_add {R : Type u_1} [comm_semiring R] (φ : power_series R) (ψ : power_series R) : min (order φ) (order ψ) ≤ order (φ + ψ) :=
  multiplicity.min_le_multiplicity_add

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
theorem order_add_of_order_eq {R : Type u_1} [comm_semiring R] (φ : power_series R) (ψ : power_series R) (h : order φ ≠ order ψ) : order (φ + ψ) = order φ ⊓ order ψ := sorry

/-- The order of the product of two formal power series
 is at least the sum of their orders.-/
theorem order_mul_ge {R : Type u_1} [comm_semiring R] (φ : power_series R) (ψ : power_series R) : order φ + order ψ ≤ order (φ * ψ) := sorry

/-- The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise.-/
theorem order_monomial {R : Type u_1} [comm_semiring R] (n : ℕ) (a : R) : order (coe_fn (monomial R n) a) = ite (a = 0) ⊤ ↑n := sorry

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
theorem order_monomial_of_ne_zero {R : Type u_1} [comm_semiring R] (n : ℕ) (a : R) (h : a ≠ 0) : order (coe_fn (monomial R n) a) = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (order (coe_fn (monomial R n) a) = ↑n)) (order_monomial n a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ite (a = 0) ⊤ ↑n = ↑n)) (if_neg h))) (Eq.refl ↑n))

/-- The order of the formal power series `1` is `0`.-/
@[simp] theorem order_one {R : Type u_1} [comm_semiring R] [nontrivial R] : order 1 = 0 := sorry

/-- The order of the formal power series `X` is `1`.-/
@[simp] theorem order_X {R : Type u_1} [comm_semiring R] [nontrivial R] : order X = 1 :=
  order_monomial_of_ne_zero 1 1 one_ne_zero

/-- The order of the formal power series `X^n` is `n`.-/
@[simp] theorem order_X_pow {R : Type u_1} [comm_semiring R] [nontrivial R] (n : ℕ) : order (X ^ n) = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (order (X ^ n) = ↑n)) (X_pow_eq n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (order (coe_fn (monomial R n) 1) = ↑n)) (order_monomial_of_ne_zero n 1 one_ne_zero)))
      (Eq.refl ↑n))

/-- The order of the product of two formal power series over an integral domain
 is the sum of their orders.-/
theorem order_mul {R : Type u_1} [integral_domain R] (φ : power_series R) (ψ : power_series R) : order (φ * ψ) = order φ + order ψ :=
  multiplicity.mul X_prime

end power_series


namespace polynomial


/-- The natural inclusion from polynomials into formal power series.-/
protected instance coe_to_power_series {R : Type u_2} [comm_semiring R] : has_coe (polynomial R) (power_series R) :=
  has_coe.mk fun (φ : polynomial R) => power_series.mk fun (n : ℕ) => coeff φ n

@[simp] theorem coeff_coe {R : Type u_2} [comm_semiring R] (φ : polynomial R) (n : ℕ) : coe_fn (power_series.coeff R n) ↑φ = coeff φ n :=
  congr_arg (coeff φ) finsupp.single_eq_same

@[simp] theorem coe_monomial {R : Type u_2} [comm_semiring R] (n : ℕ) (a : R) : ↑(coe_fn (monomial n) a) = coe_fn (power_series.monomial R n) a := sorry

@[simp] theorem coe_zero {R : Type u_2} [comm_semiring R] : ↑0 = 0 :=
  rfl

@[simp] theorem coe_one {R : Type u_2} [comm_semiring R] : ↑1 = 1 := sorry

@[simp] theorem coe_add {R : Type u_2} [comm_semiring R] (φ : polynomial R) (ψ : polynomial R) : ↑(φ + ψ) = ↑φ + ↑ψ :=
  rfl

@[simp] theorem coe_mul {R : Type u_2} [comm_semiring R] (φ : polynomial R) (ψ : polynomial R) : ↑(φ * ψ) = ↑φ * ↑ψ := sorry

@[simp] theorem coe_C {R : Type u_2} [comm_semiring R] (a : R) : ↑(coe_fn C a) = coe_fn (power_series.C R) a := sorry

@[simp] theorem coe_X {R : Type u_2} [comm_semiring R] : ↑X = power_series.X :=
  coe_monomial 1 1

/--
The coercion from polynomials to power series
as a ring homomorphism.
-/
-- TODO as an algebra homomorphism?

def coe_to_power_series.ring_hom {R : Type u_2} [comm_semiring R] : polynomial R →+* power_series R :=
  ring_hom.mk coe coe_one coe_mul coe_zero coe_add

