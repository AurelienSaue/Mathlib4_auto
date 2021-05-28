/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.ring_exp
import Mathlib.tactic.chain
import Mathlib.algebra.monoid_algebra
import Mathlib.data.finset.sort
import PostPort

universes u_1 u 

namespace Mathlib

/-!
# Theory of univariate polynomials

Polynomials are represented as `add_monoid_algebra R ℕ`, where `R` is a commutative semiring.
In this file, we define `polynomial`, provide basic instances, and prove an `ext` lemma.
-/

/-- `polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
def polynomial (R : Type u_1) [semiring R]  :=
  add_monoid_algebra R ℕ

namespace polynomial


protected instance inhabited {R : Type u} [semiring R] : Inhabited (polynomial R) :=
  add_monoid_algebra.inhabited R ℕ

protected instance semiring {R : Type u} [semiring R] : semiring (polynomial R) :=
  add_monoid_algebra.semiring

protected instance semimodule {R : Type u} [semiring R] {S : Type u_1} [semiring S] [semimodule S R] : semimodule S (polynomial R) :=
  add_monoid_algebra.semimodule

protected instance unique {R : Type u} [semiring R] [subsingleton R] : unique (polynomial R) :=
  add_monoid_algebra.unique

@[simp] theorem support_zero {R : Type u} [semiring R] : finsupp.support 0 = ∅ :=
  rfl

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial {R : Type u} [semiring R] (n : ℕ) : linear_map R R (polynomial R) :=
  finsupp.lsingle n

theorem monomial_zero_right {R : Type u} [semiring R] (n : ℕ) : coe_fn (monomial n) 0 = 0 :=
  finsupp.single_zero

theorem monomial_def {R : Type u} [semiring R] (n : ℕ) (a : R) : coe_fn (monomial n) a = finsupp.single n a :=
  rfl

theorem monomial_add {R : Type u} [semiring R] (n : ℕ) (r : R) (s : R) : coe_fn (monomial n) (r + s) = coe_fn (monomial n) r + coe_fn (monomial n) s :=
  finsupp.single_add

theorem monomial_mul_monomial {R : Type u} [semiring R] (n : ℕ) (m : ℕ) (r : R) (s : R) : coe_fn (monomial n) r * coe_fn (monomial m) s = coe_fn (monomial (n + m)) (r * s) :=
  add_monoid_algebra.single_mul_single

theorem smul_monomial {R : Type u} [semiring R] {S : Type u_1} [semiring S] [semimodule S R] (a : S) (n : ℕ) (b : R) : a • coe_fn (monomial n) b = coe_fn (monomial n) (a • b) :=
  finsupp.smul_single a n b

/-- `X` is the polynomial variable (aka indeterminant). -/
def X {R : Type u} [semiring R] : polynomial R :=
  coe_fn (monomial 1) 1

/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
theorem X_mul {R : Type u} [semiring R] {p : polynomial R} : X * p = p * X := sorry

theorem X_pow_mul {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} : X ^ n * p = p * X ^ n := sorry

theorem X_pow_mul_assoc {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} {n : ℕ} : p * X ^ n * q = p * q * X ^ n := sorry

theorem commute_X {R : Type u} [semiring R] (p : polynomial R) : commute X p :=
  X_mul

/-- coeff p n is the coefficient of X^n in p -/
def coeff {R : Type u} [semiring R] (p : polynomial R) : ℕ → R :=
  ⇑p

@[simp] theorem coeff_mk {R : Type u} [semiring R] (s : finset ℕ) (f : ℕ → R) (h : ∀ (a : ℕ), a ∈ s ↔ f a ≠ 0) : coeff (finsupp.mk s f h) = f :=
  rfl

theorem coeff_monomial {R : Type u} {a : R} {m : ℕ} {n : ℕ} [semiring R] : coeff (coe_fn (monomial n) a) m = ite (n = m) a 0 := sorry

@[simp] theorem coeff_zero {R : Type u} [semiring R] (n : ℕ) : coeff 0 n = 0 :=
  rfl

@[simp] theorem coeff_one_zero {R : Type u} [semiring R] : coeff 1 0 = 1 :=
  coeff_monomial

@[simp] theorem coeff_X_one {R : Type u} [semiring R] : coeff X 1 = 1 :=
  coeff_monomial

@[simp] theorem coeff_X_zero {R : Type u} [semiring R] : coeff X 0 = 0 :=
  coeff_monomial

theorem coeff_X {R : Type u} {n : ℕ} [semiring R] : coeff X n = ite (1 = n) 1 0 :=
  coeff_monomial

theorem coeff_X_of_ne_one {R : Type u} [semiring R] {n : ℕ} (hn : n ≠ 1) : coeff X n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coeff X n = 0)) coeff_X))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ite (1 = n) 1 0 = 0)) (if_neg (ne.symm hn)))) (Eq.refl 0))

theorem ext_iff {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} : p = q ↔ ∀ (n : ℕ), coeff p n = coeff q n :=
  finsupp.ext_iff

theorem ext {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} : (∀ (n : ℕ), coeff p n = coeff q n) → p = q :=
  finsupp.ext

theorem add_hom_ext' {R : Type u} [semiring R] {M : Type u_1} [add_monoid M] {f : polynomial R →+ M} {g : polynomial R →+ M} (h : ∀ (n : ℕ),
  add_monoid_hom.comp f (linear_map.to_add_monoid_hom (monomial n)) =
    add_monoid_hom.comp g (linear_map.to_add_monoid_hom (monomial n))) : f = g :=
  finsupp.add_hom_ext' h

theorem add_hom_ext {R : Type u} [semiring R] {M : Type u_1} [add_monoid M] {f : polynomial R →+ M} {g : polynomial R →+ M} (h : ∀ (n : ℕ) (a : R), coe_fn f (coe_fn (monomial n) a) = coe_fn g (coe_fn (monomial n) a)) : f = g :=
  finsupp.add_hom_ext h

theorem lhom_ext' {R : Type u} [semiring R] {M : Type u_1} [add_comm_monoid M] [semimodule R M] {f : linear_map R (polynomial R) M} {g : linear_map R (polynomial R) M} (h : ∀ (n : ℕ), linear_map.comp f (monomial n) = linear_map.comp g (monomial n)) : f = g :=
  finsupp.lhom_ext' h

-- this has the same content as the subsingleton

theorem eq_zero_of_eq_zero {R : Type u} [semiring R] (h : 0 = 1) (p : polynomial R) : p = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (p = 0)) (Eq.symm (one_smul R p))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 • p = 0)) (Eq.symm h)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 • p = 0)) (zero_smul R p))) (Eq.refl 0)))

theorem support_monomial {R : Type u} [semiring R] (n : ℕ) (a : R) (H : a ≠ 0) : finsupp.support (coe_fn (monomial n) a) = singleton n :=
  finsupp.support_single_ne_zero H

theorem support_monomial' {R : Type u} [semiring R] (n : ℕ) (a : R) : finsupp.support (coe_fn (monomial n) a) ⊆ singleton n :=
  finsupp.support_single_subset

theorem X_pow_eq_monomial {R : Type u} [semiring R] (n : ℕ) : X ^ n = coe_fn (monomial n) 1 := sorry

theorem support_X_pow {R : Type u} [semiring R] (H : ¬1 = 0) (n : ℕ) : finsupp.support (X ^ n) = singleton n := sorry

theorem support_X_empty {R : Type u} [semiring R] (H : 1 = 0) : finsupp.support X = ∅ := sorry

theorem support_X {R : Type u} [semiring R] (H : ¬1 = 0) : finsupp.support X = singleton 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finsupp.support X = singleton 1)) (Eq.symm (pow_one X))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (finsupp.support (X ^ 1) = singleton 1)) (support_X_pow H 1)))
      (Eq.refl (singleton 1)))

protected instance comm_semiring {R : Type u} [comm_semiring R] : comm_semiring (polynomial R) :=
  add_monoid_algebra.comm_semiring

protected instance ring {R : Type u} [ring R] : ring (polynomial R) :=
  add_monoid_algebra.ring

@[simp] theorem coeff_neg {R : Type u} [ring R] (p : polynomial R) (n : ℕ) : coeff (-p) n = -coeff p n :=
  rfl

@[simp] theorem coeff_sub {R : Type u} [ring R] (p : polynomial R) (q : polynomial R) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n :=
  rfl

protected instance comm_ring {R : Type u} [comm_ring R] : comm_ring (polynomial R) :=
  add_monoid_algebra.comm_ring

protected instance nontrivial {R : Type u} [semiring R] [nontrivial R] : nontrivial (polynomial R) :=
  add_monoid_algebra.nontrivial

theorem X_ne_zero {R : Type u} [semiring R] [nontrivial R] : X ≠ 0 := sorry

protected instance has_repr {R : Type u} [semiring R] [has_repr R] : has_repr (polynomial R) := sorry

