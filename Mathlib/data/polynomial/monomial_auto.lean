/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.polynomial.basic
import PostPort

universes u u_1 

namespace Mathlib

/-!
# Univariate monomials

Preparatory lemmas for degree_basic.
-/

namespace polynomial


/--
`C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C {R : Type u} [semiring R] : R →+* polynomial R :=
  add_monoid_algebra.single_zero_ring_hom

@[simp] theorem monomial_zero_left {R : Type u} [semiring R] (a : R) : coe_fn (monomial 0) a = coe_fn C a :=
  rfl

theorem C_0 {R : Type u} [semiring R] : coe_fn C 0 = 0 :=
  finsupp.single_zero

theorem C_1 {R : Type u} [semiring R] : coe_fn C 1 = 1 :=
  rfl

theorem C_mul {R : Type u} {a : R} {b : R} [semiring R] : coe_fn C (a * b) = coe_fn C a * coe_fn C b :=
  ring_hom.map_mul C a b

theorem C_add {R : Type u} {a : R} {b : R} [semiring R] : coe_fn C (a + b) = coe_fn C a + coe_fn C b :=
  ring_hom.map_add C a b

@[simp] theorem C_bit0 {R : Type u} {a : R} [semiring R] : coe_fn C (bit0 a) = bit0 (coe_fn C a) :=
  C_add

@[simp] theorem C_bit1 {R : Type u} {a : R} [semiring R] : coe_fn C (bit1 a) = bit1 (coe_fn C a) := sorry

theorem C_pow {R : Type u} {a : R} {n : ℕ} [semiring R] : coe_fn C (a ^ n) = coe_fn C a ^ n :=
  ring_hom.map_pow C a n

@[simp] theorem C_eq_nat_cast {R : Type u} [semiring R] (n : ℕ) : coe_fn C ↑n = ↑n :=
  ring_hom.map_nat_cast C n

@[simp] theorem sum_C_index {R : Type u} [semiring R] {a : R} {β : Type u_1} [add_comm_monoid β] {f : ℕ → R → β} (h : f 0 0 = 0) : finsupp.sum (coe_fn C a) f = f 0 a :=
  finsupp.sum_single_index h

theorem coeff_C {R : Type u} {a : R} {n : ℕ} [semiring R] : coeff (coe_fn C a) n = ite (n = 0) a 0 := sorry

@[simp] theorem coeff_C_zero {R : Type u} {a : R} [semiring R] : coeff (coe_fn C a) 0 = a :=
  coeff_monomial

theorem nontrivial.of_polynomial_ne {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : p ≠ q) : nontrivial R := sorry

theorem single_eq_C_mul_X {R : Type u} {a : R} [semiring R] {n : ℕ} : coe_fn (monomial n) a = coe_fn C a * X ^ n := sorry

@[simp] theorem C_inj {R : Type u} {a : R} {b : R} [semiring R] : coe_fn C a = coe_fn C b ↔ a = b :=
  { mp := fun (h : coe_fn C a = coe_fn C b) => Eq.trans (Eq.symm coeff_C_zero) (Eq.symm h ▸ coeff_C_zero),
    mpr := congr_arg ⇑C }

@[simp] theorem C_eq_zero {R : Type u} {a : R} [semiring R] : coe_fn C a = 0 ↔ a = 0 :=
  iff.trans
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn C a = 0 ↔ coe_fn C a = coe_fn C 0)) C_0)) (iff.refl (coe_fn C a = 0))) C_inj

protected instance infinite {R : Type u} [semiring R] [nontrivial R] : infinite (polynomial R) := sorry

theorem monomial_eq_smul_X {R : Type u} {a : R} [semiring R] {n : ℕ} : coe_fn (monomial n) a = a • X ^ n := sorry

theorem ring_hom_ext {R : Type u} [semiring R] {S : Type u_1} [semiring S] {f : polynomial R →+* S} {g : polynomial R →+* S} (h₁ : ∀ (a : R), coe_fn f (coe_fn C a) = coe_fn g (coe_fn C a)) (h₂ : coe_fn f X = coe_fn g X) : f = g :=
  add_monoid_algebra.ring_hom_ext' (ring_hom.ext fun (x : R) => h₁ x) (monoid_hom.ext_mnat h₂)

theorem ring_hom_ext' {R : Type u} [semiring R] {S : Type u_1} [semiring S] {f : polynomial R →+* S} {g : polynomial R →+* S} (h₁ : ring_hom.comp f C = ring_hom.comp g C) (h₂ : coe_fn f X = coe_fn g X) : f = g :=
  ring_hom_ext (ring_hom.congr_fun h₁) h₂

