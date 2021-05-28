/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.polynomial.algebra_map
import Mathlib.data.polynomial.monic
import PostPort

universes u v 

namespace Mathlib

/-!
# Theory of monic polynomials

We define `integral_normalization`, which relate arbitrary polynomials to monic ones.
-/

namespace polynomial


/-- If `f : polynomial R` is a nonzero polynomial with root `z`, `integral_normalization f` is
a monic polynomial with root `leading_coeff f * z`.

Moreover, `integral_normalization 0 = 0`.
-/
def integral_normalization {R : Type u} [semiring R] (f : polynomial R) : polynomial R :=
  finsupp.on_finset (finsupp.support f)
    (fun (i : ℕ) => ite (degree f = ↑i) 1 (coeff f i * leading_coeff f ^ (nat_degree f - 1 - i))) sorry

theorem integral_normalization_coeff_degree {R : Type u} [semiring R] {f : polynomial R} {i : ℕ} (hi : degree f = ↑i) : coeff (integral_normalization f) i = 1 :=
  if_pos hi

theorem integral_normalization_coeff_nat_degree {R : Type u} [semiring R] {f : polynomial R} (hf : f ≠ 0) : coeff (integral_normalization f) (nat_degree f) = 1 :=
  integral_normalization_coeff_degree (degree_eq_nat_degree hf)

theorem integral_normalization_coeff_ne_degree {R : Type u} [semiring R] {f : polynomial R} {i : ℕ} (hi : degree f ≠ ↑i) : coeff (integral_normalization f) i = coeff f i * leading_coeff f ^ (nat_degree f - 1 - i) :=
  if_neg hi

theorem integral_normalization_coeff_ne_nat_degree {R : Type u} [semiring R] {f : polynomial R} {i : ℕ} (hi : i ≠ nat_degree f) : coeff (integral_normalization f) i = coeff f i * leading_coeff f ^ (nat_degree f - 1 - i) :=
  integral_normalization_coeff_ne_degree (degree_ne_of_nat_degree_ne (ne.symm hi))

theorem monic_integral_normalization {R : Type u} [semiring R] {f : polynomial R} (hf : f ≠ 0) : monic (integral_normalization f) := sorry

@[simp] theorem support_integral_normalization {R : Type u} [integral_domain R] {f : polynomial R} (hf : f ≠ 0) : finsupp.support (integral_normalization f) = finsupp.support f := sorry

theorem integral_normalization_eval₂_eq_zero {R : Type u} {S : Type v} [integral_domain R] [comm_ring S] {p : polynomial R} (hp : p ≠ 0) (f : R →+* S) {z : S} (hz : eval₂ f z p = 0) (inj : ∀ (x : R), coe_fn f x = 0 → x = 0) : eval₂ f (z * coe_fn f (leading_coeff p)) (integral_normalization p) = 0 := sorry

theorem integral_normalization_aeval_eq_zero {R : Type u} {S : Type v} [integral_domain R] [comm_ring S] [algebra R S] {f : polynomial R} (hf : f ≠ 0) {z : S} (hz : coe_fn (aeval z) f = 0) (inj : ∀ (x : R), coe_fn (algebra_map R S) x = 0 → x = 0) : coe_fn (aeval (z * coe_fn (algebra_map R S) (leading_coeff f))) (integral_normalization f) = 0 :=
  integral_normalization_eval₂_eq_zero hf (algebra_map R S) hz inj

