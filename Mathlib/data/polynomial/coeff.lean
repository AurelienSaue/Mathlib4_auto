/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.monomial
import Mathlib.data.finset.nat_antidiagonal
import Mathlib.PostPort

universes u v u_1 

namespace Mathlib

/-!
# Theory of univariate polynomials

The theorems include formulas for computing coefficients, such as
`coeff_add`, `coeff_sum`, `coeff_mul`

-/

namespace polynomial


theorem coeff_one {R : Type u} [semiring R] (n : ℕ) : coeff 1 n = ite (0 = n) 1 0 :=
  coeff_monomial

@[simp] theorem coeff_add {R : Type u} [semiring R] (p : polynomial R) (q : polynomial R) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n :=
  rfl

theorem coeff_sum {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] (n : ℕ) (f : ℕ → R → polynomial S) : coeff (finsupp.sum p f) n = finsupp.sum p fun (a : ℕ) (b : R) => coeff (f a b) n :=
  finsupp.sum_apply

@[simp] theorem coeff_smul {R : Type u} [semiring R] (p : polynomial R) (r : R) (n : ℕ) : coeff (r • p) n = r * coeff p n :=
  finsupp.smul_apply

theorem mem_support_iff_coeff_ne_zero {R : Type u} {n : ℕ} [semiring R] {p : polynomial R} : n ∈ finsupp.support p ↔ coeff p n ≠ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n ∈ finsupp.support p ↔ coeff p n ≠ 0)) (propext (finsupp.mem_support_to_fun p n))))
    (iff.refl (finsupp.to_fun p n ≠ 0))

theorem not_mem_support_iff_coeff_zero {R : Type u} {n : ℕ} [semiring R] {p : polynomial R} : ¬n ∈ finsupp.support p ↔ coeff p n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬n ∈ finsupp.support p ↔ coeff p n = 0)) (propext (finsupp.mem_support_to_fun p n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬finsupp.to_fun p n ≠ 0 ↔ coeff p n = 0)) (propext not_not)))
      (iff.refl (finsupp.to_fun p n = 0)))

/-- The nth coefficient, as a linear map. -/
def lcoeff (R : Type u) [semiring R] (n : ℕ) : linear_map R (polynomial R) R :=
  finsupp.lapply n

@[simp] theorem lcoeff_apply {R : Type u} [semiring R] (n : ℕ) (f : polynomial R) : coe_fn (lcoeff R n) f = coeff f n :=
  rfl

@[simp] theorem finset_sum_coeff {R : Type u} [semiring R] {ι : Type u_1} (s : finset ι) (f : ι → polynomial R) (n : ℕ) : coeff (finset.sum s fun (b : ι) => f b) n = finset.sum s fun (b : ι) => coeff (f b) n :=
  Eq.symm (finset.sum_hom s fun (q : polynomial R) => coe_fn (lcoeff R n) q)

theorem coeff_mul {R : Type u} [semiring R] (p : polynomial R) (q : polynomial R) (n : ℕ) : coeff (p * q) n = finset.sum (finset.nat.antidiagonal n) fun (x : ℕ × ℕ) => coeff p (prod.fst x) * coeff q (prod.snd x) :=
  add_monoid_algebra.mul_apply_antidiagonal p q n (finset.nat.antidiagonal n)
    fun (x : ℕ × ℕ) => finset.nat.mem_antidiagonal

@[simp] theorem mul_coeff_zero {R : Type u} [semiring R] (p : polynomial R) (q : polynomial R) : coeff (p * q) 0 = coeff p 0 * coeff q 0 := sorry

theorem coeff_mul_X_zero {R : Type u} [semiring R] (p : polynomial R) : coeff (p * X) 0 = 0 := sorry

theorem coeff_X_mul_zero {R : Type u} [semiring R] (p : polynomial R) : coeff (X * p) 0 = 0 := sorry

theorem coeff_C_mul_X {R : Type u} [semiring R] (x : R) (k : ℕ) (n : ℕ) : coeff (coe_fn C x * X ^ k) n = ite (n = k) x 0 := sorry

@[simp] theorem coeff_C_mul {R : Type u} {a : R} {n : ℕ} [semiring R] (p : polynomial R) : coeff (coe_fn C a * p) n = a * coeff p n :=
  add_monoid_algebra.single_zero_mul_apply p a n

theorem C_mul' {R : Type u} [semiring R] (a : R) (f : polynomial R) : coe_fn C a * f = a • f :=
  ext fun (n : ℕ) => coeff_C_mul f

@[simp] theorem coeff_mul_C {R : Type u} [semiring R] (p : polynomial R) (n : ℕ) (a : R) : coeff (p * coe_fn C a) n = coeff p n * a :=
  add_monoid_algebra.mul_single_zero_apply p a n

theorem coeff_X_pow {R : Type u} [semiring R] (k : ℕ) (n : ℕ) : coeff (X ^ k) n = ite (n = k) 1 0 := sorry

@[simp] theorem coeff_X_pow_self {R : Type u} [semiring R] (n : ℕ) : coeff (X ^ n) n = 1 := sorry

theorem coeff_mul_X_pow {R : Type u} [semiring R] (p : polynomial R) (n : ℕ) (d : ℕ) : coeff (p * X ^ n) (d + n) = coeff p d := sorry

@[simp] theorem coeff_mul_X {R : Type u} [semiring R] (p : polynomial R) (n : ℕ) : coeff (p * X) (n + 1) = coeff p n := sorry

theorem mul_X_pow_eq_zero {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} (H : p * X ^ n = 0) : p = 0 :=
  ext fun (k : ℕ) => Eq.trans (Eq.symm (coeff_mul_X_pow p n k)) (iff.mp ext_iff H (k + n))

theorem C_mul_X_pow_eq_monomial {R : Type u} [semiring R] (c : R) (n : ℕ) : coe_fn C c * X ^ n = coe_fn (monomial n) c := sorry

theorem support_mul_X_pow {R : Type u} [semiring R] (c : R) (n : ℕ) (H : c ≠ 0) : finsupp.support (coe_fn C c * X ^ n) = singleton n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finsupp.support (coe_fn C c * X ^ n) = singleton n)) (C_mul_X_pow_eq_monomial c n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (finsupp.support (coe_fn (monomial n) c) = singleton n)) (support_monomial n c H)))
      (Eq.refl (singleton n)))

theorem support_C_mul_X_pow' {R : Type u} [semiring R] {c : R} {n : ℕ} : finsupp.support (coe_fn C c * X ^ n) ⊆ singleton n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finsupp.support (coe_fn C c * X ^ n) ⊆ singleton n)) (C_mul_X_pow_eq_monomial c n)))
    (support_monomial' n c)

theorem C_dvd_iff_dvd_coeff {R : Type u} [semiring R] (r : R) (φ : polynomial R) : coe_fn C r ∣ φ ↔ ∀ (i : ℕ), r ∣ coeff φ i := sorry

/--  If the coefficients of a polynomial belong to n ideal contains the submodule span of the
coefficients of a polynomial. -/
theorem span_le_of_coeff_mem_C_inverse {R : Type u} [semiring R] {f : polynomial R} {I : submodule (polynomial R) (polynomial R)} (cf : ∀ (i : ℕ), coeff f i ∈ ⇑C ⁻¹' submodule.carrier I) : submodule.span (polynomial R) (set_of fun (g : polynomial R) => ∃ (i : ℕ), g = coe_fn C (coeff f i)) ≤ I := sorry

theorem mem_span_C_coeff {R : Type u} [semiring R] {f : polynomial R} : f ∈ submodule.span (polynomial R) (set_of fun (g : polynomial R) => ∃ (i : ℕ), g = coe_fn C (coeff f i)) := sorry

theorem exists_coeff_not_mem_C_inverse {R : Type u} [semiring R] {f : polynomial R} {I : submodule (polynomial R) (polynomial R)} : ¬f ∈ I → ∃ (i : ℕ), ¬coeff f i ∈ ⇑C ⁻¹' submodule.carrier I :=
  imp_of_not_imp_not (¬f ∈ I) (∃ (i : ℕ), ¬coeff f i ∈ ⇑C ⁻¹' submodule.carrier I)
    fun (cf : ¬∃ (i : ℕ), ¬coeff f i ∈ ⇑C ⁻¹' submodule.carrier I) =>
      iff.mpr not_not (span_le_of_coeff_mem_C_inverse (iff.mp not_exists_not cf) mem_span_C_coeff)

