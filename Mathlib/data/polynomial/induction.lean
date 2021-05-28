/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.coeff
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Theory of univariate polynomials

The main results are `induction_on` and `as_sum`.
-/

namespace polynomial


theorem sum_C_mul_X_eq {R : Type u} [semiring R] (p : polynomial R) : (finsupp.sum p fun (n : ℕ) (a : R) => coe_fn C a * X ^ n) = p :=
  Eq.trans (finset.sum_congr rfl fun (n : ℕ) (hn : n ∈ finsupp.support p) => Eq.symm single_eq_C_mul_X)
    (finsupp.sum_single p)

theorem sum_monomial_eq {R : Type u} [semiring R] (p : polynomial R) : (finsupp.sum p fun (n : ℕ) (a : R) => coe_fn (monomial n) a) = p := sorry

protected theorem induction_on {R : Type u} [semiring R] {M : polynomial R → Prop} (p : polynomial R) (h_C : ∀ (a : R), M (coe_fn C a)) (h_add : ∀ (p q : polynomial R), M p → M q → M (p + q)) (h_monomial : ∀ (n : ℕ) (a : R), M (coe_fn C a * X ^ n) → M (coe_fn C a * X ^ (n + 1))) : M p := sorry

/--
To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
protected theorem induction_on' {R : Type u} [semiring R] {M : polynomial R → Prop} (p : polynomial R) (h_add : ∀ (p q : polynomial R), M p → M q → M (p + q)) (h_monomial : ∀ (n : ℕ) (a : R), M (coe_fn (monomial n) a)) : M p :=
  polynomial.induction_on p (h_monomial 0) h_add
    fun (n : ℕ) (a : R) (h : M (coe_fn C a * X ^ n)) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (M (coe_fn C a * X ^ (n + 1)))) (Eq.symm single_eq_C_mul_X))) (h_monomial (n + 1) a)

theorem coeff_mul_monomial {R : Type u} [semiring R] (p : polynomial R) (n : ℕ) (d : ℕ) (r : R) : coeff (p * coe_fn (monomial n) r) (d + n) = coeff p d * r := sorry

theorem coeff_monomial_mul {R : Type u} [semiring R] (p : polynomial R) (n : ℕ) (d : ℕ) (r : R) : coeff (coe_fn (monomial n) r * p) (d + n) = r * coeff p d := sorry

-- This can already be proved by `simp`.

theorem coeff_mul_monomial_zero {R : Type u} [semiring R] (p : polynomial R) (d : ℕ) (r : R) : coeff (p * coe_fn (monomial 0) r) d = coeff p d * r :=
  coeff_mul_monomial p 0 d r

-- This can already be proved by `simp`.

theorem coeff_monomial_zero_mul {R : Type u} [semiring R] (p : polynomial R) (d : ℕ) (r : R) : coeff (coe_fn (monomial 0) r * p) d = r * coeff p d :=
  coeff_monomial_mul p 0 d r

