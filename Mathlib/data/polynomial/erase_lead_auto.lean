/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.degree.default
import Mathlib.data.polynomial.degree.trailing_degree
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `erase_lead f`: the polynomial `f - leading term of f`

`erase_lead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/

namespace polynomial


/-- `erase_lead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`. -/
def erase_lead {R : Type u_1} [semiring R] (f : polynomial R) : polynomial R :=
  finsupp.erase (nat_degree f) f

theorem erase_lead_support {R : Type u_1} [semiring R] (f : polynomial R) :
    finsupp.support (erase_lead f) = finset.erase (finsupp.support f) (nat_degree f) :=
  sorry

-- `rfl` fails because LHS uses `nat.decidable_eq` but RHS is classical.

theorem erase_lead_coeff {R : Type u_1} [semiring R] {f : polynomial R} (i : ℕ) :
    coeff (erase_lead f) i = ite (i = nat_degree f) 0 (coeff f i) :=
  sorry

-- `rfl` fails because LHS uses `nat.decidable_eq` but RHS is classical.

@[simp] theorem erase_lead_coeff_nat_degree {R : Type u_1} [semiring R] {f : polynomial R} :
    coeff (erase_lead f) (nat_degree f) = 0 :=
  finsupp.erase_same

theorem erase_lead_coeff_of_ne {R : Type u_1} [semiring R] {f : polynomial R} (i : ℕ)
    (hi : i ≠ nat_degree f) : coeff (erase_lead f) i = coeff f i :=
  finsupp.erase_ne hi

@[simp] theorem erase_lead_zero {R : Type u_1} [semiring R] : erase_lead 0 = 0 :=
  finsupp.erase_zero (nat_degree 0)

@[simp] theorem erase_lead_add_monomial_nat_degree_leading_coeff {R : Type u_1} [semiring R]
    (f : polynomial R) : erase_lead f + coe_fn (monomial (nat_degree f)) (leading_coeff f) = f :=
  sorry

@[simp] theorem erase_lead_add_C_mul_X_pow {R : Type u_1} [semiring R] (f : polynomial R) :
    erase_lead f + coe_fn C (leading_coeff f) * X ^ nat_degree f = f :=
  sorry

@[simp] theorem self_sub_monomial_nat_degree_leading_coeff {R : Type u_1} [ring R]
    (f : polynomial R) : f - coe_fn (monomial (nat_degree f)) (leading_coeff f) = erase_lead f :=
  Eq.symm (iff.mpr eq_sub_iff_add_eq (erase_lead_add_monomial_nat_degree_leading_coeff f))

@[simp] theorem self_sub_C_mul_X_pow {R : Type u_1} [ring R] (f : polynomial R) :
    f - coe_fn C (leading_coeff f) * X ^ nat_degree f = erase_lead f :=
  sorry

theorem erase_lead_ne_zero {R : Type u_1} [semiring R] {f : polynomial R}
    (f0 : bit0 1 ≤ finset.card (finsupp.support f)) : erase_lead f ≠ 0 :=
  sorry

@[simp] theorem nat_degree_not_mem_erase_lead_support {R : Type u_1} [semiring R]
    {f : polynomial R} : ¬nat_degree f ∈ finsupp.support (erase_lead f) :=
  sorry

theorem ne_nat_degree_of_mem_erase_lead_support {R : Type u_1} [semiring R] {f : polynomial R}
    {a : ℕ} (h : a ∈ finsupp.support (erase_lead f)) : a ≠ nat_degree f :=
  sorry

theorem erase_lead_support_card_lt {R : Type u_1} [semiring R] {f : polynomial R} (h : f ≠ 0) :
    finset.card (finsupp.support (erase_lead f)) < finset.card (finsupp.support f) :=
  sorry

theorem erase_lead_card_support {R : Type u_1} [semiring R] {f : polynomial R} {c : ℕ}
    (fc : finset.card (finsupp.support f) = c) :
    finset.card (finsupp.support (erase_lead f)) = c - 1 :=
  sorry

theorem erase_lead_card_support' {R : Type u_1} [semiring R] {f : polynomial R} {c : ℕ}
    (fc : finset.card (finsupp.support f) = c + 1) :
    finset.card (finsupp.support (erase_lead f)) = c :=
  erase_lead_card_support fc

@[simp] theorem erase_lead_monomial {R : Type u_1} [semiring R] (i : ℕ) (r : R) :
    erase_lead (coe_fn (monomial i) r) = 0 :=
  sorry

@[simp] theorem erase_lead_C {R : Type u_1} [semiring R] (r : R) : erase_lead (coe_fn C r) = 0 :=
  erase_lead_monomial 0 r

@[simp] theorem erase_lead_X {R : Type u_1} [semiring R] : erase_lead X = 0 :=
  erase_lead_monomial 1 1

@[simp] theorem erase_lead_X_pow {R : Type u_1} [semiring R] (n : ℕ) : erase_lead (X ^ n) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (erase_lead (X ^ n) = 0)) (X_pow_eq_monomial n)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (erase_lead (coe_fn (monomial n) 1) = 0)) (erase_lead_monomial n 1)))
      (Eq.refl 0))

@[simp] theorem erase_lead_C_mul_X_pow {R : Type u_1} [semiring R] (r : R) (n : ℕ) :
    erase_lead (coe_fn C r * X ^ n) = 0 :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (erase_lead (coe_fn C r * X ^ n) = 0)) (C_mul_X_pow_eq_monomial r n)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (erase_lead (coe_fn (monomial n) r) = 0)) (erase_lead_monomial n r)))
      (Eq.refl 0))

theorem erase_lead_degree_le {R : Type u_1} [semiring R] {f : polynomial R} :
    degree (erase_lead f) ≤ degree f :=
  sorry

theorem erase_lead_nat_degree_le {R : Type u_1} [semiring R] {f : polynomial R} :
    nat_degree (erase_lead f) ≤ nat_degree f :=
  nat_degree_le_nat_degree erase_lead_degree_le

theorem erase_lead_nat_degree_lt {R : Type u_1} [semiring R] {f : polynomial R}
    (f0 : bit0 1 ≤ finset.card (finsupp.support f)) : nat_degree (erase_lead f) < nat_degree f :=
  lt_of_le_of_ne erase_lead_nat_degree_le
    (ne_nat_degree_of_mem_erase_lead_support
      (nat_degree_mem_support_of_nonzero (erase_lead_ne_zero f0)))

theorem erase_lead_nat_degree_lt_or_erase_lead_eq_zero {R : Type u_1} [semiring R]
    (f : polynomial R) : nat_degree (erase_lead f) < nat_degree f ∨ erase_lead f = 0 :=
  sorry

/-- An induction lemma for polynomials. It takes a natural number `N` as a parameter, that is
required to be at least as big as the `nat_degree` of the polynomial.  This is useful to prove
results where you want to change each term in a polynomial to something else depending on the
`nat_degree` of the polynomial itself and not on the specific `nat_degree` of each term. -/
theorem induction_with_nat_degree_le {R : Type u_1} [semiring R] {P : polynomial R → Prop} (N : ℕ)
    (P_0 : P 0) (P_C_mul_pow : ∀ (n : ℕ) (r : R), r ≠ 0 → n ≤ N → P (coe_fn C r * X ^ n))
    (P_C_add : ∀ (f g : polynomial R), nat_degree f ≤ N → nat_degree g ≤ N → P f → P g → P (f + g))
    (f : polynomial R) : nat_degree f ≤ N → P f :=
  sorry

end Mathlib