/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.degree.definitions
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Trailing degree of univariate polynomials

## Main definitions

* `trailing_degree p`: the multiplicity of `X` in the polynomial `p`
* `nat_trailing_degree`: a variant of `trailing_degree` that takes values in the natural numbers
* `trailing_coeff`: the coefficient at index `nat_trailing_degree p`

Converts most results about `degree`, `nat_degree` and `leading_coeff` to results about the bottom
end of a polynomial
-/

namespace polynomial


/-- `trailing_degree p` is the multiplicity of `x` in the polynomial `p`, i.e. the smallest
`X`-exponent in `p`.
`trailing_degree p = some n` when `p ≠ 0` and `n` is the smallest power of `X` that appears
in `p`, otherwise
`trailing_degree 0 = ⊤`. -/
def trailing_degree {R : Type u} [semiring R] (p : polynomial R) : with_top ℕ :=
  finset.inf (finsupp.support p) some

theorem trailing_degree_lt_wf {R : Type u} [semiring R] : well_founded fun (p q : polynomial R) => trailing_degree p < trailing_degree q :=
  inv_image.wf trailing_degree (with_top.well_founded_lt nat.lt_wf)

/-- `nat_trailing_degree p` forces `trailing_degree p` to `ℕ`, by defining
`nat_trailing_degree ⊤ = 0`. -/
def nat_trailing_degree {R : Type u} [semiring R] (p : polynomial R) : ℕ :=
  option.get_or_else (trailing_degree p) 0

/-- `trailing_coeff p` gives the coefficient of the smallest power of `X` in `p`-/
def trailing_coeff {R : Type u} [semiring R] (p : polynomial R) : R :=
  coeff p (nat_trailing_degree p)

/-- a polynomial is `monic_at` if its trailing coefficient is 1 -/
def trailing_monic {R : Type u} [semiring R] (p : polynomial R) :=
  trailing_coeff p = 1

theorem trailing_monic.def {R : Type u} [semiring R] {p : polynomial R} : trailing_monic p ↔ trailing_coeff p = 1 :=
  iff.rfl

protected instance trailing_monic.decidable {R : Type u} [semiring R] {p : polynomial R} [DecidableEq R] : Decidable (trailing_monic p) :=
  eq.mpr sorry (_inst_2 (trailing_coeff p) 1)

@[simp] theorem trailing_monic.trailing_coeff {R : Type u} [semiring R] {p : polynomial R} (hp : trailing_monic p) : trailing_coeff p = 1 :=
  hp

@[simp] theorem trailing_degree_zero {R : Type u} [semiring R] : trailing_degree 0 = ⊤ :=
  rfl

@[simp] theorem nat_trailing_degree_zero {R : Type u} [semiring R] : nat_trailing_degree 0 = 0 :=
  rfl

theorem trailing_degree_eq_top {R : Type u} [semiring R] {p : polynomial R} : trailing_degree p = ⊤ ↔ p = 0 := sorry

theorem trailing_degree_eq_nat_trailing_degree {R : Type u} [semiring R] {p : polynomial R} (hp : p ≠ 0) : trailing_degree p = ↑(nat_trailing_degree p) := sorry

theorem trailing_degree_eq_iff_nat_trailing_degree_eq {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} (hp : p ≠ 0) : trailing_degree p = ↑n ↔ nat_trailing_degree p = n := sorry

theorem trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} (hn : 0 < n) : trailing_degree p = ↑n ↔ nat_trailing_degree p = n := sorry

theorem nat_trailing_degree_eq_of_trailing_degree_eq_some {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} (h : trailing_degree p = ↑n) : nat_trailing_degree p = n := sorry

@[simp] theorem nat_trailing_degree_le_trailing_degree {R : Type u} [semiring R] {p : polynomial R} : ↑(nat_trailing_degree p) ≤ trailing_degree p := sorry

theorem nat_trailing_degree_eq_of_trailing_degree_eq {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] {q : polynomial S} (h : trailing_degree p = trailing_degree q) : nat_trailing_degree p = nat_trailing_degree q := sorry

theorem le_trailing_degree_of_ne_zero {R : Type u} {n : ℕ} [semiring R] {p : polynomial R} (h : coeff p n ≠ 0) : trailing_degree p ≤ ↑n :=
  (fun (this : finset.inf (finsupp.support p) some ≤ some n) => this) (finset.inf_le (iff.mpr finsupp.mem_support_iff h))

theorem nat_trailing_degree_le_of_ne_zero {R : Type u} {n : ℕ} [semiring R] {p : polynomial R} (h : coeff p n ≠ 0) : nat_trailing_degree p ≤ n := sorry

theorem trailing_degree_le_trailing_degree {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : coeff q (nat_trailing_degree p) ≠ 0) : trailing_degree q ≤ trailing_degree p := sorry

theorem trailing_degree_ne_of_nat_trailing_degree_ne {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} : nat_trailing_degree p ≠ n → trailing_degree p ≠ ↑n := sorry

theorem nat_trailing_degree_le_of_trailing_degree_le {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} {hp : p ≠ 0} (H : ↑n ≤ trailing_degree p) : n ≤ nat_trailing_degree p :=
  iff.mp with_top.coe_le_coe
    (eq.mp (Eq._oldrec (Eq.refl (↑n ≤ trailing_degree p)) (trailing_degree_eq_nat_trailing_degree hp)) H)

theorem nat_trailing_degree_le_nat_trailing_degree {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} {hq : q ≠ 0} (hpq : trailing_degree p ≤ trailing_degree q) : nat_trailing_degree p ≤ nat_trailing_degree q := sorry

@[simp] theorem trailing_degree_monomial {R : Type u} {a : R} {n : ℕ} [semiring R] (ha : a ≠ 0) : trailing_degree (coe_fn (monomial n) a) = ↑n := sorry

theorem nat_trailing_degree_monomial {R : Type u} {a : R} {n : ℕ} [semiring R] (ha : a ≠ 0) : nat_trailing_degree (coe_fn (monomial n) a) = n := sorry

theorem nat_trailing_degree_monomial_le {R : Type u} {a : R} {n : ℕ} [semiring R] : nat_trailing_degree (coe_fn (monomial n) a) ≤ n := sorry

theorem le_trailing_degree_monomial {R : Type u} {a : R} {n : ℕ} [semiring R] : ↑n ≤ trailing_degree (coe_fn (monomial n) a) := sorry

@[simp] theorem trailing_degree_C {R : Type u} {a : R} [semiring R] (ha : a ≠ 0) : trailing_degree (coe_fn C a) = 0 :=
  trailing_degree_monomial ha

theorem le_trailing_degree_C {R : Type u} {a : R} [semiring R] : 0 ≤ trailing_degree (coe_fn C a) :=
  le_trailing_degree_monomial

theorem trailing_degree_one_le {R : Type u} [semiring R] : 0 ≤ trailing_degree 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ trailing_degree 1)) (Eq.symm C_1))) le_trailing_degree_C

@[simp] theorem nat_trailing_degree_C {R : Type u} [semiring R] (a : R) : nat_trailing_degree (coe_fn C a) = 0 :=
  iff.mp nonpos_iff_eq_zero nat_trailing_degree_monomial_le

@[simp] theorem nat_trailing_degree_one {R : Type u} [semiring R] : nat_trailing_degree 1 = 0 :=
  nat_trailing_degree_C 1

@[simp] theorem nat_trailing_degree_nat_cast {R : Type u} [semiring R] (n : ℕ) : nat_trailing_degree ↑n = 0 := sorry

@[simp] theorem trailing_degree_C_mul_X_pow {R : Type u} {a : R} [semiring R] (n : ℕ) (ha : a ≠ 0) : trailing_degree (coe_fn C a * X ^ n) = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (trailing_degree (coe_fn C a * X ^ n) = ↑n)) (C_mul_X_pow_eq_monomial a n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (trailing_degree (coe_fn (monomial n) a) = ↑n)) (trailing_degree_monomial ha)))
      (Eq.refl ↑n))

theorem le_trailing_degree_C_mul_X_pow {R : Type u} [semiring R] (n : ℕ) (a : R) : ↑n ≤ trailing_degree (coe_fn C a * X ^ n) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n ≤ trailing_degree (coe_fn C a * X ^ n))) (C_mul_X_pow_eq_monomial a n)))
    le_trailing_degree_monomial

theorem coeff_eq_zero_of_trailing_degree_lt {R : Type u} {n : ℕ} [semiring R] {p : polynomial R} (h : ↑n < trailing_degree p) : coeff p n = 0 :=
  iff.mp not_not (mt le_trailing_degree_of_ne_zero (not_le_of_gt h))

theorem coeff_eq_zero_of_lt_nat_trailing_degree {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} (h : n < nat_trailing_degree p) : coeff p n = 0 := sorry

@[simp] theorem coeff_nat_trailing_degree_pred_eq_zero {R : Type u} [semiring R] {p : polynomial R} {hp : 0 < ↑(nat_trailing_degree p)} : coeff p (nat_trailing_degree p - 1) = 0 :=
  coeff_eq_zero_of_lt_nat_trailing_degree
    (nat.sub_lt (iff.mp (with_top.zero_lt_coe (nat_trailing_degree p)) hp) nat.one_pos)

theorem le_trailing_degree_X_pow {R : Type u} [semiring R] (n : ℕ) : ↑n ≤ trailing_degree (X ^ n) := sorry

theorem le_trailing_degree_X {R : Type u} [semiring R] : 1 ≤ trailing_degree X :=
  le_trailing_degree_monomial

theorem nat_trailing_degree_X_le {R : Type u} [semiring R] : nat_trailing_degree X ≤ 1 :=
  nat_trailing_degree_monomial_le

@[simp] theorem trailing_coeff_eq_zero {R : Type u} [semiring R] {p : polynomial R} : trailing_coeff p = 0 ↔ p = 0 := sorry

theorem trailing_coeff_nonzero_iff_nonzero {R : Type u} [semiring R] {p : polynomial R} : trailing_coeff p ≠ 0 ↔ p ≠ 0 :=
  not_congr trailing_coeff_eq_zero

theorem nat_trailing_degree_mem_support_of_nonzero {R : Type u} [semiring R] {p : polynomial R} : p ≠ 0 → nat_trailing_degree p ∈ finsupp.support p :=
  iff.mpr mem_support_iff_coeff_ne_zero ∘ iff.mpr trailing_coeff_nonzero_iff_nonzero

theorem nat_trailing_degree_le_of_mem_supp {R : Type u} [semiring R] {p : polynomial R} (a : ℕ) : a ∈ finsupp.support p → nat_trailing_degree p ≤ a :=
  nat_trailing_degree_le_of_ne_zero ∘ iff.mp mem_support_iff_coeff_ne_zero

theorem nat_trailing_degree_eq_support_min' {R : Type u} [semiring R] {p : polynomial R} (h : p ≠ 0) : nat_trailing_degree p = finset.min' (finsupp.support p) (iff.mpr nonempty_support_iff h) := sorry

@[simp] theorem trailing_degree_one {R : Type u} [semiring R] [nontrivial R] : trailing_degree 1 = 0 :=
  trailing_degree_C one_ne_zero

@[simp] theorem trailing_degree_X {R : Type u} [semiring R] [nontrivial R] : trailing_degree X = 1 :=
  trailing_degree_monomial one_ne_zero

@[simp] theorem nat_trailing_degree_X {R : Type u} [semiring R] [nontrivial R] : nat_trailing_degree X = 1 :=
  nat_trailing_degree_monomial one_ne_zero

@[simp] theorem trailing_degree_neg {R : Type u} [ring R] (p : polynomial R) : trailing_degree (-p) = trailing_degree p := sorry

@[simp] theorem nat_trailing_degree_neg {R : Type u} [ring R] (p : polynomial R) : nat_trailing_degree (-p) = nat_trailing_degree p := sorry

@[simp] theorem nat_trailing_degree_int_cast {R : Type u} [ring R] (n : ℤ) : nat_trailing_degree ↑n = 0 := sorry

/-- The second-lowest coefficient, or 0 for constants -/
def next_coeff_up {R : Type u} [semiring R] (p : polynomial R) : R :=
  ite (nat_trailing_degree p = 0) 0 (coeff p (nat_trailing_degree p + 1))

@[simp] theorem next_coeff_up_C_eq_zero {R : Type u} [semiring R] (c : R) : next_coeff_up (coe_fn C c) = 0 := sorry

theorem next_coeff_up_of_pos_nat_trailing_degree {R : Type u} [semiring R] (p : polynomial R) (hp : 0 < nat_trailing_degree p) : next_coeff_up p = coeff p (nat_trailing_degree p + 1) := sorry

theorem coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : trailing_degree p < trailing_degree q) : coeff q (nat_trailing_degree p) = 0 :=
  coeff_eq_zero_of_trailing_degree_lt (has_le.le.trans_lt nat_trailing_degree_le_trailing_degree h)

theorem ne_zero_of_trailing_degree_lt {R : Type u} [semiring R] {p : polynomial R} {n : with_top ℕ} (h : trailing_degree p < n) : p ≠ 0 := sorry

