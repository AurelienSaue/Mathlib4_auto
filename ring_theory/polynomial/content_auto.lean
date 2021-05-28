/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.finset.gcd
import Mathlib.data.polynomial.default
import Mathlib.data.polynomial.erase_lead
import Mathlib.data.polynomial.cancel_leads
import PostPort

universes u_1 

namespace Mathlib

/-!
# GCD structures on polynomials

Definitions and basic results about polynomials over GCD domains, particularly their contents
and primitive polynomials.

## Main Definitions
Let `p : polynomial R`.
 - `p.content` is the `gcd` of the coefficients of `p`.
 - `p.is_primitive` indicates that `p.content = 1`.

## Main Results
 - `polynomial.content_mul`:
  If `p q : polynomial R`, then `(p * q).content = p.content * q.content`.
 - `polynomial.gcd_monoid`:
  The polynomial ring of a GCD domain is itself a GCD domain.

-/

namespace polynomial


/-- `p.content` is the `gcd` of the coefficients of `p`. -/
def content {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) : R :=
  finset.gcd (finsupp.support p) (coeff p)

theorem content_dvd_coeff {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} (n : ℕ) : content p ∣ coeff p n := sorry

@[simp] theorem content_C {R : Type u_1} [integral_domain R] [gcd_monoid R] {r : R} : content (coe_fn C r) = coe_fn normalize r := sorry

@[simp] theorem content_zero {R : Type u_1} [integral_domain R] [gcd_monoid R] : content 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (content 0 = 0)) (Eq.symm C_0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (content (coe_fn C 0) = 0)) content_C))
      (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn normalize 0 = 0)) normalize_zero)) (Eq.refl 0)))

@[simp] theorem content_one {R : Type u_1} [integral_domain R] [gcd_monoid R] : content 1 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (content 1 = 1)) (Eq.symm C_1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (content (coe_fn C 1) = 1)) content_C))
      (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn normalize 1 = 1)) normalize_one)) (Eq.refl 1)))

theorem content_X_mul {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} : content (X * p) = content p := sorry

@[simp] theorem content_X_pow {R : Type u_1} [integral_domain R] [gcd_monoid R] {k : ℕ} : content (X ^ k) = 1 := sorry

@[simp] theorem content_X {R : Type u_1} [integral_domain R] [gcd_monoid R] : content X = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (content X = 1)) (Eq.symm (mul_one X))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (content (X * 1) = 1)) content_X_mul))
      (eq.mpr (id (Eq._oldrec (Eq.refl (content 1 = 1)) content_one)) (Eq.refl 1)))

theorem content_C_mul {R : Type u_1} [integral_domain R] [gcd_monoid R] (r : R) (p : polynomial R) : content (coe_fn C r * p) = coe_fn normalize r * content p := sorry

@[simp] theorem content_monomial {R : Type u_1} [integral_domain R] [gcd_monoid R] {r : R} {k : ℕ} : content (coe_fn (monomial k) r) = coe_fn normalize r := sorry

theorem content_eq_zero_iff {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} : content p = 0 ↔ p = 0 := sorry

@[simp] theorem normalize_content {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} : coe_fn normalize (content p) = content p :=
  finset.normalize_gcd

theorem content_eq_gcd_range_of_lt {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) (n : ℕ) (h : nat_degree p < n) : content p = finset.gcd (finset.range n) (coeff p) := sorry

theorem content_eq_gcd_range_succ {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) : content p = finset.gcd (finset.range (Nat.succ (nat_degree p))) (coeff p) :=
  content_eq_gcd_range_of_lt p (Nat.succ (nat_degree p)) (nat.lt_succ_self (nat_degree p))

theorem content_eq_gcd_leading_coeff_content_erase_lead {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) : content p = gcd (leading_coeff p) (content (erase_lead p)) := sorry

theorem dvd_content_iff_C_dvd {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} {r : R} : r ∣ content p ↔ coe_fn C r ∣ p := sorry

theorem C_content_dvd {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) : coe_fn C (content p) ∣ p :=
  iff.mp dvd_content_iff_C_dvd (dvd_refl (content p))

/-- A polynomial over a GCD domain is primitive when the `gcd` of its coefficients is 1 -/
def is_primitive {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R)  :=
  content p = 1

@[simp] theorem is_primitive_one {R : Type u_1} [integral_domain R] [gcd_monoid R] : is_primitive 1 := sorry

theorem monic.is_primitive {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} (hp : monic p) : is_primitive p := sorry

theorem is_primitive.ne_zero {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} (hp : is_primitive p) : p ≠ 0 := sorry

theorem is_primitive.content_eq_one {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} (hp : is_primitive p) : content p = 1 :=
  hp

theorem is_primitive_iff_is_unit_of_C_dvd {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} : is_primitive p ↔ ∀ (r : R), coe_fn C r ∣ p → is_unit r := sorry

/-- The primitive part of a polynomial `p` is the primitive polynomial gained by dividing `p` by
  `p.content`. If `p = 0`, then `p.prim_part = 1`.  -/
def prim_part {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) : polynomial R :=
  ite (p = 0) 1 (classical.some (C_content_dvd p))

theorem eq_C_content_mul_prim_part {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) : p = coe_fn C (content p) * prim_part p := sorry

@[simp] theorem prim_part_zero {R : Type u_1} [integral_domain R] [gcd_monoid R] : prim_part 0 = 1 :=
  if_pos rfl

theorem is_primitive_prim_part {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) : is_primitive (prim_part p) := sorry

theorem content_prim_part {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) : content (prim_part p) = 1 :=
  is_primitive_prim_part p

theorem prim_part_ne_zero {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) : prim_part p ≠ 0 :=
  is_primitive.ne_zero (is_primitive_prim_part p)

theorem nat_degree_prim_part {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) : nat_degree (prim_part p) = nat_degree p := sorry

@[simp] theorem is_primitive.prim_part_eq {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} (hp : is_primitive p) : prim_part p = p := sorry

theorem is_unit_prim_part_C {R : Type u_1} [integral_domain R] [gcd_monoid R] (r : R) : is_unit (prim_part (coe_fn C r)) := sorry

theorem prim_part_dvd {R : Type u_1} [integral_domain R] [gcd_monoid R] (p : polynomial R) : prim_part p ∣ p :=
  dvd.intro_left (coe_fn C (content p)) (Eq.symm (eq_C_content_mul_prim_part p))

theorem gcd_content_eq_of_dvd_sub {R : Type u_1} [integral_domain R] [gcd_monoid R] {a : R} {p : polynomial R} {q : polynomial R} (h : coe_fn C a ∣ p - q) : gcd a (content p) = gcd a (content q) := sorry

theorem content_mul_aux {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} {q : polynomial R} : gcd (content (erase_lead (p * q))) (leading_coeff p) = gcd (content (erase_lead p * q)) (leading_coeff p) := sorry

@[simp] theorem content_mul {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} {q : polynomial R} : content (p * q) = content p * content q := sorry

theorem is_primitive.mul {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} {q : polynomial R} (hp : is_primitive p) (hq : is_primitive q) : is_primitive (p * q) := sorry

@[simp] theorem prim_part_mul {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} {q : polynomial R} (h0 : p * q ≠ 0) : prim_part (p * q) = prim_part p * prim_part q := sorry

theorem is_primitive.is_primitive_of_dvd {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} {q : polynomial R} (hp : is_primitive p) (hdvd : q ∣ p) : is_primitive q := sorry

theorem is_primitive.dvd_prim_part_iff_dvd {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} {q : polynomial R} (hp : is_primitive p) (hq : q ≠ 0) : p ∣ prim_part q ↔ p ∣ q := sorry

theorem exists_primitive_lcm_of_is_primitive {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} {q : polynomial R} (hp : is_primitive p) (hq : is_primitive q) : ∃ (r : polynomial R), is_primitive r ∧ ∀ (s : polynomial R), p ∣ s ∧ q ∣ s ↔ r ∣ s := sorry

theorem dvd_iff_content_dvd_content_and_prim_part_dvd_prim_part {R : Type u_1} [integral_domain R] [gcd_monoid R] {p : polynomial R} {q : polynomial R} (hq : q ≠ 0) : p ∣ q ↔ content p ∣ content q ∧ prim_part p ∣ prim_part q := sorry

protected instance gcd_monoid {R : Type u_1} [integral_domain R] [gcd_monoid R] : gcd_monoid (polynomial R) :=
  gcd_monoid_of_exists_lcm sorry

