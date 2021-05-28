/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.degree.definitions
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Cancel the leading terms of two polynomials

## Definition

* `cancel_leads p q`: the polynomial formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting.

## Main Results
The degree of `cancel_leads` is less than that of the larger of the two polynomials being cancelled.
Thus it is useful for induction or minimal-degree arguments.
-/

namespace polynomial


/-- `cancel_leads p q` is formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting. -/
def cancel_leads {R : Type u_1} [comm_ring R] (p : polynomial R) (q : polynomial R) : polynomial R :=
  coe_fn C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q -
    coe_fn C (leading_coeff q) * X ^ (nat_degree q - nat_degree p) * p

@[simp] theorem neg_cancel_leads {R : Type u_1} [comm_ring R] {p : polynomial R} {q : polynomial R} : -cancel_leads p q = cancel_leads q p :=
  neg_sub (coe_fn C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q)
    (coe_fn C (leading_coeff q) * X ^ (nat_degree q - nat_degree p) * p)

theorem dvd_cancel_leads_of_dvd_of_dvd {R : Type u_1} [comm_ring R] {p : polynomial R} {q : polynomial R} {r : polynomial R} (pq : p ∣ q) (pr : p ∣ r) : p ∣ cancel_leads q r :=
  dvd_sub (dvd.trans pr (dvd.intro_left (coe_fn C (leading_coeff q) * X ^ (nat_degree q - nat_degree r)) rfl))
    (dvd.trans pq (dvd.intro_left (coe_fn C (leading_coeff r) * X ^ (nat_degree r - nat_degree q)) rfl))

theorem nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree {R : Type u_1} [integral_domain R] {p : polynomial R} {q : polynomial R} (h : nat_degree p ≤ nat_degree q) (hq : 0 < nat_degree q) : nat_degree (cancel_leads p q) < nat_degree q := sorry

