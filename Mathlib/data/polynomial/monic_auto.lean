/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.polynomial.reverse
import Mathlib.algebra.associated
import Mathlib.tactic.omega.default
import PostPort

universes u v y 

namespace Mathlib

/-!
# Theory of monic polynomials

We give several tools for proving that polynomials are monic, e.g.
`monic_mul`, `monic_map`.
-/

namespace polynomial


theorem monic.as_sum {R : Type u} [semiring R] {p : polynomial R} (hp : monic p) : p = X ^ nat_degree p + finset.sum (finset.range (nat_degree p)) fun (i : ℕ) => coe_fn C (coeff p i) * X ^ i := sorry

theorem ne_zero_of_monic_of_zero_ne_one {R : Type u} [semiring R] {p : polynomial R} (hp : monic p) (h : 0 ≠ 1) : p ≠ 0 := sorry

theorem ne_zero_of_ne_zero_of_monic {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (hp : p ≠ 0) (hq : monic q) : q ≠ 0 := sorry

theorem monic_map {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] (f : R →+* S) (hp : monic p) : monic (map f p) := sorry

theorem monic_mul_C_of_leading_coeff_mul_eq_one {R : Type u} [semiring R] {p : polynomial R} [nontrivial R] {b : R} (hp : leading_coeff p * b = 1) : monic (p * coe_fn C b) := sorry

theorem monic_of_degree_le {R : Type u} [semiring R] {p : polynomial R} (n : ℕ) (H1 : degree p ≤ ↑n) (H2 : coeff p n = 1) : monic p := sorry

theorem monic_X_pow_add {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} (H : degree p ≤ ↑n) : monic (X ^ (n + 1) + p) := sorry

theorem monic_X_add_C {R : Type u} [semiring R] (x : R) : monic (X + coe_fn C x) :=
  pow_one X ▸ monic_X_pow_add degree_C_le

theorem monic_mul {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (hp : monic p) (hq : monic q) : monic (p * q) := sorry

theorem monic_pow {R : Type u} [semiring R] {p : polynomial R} (hp : monic p) (n : ℕ) : monic (p ^ n) := sorry

theorem monic_add_of_left {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (hp : monic p) (hpq : degree q < degree p) : monic (p + q) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (monic (p + q))) (monic.equations._eqn_1 (p + q))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (leading_coeff (p + q) = 1)) (add_comm p q)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (leading_coeff (q + p) = 1)) (leading_coeff_add_of_degree_lt hpq))) hp))

theorem monic_add_of_right {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (hq : monic q) (hpq : degree p < degree q) : monic (p + q) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (monic (p + q))) (monic.equations._eqn_1 (p + q))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (leading_coeff (p + q) = 1)) (leading_coeff_add_of_degree_lt hpq))) hq)

namespace monic


@[simp] theorem degree_eq_zero_iff_eq_one {R : Type u} [semiring R] {p : polynomial R} (hp : monic p) : nat_degree p = 0 ↔ p = 1 := sorry

theorem nat_degree_mul {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (hp : monic p) (hq : monic q) : nat_degree (p * q) = nat_degree p + nat_degree q := sorry

theorem next_coeff_mul {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (hp : monic p) (hq : monic q) : next_coeff (p * q) = next_coeff p + next_coeff q := sorry

end monic


theorem monic_prod_of_monic {R : Type u} {ι : Type y} [comm_semiring R] (s : finset ι) (f : ι → polynomial R) (hs : ∀ (i : ι), i ∈ s → monic (f i)) : monic (finset.prod s fun (i : ι) => f i) :=
  finset.prod_induction (fun (x : ι) => f x) monic monic_mul monic_one hs

theorem is_unit_C {R : Type u} [comm_semiring R] {x : R} : is_unit (coe_fn C x) ↔ is_unit x := sorry

theorem eq_one_of_is_unit_of_monic {R : Type u} [comm_semiring R] {p : polynomial R} (hm : monic p) (hpu : is_unit p) : p = 1 := sorry

theorem monic.next_coeff_prod {R : Type u} {ι : Type y} [comm_semiring R] (s : finset ι) (f : ι → polynomial R) (h : ∀ (i : ι), i ∈ s → monic (f i)) : next_coeff (finset.prod s fun (i : ι) => f i) = finset.sum s fun (i : ι) => next_coeff (f i) := sorry

theorem monic_X_sub_C {R : Type u} [ring R] (x : R) : monic (X - coe_fn C x) := sorry

theorem monic_X_pow_sub {R : Type u} [ring R] {p : polynomial R} {n : ℕ} (H : degree p ≤ ↑n) : monic (X ^ (n + 1) - p) := sorry

/-- `X ^ n - a` is monic. -/
theorem monic_X_pow_sub_C {R : Type u} [ring R] (a : R) {n : ℕ} (h : n ≠ 0) : monic (X ^ n - coe_fn C a) := sorry

theorem monic_sub_of_left {R : Type u} [ring R] {p : polynomial R} {q : polynomial R} (hp : monic p) (hpq : degree q < degree p) : monic (p - q) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (monic (p - q))) (sub_eq_add_neg p q)))
    (monic_add_of_left hp (eq.mpr (id (Eq._oldrec (Eq.refl (degree (-q) < degree p)) (degree_neg q))) hpq))

theorem monic_sub_of_right {R : Type u} [ring R] {p : polynomial R} {q : polynomial R} (hq : leading_coeff q = -1) (hpq : degree p < degree q) : monic (p - q) := sorry

theorem leading_coeff_of_injective {R : Type u} {S : Type v} [ring R] [semiring S] {f : R →+* S} (hf : function.injective ⇑f) (p : polynomial R) : leading_coeff (map f p) = coe_fn f (leading_coeff p) := sorry

theorem monic_of_injective {R : Type u} {S : Type v} [ring R] [semiring S] {f : R →+* S} (hf : function.injective ⇑f) {p : polynomial R} (hp : monic (map f p)) : monic p := sorry

@[simp] theorem not_monic_zero {R : Type u} [semiring R] [nontrivial R] : ¬monic 0 := sorry

theorem ne_zero_of_monic {R : Type u} [semiring R] [nontrivial R] {p : polynomial R} (h : monic p) : p ≠ 0 :=
  fun (h₁ : p = 0) => not_monic_zero (h₁ ▸ h)

