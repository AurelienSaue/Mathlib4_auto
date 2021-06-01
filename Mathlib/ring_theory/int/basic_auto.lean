/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.int.gcd
import Mathlib.ring_theory.multiplicity
import Mathlib.ring_theory.principal_ideal_domain
import Mathlib.PostPort

namespace Mathlib

/-!
# Divisibility over ℕ and ℤ

This file collects results for the integers and natural numbers that use abstract algebra in
their proofs or cases of ℕ and ℤ being examples of structures in abstract algebra.

## Main statements

* `nat.prime_iff`: `nat.prime` coincides with the general definition of `prime`
* `nat.irreducible_iff_prime`: a non-unit natural number is only divisible by `1` iff it is prime
* `nat.factors_eq`: the multiset of elements of `nat.factors` is equal to the factors
   given by the `unique_factorization_monoid` instance
* ℤ is a `normalization_monoid`
* ℤ is a `gcd_monoid`

## Tags

prime, irreducible, natural numbers, integers, normalization monoid, gcd monoid,
greatest common divisor, prime factorization, prime factors, unique factorization,
unique factors
-/

theorem nat.prime_iff {p : ℕ} : nat.prime p ↔ prime p := sorry

theorem nat.irreducible_iff_prime {p : ℕ} : irreducible p ↔ prime p := sorry

namespace nat


protected instance wf_dvd_monoid : wf_dvd_monoid ℕ := sorry

protected instance unique_factorization_monoid : unique_factorization_monoid ℕ :=
  unique_factorization_monoid.mk fun (_x : ℕ) => irreducible_iff_prime

end nat


namespace int


protected instance normalization_monoid : normalization_monoid ℤ :=
  normalization_monoid.mk (fun (a : ℤ) => ite (0 ≤ a) 1 (-1)) sorry sorry sorry

theorem normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : coe_fn normalize z = z := sorry

theorem normalize_of_neg {z : ℤ} (h : z < 0) : coe_fn normalize z = -z := sorry

theorem normalize_coe_nat (n : ℕ) : coe_fn normalize ↑n = ↑n :=
  normalize_of_nonneg (coe_nat_le_coe_nat_of_le (nat.zero_le n))

theorem coe_nat_abs_eq_normalize (z : ℤ) : ↑(nat_abs z) = coe_fn normalize z := sorry

protected instance gcd_monoid : gcd_monoid ℤ :=
  gcd_monoid.mk norm_unit sorry sorry sorry (fun (a b : ℤ) => ↑(gcd a b))
    (fun (a b : ℤ) => ↑(lcm a b)) sorry sorry sorry sorry sorry sorry sorry

theorem coe_gcd (i : ℤ) (j : ℤ) : ↑(gcd i j) = gcd i j := rfl

theorem coe_lcm (i : ℤ) (j : ℤ) : ↑(lcm i j) = lcm i j := rfl

theorem nat_abs_gcd (i : ℤ) (j : ℤ) : nat_abs (gcd i j) = gcd i j := rfl

theorem nat_abs_lcm (i : ℤ) (j : ℤ) : nat_abs (lcm i j) = lcm i j := rfl

theorem exists_unit_of_abs (a : ℤ) : ∃ (u : ℤ), ∃ (h : is_unit u), ↑(nat_abs a) = u * a := sorry

theorem gcd_eq_one_iff_coprime {a : ℤ} {b : ℤ} : gcd a b = 1 ↔ is_coprime a b := sorry

theorem sqr_of_gcd_eq_one {a : ℤ} {b : ℤ} {c : ℤ} (h : gcd a b = 1) (heq : a * b = c ^ bit0 1) :
    ∃ (a0 : ℤ), a = a0 ^ bit0 1 ∨ a = -a0 ^ bit0 1 :=
  sorry

theorem sqr_of_coprime {a : ℤ} {b : ℤ} {c : ℤ} (h : is_coprime a b) (heq : a * b = c ^ bit0 1) :
    ∃ (a0 : ℤ), a = a0 ^ bit0 1 ∨ a = -a0 ^ bit0 1 :=
  sqr_of_gcd_eq_one (iff.mpr gcd_eq_one_iff_coprime h) heq

end int


theorem irreducible_iff_nat_prime (a : ℕ) : irreducible a ↔ nat.prime a := sorry

theorem nat.prime_iff_prime {p : ℕ} : nat.prime p ↔ prime p := sorry

theorem nat.prime_iff_prime_int {p : ℕ} : nat.prime p ↔ prime ↑p := sorry

/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
def associates_int_equiv_nat : associates ℤ ≃ ℕ :=
  equiv.mk (fun (z : associates ℤ) => int.nat_abs (associates.out z))
    (fun (n : ℕ) => associates.mk ↑n) sorry sorry

theorem int.prime.dvd_mul {m : ℤ} {n : ℤ} {p : ℕ} (hp : nat.prime p) (h : ↑p ∣ m * n) :
    p ∣ int.nat_abs m ∨ p ∣ int.nat_abs n :=
  iff.mp (nat.prime.dvd_mul hp)
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (p ∣ int.nat_abs m * int.nat_abs n)) (Eq.symm (int.nat_abs_mul m n))))
      (iff.mp int.coe_nat_dvd_left h))

theorem int.prime.dvd_mul' {m : ℤ} {n : ℤ} {p : ℕ} (hp : nat.prime p) (h : ↑p ∣ m * n) :
    ↑p ∣ m ∨ ↑p ∣ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑p ∣ m ∨ ↑p ∣ n)) (propext int.coe_nat_dvd_left)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (p ∣ int.nat_abs m ∨ ↑p ∣ n)) (propext int.coe_nat_dvd_left)))
      (int.prime.dvd_mul hp h))

theorem int.prime.dvd_pow {n : ℤ} {k : ℕ} {p : ℕ} (hp : nat.prime p) (h : ↑p ∣ n ^ k) :
    p ∣ int.nat_abs n :=
  nat.prime.dvd_of_dvd_pow hp
    (eq.mpr (id (Eq._oldrec (Eq.refl (p ∣ int.nat_abs n ^ k)) (Eq.symm (int.nat_abs_pow n k))))
      (iff.mp int.coe_nat_dvd_left h))

theorem int.prime.dvd_pow' {n : ℤ} {k : ℕ} {p : ℕ} (hp : nat.prime p) (h : ↑p ∣ n ^ k) : ↑p ∣ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑p ∣ n)) (propext int.coe_nat_dvd_left)))
    (int.prime.dvd_pow hp h)

theorem prime_two_or_dvd_of_dvd_two_mul_pow_self_two {m : ℤ} {p : ℕ} (hp : nat.prime p)
    (h : ↑p ∣ bit0 1 * m ^ bit0 1) : p = bit0 1 ∨ p ∣ int.nat_abs m :=
  sorry

protected instance nat.unique_units : unique (units ℕ) :=
  unique.mk { default := 1 } nat.units_eq_one

theorem nat.factors_eq {n : ℕ} : unique_factorization_monoid.factors n = ↑(nat.factors n) := sorry

theorem nat.factors_multiset_prod_of_irreducible {s : multiset ℕ}
    (h : ∀ (x : ℕ), x ∈ s → irreducible x) :
    unique_factorization_monoid.factors (multiset.prod s) = s :=
  sorry

namespace multiplicity


theorem finite_int_iff_nat_abs_finite {a : ℤ} {b : ℤ} :
    finite a b ↔ finite (int.nat_abs a) (int.nat_abs b) :=
  sorry

theorem finite_int_iff {a : ℤ} {b : ℤ} : finite a b ↔ int.nat_abs a ≠ 1 ∧ b ≠ 0 := sorry

protected instance decidable_nat : DecidableRel fun (a b : ℕ) => roption.dom (multiplicity a b) :=
  fun (a b : ℕ) => decidable_of_iff (a ≠ 1 ∧ 0 < b) sorry

protected instance decidable_int : DecidableRel fun (a b : ℤ) => roption.dom (multiplicity a b) :=
  fun (a b : ℤ) => decidable_of_iff (int.nat_abs a ≠ 1 ∧ b ≠ 0) sorry

end Mathlib