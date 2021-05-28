/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Neil Strickland
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.prime
import Mathlib.data.pnat.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# Primality and GCD on pnat

This file extends the theory of `ℕ+` with `gcd`, `lcm` and `prime` functions, analogous to those on
`nat`.
-/

namespace nat.primes


protected instance coe_pnat : has_coe primes ℕ+ :=
  has_coe.mk fun (p : primes) => { val := ↑p, property := sorry }

theorem coe_pnat_nat (p : primes) : ↑↑p = ↑p :=
  rfl

theorem coe_pnat_inj (p : primes) (q : primes) : ↑p = ↑q → p = q := sorry

end nat.primes


namespace pnat


/-- The greatest common divisor (gcd) of two positive natural numbers,
  viewed as positive natural number. -/
def gcd (n : ℕ+) (m : ℕ+) : ℕ+ :=
  { val := nat.gcd ↑n ↑m, property := sorry }

/-- The least common multiple (lcm) of two positive natural numbers,
  viewed as positive natural number. -/
def lcm (n : ℕ+) (m : ℕ+) : ℕ+ :=
  { val := nat.lcm ↑n ↑m, property := sorry }

@[simp] theorem gcd_coe (n : ℕ+) (m : ℕ+) : ↑(gcd n m) = nat.gcd ↑n ↑m :=
  rfl

@[simp] theorem lcm_coe (n : ℕ+) (m : ℕ+) : ↑(lcm n m) = nat.lcm ↑n ↑m :=
  rfl

theorem gcd_dvd_left (n : ℕ+) (m : ℕ+) : gcd n m ∣ n :=
  iff.mpr dvd_iff (nat.gcd_dvd_left ↑n ↑m)

theorem gcd_dvd_right (n : ℕ+) (m : ℕ+) : gcd n m ∣ m :=
  iff.mpr dvd_iff (nat.gcd_dvd_right ↑n ↑m)

theorem dvd_gcd {m : ℕ+} {n : ℕ+} {k : ℕ+} (hm : k ∣ m) (hn : k ∣ n) : k ∣ gcd m n :=
  iff.mpr dvd_iff (nat.dvd_gcd (iff.mp dvd_iff hm) (iff.mp dvd_iff hn))

theorem dvd_lcm_left (n : ℕ+) (m : ℕ+) : n ∣ lcm n m :=
  iff.mpr dvd_iff (nat.dvd_lcm_left ↑n ↑m)

theorem dvd_lcm_right (n : ℕ+) (m : ℕ+) : m ∣ lcm n m :=
  iff.mpr dvd_iff (nat.dvd_lcm_right ↑n ↑m)

theorem lcm_dvd {m : ℕ+} {n : ℕ+} {k : ℕ+} (hm : m ∣ k) (hn : n ∣ k) : lcm m n ∣ k :=
  iff.mpr dvd_iff (nat.lcm_dvd (iff.mp dvd_iff hm) (iff.mp dvd_iff hn))

theorem gcd_mul_lcm (n : ℕ+) (m : ℕ+) : gcd n m * lcm n m = n * m :=
  subtype.eq (nat.gcd_mul_lcm ↑n ↑m)

theorem eq_one_of_lt_two {n : ℕ+} : n < bit0 1 → n = 1 :=
  fun (h : n < bit0 1) =>
    le_antisymm (id (fun (h : n < 1 + 1) => eq.mp (Eq._oldrec (Eq.refl (n < 1 + 1)) (propext lt_add_one_iff)) h) h)
      (one_le n)

/-! ### Prime numbers -/

/-- Primality predicate for `ℕ+`, defined in terms of `nat.prime`. -/
def prime (p : ℕ+)  :=
  nat.prime ↑p

theorem prime.one_lt {p : ℕ+} : prime p → 1 < p :=
  nat.prime.one_lt

theorem prime_two : prime (bit0 1) :=
  nat.prime_two

theorem dvd_prime {p : ℕ+} {m : ℕ+} (pp : prime p) : m ∣ p ↔ m = 1 ∨ m = p := sorry

theorem prime.ne_one {p : ℕ+} : prime p → p ≠ 1 := sorry

@[simp] theorem not_prime_one : ¬prime 1 :=
  nat.not_prime_one

theorem prime.not_dvd_one {p : ℕ+} : prime p → ¬p ∣ 1 :=
  fun (pp : prime p) => eq.mpr (id (Eq._oldrec (Eq.refl (¬p ∣ 1)) (propext dvd_iff))) (nat.prime.not_dvd_one pp)

theorem exists_prime_and_dvd {n : ℕ+} : bit0 1 ≤ n → ∃ (p : ℕ+), prime p ∧ p ∣ n := sorry

/-! ### Coprime numbers and gcd -/

/-- Two pnats are coprime if their gcd is 1. -/
def coprime (m : ℕ+) (n : ℕ+)  :=
  gcd m n = 1

@[simp] theorem coprime_coe {m : ℕ+} {n : ℕ+} : nat.coprime ↑m ↑n ↔ coprime m n := sorry

theorem coprime.mul {k : ℕ+} {m : ℕ+} {n : ℕ+} : coprime m k → coprime n k → coprime (m * n) k := sorry

theorem coprime.mul_right {k : ℕ+} {m : ℕ+} {n : ℕ+} : coprime k m → coprime k n → coprime k (m * n) := sorry

theorem gcd_comm {m : ℕ+} {n : ℕ+} : gcd m n = gcd n m := sorry

theorem gcd_eq_left_iff_dvd {m : ℕ+} {n : ℕ+} : m ∣ n ↔ gcd m n = m := sorry

theorem gcd_eq_right_iff_dvd {m : ℕ+} {n : ℕ+} : m ∣ n ↔ gcd n m = m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m ∣ n ↔ gcd n m = m)) gcd_comm)) gcd_eq_left_iff_dvd

theorem coprime.gcd_mul_left_cancel (m : ℕ+) {n : ℕ+} {k : ℕ+} : coprime k n → gcd (k * m) n = gcd m n := sorry

theorem coprime.gcd_mul_right_cancel (m : ℕ+) {n : ℕ+} {k : ℕ+} : coprime k n → gcd (m * k) n = gcd m n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coprime k n → gcd (m * k) n = gcd m n)) (mul_comm m k)))
    (coprime.gcd_mul_left_cancel m)

theorem coprime.gcd_mul_left_cancel_right (m : ℕ+) {n : ℕ+} {k : ℕ+} : coprime k m → gcd m (k * n) = gcd m n := sorry

theorem coprime.gcd_mul_right_cancel_right (m : ℕ+) {n : ℕ+} {k : ℕ+} : coprime k m → gcd m (n * k) = gcd m n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coprime k m → gcd m (n * k) = gcd m n)) (mul_comm n k)))
    (coprime.gcd_mul_left_cancel_right m)

@[simp] theorem one_gcd {n : ℕ+} : gcd 1 n = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd 1 n = 1)) (Eq.symm (propext gcd_eq_left_iff_dvd)))) (one_dvd n)

@[simp] theorem gcd_one {n : ℕ+} : gcd n 1 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd n 1 = 1)) gcd_comm)) one_gcd

theorem coprime.symm {m : ℕ+} {n : ℕ+} : coprime m n → coprime n m :=
  eq.mpr (id (imp_congr_eq (coprime.equations._eqn_1 m n) (coprime.equations._eqn_1 n m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd m n = 1 → gcd n m = 1)) gcd_comm)) (eq.mpr (id (propext imp_self)) trivial))

@[simp] theorem one_coprime {n : ℕ+} : coprime 1 n :=
  one_gcd

@[simp] theorem coprime_one {n : ℕ+} : coprime n 1 :=
  coprime.symm one_coprime

theorem coprime.coprime_dvd_left {m : ℕ+} {k : ℕ+} {n : ℕ+} : m ∣ k → coprime k n → coprime m n := sorry

theorem coprime.factor_eq_gcd_left {a : ℕ+} {b : ℕ+} {m : ℕ+} {n : ℕ+} (cop : coprime m n) (am : a ∣ m) (bn : b ∣ n) : a = gcd (a * b) m := sorry

theorem coprime.factor_eq_gcd_right {a : ℕ+} {b : ℕ+} {m : ℕ+} {n : ℕ+} (cop : coprime m n) (am : a ∣ m) (bn : b ∣ n) : a = gcd (b * a) m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = gcd (b * a) m)) (mul_comm b a))) (coprime.factor_eq_gcd_left cop am bn)

theorem coprime.factor_eq_gcd_left_right {a : ℕ+} {b : ℕ+} {m : ℕ+} {n : ℕ+} (cop : coprime m n) (am : a ∣ m) (bn : b ∣ n) : a = gcd m (a * b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = gcd m (a * b))) gcd_comm)) (coprime.factor_eq_gcd_left cop am bn)

theorem coprime.factor_eq_gcd_right_right {a : ℕ+} {b : ℕ+} {m : ℕ+} {n : ℕ+} (cop : coprime m n) (am : a ∣ m) (bn : b ∣ n) : a = gcd m (b * a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = gcd m (b * a))) gcd_comm)) (coprime.factor_eq_gcd_right cop am bn)

theorem coprime.gcd_mul (k : ℕ+) {m : ℕ+} {n : ℕ+} (h : coprime m n) : gcd k (m * n) = gcd k m * gcd k n := sorry

theorem gcd_eq_left {m : ℕ+} {n : ℕ+} : m ∣ n → gcd m n = m := sorry

theorem coprime.pow {m : ℕ+} {n : ℕ+} (k : ℕ) (l : ℕ) (h : coprime m n) : coprime (m ^ k) (n ^ l) := sorry

