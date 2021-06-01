/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.bitwise
import Mathlib.data.nat.parity
import Mathlib.ring_theory.int.basic
import Mathlib.algebra.big_operators.intervals
import Mathlib.PostPort

namespace Mathlib

/-!

# Natural number multiplicity

This file contains lemmas about the multiplicity function (the maximum prime power divding a number).

# Main results

There are natural number versions of some basic lemmas about multiplicity.

There are also lemmas about the multiplicity of primes in factorials and in binomial coefficients.
-/

namespace nat


/-- The multiplicity of a divisor `m` of `n`, is the cardinality of the set of
  positive natural numbers `i` such that `p ^ i` divides `n`. The set is expressed
  by filtering `Ico 1 b` where `b` is any bound at least `n` -/
theorem multiplicity_eq_card_pow_dvd {m : ℕ} {n : ℕ} {b : ℕ} (hm1 : m ≠ 1) (hn0 : 0 < n)
    (hb : n ≤ b) :
    multiplicity m n = ↑(finset.card (finset.filter (fun (i : ℕ) => m ^ i ∣ n) (finset.Ico 1 b))) :=
  sorry

namespace prime


theorem multiplicity_one {p : ℕ} (hp : prime p) : multiplicity p 1 = 0 :=
  multiplicity.one_right (prime.not_unit (iff.mp prime_iff_prime hp))

theorem multiplicity_mul {p : ℕ} {m : ℕ} {n : ℕ} (hp : prime p) :
    multiplicity p (m * n) = multiplicity p m + multiplicity p n :=
  multiplicity.mul (iff.mp prime_iff_prime hp)

theorem multiplicity_pow {p : ℕ} {m : ℕ} {n : ℕ} (hp : prime p) :
    multiplicity p (m ^ n) = n •ℕ multiplicity p m :=
  multiplicity.pow (iff.mp prime_iff_prime hp)

theorem multiplicity_self {p : ℕ} (hp : prime p) : multiplicity p p = 1 :=
  multiplicity.multiplicity_self (prime.not_unit (iff.mp prime_iff_prime hp)) (ne_zero hp)

theorem multiplicity_pow_self {p : ℕ} {n : ℕ} (hp : prime p) : multiplicity p (p ^ n) = ↑n :=
  multiplicity.multiplicity_pow_self (ne_zero hp) (prime.not_unit (iff.mp prime_iff_prime hp)) n

/-- The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound at least `n` -/
theorem multiplicity_factorial {p : ℕ} (hp : prime p) {n : ℕ} {b : ℕ} :
    n ≤ b →
        multiplicity p (factorial n) = ↑(finset.sum (finset.Ico 1 b) fun (i : ℕ) => n / p ^ i) :=
  sorry

/-- The multiplicity of `p` in `(p(n+1))!` is one more than the sum
  of the multiplicities of `p` in `(p * n)!` and `n + 1`. -/
theorem multiplicity_factorial_mul_succ {n : ℕ} {p : ℕ} (hp : prime p) :
    multiplicity p (factorial (p * (n + 1))) =
        multiplicity p (factorial (p * n)) + multiplicity p (n + 1) + 1 :=
  sorry

/-- The multiplicity of `p` in `(pn)!` is `n` more than that of `n!`. -/
theorem multiplicity_factorial_mul {n : ℕ} {p : ℕ} (hp : prime p) :
    multiplicity p (factorial (p * n)) = multiplicity p (factorial n) + ↑n :=
  sorry

/-- A prime power divides `n!` iff it is at most the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound at least `n` -/
theorem pow_dvd_factorial_iff {p : ℕ} {n : ℕ} {r : ℕ} {b : ℕ} (hp : prime p) (hbn : n ≤ b) :
    p ^ r ∣ factorial n ↔ r ≤ finset.sum (finset.Ico 1 b) fun (i : ℕ) => n / p ^ i :=
  sorry

theorem multiplicity_choose_aux {p : ℕ} {n : ℕ} {b : ℕ} {k : ℕ} (hp : prime p) (hkn : k ≤ n) :
    (finset.sum (finset.Ico 1 b) fun (i : ℕ) => n / p ^ i) =
        ((finset.sum (finset.Ico 1 b) fun (i : ℕ) => k / p ^ i) +
            finset.sum (finset.Ico 1 b) fun (i : ℕ) => (n - k) / p ^ i) +
          finset.card
            (finset.filter (fun (i : ℕ) => p ^ i ≤ k % p ^ i + (n - k) % p ^ i) (finset.Ico 1 b)) :=
  sorry

/-- The multiplity of `p` in `choose n k` is the number of carries when `k` and `n - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound at least `n`. -/
theorem multiplicity_choose {p : ℕ} {n : ℕ} {k : ℕ} {b : ℕ} (hp : prime p) (hkn : k ≤ n)
    (hnb : n ≤ b) :
    multiplicity p (choose n k) =
        ↑(finset.card
            (finset.filter (fun (i : ℕ) => p ^ i ≤ k % p ^ i + (n - k) % p ^ i)
              (finset.Ico 1 b))) :=
  sorry

/-- A lower bound on the multiplicity of `p` in `choose n k`. -/
theorem multiplicity_le_multiplicity_choose_add {p : ℕ} (hp : prime p) (n : ℕ) (k : ℕ) :
    multiplicity p n ≤ multiplicity p (choose n k) + multiplicity p k :=
  sorry

theorem multiplicity_choose_prime_pow {p : ℕ} {n : ℕ} {k : ℕ} (hp : prime p) (hkn : k ≤ p ^ n)
    (hk0 : 0 < k) : multiplicity p (choose (p ^ n) k) + multiplicity p k = ↑n :=
  sorry

end prime


theorem multiplicity_two_factorial_lt {n : ℕ} (h : n ≠ 0) :
    multiplicity (bit0 1) (factorial n) < ↑n :=
  sorry

end Mathlib