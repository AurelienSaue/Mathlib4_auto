/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro

-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.sqrt
import Mathlib.data.nat.gcd
import Mathlib.algebra.group_power.default
import Mathlib.tactic.wlog
import Mathlib.tactic.norm_num
import PostPort

universes u_1 

namespace Mathlib

/-!
# Prime numbers

This file deals with prime numbers: natural numbers `p ≥ 2` whose only divisors are `p` and `1`.

## Important declarations

All the following declarations exist in the namespace `nat`.

- `prime`: the predicate that expresses that a natural number `p` is prime
- `primes`: the subtype of natural numbers that are prime
- `min_fac n`: the minimal prime factor of a natural number `n ≠ 1`
- `exists_infinite_primes`: Euclid's theorem that there exist infinitely many prime numbers
- `factors n`: the prime factorization of `n`
- `factors_unique`: uniqueness of the prime factorisation

-/

namespace nat


/-- `prime p` means that `p` is a prime number, that is, a natural number
  at least 2 whose only divisors are `p` and `1`. -/
def prime (p : ℕ)  :=
  bit0 1 ≤ p ∧ ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p

theorem prime.two_le {p : ℕ} : prime p → bit0 1 ≤ p :=
  and.left

theorem prime.one_lt {p : ℕ} : prime p → 1 < p :=
  prime.two_le

protected instance prime.one_lt' (p : ℕ) [hp : fact (prime p)] : fact (1 < p) :=
  prime.one_lt hp

theorem prime.ne_one {p : ℕ} (hp : prime p) : p ≠ 1 :=
  ne.symm (ne_of_lt (prime.one_lt hp))

theorem prime_def_lt {p : ℕ} : prime p ↔ bit0 1 ≤ p ∧ ∀ (m : ℕ), m < p → m ∣ p → m = 1 := sorry

theorem prime_def_lt' {p : ℕ} : prime p ↔ bit0 1 ≤ p ∧ ∀ (m : ℕ), bit0 1 ≤ m → m < p → ¬m ∣ p := sorry

theorem prime_def_le_sqrt {p : ℕ} : prime p ↔ bit0 1 ≤ p ∧ ∀ (m : ℕ), bit0 1 ≤ m → m ≤ sqrt p → ¬m ∣ p := sorry

/--
  This instance is slower than the instance `decidable_prime` defined below,
  but has the advantage that it works in the kernel.

  If you need to prove that a particular number is prime, in any case
  you should not use `dec_trivial`, but rather `by norm_num`, which is
  much faster.
  -/
def decidable_prime_1 (p : ℕ) : Decidable (prime p) :=
  decidable_of_iff' (bit0 1 ≤ p ∧ ∀ (m : ℕ), bit0 1 ≤ m → m < p → ¬m ∣ p) prime_def_lt'

theorem prime.ne_zero {n : ℕ} (h : prime n) : n ≠ 0 :=
  id fun (ᾰ : n = 0) => Eq._oldrec (fun (h : prime 0) => of_as_true trivial h) (Eq.symm ᾰ) h

theorem prime.pos {p : ℕ} (pp : prime p) : 0 < p :=
  lt_of_succ_lt (prime.one_lt pp)

theorem not_prime_zero : ¬prime 0 :=
  of_as_true trivial

theorem not_prime_one : ¬prime 1 :=
  of_as_true trivial

theorem prime_two : prime (bit0 1) :=
  of_as_true trivial

theorem prime_three : prime (bit1 1) :=
  of_as_true trivial

theorem prime.pred_pos {p : ℕ} (pp : prime p) : 0 < Nat.pred p :=
  iff.mpr lt_pred_iff (prime.one_lt pp)

theorem succ_pred_prime {p : ℕ} (pp : prime p) : Nat.succ (Nat.pred p) = p :=
  succ_pred_eq_of_pos (prime.pos pp)

theorem dvd_prime {p : ℕ} {m : ℕ} (pp : prime p) : m ∣ p ↔ m = 1 ∨ m = p := sorry

theorem dvd_prime_two_le {p : ℕ} {m : ℕ} (pp : prime p) (H : bit0 1 ≤ m) : m ∣ p ↔ m = p :=
  iff.trans (dvd_prime pp) (or_iff_right_of_imp (not.elim (ne_of_gt H)))

theorem prime_dvd_prime_iff_eq {p : ℕ} {q : ℕ} (pp : prime p) (qp : prime q) : p ∣ q ↔ p = q :=
  dvd_prime_two_le qp (prime.two_le pp)

theorem prime.not_dvd_one {p : ℕ} (pp : prime p) : ¬p ∣ 1 :=
  fun (ᾰ : p ∣ 1) => idRhs False (not_le_of_gt (prime.one_lt pp) (le_of_dvd (of_as_true trivial) ᾰ))

theorem not_prime_mul {a : ℕ} {b : ℕ} (a1 : 1 < a) (b1 : 1 < b) : ¬prime (a * b) := sorry

theorem not_prime_mul' {a : ℕ} {b : ℕ} {n : ℕ} (h : a * b = n) (h₁ : 1 < a) (h₂ : 1 < b) : ¬prime n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬prime n)) (Eq.symm h))) (not_prime_mul h₁ h₂)

def min_fac_aux (n : ℕ) : ℕ → ℕ :=
  sorry

def min_fac : ℕ → ℕ :=
  sorry

@[simp] theorem min_fac_zero : min_fac 0 = bit0 1 :=
  rfl

@[simp] theorem min_fac_one : min_fac 1 = 1 :=
  rfl

theorem min_fac_eq (n : ℕ) : min_fac n = ite (bit0 1 ∣ n) (bit0 1) (min_fac_aux n (bit1 1)) := sorry

theorem min_fac_aux_has_prop {n : ℕ} (n2 : bit0 1 ≤ n) (nd2 : ¬bit0 1 ∣ n) (k : ℕ) (i : ℕ) : k = bit0 1 * i + bit1 1 → (∀ (m : ℕ), bit0 1 ≤ m → m ∣ n → k ≤ m) → min_fac_prop n (min_fac_aux n k) := sorry

theorem min_fac_has_prop {n : ℕ} (n1 : n ≠ 1) : min_fac_prop n (min_fac n) := sorry

theorem min_fac_dvd (n : ℕ) : min_fac n ∣ n :=
  dite (n = 1) (fun (n1 : n = 1) => Eq.symm n1 ▸ of_as_true trivial)
    fun (n1 : ¬n = 1) => and.left (and.right (min_fac_has_prop n1))

theorem min_fac_prime {n : ℕ} (n1 : n ≠ 1) : prime (min_fac n) := sorry

theorem min_fac_le_of_dvd {n : ℕ} {m : ℕ} : bit0 1 ≤ m → m ∣ n → min_fac n ≤ m :=
  dite (n = 1) (fun (n1 : n = 1) (m : ℕ) (m2 : bit0 1 ≤ m) (d : m ∣ n) => Eq.symm n1 ▸ le_trans (of_as_true trivial) m2)
    fun (n1 : ¬n = 1) => and.right (and.right (min_fac_has_prop n1))

theorem min_fac_pos (n : ℕ) : 0 < min_fac n :=
  dite (n = 1) (fun (n1 : n = 1) => Eq.symm n1 ▸ of_as_true trivial) fun (n1 : ¬n = 1) => prime.pos (min_fac_prime n1)

theorem min_fac_le {n : ℕ} (H : 0 < n) : min_fac n ≤ n :=
  le_of_dvd H (min_fac_dvd n)

theorem prime_def_min_fac {p : ℕ} : prime p ↔ bit0 1 ≤ p ∧ min_fac p = p := sorry

protected instance decidable_prime (p : ℕ) : Decidable (prime p) :=
  decidable_of_iff' (bit0 1 ≤ p ∧ min_fac p = p) prime_def_min_fac

theorem not_prime_iff_min_fac_lt {n : ℕ} (n2 : bit0 1 ≤ n) : ¬prime n ↔ min_fac n < n :=
  iff.trans (not_congr (iff.trans prime_def_min_fac (and_iff_right n2)))
    (iff.symm (iff.trans lt_iff_le_and_ne (and_iff_right (min_fac_le (le_of_succ_le n2)))))

theorem min_fac_le_div {n : ℕ} (pos : 0 < n) (np : ¬prime n) : min_fac n ≤ n / min_fac n := sorry

theorem min_fac_sq_le_self {n : ℕ} (w : 0 < n) (h : ¬prime n) : min_fac n ^ bit0 1 ≤ n := sorry

@[simp] theorem min_fac_eq_one_iff {n : ℕ} : min_fac n = 1 ↔ n = 1 := sorry

@[simp] theorem min_fac_eq_two_iff (n : ℕ) : min_fac n = bit0 1 ↔ bit0 1 ∣ n := sorry

theorem exists_dvd_of_not_prime {n : ℕ} (n2 : bit0 1 ≤ n) (np : ¬prime n) : ∃ (m : ℕ), m ∣ n ∧ m ≠ 1 ∧ m ≠ n := sorry

theorem exists_dvd_of_not_prime2 {n : ℕ} (n2 : bit0 1 ≤ n) (np : ¬prime n) : ∃ (m : ℕ), m ∣ n ∧ bit0 1 ≤ m ∧ m < n :=
  Exists.intro (min_fac n)
    { left := min_fac_dvd n,
      right := { left := prime.two_le (min_fac_prime (ne_of_gt n2)), right := iff.mp (not_prime_iff_min_fac_lt n2) np } }

theorem exists_prime_and_dvd {n : ℕ} (n2 : bit0 1 ≤ n) : ∃ (p : ℕ), prime p ∧ p ∣ n :=
  Exists.intro (min_fac n) { left := min_fac_prime (ne_of_gt n2), right := min_fac_dvd n }

/-- Euclid's theorem. There exist infinitely many prime numbers.
Here given in the form: for every `n`, there exists a prime number `p ≥ n`. -/
theorem exists_infinite_primes (n : ℕ) : ∃ (p : ℕ), n ≤ p ∧ prime p := sorry

theorem prime.eq_two_or_odd {p : ℕ} (hp : prime p) : p = bit0 1 ∨ p % bit0 1 = 1 := sorry

theorem coprime_of_dvd {m : ℕ} {n : ℕ} (H : ∀ (k : ℕ), prime k → k ∣ m → ¬k ∣ n) : coprime m n := sorry

theorem coprime_of_dvd' {m : ℕ} {n : ℕ} (H : ∀ (k : ℕ), prime k → k ∣ m → k ∣ n → k ∣ 1) : coprime m n :=
  coprime_of_dvd
    fun (k : ℕ) (kp : prime k) (km : k ∣ m) (kn : k ∣ n) =>
      not_le_of_gt (prime.one_lt kp) (le_of_dvd zero_lt_one (H k kp km kn))

theorem factors_lemma {k : ℕ} : (k + bit0 1) / min_fac (k + bit0 1) < k + bit0 1 :=
  div_lt_self (of_as_true trivial) (prime.one_lt (min_fac_prime (of_as_true trivial)))

/-- `factors n` is the prime factorization of `n`, listed in increasing order. -/
def factors : ℕ → List ℕ :=
  sorry

theorem mem_factors {n : ℕ} {p : ℕ} : p ∈ factors n → prime p := sorry

theorem prod_factors {n : ℕ} : 0 < n → list.prod (factors n) = n := sorry

theorem factors_prime {p : ℕ} (hp : prime p) : factors p = [p] := sorry

/-- `factors` can be constructed inductively by extracting `min_fac`, for sufficiently large `n`. -/
theorem factors_add_two (n : ℕ) : factors (n + bit0 1) = min_fac (n + bit0 1) :: factors ((n + bit0 1) / min_fac (n + bit0 1)) :=
  rfl

theorem prime.coprime_iff_not_dvd {p : ℕ} {n : ℕ} (pp : prime p) : coprime p n ↔ ¬p ∣ n := sorry

theorem prime.dvd_iff_not_coprime {p : ℕ} {n : ℕ} (pp : prime p) : p ∣ n ↔ ¬coprime p n :=
  iff.mpr iff_not_comm (prime.coprime_iff_not_dvd pp)

theorem prime.not_coprime_iff_dvd {m : ℕ} {n : ℕ} : ¬coprime m n ↔ ∃ (p : ℕ), prime p ∧ p ∣ m ∧ p ∣ n := sorry

theorem prime.dvd_mul {p : ℕ} {m : ℕ} {n : ℕ} (pp : prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n := sorry

theorem prime.not_dvd_mul {p : ℕ} {m : ℕ} {n : ℕ} (pp : prime p) (Hm : ¬p ∣ m) (Hn : ¬p ∣ n) : ¬p ∣ m * n := sorry

theorem prime.dvd_of_dvd_pow {p : ℕ} {m : ℕ} {n : ℕ} (pp : prime p) (h : p ∣ m ^ n) : p ∣ m :=
  Nat.rec (fun (h : p ∣ m ^ 0) => not.elim (prime.not_dvd_one pp) h)
    (fun (n : ℕ) (IH : p ∣ m ^ n → p ∣ m) (h : p ∣ m ^ Nat.succ n) => or.elim (iff.mp (prime.dvd_mul pp) h) id IH) n h

theorem prime.pow_not_prime {x : ℕ} {n : ℕ} (hn : bit0 1 ≤ n) : ¬prime (x ^ n) := sorry

theorem prime.mul_eq_prime_pow_two_iff {x : ℕ} {y : ℕ} {p : ℕ} (hp : prime p) (hx : x ≠ 1) (hy : y ≠ 1) : x * y = p ^ bit0 1 ↔ x = p ∧ y = p := sorry

theorem prime.dvd_factorial {n : ℕ} {p : ℕ} (hp : prime p) : p ∣ factorial n ↔ p ≤ n := sorry

theorem prime.coprime_pow_of_not_dvd {p : ℕ} {m : ℕ} {a : ℕ} (pp : prime p) (h : ¬p ∣ a) : coprime a (p ^ m) :=
  coprime.pow_right m (coprime.symm (iff.mpr (prime.coprime_iff_not_dvd pp) h))

theorem coprime_primes {p : ℕ} {q : ℕ} (pp : prime p) (pq : prime q) : coprime p q ↔ p ≠ q :=
  iff.trans (prime.coprime_iff_not_dvd pp) (not_congr (dvd_prime_two_le pq (prime.two_le pp)))

theorem coprime_pow_primes {p : ℕ} {q : ℕ} (n : ℕ) (m : ℕ) (pp : prime p) (pq : prime q) (h : p ≠ q) : coprime (p ^ n) (q ^ m) :=
  coprime.pow n m (iff.mpr (coprime_primes pp pq) h)

theorem coprime_or_dvd_of_prime {p : ℕ} (pp : prime p) (i : ℕ) : coprime p i ∨ p ∣ i :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coprime p i ∨ p ∣ i)) (propext (prime.dvd_iff_not_coprime pp)))) (em (coprime p i))

theorem dvd_prime_pow {p : ℕ} (pp : prime p) {m : ℕ} {i : ℕ} : i ∣ p ^ m ↔ ∃ (k : ℕ), ∃ (H : k ≤ m), i = p ^ k := sorry

/--
If `p` is prime,
and `a` doesn't divide `p^k`, but `a` does divide `p^(k+1)`
then `a = p^(k+1)`.
-/
theorem eq_prime_pow_of_dvd_least_prime_pow {a : ℕ} {p : ℕ} {k : ℕ} (pp : prime p) (h₁ : ¬a ∣ p ^ k) (h₂ : a ∣ p ^ (k + 1)) : a = p ^ (k + 1) := sorry

theorem mem_list_primes_of_dvd_prod {p : ℕ} (hp : prime p) {l : List ℕ} : (∀ (p : ℕ), p ∈ l → prime p) → p ∣ list.prod l → p ∈ l := sorry

theorem mem_factors_iff_dvd {n : ℕ} {p : ℕ} (hn : 0 < n) (hp : prime p) : p ∈ factors n ↔ p ∣ n :=
  { mp := fun (h : p ∈ factors n) => prod_factors hn ▸ list.dvd_prod h,
    mpr := fun (h : p ∣ n) => mem_list_primes_of_dvd_prod hp mem_factors (Eq.symm (prod_factors hn) ▸ h) }

theorem perm_of_prod_eq_prod {l₁ : List ℕ} {l₂ : List ℕ} : list.prod l₁ = list.prod l₂ → (∀ (p : ℕ), p ∈ l₁ → prime p) → (∀ (p : ℕ), p ∈ l₂ → prime p) → l₁ ~ l₂ := sorry

theorem factors_unique {n : ℕ} {l : List ℕ} (h₁ : list.prod l = n) (h₂ : ∀ (p : ℕ), p ∈ l → prime p) : l ~ factors n := sorry

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : prime p) {m : ℕ} {n : ℕ} {k : ℕ} {l : ℕ} (hpm : p ^ k ∣ m) (hpn : p ^ l ∣ n) (hpmn : p ^ (k + l + 1) ∣ m * n) : p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n := sorry

/-- The type of prime numbers -/
def primes  :=
  Subtype fun (p : ℕ) => prime p

namespace primes


protected instance has_repr : has_repr primes :=
  has_repr.mk fun (p : primes) => repr (subtype.val p)

protected instance inhabited : Inhabited primes :=
  { default := { val := bit0 1, property := prime_two } }

protected instance coe_nat : has_coe primes ℕ :=
  has_coe.mk subtype.val

theorem coe_nat_inj (p : primes) (q : primes) : ↑p = ↑q → p = q :=
  fun (h : ↑p = ↑q) => subtype.eq h

end primes


protected instance monoid.prime_pow {α : Type u_1} [monoid α] : has_pow α primes :=
  has_pow.mk fun (x : α) (p : primes) => x ^ subtype.val p

end nat


/-! ### Primality prover -/

namespace tactic


namespace norm_num


theorem is_prime_helper (n : ℕ) (h₁ : 1 < n) (h₂ : nat.min_fac n = n) : nat.prime n :=
  iff.mpr nat.prime_def_min_fac { left := h₁, right := h₂ }

theorem min_fac_bit0 (n : ℕ) : nat.min_fac (bit0 n) = bit0 1 := sorry

/-- A predicate representing partial progress in a proof of `min_fac`. -/
def min_fac_helper (n : ℕ) (k : ℕ)  :=
  0 < k ∧ bit1 k ≤ nat.min_fac (bit1 n)

theorem min_fac_helper.n_pos {n : ℕ} {k : ℕ} (h : min_fac_helper n k) : 0 < n := sorry

theorem min_fac_ne_bit0 {n : ℕ} {k : ℕ} : nat.min_fac (bit1 n) ≠ bit0 k := sorry

theorem min_fac_helper_0 (n : ℕ) (h : 0 < n) : min_fac_helper n 1 := sorry

theorem min_fac_helper_1 {n : ℕ} {k : ℕ} {k' : ℕ} (e : k + 1 = k') (np : nat.min_fac (bit1 n) ≠ bit1 k) (h : min_fac_helper n k) : min_fac_helper n k' := sorry

theorem min_fac_helper_2 (n : ℕ) (k : ℕ) (k' : ℕ) (e : k + 1 = k') (np : ¬nat.prime (bit1 k)) (h : min_fac_helper n k) : min_fac_helper n k' := sorry

theorem min_fac_helper_3 (n : ℕ) (k : ℕ) (k' : ℕ) (c : ℕ) (e : k + 1 = k') (nc : bit1 n % bit1 k = c) (c0 : 0 < c) (h : min_fac_helper n k) : min_fac_helper n k' := sorry

theorem min_fac_helper_4 (n : ℕ) (k : ℕ) (hd : bit1 n % bit1 k = 0) (h : min_fac_helper n k) : nat.min_fac (bit1 n) = bit1 k := sorry

theorem min_fac_helper_5 (n : ℕ) (k : ℕ) (k' : ℕ) (e : bit1 k * bit1 k = k') (hd : bit1 n < k') (h : min_fac_helper n k) : nat.min_fac (bit1 n) = bit1 n := sorry

