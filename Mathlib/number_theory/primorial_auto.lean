/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.ring_exp
import Mathlib.data.nat.parity
import Mathlib.data.nat.choose.sum
import Mathlib.PostPort

namespace Mathlib

/-!
# Primorial

This file defines the primorial function (the product of primes less than or equal to some bound),
and proves that `primorial n ≤ 4 ^ n`.

## Notations

We use the local notation `n#` for the primorial of `n`: that is, the product of the primes less
than or equal to `n`.
-/

/-- The primorial `n#` of `n` is the product of the primes less than or equal to `n`.
-/
def primorial (n : ℕ) : ℕ :=
  finset.prod (finset.filter nat.prime (finset.range (n + 1))) fun (p : ℕ) => p

theorem primorial_succ {n : ℕ} (n_big : 1 < n) (r : n % bit0 1 = 1) :
    primorial (n + 1) = primorial n :=
  sorry

theorem dvd_choose_of_middling_prime (p : ℕ) (is_prime : nat.prime p) (m : ℕ) (p_big : m + 1 < p)
    (p_small : p ≤ bit0 1 * m + 1) : p ∣ nat.choose (bit0 1 * m + 1) (m + 1) :=
  sorry

theorem prod_primes_dvd {s : finset ℕ} (n : ℕ) (h : ∀ (a : ℕ), a ∈ s → nat.prime a)
    (div : ∀ (a : ℕ), a ∈ s → a ∣ n) : (finset.prod s fun (p : ℕ) => p) ∣ n :=
  sorry

theorem primorial_le_4_pow (n : ℕ) : primorial n ≤ bit0 (bit0 1) ^ n := sorry

end Mathlib