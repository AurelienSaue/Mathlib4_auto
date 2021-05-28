/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.stream.basic
import Mathlib.tactic.default
import Mathlib.data.nat.gcd
import PostPort

namespace Mathlib

/-!
# The Fibonacci Sequence

## Summary

Definition of the Fibonacci sequence `F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`.

## Main Definitions

- `fib` returns the stream of Fibonacci numbers.

## Main Statements

- `fib_succ_succ` : shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.`.
- `fib_gcd`       : `fib n` is a strong divisibility sequence.

## Implementation Notes

For efficiency purposes, the sequence is defined using `stream.iterate`.

## Tags

fib, fibonacci
-/

namespace nat


/-- Auxiliary function used in the definition of `fib_aux_stream`. -/
/-- Auxiliary stream creating Fibonacci pairs `⟨Fₙ, Fₙ₊₁⟩`. -/
/--
Implementation of the fibonacci sequence satisfying
`fib 0 = 0, fib 1 = 1, fib (n + 2) = fib n + fib (n + 1)`.

*Note:* We use a stream iterator for better performance when compared to the naive recursive
implementation.
-/
def fib (n : ℕ) : ℕ :=
  prod.fst (fib_aux_stream n)

@[simp] theorem fib_zero : fib 0 = 0 :=
  rfl

@[simp] theorem fib_one : fib 1 = 1 :=
  rfl

@[simp] theorem fib_two : fib (bit0 1) = 1 :=
  rfl

/-- Shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.` -/
theorem fib_succ_succ {n : ℕ} : fib (n + bit0 1) = fib n + fib (n + 1) := sorry

theorem fib_pos {n : ℕ} (n_pos : 0 < n) : 0 < fib n := sorry

theorem fib_le_fib_succ {n : ℕ} : fib n ≤ fib (n + 1) := sorry

theorem fib_mono : monotone fib :=
  monotone_of_monotone_nat fun (_x : ℕ) => fib_le_fib_succ

theorem le_fib_self {n : ℕ} (five_le_n : bit1 (bit0 1) ≤ n) : n ≤ fib n := sorry

/-- Subsequent Fibonacci numbers are coprime,
  see https://proofwiki.org/wiki/Consecutive_Fibonacci_Numbers_are_Coprime -/
theorem fib_coprime_fib_succ (n : ℕ) : coprime (fib n) (fib (n + 1)) := sorry

/-- See https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers -/
theorem fib_add (m : ℕ) (n : ℕ) : fib m * fib n + fib (m + 1) * fib (n + 1) = fib (m + n + 1) := sorry

theorem gcd_fib_add_self (m : ℕ) (n : ℕ) : gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n) := sorry

theorem gcd_fib_add_mul_self (m : ℕ) (n : ℕ) (k : ℕ) : gcd (fib m) (fib (n + k * m)) = gcd (fib m) (fib n) := sorry

/-- `fib n` is a strong divisibility sequence,
  see https://proofwiki.org/wiki/GCD_of_Fibonacci_Numbers -/
theorem fib_gcd (m : ℕ) (n : ℕ) : fib (gcd m n) = gcd (fib m) (fib n) := sorry

theorem fib_dvd (m : ℕ) (n : ℕ) (h : m ∣ n) : fib m ∣ fib n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (fib m ∣ fib n)) (propext gcd_eq_left_iff_dvd)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd (fib m) (fib n) = fib m)) (Eq.symm (fib_gcd m n))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (fib (gcd m n) = fib m)) (iff.mp gcd_eq_left_iff_dvd h))) (Eq.refl (fib m))))

