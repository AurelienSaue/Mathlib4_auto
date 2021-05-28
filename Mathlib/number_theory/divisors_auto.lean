/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.big_operators.order
import Mathlib.tactic.default
import Mathlib.data.nat.prime
import PostPort

universes u_1 

namespace Mathlib

/-!
# Divisor finsets

This file defines sets of divisors of a natural number. This is particularly useful as background
for defining Dirichlet convolution.

## Main Definitions
Let `n : ℕ`. All of the following definitions are in the `nat` namespace:
 * `divisors n` is the `finset` of natural numbers that divide `n`.
 * `proper_divisors n` is the `finset` of natural numbers that divide `n`, other than `n`.
 * `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.
 * `perfect n` is true when `n` is positive and the sum of `proper_divisors n` is `n`.

## Implementation details
 * `divisors 0`, `proper_divisors 0`, and `divisors_antidiagonal 0` are defined to be `∅`.

## Tags
divisors, perfect numbers

-/

namespace nat


/-- `divisors n` is the `finset` of divisors of `n`. As a special case, `divisors 0 = ∅`. -/
def divisors (n : ℕ) : finset ℕ :=
  finset.filter (fun (x : ℕ) => x ∣ n) (finset.Ico 1 (n + 1))

/-- `proper_divisors n` is the `finset` of divisors of `n`, other than `n`.
  As a special case, `proper_divisors 0 = ∅`. -/
def proper_divisors (n : ℕ) : finset ℕ :=
  finset.filter (fun (x : ℕ) => x ∣ n) (finset.Ico 1 n)

/-- `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.
  As a special case, `divisors_antidiagonal 0 = ∅`. -/
def divisors_antidiagonal (n : ℕ) : finset (ℕ × ℕ) :=
  finset.filter (fun (x : ℕ × ℕ) => prod.fst x * prod.snd x = n)
    (finset.product (finset.Ico 1 (n + 1)) (finset.Ico 1 (n + 1)))

theorem proper_divisors.not_self_mem {n : ℕ} : ¬n ∈ proper_divisors n := sorry

@[simp] theorem mem_proper_divisors {n : ℕ} {m : ℕ} : n ∈ proper_divisors m ↔ n ∣ m ∧ n < m := sorry

theorem divisors_eq_proper_divisors_insert_self_of_pos {n : ℕ} (h : 0 < n) : divisors n = insert n (proper_divisors n) := sorry

@[simp] theorem mem_divisors {n : ℕ} {m : ℕ} : n ∈ divisors m ↔ n ∣ m ∧ m ≠ 0 := sorry

theorem dvd_of_mem_divisors {n : ℕ} {m : ℕ} (h : n ∈ divisors m) : n ∣ m := sorry

@[simp] theorem mem_divisors_antidiagonal {n : ℕ} {x : ℕ × ℕ} : x ∈ divisors_antidiagonal n ↔ prod.fst x * prod.snd x = n ∧ n ≠ 0 := sorry

theorem divisor_le {n : ℕ} {m : ℕ} : n ∈ divisors m → n ≤ m := sorry

theorem divisors_subset_of_dvd {n : ℕ} {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) : divisors m ⊆ divisors n :=
  iff.mpr finset.subset_iff
    fun (x : ℕ) (hx : x ∈ divisors m) =>
      iff.mpr mem_divisors { left := dvd.trans (and.left (iff.mp mem_divisors hx)) h, right := hzero }

theorem divisors_subset_proper_divisors {n : ℕ} {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) (hdiff : m ≠ n) : divisors m ⊆ proper_divisors n := sorry

@[simp] theorem divisors_zero : divisors 0 = ∅ := sorry

@[simp] theorem proper_divisors_zero : proper_divisors 0 = ∅ := sorry

theorem proper_divisors_subset_divisors {n : ℕ} : proper_divisors n ⊆ divisors n := sorry

@[simp] theorem divisors_one : divisors 1 = singleton 1 := sorry

@[simp] theorem proper_divisors_one : proper_divisors 1 = ∅ := sorry

theorem pos_of_mem_divisors {n : ℕ} {m : ℕ} (h : m ∈ divisors n) : 0 < m := sorry

theorem pos_of_mem_proper_divisors {n : ℕ} {m : ℕ} (h : m ∈ proper_divisors n) : 0 < m :=
  pos_of_mem_divisors (proper_divisors_subset_divisors h)

theorem one_mem_proper_divisors_iff_one_lt {n : ℕ} : 1 ∈ proper_divisors n ↔ 1 < n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ∈ proper_divisors n ↔ 1 < n)) (propext mem_proper_divisors)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 ∣ n ∧ 1 < n ↔ 1 < n)) (propext (and_iff_right (one_dvd n))))) (iff.refl (1 < n)))

@[simp] theorem divisors_antidiagonal_zero : divisors_antidiagonal 0 = ∅ := sorry

@[simp] theorem divisors_antidiagonal_one : divisors_antidiagonal 1 = singleton (1, 1) := sorry

theorem swap_mem_divisors_antidiagonal {n : ℕ} {x : ℕ × ℕ} (h : x ∈ divisors_antidiagonal n) : prod.swap x ∈ divisors_antidiagonal n := sorry

theorem fst_mem_divisors_of_mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} (h : x ∈ divisors_antidiagonal n) : prod.fst x ∈ divisors n := sorry

theorem snd_mem_divisors_of_mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} (h : x ∈ divisors_antidiagonal n) : prod.snd x ∈ divisors n := sorry

@[simp] theorem map_swap_divisors_antidiagonal {n : ℕ} : finset.map (function.embedding.mk prod.swap (function.right_inverse.injective prod.swap_right_inverse))
    (divisors_antidiagonal n) =
  divisors_antidiagonal n := sorry

theorem sum_divisors_eq_sum_proper_divisors_add_self {n : ℕ} : (finset.sum (divisors n) fun (i : ℕ) => i) = (finset.sum (proper_divisors n) fun (i : ℕ) => i) + n := sorry

/-- `n : ℕ` is perfect if and only the sum of the proper divisors of `n` is `n` and `n`
  is positive. -/
def perfect (n : ℕ)  :=
  (finset.sum (proper_divisors n) fun (i : ℕ) => i) = n ∧ 0 < n

theorem perfect_iff_sum_proper_divisors {n : ℕ} (h : 0 < n) : perfect n ↔ (finset.sum (proper_divisors n) fun (i : ℕ) => i) = n :=
  and_iff_left h

theorem perfect_iff_sum_divisors_eq_two_mul {n : ℕ} (h : 0 < n) : perfect n ↔ (finset.sum (divisors n) fun (i : ℕ) => i) = bit0 1 * n := sorry

theorem mem_divisors_prime_pow {p : ℕ} (pp : prime p) (k : ℕ) {x : ℕ} : x ∈ divisors (p ^ k) ↔ ∃ (j : ℕ), ∃ (H : j ≤ k), x = p ^ j := sorry

theorem prime.divisors {p : ℕ} (pp : prime p) : divisors p = insert 1 (singleton p) := sorry

theorem prime.proper_divisors {p : ℕ} (pp : prime p) : proper_divisors p = singleton 1 := sorry

theorem divisors_prime_pow {p : ℕ} (pp : prime p) (k : ℕ) : divisors (p ^ k) =
  finset.map (function.embedding.mk (pow p) (pow_right_injective (prime.two_le pp))) (finset.range (k + 1)) := sorry

theorem eq_proper_divisors_of_subset_of_sum_eq_sum {n : ℕ} {s : finset ℕ} (hsub : s ⊆ proper_divisors n) : ((finset.sum s fun (x : ℕ) => x) = finset.sum (proper_divisors n) fun (x : ℕ) => x) → s = proper_divisors n := sorry

theorem sum_proper_divisors_dvd {n : ℕ} (h : (finset.sum (proper_divisors n) fun (x : ℕ) => x) ∣ n) : (finset.sum (proper_divisors n) fun (x : ℕ) => x) = 1 ∨ (finset.sum (proper_divisors n) fun (x : ℕ) => x) = n := sorry

@[simp] theorem prime.sum_proper_divisors {α : Type u_1} [add_comm_monoid α] {p : ℕ} {f : ℕ → α} (h : prime p) : (finset.sum (proper_divisors p) fun (x : ℕ) => f x) = f 1 := sorry

@[simp] theorem prime.sum_divisors {α : Type u_1} [add_comm_monoid α] {p : ℕ} {f : ℕ → α} (h : prime p) : (finset.sum (divisors p) fun (x : ℕ) => f x) = f p + f 1 := sorry

theorem proper_divisors_eq_singleton_one_iff_prime {n : ℕ} : proper_divisors n = singleton 1 ↔ prime n := sorry

theorem sum_proper_divisors_eq_one_iff_prime {n : ℕ} : (finset.sum (proper_divisors n) fun (x : ℕ) => x) = 1 ↔ prime n := sorry

@[simp] theorem prod_divisors_prime {α : Type u_1} [comm_monoid α] {p : ℕ} {f : ℕ → α} (h : prime p) : (finset.prod (divisors p) fun (x : ℕ) => f x) = f p * f 1 :=
  prime.sum_divisors h

@[simp] theorem sum_divisors_prime_pow {α : Type u_1} [add_comm_monoid α] {k : ℕ} {p : ℕ} {f : ℕ → α} (h : prime p) : (finset.sum (divisors (p ^ k)) fun (x : ℕ) => f x) = finset.sum (finset.range (k + 1)) fun (x : ℕ) => f (p ^ x) := sorry

@[simp] theorem prod_divisors_prime_pow {α : Type u_1} [comm_monoid α] {k : ℕ} {p : ℕ} {f : ℕ → α} (h : prime p) : (finset.prod (divisors (p ^ k)) fun (x : ℕ) => f x) = finset.prod (finset.range (k + 1)) fun (x : ℕ) => f (p ^ x) :=
  sum_divisors_prime_pow h

@[simp] theorem filter_dvd_eq_divisors {n : ℕ} (h : n ≠ 0) : finset.filter (fun (x : ℕ) => x ∣ n) (finset.range (Nat.succ n)) = divisors n := sorry

