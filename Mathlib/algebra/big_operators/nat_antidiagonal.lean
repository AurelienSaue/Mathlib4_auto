/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finset.nat_antidiagonal
import Mathlib.algebra.big_operators.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Big operators for `nat_antidiagonal`

This file contains theorems relevant to big operators over `finset.nat.antidiagonal`.
-/

namespace finset


namespace nat


theorem prod_antidiagonal_succ {M : Type u_1} [comm_monoid M] {n : ℕ} {f : ℕ × ℕ → M} : (finset.prod (antidiagonal (n + 1)) fun (p : ℕ × ℕ) => f p) =
  f (0, n + 1) * finset.prod (antidiagonal n) fun (p : ℕ × ℕ) => f (prod.fst p + 1, prod.snd p) := sorry

theorem sum_antidiagonal_succ {N : Type u_2} [add_comm_monoid N] {n : ℕ} {f : ℕ × ℕ → N} : (finset.sum (antidiagonal (n + 1)) fun (p : ℕ × ℕ) => f p) =
  f (0, n + 1) + finset.sum (antidiagonal n) fun (p : ℕ × ℕ) => f (prod.fst p + 1, prod.snd p) :=
  prod_antidiagonal_succ

theorem sum_antidiagonal_swap {M : Type u_1} [add_comm_monoid M] {n : ℕ} {f : ℕ × ℕ → M} : (finset.sum (antidiagonal n) fun (p : ℕ × ℕ) => f (prod.swap p)) = finset.sum (antidiagonal n) fun (p : ℕ × ℕ) => f p := sorry

theorem prod_antidiagonal_succ' {M : Type u_1} [comm_monoid M] {n : ℕ} {f : ℕ × ℕ → M} : (finset.prod (antidiagonal (n + 1)) fun (p : ℕ × ℕ) => f p) =
  f (n + 1, 0) * finset.prod (antidiagonal n) fun (p : ℕ × ℕ) => f (prod.fst p, prod.snd p + 1) := sorry

theorem sum_antidiagonal_succ' {N : Type u_2} [add_comm_monoid N] {n : ℕ} {f : ℕ × ℕ → N} : (finset.sum (antidiagonal (n + 1)) fun (p : ℕ × ℕ) => f p) =
  f (n + 1, 0) + finset.sum (antidiagonal n) fun (p : ℕ × ℕ) => f (prod.fst p, prod.snd p + 1) :=
  prod_antidiagonal_succ'

theorem prod_antidiagonal_subst {M : Type u_1} [comm_monoid M] {n : ℕ} {f : ℕ × ℕ → ℕ → M} : (finset.prod (antidiagonal n) fun (p : ℕ × ℕ) => f p n) =
  finset.prod (antidiagonal n) fun (p : ℕ × ℕ) => f p (prod.fst p + prod.snd p) := sorry

theorem prod_antidiagonal_eq_prod_range_succ {M : Type u_1} [comm_monoid M] (f : ℕ → ℕ → M) (n : ℕ) : (finset.prod (antidiagonal n) fun (ij : ℕ × ℕ) => f (prod.fst ij) (prod.snd ij)) =
  finset.prod (range (Nat.succ n)) fun (k : ℕ) => f k (n - k) := sorry

