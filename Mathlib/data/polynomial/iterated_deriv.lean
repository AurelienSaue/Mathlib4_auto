/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.derivative
import Mathlib.logic.function.iterate
import Mathlib.data.finset.intervals
import Mathlib.tactic.ring
import Mathlib.tactic.linarith.default
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Theory of iterated derivative
We define and prove some lemmas about iterated (formal) derivative for polynomials over a semiring.
-/

namespace polynomial


/-- `iterated_deriv f n` is the `n`-th formal derivative of the polynomial `f` -/
def iterated_deriv {R : Type u} [semiring R] (f : polynomial R) (n : ℕ) : polynomial R :=
  nat.iterate (⇑derivative) n f

@[simp] theorem iterated_deriv_zero_right {R : Type u} [semiring R] (f : polynomial R) : iterated_deriv f 0 = f :=
  rfl

theorem iterated_deriv_succ {R : Type u} [semiring R] (f : polynomial R) (n : ℕ) : iterated_deriv f (n + 1) = coe_fn derivative (iterated_deriv f n) := sorry

@[simp] theorem iterated_deriv_zero_left {R : Type u} [semiring R] (n : ℕ) : iterated_deriv 0 n = 0 := sorry

@[simp] theorem iterated_deriv_add {R : Type u} [semiring R] (p : polynomial R) (q : polynomial R) (n : ℕ) : iterated_deriv (p + q) n = iterated_deriv p n + iterated_deriv q n := sorry

@[simp] theorem iterated_deriv_smul {R : Type u} [semiring R] (r : R) (p : polynomial R) (n : ℕ) : iterated_deriv (r • p) n = r • iterated_deriv p n := sorry

@[simp] theorem iterated_deriv_X_zero {R : Type u} [semiring R] : iterated_deriv X 0 = X := sorry

@[simp] theorem iterated_deriv_X_one {R : Type u} [semiring R] : iterated_deriv X 1 = 1 := sorry

@[simp] theorem iterated_deriv_X {R : Type u} [semiring R] (n : ℕ) (h : 1 < n) : iterated_deriv X n = 0 := sorry

@[simp] theorem iterated_deriv_C_zero {R : Type u} [semiring R] (r : R) : iterated_deriv (coe_fn C r) 0 = coe_fn C r := sorry

@[simp] theorem iterated_deriv_C {R : Type u} [semiring R] (r : R) (n : ℕ) (h : 0 < n) : iterated_deriv (coe_fn C r) n = 0 := sorry

@[simp] theorem iterated_deriv_one_zero {R : Type u} [semiring R] : iterated_deriv 1 0 = 1 := sorry

@[simp] theorem iterated_deriv_one {R : Type u} [semiring R] (n : ℕ) : 0 < n → iterated_deriv 1 n = 0 := sorry

@[simp] theorem iterated_deriv_neg {R : Type u} [ring R] (p : polynomial R) (n : ℕ) : iterated_deriv (-p) n = -iterated_deriv p n := sorry

@[simp] theorem iterated_deriv_sub {R : Type u} [ring R] (p : polynomial R) (q : polynomial R) (n : ℕ) : iterated_deriv (p - q) n = iterated_deriv p n - iterated_deriv q n := sorry

theorem coeff_iterated_deriv_as_prod_Ico {R : Type u} [comm_semiring R] (f : polynomial R) (k : ℕ) (m : ℕ) : coeff (iterated_deriv f k) m =
  (finset.prod (finset.Ico (Nat.succ m) (m + Nat.succ k)) fun (i : ℕ) => ↑i) * coeff f (m + k) := sorry

theorem coeff_iterated_deriv_as_prod_range {R : Type u} [comm_semiring R] (f : polynomial R) (k : ℕ) (m : ℕ) : coeff (iterated_deriv f k) m = coeff f (m + k) * finset.prod (finset.range k) fun (i : ℕ) => ↑(m + k - i) := sorry

theorem iterated_deriv_eq_zero_of_nat_degree_lt {R : Type u} [comm_semiring R] (f : polynomial R) (n : ℕ) (h : nat_degree f < n) : iterated_deriv f n = 0 := sorry

theorem iterated_deriv_mul {R : Type u} [comm_semiring R] (p : polynomial R) (q : polynomial R) (n : ℕ) : iterated_deriv (p * q) n =
  finset.sum (finset.range (Nat.succ n))
    fun (k : ℕ) => coe_fn C ↑(nat.choose n k) * iterated_deriv p (n - k) * iterated_deriv q k := sorry

