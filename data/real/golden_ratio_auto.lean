/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Alexey Soloyev, Junyan Xu
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.real.irrational
import Mathlib.data.nat.fib
import Mathlib.data.matrix.notation
import Mathlib.tactic.ring_exp
import Mathlib.algebra.linear_recurrence
import PostPort

universes u_1 

namespace Mathlib

/-!
# The golden ratio and its conjugate

This file defines the golden ratio `φ := (1 + √5)/2` and its conjugate
`ψ := (1 - √5)/2`, which are the two real roots of `X² - X - 1`.

Along with various computational facts about them, we prove their
irrationality, and we link them to the Fibonacci sequence by proving
Binet's formula.
-/

/-- The golden ratio `φ := (1 + √5)/2`. -/
def golden_ratio : ℝ :=
  (1 + real.sqrt (bit1 (bit0 1))) / bit0 1

/-- The conjugate of the golden ratio `ψ := (1 - √5)/2`. -/
def golden_conj : ℝ :=
  (1 - real.sqrt (bit1 (bit0 1))) / bit0 1

/-- The inverse of the golden ratio is the opposite of its conjugate. -/
theorem inv_gold : golden_ratio⁻¹ = -golden_conj := sorry

/-- The opposite of the golden ratio is the inverse of its conjugate. -/
theorem inv_gold_conj : golden_conj⁻¹ = -golden_ratio := sorry

@[simp] theorem gold_mul_gold_conj : golden_ratio * golden_conj = -1 := sorry

@[simp] theorem gold_conj_mul_gold : golden_conj * golden_ratio = -1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (golden_conj * golden_ratio = -1)) (mul_comm golden_conj golden_ratio)))
    gold_mul_gold_conj

@[simp] theorem gold_add_gold_conj : golden_ratio + golden_conj = 1 := sorry

theorem one_sub_gold_conj : 1 - golden_ratio = golden_conj := sorry

theorem one_sub_gold : 1 - golden_conj = golden_ratio := sorry

@[simp] theorem gold_sub_gold_conj : golden_ratio - golden_conj = real.sqrt (bit1 (bit0 1)) := sorry

@[simp] theorem gold_sq : golden_ratio ^ bit0 1 = golden_ratio + 1 := sorry

@[simp] theorem gold_conj_sq : golden_conj ^ bit0 1 = golden_conj + 1 := sorry

theorem gold_pos : 0 < golden_ratio := sorry

theorem gold_ne_zero : golden_ratio ≠ 0 :=
  ne_of_gt gold_pos

theorem one_lt_gold : 1 < golden_ratio := sorry

theorem gold_conj_neg : golden_conj < 0 := sorry

theorem gold_conj_ne_zero : golden_conj ≠ 0 :=
  ne_of_lt gold_conj_neg

theorem neg_one_lt_gold_conj : -1 < golden_conj :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-1 < golden_conj)) (propext neg_lt)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-golden_conj < 1)) (Eq.symm inv_gold))) (inv_lt_one one_lt_gold))

/-!
## Irrationality
-/

/-- The golden ratio is irrational. -/
theorem gold_irrational : irrational golden_ratio := sorry

/-- The conjugate of the golden ratio is irrational. -/
theorem gold_conj_irrational : irrational golden_conj := sorry

/-!
## Links with Fibonacci sequence
-/

/-- The recurrence relation satisfied by the Fibonacci sequence. -/
def fib_rec {α : Type u_1} [comm_semiring α] : linear_recurrence α :=
  linear_recurrence.mk (bit0 1) (matrix.vec_cons 1 (matrix.vec_cons 1 matrix.vec_empty))

/-- The characteristic polynomial of `fib_rec` is `X² - (X + 1)`. -/
theorem fib_rec_char_poly_eq {β : Type u_1} [comm_ring β] : linear_recurrence.char_poly fib_rec = polynomial.X ^ bit0 1 - (polynomial.X + 1) := sorry

/-- As expected, the Fibonacci sequence is a solution of `fib_rec`. -/
theorem fib_is_sol_fib_rec {α : Type u_1} [comm_semiring α] : linear_recurrence.is_solution fib_rec fun (x : ℕ) => ↑(nat.fib x) := sorry

/-- The geometric sequence `λ n, φ^n` is a solution of `fib_rec`. -/
theorem geom_gold_is_sol_fib_rec : linear_recurrence.is_solution fib_rec (pow golden_ratio) := sorry

/-- The geometric sequence `λ n, ψ^n` is a solution of `fib_rec`. -/
theorem geom_gold_conj_is_sol_fib_rec : linear_recurrence.is_solution fib_rec (pow golden_conj) := sorry

/-- Binet's formula as a function equality. -/
theorem real.coe_fib_eq' : (fun (n : ℕ) => ↑(nat.fib n)) = fun (n : ℕ) => (golden_ratio ^ n - golden_conj ^ n) / real.sqrt (bit1 (bit0 1)) := sorry

/-- Binet's formula as a dependent equality. -/
theorem real.coe_fib_eq (n : ℕ) : ↑(nat.fib n) = (golden_ratio ^ n - golden_conj ^ n) / real.sqrt (bit1 (bit0 1)) := sorry

