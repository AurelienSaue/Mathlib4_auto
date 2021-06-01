/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.ordered_ring
import Mathlib.data.int.basic
import Mathlib.tactic.norm_num
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Lemmas for `linarith`

This file contains auxiliary lemmas that `linarith` uses to construct proofs.
If you find yourself looking for a theorem here, you might be in the wrong place.
-/

namespace linarith


theorem int.coe_nat_bit0 (n : ℕ) : ↑(bit0 n) = bit0 ↑n := sorry

theorem int.coe_nat_bit1 (n : ℕ) : ↑(bit1 n) = bit1 ↑n := sorry

theorem int.coe_nat_bit0_mul (n : ℕ) (x : ℕ) : ↑(bit0 n * x) = ↑(bit0 n) * ↑x := sorry

theorem int.coe_nat_bit1_mul (n : ℕ) (x : ℕ) : ↑(bit1 n * x) = ↑(bit1 n) * ↑x := sorry

theorem int.coe_nat_one_mul (x : ℕ) : ↑(1 * x) = 1 * ↑x := sorry

theorem int.coe_nat_zero_mul (x : ℕ) : ↑(0 * x) = 0 * ↑x := sorry

theorem int.coe_nat_mul_bit0 (n : ℕ) (x : ℕ) : ↑(x * bit0 n) = ↑x * ↑(bit0 n) := sorry

theorem int.coe_nat_mul_bit1 (n : ℕ) (x : ℕ) : ↑(x * bit1 n) = ↑x * ↑(bit1 n) := sorry

theorem int.coe_nat_mul_one (x : ℕ) : ↑(x * 1) = ↑x * 1 := sorry

theorem int.coe_nat_mul_zero (x : ℕ) : ↑(x * 0) = ↑x * 0 := sorry

theorem nat_eq_subst {n1 : ℕ} {n2 : ℕ} {z1 : ℤ} {z2 : ℤ} (hn : n1 = n2) (h1 : ↑n1 = z1)
    (h2 : ↑n2 = z2) : z1 = z2 :=
  sorry

theorem nat_le_subst {n1 : ℕ} {n2 : ℕ} {z1 : ℤ} {z2 : ℤ} (hn : n1 ≤ n2) (h1 : ↑n1 = z1)
    (h2 : ↑n2 = z2) : z1 ≤ z2 :=
  sorry

theorem nat_lt_subst {n1 : ℕ} {n2 : ℕ} {z1 : ℤ} {z2 : ℤ} (hn : n1 < n2) (h1 : ↑n1 = z1)
    (h2 : ↑n2 = z2) : z1 < z2 :=
  sorry

theorem eq_of_eq_of_eq {α : Type u_1} [ordered_semiring α] {a : α} {b : α} (ha : a = 0)
    (hb : b = 0) : a + b = 0 :=
  sorry

theorem le_of_eq_of_le {α : Type u_1} [ordered_semiring α] {a : α} {b : α} (ha : a = 0)
    (hb : b ≤ 0) : a + b ≤ 0 :=
  sorry

theorem lt_of_eq_of_lt {α : Type u_1} [ordered_semiring α] {a : α} {b : α} (ha : a = 0)
    (hb : b < 0) : a + b < 0 :=
  sorry

theorem le_of_le_of_eq {α : Type u_1} [ordered_semiring α] {a : α} {b : α} (ha : a ≤ 0)
    (hb : b = 0) : a + b ≤ 0 :=
  sorry

theorem lt_of_lt_of_eq {α : Type u_1} [ordered_semiring α] {a : α} {b : α} (ha : a < 0)
    (hb : b = 0) : a + b < 0 :=
  sorry

theorem mul_neg {α : Type u_1} [ordered_ring α] {a : α} {b : α} (ha : a < 0) (hb : 0 < b) :
    b * a < 0 :=
  sorry

theorem mul_nonpos {α : Type u_1} [ordered_ring α] {a : α} {b : α} (ha : a ≤ 0) (hb : 0 < b) :
    b * a ≤ 0 :=
  sorry

-- used alongside `mul_neg` and `mul_nonpos`, so has the same argument pattern for uniformity

theorem mul_eq {α : Type u_1} [ordered_semiring α] {a : α} {b : α} (ha : a = 0) (hb : 0 < b) :
    b * a = 0 :=
  sorry

theorem eq_of_not_lt_of_not_gt {α : Type u_1} [linear_order α] (a : α) (b : α) (h1 : ¬a < b)
    (h2 : ¬b < a) : a = b :=
  le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.

theorem mul_zero_eq {α : Type u_1} {R : α → α → Prop} [semiring α] {a : α} {b : α} (_x : R a 0)
    (h : b = 0) : a * b = 0 :=
  sorry

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.

theorem zero_mul_eq {α : Type u_1} {R : α → α → Prop} [semiring α] {a : α} {b : α} (h : a = 0)
    (_x : R b 0) : a * b = 0 :=
  sorry

end Mathlib