/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

Sums of finite geometric series
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group_with_zero.power
import Mathlib.algebra.big_operators.order
import Mathlib.algebra.big_operators.ring
import Mathlib.algebra.big_operators.intervals
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-- Sum of the finite geometric series $\sum_{i=0}^{n-1} x^i$. -/
def geom_series {α : Type u} [semiring α] (x : α) (n : ℕ) : α :=
  finset.sum (finset.range n) fun (i : ℕ) => x ^ i

theorem geom_series_def {α : Type u} [semiring α] (x : α) (n : ℕ) : geom_series x n = finset.sum (finset.range n) fun (i : ℕ) => x ^ i :=
  rfl

@[simp] theorem geom_series_zero {α : Type u} [semiring α] (x : α) : geom_series x 0 = 0 :=
  rfl

@[simp] theorem geom_series_one {α : Type u} [semiring α] (x : α) : geom_series x 1 = 1 := sorry

@[simp] theorem op_geom_series {α : Type u} [ring α] (x : α) (n : ℕ) : opposite.op (geom_series x n) = geom_series (opposite.op x) n := sorry

/-- Sum of the finite geometric series $\sum_{i=0}^{n-1} x^i y^{n-1-i}$. -/
def geom_series₂ {α : Type u} [semiring α] (x : α) (y : α) (n : ℕ) : α :=
  finset.sum (finset.range n) fun (i : ℕ) => x ^ i * y ^ (n - 1 - i)

theorem geom_series₂_def {α : Type u} [semiring α] (x : α) (y : α) (n : ℕ) : geom_series₂ x y n = finset.sum (finset.range n) fun (i : ℕ) => x ^ i * y ^ (n - 1 - i) :=
  rfl

@[simp] theorem geom_series₂_zero {α : Type u} [semiring α] (x : α) (y : α) : geom_series₂ x y 0 = 0 :=
  rfl

@[simp] theorem geom_series₂_one {α : Type u} [semiring α] (x : α) (y : α) : geom_series₂ x y 1 = 1 := sorry

@[simp] theorem geom_series₂_with_one {α : Type u} [semiring α] (x : α) (n : ℕ) : geom_series₂ x 1 n = geom_series x n := sorry

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
protected theorem commute.geom_sum₂_mul_add {α : Type u} [semiring α] {x : α} {y : α} (h : commute x y) (n : ℕ) : geom_series₂ (x + y) y n * x + y ^ n = (x + y) ^ n := sorry

theorem geom_series₂_self {α : Type u_1} [comm_ring α] (x : α) (n : ℕ) : geom_series₂ x x n = ↑n * x ^ (n - 1) := sorry

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
theorem geom_sum₂_mul_add {α : Type u} [comm_semiring α] (x : α) (y : α) (n : ℕ) : geom_series₂ (x + y) y n * x + y ^ n = (x + y) ^ n :=
  commute.geom_sum₂_mul_add (commute.all x y) n

theorem geom_sum_mul_add {α : Type u} [semiring α] (x : α) (n : ℕ) : geom_series (x + 1) n * x + 1 = (x + 1) ^ n :=
  eq.mp (Eq._oldrec (Eq.refl (geom_series₂ (x + 1) 1 n * x + 1 = (x + 1) ^ n)) (geom_series₂_with_one (x + 1) n))
    (eq.mp (Eq._oldrec (Eq.refl (geom_series₂ (x + 1) 1 n * x + 1 ^ n = (x + 1) ^ n)) (one_pow n))
      (commute.geom_sum₂_mul_add (commute.one_right x) n))

theorem geom_sum₂_mul_comm {α : Type u} [ring α] {x : α} {y : α} (h : commute x y) (n : ℕ) : geom_series₂ x y n * (x - y) = x ^ n - y ^ n := sorry

theorem geom_sum₂_mul {α : Type u} [comm_ring α] (x : α) (y : α) (n : ℕ) : geom_series₂ x y n * (x - y) = x ^ n - y ^ n :=
  geom_sum₂_mul_comm (commute.all x y) n

theorem geom_sum_mul {α : Type u} [ring α] (x : α) (n : ℕ) : geom_series x n * (x - 1) = x ^ n - 1 :=
  eq.mp (Eq._oldrec (Eq.refl (geom_series₂ x 1 n * (x - 1) = x ^ n - 1)) (geom_series₂_with_one x n))
    (eq.mp (Eq._oldrec (Eq.refl (geom_series₂ x 1 n * (x - 1) = x ^ n - 1 ^ n)) (one_pow n))
      (geom_sum₂_mul_comm (commute.one_right x) n))

theorem mul_geom_sum {α : Type u} [ring α] (x : α) (n : ℕ) : (x - 1) * geom_series x n = x ^ n - 1 := sorry

theorem geom_sum_mul_neg {α : Type u} [ring α] (x : α) (n : ℕ) : geom_series x n * (1 - x) = 1 - x ^ n := sorry

theorem mul_neg_geom_sum {α : Type u} [ring α] (x : α) (n : ℕ) : (1 - x) * geom_series x n = 1 - x ^ n := sorry

theorem geom_sum {α : Type u} [division_ring α] {x : α} (h : x ≠ 1) (n : ℕ) : geom_series x n = (x ^ n - 1) / (x - 1) := sorry

theorem geom_sum_Ico_mul {α : Type u} [ring α] (x : α) {m : ℕ} {n : ℕ} (hmn : m ≤ n) : (finset.sum (finset.Ico m n) fun (i : ℕ) => x ^ i) * (x - 1) = x ^ n - x ^ m := sorry

theorem geom_sum_Ico_mul_neg {α : Type u} [ring α] (x : α) {m : ℕ} {n : ℕ} (hmn : m ≤ n) : (finset.sum (finset.Ico m n) fun (i : ℕ) => x ^ i) * (1 - x) = x ^ m - x ^ n := sorry

theorem geom_sum_Ico {α : Type u} [division_ring α] {x : α} (hx : x ≠ 1) {m : ℕ} {n : ℕ} (hmn : m ≤ n) : (finset.sum (finset.Ico m n) fun (i : ℕ) => x ^ i) = (x ^ n - x ^ m) / (x - 1) := sorry

theorem geom_sum_inv {α : Type u} [division_ring α] {x : α} (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) : geom_series (x⁻¹) n = x - 1⁻¹ * (x - x⁻¹ ^ n * x) := sorry

theorem ring_hom.map_geom_series {α : Type u} {β : Type u_1} [semiring α] [semiring β] (x : α) (n : ℕ) (f : α →+* β) : coe_fn f (geom_series x n) = geom_series (coe_fn f x) n := sorry

theorem ring_hom.map_geom_series₂ {α : Type u} {β : Type u_1} [semiring α] [semiring β] (x : α) (y : α) (n : ℕ) (f : α →+* β) : coe_fn f (geom_series₂ x y n) = geom_series₂ (coe_fn f x) (coe_fn f y) n := sorry

