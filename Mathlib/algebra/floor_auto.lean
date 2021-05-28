/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.linarith.default
import Mathlib.tactic.abel
import Mathlib.algebra.ordered_group
import Mathlib.data.set.intervals.basic
import PostPort

universes u_2 l u_1 

namespace Mathlib

/-!
# Floor and Ceil

## Summary

We define `floor`, `ceil`, and `nat_ceil` functions on linear ordered rings.

## Main Definitions

- `floor_ring` is a linear ordered ring with floor function.
- `floor x` is the greatest integer `z` such that `z ≤ x`.
- `fract x` is the fractional part of x, that is `x - floor x`.
- `ceil x` is the smallest integer `z` such that `x ≤ z`.
- `nat_ceil x` is the smallest nonnegative integer `n` with `x ≤ n`.

## Notations

- `⌊x⌋` is `floor x`.
- `⌈x⌉` is `ceil x`.

## Tags

rounding
-/

/--
A `floor_ring` is a linear ordered ring over `α` with a function
`floor : α → ℤ` satisfying `∀ (z : ℤ) (x : α), z ≤ floor x ↔ (z : α) ≤ x)`.
-/
class floor_ring (α : Type u_2) [linear_ordered_ring α] 
where
  floor : α → ℤ
  le_floor : ∀ (z : ℤ) (x : α), z ≤ floor x ↔ ↑z ≤ x

protected instance int.floor_ring : floor_ring ℤ :=
  floor_ring.mk id sorry

/-- `floor x` is the greatest integer `z` such that `z ≤ x` -/
def floor {α : Type u_1} [linear_ordered_ring α] [floor_ring α] : α → ℤ :=
  floor_ring.floor

theorem le_floor {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {z : ℤ} {x : α} : z ≤ floor x ↔ ↑z ≤ x :=
  floor_ring.le_floor

theorem floor_lt {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {x : α} {z : ℤ} : floor x < z ↔ x < ↑z :=
  lt_iff_lt_of_le_iff_le le_floor

theorem floor_le {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) : ↑(floor x) ≤ x :=
  iff.mp le_floor (le_refl (floor x))

theorem floor_nonneg {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {x : α} : 0 ≤ floor x ↔ 0 ≤ x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ floor x ↔ 0 ≤ x)) (propext le_floor))) (iff.refl (↑0 ≤ x))

theorem lt_succ_floor {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) : x < ↑(int.succ (floor x)) :=
  iff.mp floor_lt (int.lt_succ_self (floor x))

theorem lt_floor_add_one {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) : x < ↑(floor x) + 1 := sorry

theorem sub_one_lt_floor {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) : x - 1 < ↑(floor x) :=
  iff.mpr sub_lt_iff_lt_add (lt_floor_add_one x)

@[simp] theorem floor_coe {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (z : ℤ) : floor ↑z = z := sorry

@[simp] theorem floor_zero {α : Type u_1} [linear_ordered_ring α] [floor_ring α] : floor 0 = 0 :=
  floor_coe 0

@[simp] theorem floor_one {α : Type u_1} [linear_ordered_ring α] [floor_ring α] : floor 1 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (floor 1 = 1)) (Eq.symm int.cast_one)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (floor ↑1 = 1)) (floor_coe 1))) (Eq.refl 1))

theorem floor_mono {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {a : α} {b : α} (h : a ≤ b) : floor a ≤ floor b :=
  iff.mpr le_floor (le_trans (floor_le a) h)

@[simp] theorem floor_add_int {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) (z : ℤ) : floor (x + ↑z) = floor x + z := sorry

theorem floor_sub_int {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) (z : ℤ) : floor (x - ↑z) = floor x - z := sorry

theorem abs_sub_lt_one_of_floor_eq_floor {α : Type u_1} [linear_ordered_comm_ring α] [floor_ring α] {x : α} {y : α} (h : floor x = floor y) : abs (x - y) < 1 := sorry

theorem floor_eq_iff {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {r : α} {z : ℤ} : floor r = z ↔ ↑z ≤ r ∧ r < ↑z + 1 := sorry

theorem floor_ring_unique {α : Type u_1} [linear_ordered_ring α] (inst1 : floor_ring α) (inst2 : floor_ring α) : floor = floor := sorry

theorem floor_eq_on_Ico {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (n : ℤ) (x : α) (H : x ∈ set.Ico (↑n) (↑n + 1)) : floor x = n := sorry

theorem floor_eq_on_Ico' {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (n : ℤ) (x : α) (H : x ∈ set.Ico (↑n) (↑n + 1)) : ↑(floor x) = ↑n :=
  eq.mpr (id (propext int.cast_inj)) (floor_eq_on_Ico n x hx)

/-- The fractional part fract r of r is just r - ⌊r⌋ -/
def fract {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (r : α) : α :=
  r - ↑(floor r)

-- Mathematical notation is usually {r}. Let's not even go there.

@[simp] theorem floor_add_fract {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (r : α) : ↑(floor r) + fract r = r := sorry

@[simp] theorem fract_add_floor {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (r : α) : fract r + ↑(floor r) = r :=
  sub_add_cancel r ↑(floor r)

theorem fract_nonneg {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (r : α) : 0 ≤ fract r :=
  iff.mpr sub_nonneg (floor_le r)

theorem fract_lt_one {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (r : α) : fract r < 1 :=
  iff.mp sub_lt (sub_one_lt_floor r)

@[simp] theorem fract_zero {α : Type u_1} [linear_ordered_ring α] [floor_ring α] : fract 0 = 0 := sorry

@[simp] theorem fract_coe {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (z : ℤ) : fract ↑z = 0 := sorry

@[simp] theorem fract_floor {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (r : α) : fract ↑(floor r) = 0 :=
  fract_coe (floor r)

@[simp] theorem floor_fract {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (r : α) : floor (fract r) = 0 := sorry

theorem fract_eq_iff {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {r : α} {s : α} : fract r = s ↔ 0 ≤ s ∧ s < 1 ∧ ∃ (z : ℤ), r - s = ↑z := sorry

theorem fract_eq_fract {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {r : α} {s : α} : fract r = fract s ↔ ∃ (z : ℤ), r - s = ↑z := sorry

@[simp] theorem fract_fract {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (r : α) : fract (fract r) = fract r := sorry

theorem fract_add {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (r : α) (s : α) : ∃ (z : ℤ), fract (r + s) - fract r - fract s = ↑z := sorry

theorem fract_mul_nat {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (r : α) (b : ℕ) : ∃ (z : ℤ), fract r * ↑b - fract (r * ↑b) = ↑z := sorry

/-- `ceil x` is the smallest integer `z` such that `x ≤ z` -/
def ceil {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) : ℤ :=
  -floor (-x)

theorem ceil_le {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {z : ℤ} {x : α} : ceil x ≤ z ↔ x ≤ ↑z := sorry

theorem lt_ceil {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {x : α} {z : ℤ} : z < ceil x ↔ ↑z < x :=
  lt_iff_lt_of_le_iff_le ceil_le

theorem ceil_le_floor_add_one {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) : ceil x ≤ floor x + 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ceil x ≤ floor x + 1)) (propext ceil_le)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x ≤ ↑(floor x + 1))) (int.cast_add (floor x) 1)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (x ≤ ↑(floor x) + ↑1)) int.cast_one)) (le_of_lt (lt_floor_add_one x))))

theorem le_ceil {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) : x ≤ ↑(ceil x) :=
  iff.mp ceil_le (le_refl (ceil x))

@[simp] theorem ceil_coe {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (z : ℤ) : ceil ↑z = z := sorry

theorem ceil_mono {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {a : α} {b : α} (h : a ≤ b) : ceil a ≤ ceil b :=
  iff.mpr ceil_le (le_trans h (le_ceil b))

@[simp] theorem ceil_add_int {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) (z : ℤ) : ceil (x + ↑z) = ceil x + z := sorry

theorem ceil_sub_int {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) (z : ℤ) : ceil (x - ↑z) = ceil x - z := sorry

theorem ceil_lt_add_one {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (x : α) : ↑(ceil x) < x + 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(ceil x) < x + 1)) (Eq.symm (propext lt_ceil))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ceil x < ceil (x + 1))) (Eq.symm int.cast_one)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (ceil x < ceil (x + ↑1))) (ceil_add_int x 1))) (lt_add_one (ceil x))))

theorem ceil_pos {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {a : α} : 0 < ceil a ↔ 0 < a := sorry

@[simp] theorem ceil_zero {α : Type u_1} [linear_ordered_ring α] [floor_ring α] : ceil 0 = 0 := sorry

theorem ceil_nonneg {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {q : α} (hq : 0 ≤ q) : 0 ≤ ceil q := sorry

theorem ceil_eq_iff {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {r : α} {z : ℤ} : ceil r = z ↔ ↑z - 1 < r ∧ r ≤ ↑z := sorry

theorem ceil_eq_on_Ioc {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (n : ℤ) (x : α) (H : x ∈ set.Ioc (↑n - 1) ↑n) : ceil x = n := sorry

theorem ceil_eq_on_Ioc' {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (n : ℤ) (x : α) (H : x ∈ set.Ioc (↑n - 1) ↑n) : ↑(ceil x) = ↑n :=
  eq.mpr (id (propext int.cast_inj)) (ceil_eq_on_Ioc n x hx)

/--
`nat_ceil x` is the smallest nonnegative integer `n` with `x ≤ n`.
It is the same as `⌈q⌉` when `q ≥ 0`, otherwise it is `0`.
-/
def nat_ceil {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (a : α) : ℕ :=
  int.to_nat (ceil a)

theorem nat_ceil_le {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {a : α} {n : ℕ} : nat_ceil a ≤ n ↔ a ≤ ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_ceil a ≤ n ↔ a ≤ ↑n)) (nat_ceil.equations._eqn_1 a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (int.to_nat (ceil a) ≤ n ↔ a ≤ ↑n)) (propext int.to_nat_le)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (ceil a ≤ ↑n ↔ a ≤ ↑n)) (propext ceil_le))) (iff.refl (a ≤ ↑↑n))))

theorem lt_nat_ceil {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {a : α} {n : ℕ} : n < nat_ceil a ↔ ↑n < a := sorry

theorem le_nat_ceil {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (a : α) : a ≤ ↑(nat_ceil a) :=
  iff.mp nat_ceil_le (le_refl (nat_ceil a))

theorem nat_ceil_mono {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {a₁ : α} {a₂ : α} (h : a₁ ≤ a₂) : nat_ceil a₁ ≤ nat_ceil a₂ :=
  iff.mpr nat_ceil_le (le_trans h (le_nat_ceil a₂))

@[simp] theorem nat_ceil_coe {α : Type u_1} [linear_ordered_ring α] [floor_ring α] (n : ℕ) : nat_ceil ↑n = n :=
  (fun (this : int.to_nat (ceil ↑↑n) = n) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (int.to_nat (ceil ↑↑n) = n)) (ceil_coe ↑n))) (Eq.refl (int.to_nat ↑n)))

@[simp] theorem nat_ceil_zero {α : Type u_1} [linear_ordered_ring α] [floor_ring α] : nat_ceil 0 = 0 :=
  nat_ceil_coe 0

theorem nat_ceil_add_nat {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {a : α} (a_nonneg : 0 ≤ a) (n : ℕ) : nat_ceil (a + ↑n) = nat_ceil a + n := sorry

theorem nat_ceil_lt_add_one {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {a : α} (a_nonneg : 0 ≤ a) : ↑(nat_ceil a) < a + 1 := sorry

theorem lt_of_nat_ceil_lt {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {x : α} {n : ℕ} (h : nat_ceil x < n) : x < ↑n :=
  lt_of_le_of_lt (le_nat_ceil x) (eq.mpr (id (propext nat.cast_lt)) h)

theorem le_of_nat_ceil_le {α : Type u_1} [linear_ordered_ring α] [floor_ring α] {x : α} {n : ℕ} (h : nat_ceil x ≤ n) : x ≤ ↑n :=
  le_trans (le_nat_ceil x) (eq.mpr (id (propext nat.cast_le)) h)

