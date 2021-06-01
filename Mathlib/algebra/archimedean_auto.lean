/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Archimedean groups and fields.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.field_power
import Mathlib.data.rat.default
import Mathlib.PostPort

universes u_2 l u_1 

namespace Mathlib

/-- An ordered additive commutative monoid is called `archimedean` if for any two elements `x`, `y`
such that `0 < y` there exists a natural number `n` such that `x ≤ n •ℕ y`. -/
class archimedean (α : Type u_2) [ordered_add_comm_monoid α] where
  arch : ∀ (x : α) {y : α}, 0 < y → ∃ (n : ℕ), x ≤ n •ℕ y

namespace linear_ordered_add_comm_group


/-- An archimedean decidable linearly ordered `add_comm_group` has a version of the floor: for
`a > 0`, any `g` in the group lies between some two consecutive multiples of `a`. -/
theorem exists_int_smul_near_of_pos {α : Type u_1} [linear_ordered_add_comm_group α] [archimedean α]
    {a : α} (ha : 0 < a) (g : α) : ∃ (k : ℤ), k •ℤ a ≤ g ∧ g < (k + 1) •ℤ a :=
  sorry

theorem exists_int_smul_near_of_pos' {α : Type u_1} [linear_ordered_add_comm_group α]
    [archimedean α] {a : α} (ha : 0 < a) (g : α) : ∃ (k : ℤ), 0 ≤ g - k •ℤ a ∧ g - k •ℤ a < a :=
  sorry

end linear_ordered_add_comm_group


theorem exists_nat_gt {α : Type u_1} [ordered_semiring α] [nontrivial α] [archimedean α] (x : α) :
    ∃ (n : ℕ), x < ↑n :=
  sorry

theorem exists_nat_ge {α : Type u_1} [ordered_semiring α] [archimedean α] (x : α) :
    ∃ (n : ℕ), x ≤ ↑n :=
  sorry

theorem add_one_pow_unbounded_of_pos {α : Type u_1} [ordered_semiring α] [nontrivial α]
    [archimedean α] (x : α) {y : α} (hy : 0 < y) : ∃ (n : ℕ), x < (y + 1) ^ n :=
  sorry

theorem pow_unbounded_of_one_lt {α : Type u_1} [linear_ordered_ring α] [archimedean α] (x : α)
    {y : α} (hy1 : 1 < y) : ∃ (n : ℕ), x < y ^ n :=
  sub_add_cancel y 1 ▸ add_one_pow_unbounded_of_pos x (iff.mpr sub_pos hy1)

/-- Every x greater than or equal to 1 is between two successive
natural-number powers of every y greater than one. -/
theorem exists_nat_pow_near {α : Type u_1} [linear_ordered_ring α] [archimedean α] {x : α} {y : α}
    (hx : 1 ≤ x) (hy : 1 < y) : ∃ (n : ℕ), y ^ n ≤ x ∧ x < y ^ (n + 1) :=
  sorry

theorem exists_int_gt {α : Type u_1} [linear_ordered_ring α] [archimedean α] (x : α) :
    ∃ (n : ℤ), x < ↑n :=
  sorry

theorem exists_int_lt {α : Type u_1} [linear_ordered_ring α] [archimedean α] (x : α) :
    ∃ (n : ℤ), ↑n < x :=
  sorry

theorem exists_floor {α : Type u_1} [linear_ordered_ring α] [archimedean α] (x : α) :
    ∃ (fl : ℤ), ∀ (z : ℤ), z ≤ fl ↔ ↑z ≤ x :=
  sorry

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_int_pow_near'`,
but with ≤ and < the other way around. -/
theorem exists_int_pow_near {α : Type u_1} [linear_ordered_field α] [archimedean α] {x : α} {y : α}
    (hx : 0 < x) (hy : 1 < y) : ∃ (n : ℤ), y ^ n ≤ x ∧ x < y ^ (n + 1) :=
  sorry

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_int_pow_near`,
but with ≤ and < the other way around. -/
theorem exists_int_pow_near' {α : Type u_1} [linear_ordered_field α] [archimedean α] {x : α} {y : α}
    (hx : 0 < x) (hy : 1 < y) : ∃ (n : ℤ), y ^ n < x ∧ x ≤ y ^ (n + 1) :=
  sorry

/-- For any `y < 1` and any positive `x`, there exists `n : ℕ` with `y ^ n < x`. -/
theorem exists_pow_lt_of_lt_one {α : Type u_1} [linear_ordered_field α] [archimedean α] {x : α}
    {y : α} (hx : 0 < x) (hy : y < 1) : ∃ (n : ℕ), y ^ n < x :=
  sorry

/-- Given `x` and `y` between `0` and `1`, `x` is between two successive powers of `y`.
This is the same as `exists_nat_pow_near`, but for elements between `0` and `1` -/
theorem exists_nat_pow_near_of_lt_one {α : Type u_1} [linear_ordered_field α] [archimedean α]
    {x : α} {y : α} (xpos : 0 < x) (hx : x ≤ 1) (ypos : 0 < y) (hy : y < 1) :
    ∃ (n : ℕ), y ^ (n + 1) < x ∧ x ≤ y ^ n :=
  sorry

theorem sub_floor_div_mul_nonneg {α : Type u_1} [linear_ordered_field α] [floor_ring α] (x : α)
    {y : α} (hy : 0 < y) : 0 ≤ x - ↑(floor (x / y)) * y :=
  sorry

theorem sub_floor_div_mul_lt {α : Type u_1} [linear_ordered_field α] [floor_ring α] (x : α) {y : α}
    (hy : 0 < y) : x - ↑(floor (x / y)) * y < y :=
  sorry

protected instance nat.archimedean : archimedean ℕ :=
  archimedean.mk
    fun (n m : ℕ) (m0 : 0 < m) =>
      Exists.intro n
        (eq.mpr
          (id
            ((fun (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℕ) (e_3 : ᾰ_2 = ᾰ_3) =>
                congr (congr_arg LessEq e_2) e_3)
              n n (Eq.refl n) (n •ℕ m) (n * m) (nat.nsmul_eq_mul n m)))
          (eq.mp
            ((fun (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℕ) (e_3 : ᾰ_2 = ᾰ_3) =>
                congr (congr_arg LessEq e_2) e_3)
              (n * Nat.succ 0) n (mul_one n) (n * m) (n * m) (Eq.refl (n * m)))
            (nat.mul_le_mul_left n m0)))

protected instance int.archimedean : archimedean ℤ := sorry

/-- A linear ordered archimedean ring is a floor ring. This is not an `instance` because in some
cases we have a computable `floor` function. -/
def archimedean.floor_ring (α : Type u_1) [linear_ordered_ring α] [archimedean α] : floor_ring α :=
  floor_ring.mk (fun (x : α) => classical.some (exists_floor x)) sorry

theorem archimedean_iff_nat_lt {α : Type u_1} [linear_ordered_field α] :
    archimedean α ↔ ∀ (x : α), ∃ (n : ℕ), x < ↑n :=
  sorry

theorem archimedean_iff_nat_le {α : Type u_1} [linear_ordered_field α] :
    archimedean α ↔ ∀ (x : α), ∃ (n : ℕ), x ≤ ↑n :=
  sorry

theorem exists_rat_gt {α : Type u_1} [linear_ordered_field α] [archimedean α] (x : α) :
    ∃ (q : ℚ), x < ↑q :=
  sorry

theorem archimedean_iff_rat_lt {α : Type u_1} [linear_ordered_field α] :
    archimedean α ↔ ∀ (x : α), ∃ (q : ℚ), x < ↑q :=
  sorry

theorem archimedean_iff_rat_le {α : Type u_1} [linear_ordered_field α] :
    archimedean α ↔ ∀ (x : α), ∃ (q : ℚ), x ≤ ↑q :=
  sorry

theorem exists_rat_lt {α : Type u_1} [linear_ordered_field α] [archimedean α] (x : α) :
    ∃ (q : ℚ), ↑q < x :=
  sorry

theorem exists_rat_btwn {α : Type u_1} [linear_ordered_field α] [archimedean α] {x : α} {y : α}
    (h : x < y) : ∃ (q : ℚ), x < ↑q ∧ ↑q < y :=
  sorry

theorem exists_nat_one_div_lt {α : Type u_1} [linear_ordered_field α] [archimedean α] {ε : α}
    (hε : 0 < ε) : ∃ (n : ℕ), 1 / (↑n + 1) < ε :=
  sorry

theorem exists_pos_rat_lt {α : Type u_1} [linear_ordered_field α] [archimedean α] {x : α}
    (x0 : 0 < x) : ∃ (q : ℚ), 0 < q ∧ ↑q < x :=
  sorry

@[simp] theorem rat.cast_floor {α : Type u_1} [linear_ordered_field α] [archimedean α] (x : ℚ) :
    floor ↑x = floor x :=
  sorry

/-- `round` rounds a number to the nearest integer. `round (1 / 2) = 1` -/
def round {α : Type u_1} [linear_ordered_field α] [floor_ring α] (x : α) : ℤ :=
  floor (x + 1 / bit0 1)

theorem abs_sub_round {α : Type u_1} [linear_ordered_field α] [floor_ring α] (x : α) :
    abs (x - ↑(round x)) ≤ 1 / bit0 1 :=
  sorry

theorem exists_rat_near {α : Type u_1} [linear_ordered_field α] [archimedean α] (x : α) {ε : α}
    (ε0 : 0 < ε) : ∃ (q : ℚ), abs (x - ↑q) < ε :=
  sorry

protected instance rat.archimedean : archimedean ℚ :=
  iff.mpr archimedean_iff_rat_le
    fun (q : ℚ) =>
      Exists.intro q (eq.mpr (id (Eq._oldrec (Eq.refl (q ≤ ↑q)) (rat.cast_id q))) (le_refl q))

@[simp] theorem rat.cast_round {α : Type u_1} [linear_ordered_field α] [archimedean α] (x : ℚ) :
    round ↑x = round x :=
  sorry

end Mathlib