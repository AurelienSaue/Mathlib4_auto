/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group_power.default
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Powers of elements of groups with an adjoined zero element

In this file we define integer power functions for groups with an adjoined zero element.
This generalises the integer power function on a division ring.
-/

@[simp] theorem zero_pow' {M : Type u_1} [monoid_with_zero M] (n : ℕ) : n ≠ 0 → 0 ^ n = 0 := sorry

theorem ne_zero_pow {M : Type u_1} [monoid_with_zero M] {a : M} {n : ℕ} (hn : n ≠ 0) : a ^ n ≠ 0 → a ≠ 0 :=
  imp_of_not_imp_not (a ^ n ≠ 0) (a ≠ 0)
    (eq.mpr (id (imp_congr_eq (push_neg.not_not_eq (a = 0)) (push_neg.not_not_eq (a ^ n = 0))))
      fun (ᾰ : a = 0) => Eq._oldrec (zero_pow' n hn) (Eq.symm ᾰ))

@[simp] theorem zero_pow_eq_zero {M : Type u_1} [monoid_with_zero M] [nontrivial M] {n : ℕ} : 0 ^ n = 0 ↔ 0 < n := sorry

@[simp] theorem inv_pow' {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℕ) : a⁻¹ ^ n = (a ^ n⁻¹) := sorry

theorem pow_sub' {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) {m : ℕ} {n : ℕ} (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n⁻¹) := sorry

theorem pow_inv_comm' {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (m : ℕ) (n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  commute.pow_pow (commute.inv_left' (commute.refl a)) m n

/--
The power operation in a group with zero.
This extends `monoid.pow` to negative integers
with the definition `a ^ (-n) = (a ^ n)⁻¹`.
-/
def fpow {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) : ℤ → G₀ :=
  sorry

protected instance int.has_pow {G₀ : Type u_1} [group_with_zero G₀] : has_pow G₀ ℤ :=
  has_pow.mk fpow

@[simp] theorem fpow_coe_nat {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℕ) : a ^ ↑n = a ^ n :=
  rfl

theorem fpow_of_nat {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℕ) : a ^ Int.ofNat n = a ^ n :=
  rfl

@[simp] theorem fpow_neg_succ_of_nat {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℕ) : a ^ Int.negSucc n = (a ^ Nat.succ n⁻¹) :=
  rfl

@[simp] theorem fpow_zero {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) : a ^ 0 = 1 :=
  rfl

@[simp] theorem fpow_one {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) : a ^ 1 = a :=
  mul_one a

@[simp] theorem one_fpow {G₀ : Type u_1} [group_with_zero G₀] (n : ℤ) : 1 ^ n = 1 := sorry

theorem zero_fpow {G₀ : Type u_1} [group_with_zero G₀] (z : ℤ) : z ≠ 0 → 0 ^ z = 0 := sorry

@[simp] theorem fpow_neg {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℤ) : a ^ (-n) = (a ^ n⁻¹) := sorry

theorem fpow_neg_one {G₀ : Type u_1} [group_with_zero G₀] (x : G₀) : x ^ (-1) = (x⁻¹) :=
  congr_arg has_inv.inv (pow_one x)

theorem inv_fpow {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℤ) : a⁻¹ ^ n = (a ^ n⁻¹) :=
  int.cases_on n (fun (n : ℕ) => idRhs (a⁻¹ ^ n = (a ^ n⁻¹)) (inv_pow' a n))
    fun (n : ℕ) => idRhs (a⁻¹ ^ (n + 1)⁻¹ = (a ^ (n + 1)⁻¹⁻¹)) (congr_arg has_inv.inv (inv_pow' a (n + 1)))

theorem fpow_add_one {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} (ha : a ≠ 0) (n : ℤ) : a ^ (n + 1) = a ^ n * a := sorry

theorem fpow_sub_one {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * (a⁻¹) := sorry

theorem fpow_add {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} (ha : a ≠ 0) (m : ℤ) (n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := sorry

theorem fpow_add' {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} {m : ℤ} {n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) : a ^ (m + n) = a ^ m * a ^ n := sorry

theorem fpow_one_add {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (1 + i) = a * a ^ i)) (fpow_add h 1 i)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ 1 * a ^ i = a * a ^ i)) (fpow_one a))) (Eq.refl (a * a ^ i)))

theorem semiconj_by.fpow_right {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} {x : G₀} {y : G₀} (h : semiconj_by a x y) (m : ℤ) : semiconj_by a (x ^ m) (y ^ m) :=
  int.cases_on m (fun (m : ℕ) => idRhs (semiconj_by a (x ^ m) (y ^ m)) (semiconj_by.pow_right h m))
    fun (m : ℕ) =>
      idRhs (semiconj_by a (x ^ (m + 1)⁻¹) (y ^ (m + 1)⁻¹)) (semiconj_by.inv_right' (semiconj_by.pow_right h (m + 1)))

theorem commute.fpow_right {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} {b : G₀} (h : commute a b) (m : ℤ) : commute a (b ^ m) :=
  semiconj_by.fpow_right h

theorem commute.fpow_left {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} {b : G₀} (h : commute a b) (m : ℤ) : commute (a ^ m) b :=
  commute.symm (commute.fpow_right (commute.symm h) m)

theorem commute.fpow_fpow {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} {b : G₀} (h : commute a b) (m : ℤ) (n : ℤ) : commute (a ^ m) (b ^ n) :=
  commute.fpow_right (commute.fpow_left h m) n

theorem commute.fpow_self {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℤ) : commute (a ^ n) a :=
  commute.fpow_left (commute.refl a) n

theorem commute.self_fpow {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℤ) : commute a (a ^ n) :=
  commute.fpow_right (commute.refl a) n

theorem commute.fpow_fpow_self {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (m : ℤ) (n : ℤ) : commute (a ^ m) (a ^ n) :=
  commute.fpow_fpow (commute.refl a) m n

theorem fpow_bit0 {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n := sorry

theorem fpow_bit1 {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a := sorry

theorem fpow_mul {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (m : ℤ) (n : ℤ) : a ^ (m * n) = (a ^ m) ^ n := sorry

theorem fpow_mul' {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (m : ℤ) (n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (m * n) = (a ^ n) ^ m)) (mul_comm m n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (n * m) = (a ^ n) ^ m)) (fpow_mul a n m))) (Eq.refl ((a ^ n) ^ m)))

@[simp] theorem units.coe_gpow' {G₀ : Type u_1} [group_with_zero G₀] (u : units G₀) (n : ℤ) : ↑(u ^ n) = ↑u ^ n := sorry

theorem fpow_ne_zero_of_ne_zero {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} (ha : a ≠ 0) (z : ℤ) : a ^ z ≠ 0 :=
  int.cases_on z (fun (z : ℕ) => idRhs (a ^ z ≠ 0) (pow_ne_zero z ha))
    fun (z : ℕ) => idRhs (a ^ Nat.succ z⁻¹ ≠ 0) (inv_ne_zero (pow_ne_zero (Nat.succ z) ha))

theorem fpow_sub {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} (ha : a ≠ 0) (z1 : ℤ) (z2 : ℤ) : a ^ (z1 - z2) = a ^ z1 / a ^ z2 := sorry

theorem commute.mul_fpow {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} {b : G₀} (h : commute a b) (i : ℤ) : (a * b) ^ i = a ^ i * b ^ i := sorry

theorem mul_fpow {G₀ : Type u_1} [comm_group_with_zero G₀] (a : G₀) (b : G₀) (m : ℤ) : (a * b) ^ m = a ^ m * b ^ m :=
  commute.mul_fpow (commute.all a b) m

theorem fpow_bit0' {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℤ) : a ^ bit0 n = (a * a) ^ n :=
  Eq.trans (fpow_bit0 a n) (Eq.symm (commute.mul_fpow (commute.refl a) n))

theorem fpow_bit1' {G₀ : Type u_1} [group_with_zero G₀] (a : G₀) (n : ℤ) : a ^ bit1 n = (a * a) ^ n * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ bit1 n = (a * a) ^ n * a)) (fpow_bit1 a n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ n * a ^ n * a = (a * a) ^ n * a)) (commute.mul_fpow (commute.refl a) n)))
      (Eq.refl (a ^ n * a ^ n * a)))

theorem fpow_eq_zero {G₀ : Type u_1} [group_with_zero G₀] {x : G₀} {n : ℤ} (h : x ^ n = 0) : x = 0 :=
  classical.by_contradiction fun (hx : ¬x = 0) => fpow_ne_zero_of_ne_zero hx n h

theorem fpow_ne_zero {G₀ : Type u_1} [group_with_zero G₀] {x : G₀} (n : ℤ) : x ≠ 0 → x ^ n ≠ 0 :=
  mt fpow_eq_zero

theorem fpow_neg_mul_fpow_self {G₀ : Type u_1} [group_with_zero G₀] (n : ℤ) {x : G₀} (h : x ≠ 0) : x ^ (-n) * x ^ n = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ^ (-n) * x ^ n = 1)) (fpow_neg x n))) (inv_mul_cancel (fpow_ne_zero n h))

theorem one_div_pow {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} (n : ℕ) : (1 / a) ^ n = 1 / a ^ n := sorry

theorem one_div_fpow {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} (n : ℤ) : (1 / a) ^ n = 1 / a ^ n := sorry

@[simp] theorem inv_fpow' {G₀ : Type u_1} [group_with_zero G₀] {a : G₀} (n : ℤ) : a⁻¹ ^ n = a ^ (-n) := sorry

@[simp] theorem div_pow {G₀ : Type u_1} [comm_group_with_zero G₀] (a : G₀) (b : G₀) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := sorry

@[simp] theorem div_fpow {G₀ : Type u_1} [comm_group_with_zero G₀] (a : G₀) {b : G₀} (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n := sorry

theorem div_sq_cancel {G₀ : Type u_1} [comm_group_with_zero G₀] {a : G₀} (ha : a ≠ 0) (b : G₀) : a ^ bit0 1 * b / a = a * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ bit0 1 * b / a = a * b)) (pow_two a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * a * b / a = a * b)) (mul_assoc a a b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * (a * b) / a = a * b)) (mul_div_cancel_left (a * b) ha))) (Eq.refl (a * b))))

/-- If a monoid homomorphism `f` between two `group_with_zero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
theorem monoid_with_zero_hom.map_fpow {G₀ : Type u_1} {G₀' : Type u_2} [group_with_zero G₀] [group_with_zero G₀'] (f : monoid_with_zero_hom G₀ G₀') (x : G₀) (n : ℤ) : coe_fn f (x ^ n) = coe_fn f x ^ n := sorry

