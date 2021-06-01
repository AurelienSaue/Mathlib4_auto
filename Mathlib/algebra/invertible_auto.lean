/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen

A typeclass for the two-sided multiplicative inverse.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.char_zero
import Mathlib.algebra.char_p.basic
import Mathlib.PostPort

universes u l u_1 u_2 

namespace Mathlib

/-!
# Invertible elements

This file defines a typeclass `invertible a` for elements `a` with a
multiplicative inverse.

The intent of the typeclass is to provide a way to write e.g. `⅟2` in a ring
like `ℤ[1/2]` where some inverses exist but there is no general `⁻¹` operator;
or to specify that a field has characteristic `≠ 2`.
It is the `Type`-valued analogue to the `Prop`-valued `is_unit`.

This file also includes some instances of `invertible` for specific numbers in
characteristic zero. Some more cases are given as a `def`, to be included only
when needed. To construct instances for concrete numbers,
`invertible_of_nonzero` is a useful definition.

## Notation

 * `⅟a` is `invertible.inv_of a`, the inverse of `a`

## Implementation notes

The `invertible` class lives in `Type`, not `Prop`, to make computation easier.
If multiplication is associative, `invertible` is a subsingleton anyway.

The `simp` normal form tries to normalize `⅟a` to `a ⁻¹`. Otherwise, it pushes
`⅟` inside the expression as much as possible.

## Tags

invertible, inverse element, inv_of, a half, one half, a third, one third, ½, ⅓

-/

/-- `invertible a` gives a two-sided multiplicative inverse of `a`. -/
class invertible {α : Type u} [Mul α] [HasOne α] (a : α) where
  inv_of : α
  inv_of_mul_self : inv_of * a = 1
  mul_inv_of_self : a * inv_of = 1

notation:1024 "⅟" => Mathlib.invertible.inv_of

-- This notation has the same precedence as `has_inv.inv`.

@[simp] theorem inv_of_mul_self {α : Type u} [Mul α] [HasOne α] (a : α) [invertible a] :
    ⅟ * a = 1 :=
  invertible.inv_of_mul_self

@[simp] theorem mul_inv_of_self {α : Type u} [Mul α] [HasOne α] (a : α) [invertible a] :
    a * ⅟ = 1 :=
  invertible.mul_inv_of_self

@[simp] theorem inv_of_mul_self_assoc {α : Type u} [monoid α] (a : α) (b : α) [invertible a] :
    ⅟ * (a * b) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (⅟ * (a * b) = b)) (Eq.symm (mul_assoc ⅟ a b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (⅟ * a * b = b)) (inv_of_mul_self a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 * b = b)) (one_mul b))) (Eq.refl b)))

@[simp] theorem mul_inv_of_self_assoc {α : Type u} [monoid α] (a : α) (b : α) [invertible a] :
    a * (⅟ * b) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (⅟ * b) = b)) (Eq.symm (mul_assoc a ⅟ b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * ⅟ * b = b)) (mul_inv_of_self a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 * b = b)) (one_mul b))) (Eq.refl b)))

@[simp] theorem mul_inv_of_mul_self_cancel {α : Type u} [monoid α] (a : α) (b : α) [invertible b] :
    a * ⅟ * b = a :=
  sorry

@[simp] theorem mul_mul_inv_of_self_cancel {α : Type u} [monoid α] (a : α) (b : α) [invertible b] :
    a * b * ⅟ = a :=
  sorry

theorem inv_of_eq_right_inv {α : Type u} [monoid α] {a : α} {b : α} [invertible a]
    (hac : a * b = 1) : ⅟ = b :=
  left_inv_eq_right_inv (inv_of_mul_self a) hac

theorem invertible_unique {α : Type u} [monoid α] (a : α) (b : α) (h : a = b) [invertible a]
    [invertible b] : ⅟ = ⅟ :=
  inv_of_eq_right_inv
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * ⅟ = 1)) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b * ⅟ = 1)) (mul_inv_of_self b))) (Eq.refl 1)))

protected instance invertible.subsingleton {α : Type u} [monoid α] (a : α) :
    subsingleton (invertible a) :=
  subsingleton.intro fun (_x : invertible a) => sorry

/-- An `invertible` element is a unit. -/
def unit_of_invertible {α : Type u} [monoid α] (a : α) [invertible a] : units α :=
  units.mk a ⅟ sorry sorry

@[simp] theorem unit_of_invertible_val {α : Type u} [monoid α] (a : α) [invertible a] :
    ↑(unit_of_invertible a) = a :=
  rfl

@[simp] theorem unit_of_invertible_inv {α : Type u} [monoid α] (a : α) [invertible a] :
    ↑(unit_of_invertible a⁻¹) = ⅟ :=
  rfl

theorem is_unit_of_invertible {α : Type u} [monoid α] (a : α) [invertible a] : is_unit a :=
  Exists.intro (unit_of_invertible a) rfl

/-- Each element of a group is invertible. -/
def invertible_of_group {α : Type u} [group α] (a : α) : invertible a :=
  invertible.mk (a⁻¹) (inv_mul_self a) (mul_inv_self a)

@[simp] theorem inv_of_eq_group_inv {α : Type u} [group α] (a : α) [invertible a] : ⅟ = (a⁻¹) :=
  inv_of_eq_right_inv (mul_inv_self a)

/-- `1` is the inverse of itself -/
def invertible_one {α : Type u} [monoid α] : invertible 1 := invertible.mk 1 sorry sorry

@[simp] theorem inv_of_one {α : Type u} [monoid α] [invertible 1] : ⅟ = 1 :=
  inv_of_eq_right_inv (mul_one 1)

/-- `-⅟a` is the inverse of `-a` -/
def invertible_neg {α : Type u} [ring α] (a : α) [invertible a] : invertible (-a) :=
  invertible.mk (-⅟) sorry sorry

@[simp] theorem inv_of_neg {α : Type u} [ring α] (a : α) [invertible a] [invertible (-a)] :
    ⅟ = -⅟ :=
  sorry

@[simp] theorem one_sub_inv_of_two {α : Type u} [ring α] [invertible (bit0 1)] : 1 - ⅟ = ⅟ := sorry

/-- `a` is the inverse of `⅟a`. -/
protected instance invertible_inv_of {α : Type u} [HasOne α] [Mul α] {a : α} [invertible a] :
    invertible ⅟ :=
  invertible.mk a (mul_inv_of_self a) (inv_of_mul_self a)

@[simp] theorem inv_of_inv_of {α : Type u} [monoid α] {a : α} [invertible a] [invertible ⅟] :
    ⅟ = a :=
  inv_of_eq_right_inv (inv_of_mul_self a)

/-- `⅟b * ⅟a` is the inverse of `a * b` -/
def invertible_mul {α : Type u} [monoid α] (a : α) (b : α) [invertible a] [invertible b] :
    invertible (a * b) :=
  invertible.mk (⅟ * ⅟) sorry sorry

@[simp] theorem inv_of_mul {α : Type u} [monoid α] (a : α) (b : α) [invertible a] [invertible b]
    [invertible (a * b)] : ⅟ = ⅟ * ⅟ :=
  sorry

/--
If `r` is invertible and `s = r`, then `s` is invertible.
-/
def invertible.copy {α : Type u} [monoid α] {r : α} (hr : invertible r) (s : α) (hs : s = r) :
    invertible s :=
  invertible.mk ⅟ sorry sorry

theorem commute_inv_of {M : Type u_1} [HasOne M] [Mul M] (m : M) [invertible m] : commute m ⅟ :=
  Eq.trans (mul_inv_of_self m) (Eq.symm (inv_of_mul_self m))

protected instance invertible_pow {M : Type u_1} [monoid M] (m : M) [invertible m] (n : ℕ) :
    invertible (m ^ n) :=
  invertible.mk (⅟ ^ n) sorry sorry

theorem nonzero_of_invertible {α : Type u} [group_with_zero α] (a : α) [invertible a] : a ≠ 0 :=
  sorry

/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
def invertible_of_nonzero {α : Type u} [group_with_zero α] {a : α} (h : a ≠ 0) : invertible a :=
  invertible.mk (a⁻¹) (inv_mul_cancel h) (mul_inv_cancel h)

@[simp] theorem inv_of_eq_inv {α : Type u} [group_with_zero α] (a : α) [invertible a] : ⅟ = (a⁻¹) :=
  inv_of_eq_right_inv (mul_inv_cancel (nonzero_of_invertible a))

@[simp] theorem inv_mul_cancel_of_invertible {α : Type u} [group_with_zero α] (a : α)
    [invertible a] : a⁻¹ * a = 1 :=
  inv_mul_cancel (nonzero_of_invertible a)

@[simp] theorem mul_inv_cancel_of_invertible {α : Type u} [group_with_zero α] (a : α)
    [invertible a] : a * (a⁻¹) = 1 :=
  mul_inv_cancel (nonzero_of_invertible a)

@[simp] theorem div_mul_cancel_of_invertible {α : Type u} [group_with_zero α] (a : α) (b : α)
    [invertible b] : a / b * b = a :=
  div_mul_cancel a (nonzero_of_invertible b)

@[simp] theorem mul_div_cancel_of_invertible {α : Type u} [group_with_zero α] (a : α) (b : α)
    [invertible b] : a * b / b = a :=
  mul_div_cancel a (nonzero_of_invertible b)

@[simp] theorem div_self_of_invertible {α : Type u} [group_with_zero α] (a : α) [invertible a] :
    a / a = 1 :=
  div_self (nonzero_of_invertible a)

/-- `b / a` is the inverse of `a / b` -/
def invertible_div {α : Type u} [group_with_zero α] (a : α) (b : α) [invertible a] [invertible b] :
    invertible (a / b) :=
  invertible.mk (b / a) sorry sorry

@[simp] theorem inv_of_div {α : Type u} [group_with_zero α] (a : α) (b : α) [invertible a]
    [invertible b] [invertible (a / b)] : ⅟ = b / a :=
  sorry

/-- `a` is the inverse of `a⁻¹` -/
def invertible_inv {α : Type u} [group_with_zero α] {a : α} [invertible a] : invertible (a⁻¹) :=
  invertible.mk a sorry sorry

/--
Monoid homs preserve invertibility.
-/
def invertible.map {R : Type u_1} {S : Type u_2} [monoid R] [monoid S] (f : R →* S) (r : R)
    [invertible r] : invertible (coe_fn f r) :=
  invertible.mk (coe_fn f ⅟) sorry sorry

/-- A natural number `t` is invertible in a field `K` if the charactistic of `K` does not divide
`t`. -/
def invertible_of_ring_char_not_dvd {K : Type u_1} [field K] {t : ℕ} (not_dvd : ¬ring_char K ∣ t) :
    invertible ↑t :=
  invertible_of_nonzero sorry

/-- A natural number `t` is invertible in a field `K` of charactistic `p` if `p` does not divide
`t`. -/
def invertible_of_char_p_not_dvd {K : Type u_1} [field K] {p : ℕ} [char_p K p] {t : ℕ}
    (not_dvd : ¬p ∣ t) : invertible ↑t :=
  invertible_of_nonzero sorry

protected instance invertible_of_pos {K : Type u_1} [field K] [char_zero K] (n : ℕ)
    [h : fact (0 < n)] : invertible ↑n :=
  invertible_of_nonzero sorry

protected instance invertible_succ {α : Type u} [division_ring α] [char_zero α] (n : ℕ) :
    invertible ↑(Nat.succ n) :=
  invertible_of_nonzero sorry

/-!
A few `invertible n` instances for small numerals `n`. Feel free to add your own
number when you need its inverse.
-/

protected instance invertible_two {α : Type u} [division_ring α] [char_zero α] :
    invertible (bit0 1) :=
  invertible_of_nonzero sorry

protected instance invertible_three {α : Type u} [division_ring α] [char_zero α] :
    invertible (bit1 1) :=
  invertible_of_nonzero sorry

end Mathlib