/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group_with_zero.default
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Divisibility

This file defines the basics of the divisibility relation in the context of `(comm_)` `monoid`s
`(_with_zero)`.

## Main definitions

 * `monoid.has_dvd`

## Implementation notes

The divisibility relation is defined for all monoids, and as such, depends on the order of
  multiplication if the monoid is not commutative. There are two possible conventions for
  divisibility in the noncommutative context, and this relation follows the convention for ordinals,
  so `a | b` is defined as `∃ c, b = a * c`.

## Tags

divisibility, divides
-/

/-- There are two possible conventions for divisibility, which coincide in a `comm_monoid`.
    This matches the convention for ordinals. -/
protected instance monoid_has_dvd {α : Type u_1} [monoid α] : has_dvd α :=
  has_dvd.mk fun (a b : α) => ∃ (c : α), b = a * c

-- TODO: this used to not have c explicit, but that seems to be important

--       for use with tactics, similar to exist.intro

theorem dvd.intro {α : Type u_1} [monoid α] {a : α} {b : α} (c : α) (h : a * c = b) : a ∣ b :=
  exists.intro c (Eq.symm h)

theorem dvd_of_mul_right_eq {α : Type u_1} [monoid α] {a : α} {b : α} (c : α) (h : a * c = b) : a ∣ b :=
  dvd.intro

theorem exists_eq_mul_right_of_dvd {α : Type u_1} [monoid α] {a : α} {b : α} (h : a ∣ b) : ∃ (c : α), b = a * c :=
  h

theorem dvd.elim {α : Type u_1} [monoid α] {P : Prop} {a : α} {b : α} (H₁ : a ∣ b) (H₂ : ∀ (c : α), b = a * c → P) : P :=
  exists.elim H₁ H₂

@[simp] theorem dvd_refl {α : Type u_1} [monoid α] (a : α) : a ∣ a := sorry

theorem dvd_trans {α : Type u_1} [monoid α] {a : α} {b : α} {c : α} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := sorry

theorem dvd.trans {α : Type u_1} [monoid α] {a : α} {b : α} {c : α} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
  dvd_trans

theorem one_dvd {α : Type u_1} [monoid α] (a : α) : 1 ∣ a := sorry

@[simp] theorem dvd_mul_right {α : Type u_1} [monoid α] (a : α) (b : α) : a ∣ a * b :=
  dvd.intro b rfl

theorem dvd_mul_of_dvd_left {α : Type u_1} [monoid α] {a : α} {b : α} (h : a ∣ b) (c : α) : a ∣ b * c := sorry

theorem dvd_of_mul_right_dvd {α : Type u_1} [monoid α] {a : α} {b : α} {c : α} (h : a * b ∣ c) : a ∣ c := sorry

theorem dvd.intro_left {α : Type u_1} [comm_monoid α] {a : α} {b : α} (c : α) (h : c * a = b) : a ∣ b :=
  dvd.intro c (eq.mp (Eq._oldrec (Eq.refl (c * a = b)) (mul_comm c a)) h)

theorem dvd_of_mul_left_eq {α : Type u_1} [comm_monoid α] {a : α} {b : α} (c : α) (h : c * a = b) : a ∣ b :=
  dvd.intro_left

theorem exists_eq_mul_left_of_dvd {α : Type u_1} [comm_monoid α] {a : α} {b : α} (h : a ∣ b) : ∃ (c : α), b = c * a :=
  dvd.elim h fun (c : α) (H1 : b = a * c) => exists.intro c (Eq.trans H1 (mul_comm a c))

theorem dvd.elim_left {α : Type u_1} [comm_monoid α] {a : α} {b : α} {P : Prop} (h₁ : a ∣ b) (h₂ : ∀ (c : α), b = c * a → P) : P :=
  exists.elim (exists_eq_mul_left_of_dvd h₁) fun (c : α) (h₃ : b = c * a) => h₂ c h₃

@[simp] theorem dvd_mul_left {α : Type u_1} [comm_monoid α] (a : α) (b : α) : a ∣ b * a :=
  dvd.intro b (mul_comm a b)

theorem dvd_mul_of_dvd_right {α : Type u_1} [comm_monoid α] {a : α} {b : α} (h : a ∣ b) (c : α) : a ∣ c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∣ c * b)) (mul_comm c b))) (dvd_mul_of_dvd_left h c)

theorem mul_dvd_mul {α : Type u_1} [comm_monoid α] {a : α} {b : α} {c : α} {d : α} : a ∣ b → c ∣ d → a * c ∣ b * d := sorry

theorem mul_dvd_mul_left {α : Type u_1} [comm_monoid α] (a : α) {b : α} {c : α} (h : b ∣ c) : a * b ∣ a * c :=
  mul_dvd_mul (dvd_refl a) h

theorem mul_dvd_mul_right {α : Type u_1} [comm_monoid α] {a : α} {b : α} (h : a ∣ b) (c : α) : a * c ∣ b * c :=
  mul_dvd_mul h (dvd_refl c)

theorem dvd_of_mul_left_dvd {α : Type u_1} [comm_monoid α] {a : α} {b : α} {c : α} (h : a * b ∣ c) : b ∣ c := sorry

theorem eq_zero_of_zero_dvd {α : Type u_1} [monoid_with_zero α] {a : α} (h : 0 ∣ a) : a = 0 :=
  dvd.elim h fun (c : α) (H' : a = 0 * c) => Eq.trans H' (zero_mul c)

/-- Given an element `a` of a commutative monoid with zero, there exists another element whose
    product with zero equals `a` iff `a` equals zero. -/
@[simp] theorem zero_dvd_iff {α : Type u_1} [monoid_with_zero α] {a : α} : 0 ∣ a ↔ a = 0 :=
  { mp := eq_zero_of_zero_dvd, mpr := fun (h : a = 0) => eq.mpr (id (Eq._oldrec (Eq.refl (0 ∣ a)) h)) (dvd_refl 0) }

@[simp] theorem dvd_zero {α : Type u_1} [monoid_with_zero α] (a : α) : a ∣ 0 := sorry

/-- Given two elements `b`, `c` of a `cancel_monoid_with_zero` and a nonzero element `a`,
 `a*b` divides `a*c` iff `b` divides `c`. -/
theorem mul_dvd_mul_iff_left {α : Type u_1} [cancel_monoid_with_zero α] {a : α} {b : α} {c : α} (ha : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c := sorry

/-- Given two elements `a`, `b` of a commutative `cancel_monoid_with_zero` and a nonzero
  element `c`, `a*c` divides `b*c` iff `a` divides `b`. -/
theorem mul_dvd_mul_iff_right {α : Type u_1} [comm_cancel_monoid_with_zero α] {a : α} {b : α} {c : α} (hc : c ≠ 0) : a * c ∣ b * c ↔ a ∣ b := sorry

/-!
### Units in various monoids
-/

namespace units


/-- Elements of the unit group of a monoid represented as elements of the monoid
    divide any element of the monoid. -/
theorem coe_dvd {α : Type u_1} [monoid α] {a : α} {u : units α} : ↑u ∣ a := sorry

/-- In a monoid, an element `a` divides an element `b` iff `a` divides all
    associates of `b`. -/
theorem dvd_mul_right {α : Type u_1} [monoid α] {a : α} {b : α} {u : units α} : a ∣ b * ↑u ↔ a ∣ b := sorry

/-- In a monoid, an element a divides an element b iff all associates of `a` divide `b`.-/
theorem mul_right_dvd {α : Type u_1} [monoid α] {a : α} {b : α} {u : units α} : a * ↑u ∣ b ↔ a ∣ b := sorry

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
theorem dvd_mul_left {α : Type u_1} [comm_monoid α] {a : α} {b : α} {u : units α} : a ∣ ↑u * b ↔ a ∣ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∣ ↑u * b ↔ a ∣ b)) (mul_comm (↑u) b))) dvd_mul_right

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
theorem mul_left_dvd {α : Type u_1} [comm_monoid α] {a : α} {b : α} {u : units α} : ↑u * a ∣ b ↔ a ∣ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑u * a ∣ b ↔ a ∣ b)) (mul_comm (↑u) a))) mul_right_dvd

end units


namespace is_unit


/-- Units of a monoid divide any element of the monoid. -/
@[simp] theorem dvd {α : Type u_1} [monoid α] {a : α} {u : α} (hu : is_unit u) : u ∣ a :=
  Exists.dcases_on hu fun (u_1 : units α) (hu_h : ↑u_1 = u) => Eq._oldrec units.coe_dvd hu_h

@[simp] theorem dvd_mul_right {α : Type u_1} [monoid α] {a : α} {b : α} {u : α} (hu : is_unit u) : a ∣ b * u ↔ a ∣ b :=
  Exists.dcases_on hu fun (u_1 : units α) (hu_h : ↑u_1 = u) => Eq._oldrec units.dvd_mul_right hu_h

/-- In a monoid, an element a divides an element b iff all associates of `a` divide `b`.-/
@[simp] theorem mul_right_dvd {α : Type u_1} [monoid α] {a : α} {b : α} {u : α} (hu : is_unit u) : a * u ∣ b ↔ a ∣ b :=
  Exists.dcases_on hu fun (u_1 : units α) (hu_h : ↑u_1 = u) => Eq._oldrec units.mul_right_dvd hu_h

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
@[simp] theorem dvd_mul_left {α : Type u_1} [comm_monoid α] (a : α) (b : α) (u : α) (hu : is_unit u) : a ∣ u * b ↔ a ∣ b :=
  Exists.dcases_on hu fun (u_1 : units α) (hu_h : ↑u_1 = u) => Eq._oldrec units.dvd_mul_left hu_h

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
@[simp] theorem mul_left_dvd {α : Type u_1} [comm_monoid α] (a : α) (b : α) (u : α) (hu : is_unit u) : u * a ∣ b ↔ a ∣ b :=
  Exists.dcases_on hu fun (u_1 : units α) (hu_h : ↑u_1 = u) => Eq._oldrec units.mul_left_dvd hu_h

end is_unit


/-- `dvd_not_unit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divided by `a` is not a unit. -/
def dvd_not_unit {α : Type u_1} [comm_monoid_with_zero α] (a : α) (b : α) :=
  a ≠ 0 ∧ ∃ (x : α), ¬is_unit x ∧ b = a * x

theorem dvd_not_unit_of_dvd_of_not_dvd {α : Type u_1} [comm_monoid_with_zero α] {a : α} {b : α} (hd : a ∣ b) (hnd : ¬b ∣ a) : dvd_not_unit a b := sorry

