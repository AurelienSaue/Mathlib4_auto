/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.ordered_monoid
import PostPort

universes u l u_1 u_2 

namespace Mathlib

/-!
# Ordered groups

This file develops the basics of ordered groups.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

-/

/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
class ordered_add_comm_group (α : Type u) 
extends partial_order α, add_comm_group α
where
  add_le_add_left : ∀ (a b : α), a ≤ b → ∀ (c : α), c + a ≤ c + b

/-- An ordered commutative group is an commutative group
with a partial order in which multiplication is strictly monotone. -/
class ordered_comm_group (α : Type u) 
extends comm_group α, partial_order α
where
  mul_le_mul_left : ∀ (a b : α), a ≤ b → ∀ (c : α), c * a ≤ c * b

/--The units of an ordered commutative monoid form an ordered commutative group. -/
protected instance add_units.ordered_add_comm_group {α : Type u} [ordered_add_comm_monoid α] : ordered_add_comm_group (add_units α) :=
  ordered_add_comm_group.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub
    sorry sorry partial_order.le partial_order.lt sorry sorry sorry sorry

theorem ordered_comm_group.mul_lt_mul_left' {α : Type u} [ordered_comm_group α] (a : α) (b : α) (h : a < b) (c : α) : c * a < c * b := sorry

theorem ordered_comm_group.le_of_mul_le_mul_left {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} (h : a * b ≤ a * c) : b ≤ c := sorry

theorem ordered_comm_group.lt_of_mul_lt_mul_left {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} (h : a * b < a * c) : b < c := sorry

protected instance ordered_add_comm_group.to_ordered_cancel_add_comm_monoid (α : Type u) [s : ordered_add_comm_group α] : ordered_cancel_add_comm_monoid α :=
  ordered_cancel_add_comm_monoid.mk ordered_add_comm_group.add ordered_add_comm_group.add_assoc sorry
    ordered_add_comm_group.zero ordered_add_comm_group.zero_add ordered_add_comm_group.add_zero
    ordered_add_comm_group.add_comm sorry ordered_add_comm_group.le ordered_add_comm_group.lt
    ordered_add_comm_group.le_refl ordered_add_comm_group.le_trans ordered_add_comm_group.le_antisymm
    ordered_add_comm_group.add_le_add_left ordered_add_comm_group.le_of_add_le_add_left

theorem neg_le_neg {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} (h : a ≤ b) : -b ≤ -a := sorry

theorem le_of_inv_le_inv {α : Type u} [ordered_comm_group α] {a : α} {b : α} (h : b⁻¹ ≤ (a⁻¹)) : a ≤ b := sorry

theorem one_le_of_inv_le_one {α : Type u} [ordered_comm_group α] {a : α} (h : a⁻¹ ≤ 1) : 1 ≤ a :=
  (fun (this : a⁻¹ ≤ (1⁻¹)) => le_of_inv_le_inv this) (eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ ≤ (1⁻¹))) one_inv)) h)

theorem inv_le_one_of_one_le {α : Type u} [ordered_comm_group α] {a : α} (h : 1 ≤ a) : a⁻¹ ≤ 1 :=
  (fun (this : a⁻¹ ≤ (1⁻¹)) => eq.mp (Eq._oldrec (Eq.refl (a⁻¹ ≤ (1⁻¹))) one_inv) this) (inv_le_inv' h)

theorem le_one_of_one_le_inv {α : Type u} [ordered_comm_group α] {a : α} (h : 1 ≤ (a⁻¹)) : a ≤ 1 :=
  (fun (this : 1⁻¹ ≤ (a⁻¹)) => le_of_inv_le_inv this) (eq.mpr (id (Eq._oldrec (Eq.refl (1⁻¹ ≤ (a⁻¹))) one_inv)) h)

theorem neg_nonneg_of_nonpos {α : Type u} [ordered_add_comm_group α] {a : α} (h : a ≤ 0) : 0 ≤ -a :=
  (fun (this : -0 ≤ -a) => eq.mp (Eq._oldrec (Eq.refl (-0 ≤ -a)) neg_zero) this) (neg_le_neg h)

theorem neg_lt_neg {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} (h : a < b) : -b < -a := sorry

theorem lt_of_neg_lt_neg {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} (h : -b < -a) : a < b :=
  neg_neg a ▸ neg_neg b ▸ neg_lt_neg h

theorem pos_of_neg_neg {α : Type u} [ordered_add_comm_group α] {a : α} (h : -a < 0) : 0 < a :=
  (fun (this : -a < -0) => lt_of_neg_lt_neg this) (eq.mpr (id (Eq._oldrec (Eq.refl (-a < -0)) neg_zero)) h)

theorem inv_inv_of_one_lt {α : Type u} [ordered_comm_group α] {a : α} (h : 1 < a) : a⁻¹ < 1 :=
  (fun (this : a⁻¹ < (1⁻¹)) => eq.mp (Eq._oldrec (Eq.refl (a⁻¹ < (1⁻¹))) one_inv) this) (inv_lt_inv' h)

theorem inv_of_one_lt_inv {α : Type u} [ordered_comm_group α] {a : α} (h : 1 < (a⁻¹)) : a < 1 :=
  (fun (this : 1⁻¹ < (a⁻¹)) => lt_of_inv_lt_inv this) (eq.mpr (id (Eq._oldrec (Eq.refl (1⁻¹ < (a⁻¹))) one_inv)) h)

theorem one_lt_inv_of_inv {α : Type u} [ordered_comm_group α] {a : α} (h : a < 1) : 1 < (a⁻¹) :=
  (fun (this : 1⁻¹ < (a⁻¹)) => eq.mp (Eq._oldrec (Eq.refl (1⁻¹ < (a⁻¹))) one_inv) this) (inv_lt_inv' h)

theorem le_inv_of_le_inv {α : Type u} [ordered_comm_group α] {a : α} {b : α} (h : a ≤ (b⁻¹)) : b ≤ (a⁻¹) :=
  eq.mp (Eq._oldrec (Eq.refl (b⁻¹⁻¹ ≤ (a⁻¹))) (inv_inv b)) (inv_le_inv' h)

theorem neg_le_of_neg_le {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} (h : -a ≤ b) : -b ≤ a :=
  eq.mp (Eq._oldrec (Eq.refl (-b ≤ --a)) (neg_neg a)) (neg_le_neg h)

theorem lt_inv_of_lt_inv {α : Type u} [ordered_comm_group α] {a : α} {b : α} (h : a < (b⁻¹)) : b < (a⁻¹) :=
  eq.mp (Eq._oldrec (Eq.refl (b⁻¹⁻¹ < (a⁻¹))) (inv_inv b)) (inv_lt_inv' h)

theorem neg_lt_of_neg_lt {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} (h : -a < b) : -b < a :=
  eq.mp (Eq._oldrec (Eq.refl (-b < --a)) (neg_neg a)) (neg_lt_neg h)

theorem add_le_of_le_neg_add {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : b ≤ -a + c) : a + b ≤ c :=
  eq.mp (Eq._oldrec (Eq.refl (a + b ≤ a + (-a + c))) (add_neg_cancel_left a c)) (add_le_add_left h a)

theorem le_inv_mul_of_mul_le {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} (h : a * b ≤ c) : b ≤ a⁻¹ * c :=
  eq.mp (Eq._oldrec (Eq.refl (a⁻¹ * (a * b) ≤ a⁻¹ * c)) (inv_mul_cancel_left a b)) (mul_le_mul_left' h (a⁻¹))

theorem le_mul_of_inv_mul_le {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} (h : b⁻¹ * a ≤ c) : a ≤ b * c :=
  eq.mp (Eq._oldrec (Eq.refl (b * (b⁻¹ * a) ≤ b * c)) (mul_inv_cancel_left b a)) (mul_le_mul_left' h b)

theorem inv_mul_le_of_le_mul {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} (h : a ≤ b * c) : b⁻¹ * a ≤ c :=
  eq.mp (Eq._oldrec (Eq.refl (b⁻¹ * a ≤ b⁻¹ * (b * c))) (inv_mul_cancel_left b c)) (mul_le_mul_left' h (b⁻¹))

theorem le_mul_of_inv_mul_le_left {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} (h : b⁻¹ * a ≤ c) : a ≤ b * c :=
  le_mul_of_inv_mul_le h

theorem neg_add_le_left_of_le_add {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : a ≤ b + c) : -b + a ≤ c :=
  neg_add_le_of_le_add h

theorem le_add_of_neg_add_le_right {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : -c + a ≤ b) : a ≤ b + c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b + c)) (add_comm b c))) (le_add_of_neg_add_le h)

theorem inv_mul_le_right_of_le_mul {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} (h : a ≤ b * c) : c⁻¹ * a ≤ b :=
  inv_mul_le_left_of_le_mul (eq.mp (Eq._oldrec (Eq.refl (a ≤ b * c)) (mul_comm b c)) h)

theorem mul_lt_of_lt_inv_mul {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} (h : b < a⁻¹ * c) : a * b < c :=
  eq.mp (Eq._oldrec (Eq.refl (a * b < a * (a⁻¹ * c))) (mul_inv_cancel_left a c)) (mul_lt_mul_left' h a)

theorem lt_neg_add_of_add_lt {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : a + b < c) : b < -a + c :=
  eq.mp (Eq._oldrec (Eq.refl (-a + (a + b) < -a + c)) (neg_add_cancel_left a b)) (add_lt_add_left h (-a))

theorem lt_mul_of_inv_mul_lt {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} (h : b⁻¹ * a < c) : a < b * c :=
  eq.mp (Eq._oldrec (Eq.refl (b * (b⁻¹ * a) < b * c)) (mul_inv_cancel_left b a)) (mul_lt_mul_left' h b)

theorem neg_add_lt_of_lt_add {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : a < b + c) : -b + a < c :=
  eq.mp (Eq._oldrec (Eq.refl (-b + a < -b + (b + c))) (neg_add_cancel_left b c)) (add_lt_add_left h (-b))

theorem lt_add_of_neg_add_lt_left {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : -b + a < c) : a < b + c :=
  lt_add_of_neg_add_lt h

theorem neg_add_lt_left_of_lt_add {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : a < b + c) : -b + a < c :=
  neg_add_lt_of_lt_add h

theorem lt_add_of_neg_add_lt_right {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : -c + a < b) : a < b + c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a < b + c)) (add_comm b c))) (lt_add_of_neg_add_lt h)

theorem neg_add_lt_right_of_lt_add {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : a < b + c) : -c + a < b :=
  neg_add_lt_of_lt_add (eq.mp (Eq._oldrec (Eq.refl (a < b + c)) (add_comm b c)) h)

@[simp] theorem neg_neg_iff_pos {α : Type u} [ordered_add_comm_group α] {a : α} : -a < 0 ↔ 0 < a :=
  { mp := pos_of_neg_neg, mpr := neg_neg_of_pos }

@[simp] theorem neg_le_neg_iff {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : -a ≤ -b ↔ b ≤ a := sorry

theorem inv_le' {α : Type u} [ordered_comm_group α] {a : α} {b : α} : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
  (fun (this : a⁻¹ ≤ (b⁻¹⁻¹) ↔ b⁻¹ ≤ a) => eq.mp (Eq._oldrec (Eq.refl (a⁻¹ ≤ (b⁻¹⁻¹) ↔ b⁻¹ ≤ a)) (inv_inv b)) this)
    inv_le_inv_iff

theorem le_inv' {α : Type u} [ordered_comm_group α] {a : α} {b : α} : a ≤ (b⁻¹) ↔ b ≤ (a⁻¹) :=
  (fun (this : a⁻¹⁻¹ ≤ (b⁻¹) ↔ b ≤ (a⁻¹)) => eq.mp (Eq._oldrec (Eq.refl (a⁻¹⁻¹ ≤ (b⁻¹) ↔ b ≤ (a⁻¹))) (inv_inv a)) this)
    inv_le_inv_iff

theorem inv_le_iff_one_le_mul {α : Type u} [ordered_comm_group α] {a : α} {b : α} : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
  iff.trans (iff.symm (mul_le_mul_iff_right a))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ * a ≤ b * a ↔ 1 ≤ b * a)) (inv_mul_self a))) (iff.refl (1 ≤ b * a)))

theorem neg_le_iff_add_nonneg' {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : -a ≤ b ↔ 0 ≤ a + b :=
  iff.trans (iff.symm (add_le_add_iff_left a))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -a ≤ a + b ↔ 0 ≤ a + b)) (add_neg_self a))) (iff.refl (0 ≤ a + b)))

theorem inv_lt_iff_one_lt_mul {α : Type u} [ordered_comm_group α] {a : α} {b : α} : a⁻¹ < b ↔ 1 < b * a :=
  iff.trans (iff.symm (mul_lt_mul_iff_right a))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ * a < b * a ↔ 1 < b * a)) (inv_mul_self a))) (iff.refl (1 < b * a)))

theorem neg_lt_iff_pos_add' {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : -a < b ↔ 0 < a + b :=
  iff.trans (iff.symm (add_lt_add_iff_left a))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -a < a + b ↔ 0 < a + b)) (add_neg_self a))) (iff.refl (0 < a + b)))

theorem le_neg_iff_add_nonpos {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : a ≤ -b ↔ a + b ≤ 0 :=
  iff.trans (iff.symm (add_le_add_iff_right b))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + b ≤ -b + b ↔ a + b ≤ 0)) (neg_add_self b))) (iff.refl (a + b ≤ 0)))

theorem le_inv_iff_mul_le_one' {α : Type u} [ordered_comm_group α] {a : α} {b : α} : a ≤ (b⁻¹) ↔ b * a ≤ 1 :=
  iff.trans (iff.symm (mul_le_mul_iff_left b))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a ≤ b * (b⁻¹) ↔ b * a ≤ 1)) (mul_inv_self b))) (iff.refl (b * a ≤ 1)))

theorem lt_neg_iff_add_neg {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : a < -b ↔ a + b < 0 :=
  iff.trans (iff.symm (add_lt_add_iff_right b))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + b < -b + b ↔ a + b < 0)) (neg_add_self b))) (iff.refl (a + b < 0)))

theorem lt_inv_iff_mul_lt_one' {α : Type u} [ordered_comm_group α] {a : α} {b : α} : a < (b⁻¹) ↔ b * a < 1 :=
  iff.trans (iff.symm (mul_lt_mul_iff_left b))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a < b * (b⁻¹) ↔ b * a < 1)) (mul_inv_self b))) (iff.refl (b * a < 1)))

@[simp] theorem inv_le_one' {α : Type u} [ordered_comm_group α] {a : α} : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
  (fun (this : a⁻¹ ≤ (1⁻¹) ↔ 1 ≤ a) => eq.mp (Eq._oldrec (Eq.refl (a⁻¹ ≤ (1⁻¹) ↔ 1 ≤ a)) one_inv) this) inv_le_inv_iff

@[simp] theorem one_le_inv' {α : Type u} [ordered_comm_group α] {a : α} : 1 ≤ (a⁻¹) ↔ a ≤ 1 :=
  (fun (this : 1⁻¹ ≤ (a⁻¹) ↔ a ≤ 1) => eq.mp (Eq._oldrec (Eq.refl (1⁻¹ ≤ (a⁻¹) ↔ a ≤ 1)) one_inv) this) inv_le_inv_iff

theorem inv_le_self {α : Type u} [ordered_comm_group α] {a : α} (h : 1 ≤ a) : a⁻¹ ≤ a :=
  le_trans (iff.mpr inv_le_one' h) h

theorem self_le_inv {α : Type u} [ordered_comm_group α] {a : α} (h : a ≤ 1) : a ≤ (a⁻¹) :=
  le_trans h (iff.mpr one_le_inv' h)

@[simp] theorem neg_lt_neg_iff {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : -a < -b ↔ b < a := sorry

theorem neg_lt_zero {α : Type u} [ordered_add_comm_group α] {a : α} : -a < 0 ↔ 0 < a :=
  (fun (this : -a < -0 ↔ 0 < a) => eq.mp (Eq._oldrec (Eq.refl (-a < -0 ↔ 0 < a)) neg_zero) this) neg_lt_neg_iff

theorem one_lt_inv' {α : Type u} [ordered_comm_group α] {a : α} : 1 < (a⁻¹) ↔ a < 1 :=
  (fun (this : 1⁻¹ < (a⁻¹) ↔ a < 1) => eq.mp (Eq._oldrec (Eq.refl (1⁻¹ < (a⁻¹) ↔ a < 1)) one_inv) this) inv_lt_inv_iff

theorem neg_lt {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : -a < b ↔ -b < a :=
  (fun (this : -a < --b ↔ -b < a) => eq.mp (Eq._oldrec (Eq.refl (-a < --b ↔ -b < a)) (neg_neg b)) this) neg_lt_neg_iff

theorem lt_neg {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : a < -b ↔ b < -a :=
  (fun (this : --a < -b ↔ b < -a) => eq.mp (Eq._oldrec (Eq.refl ( --a < -b ↔ b < -a)) (neg_neg a)) this) neg_lt_neg_iff

theorem neg_lt_self {α : Type u} [ordered_add_comm_group α] {a : α} (h : 0 < a) : -a < a :=
  has_lt.lt.trans (iff.mpr neg_lt_zero h) h

theorem le_inv_mul_iff_mul_le {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} : b ≤ a⁻¹ * c ↔ a * b ≤ c :=
  (fun (this : a⁻¹ * (a * b) ≤ a⁻¹ * c ↔ a * b ≤ c) =>
      eq.mp (Eq._oldrec (Eq.refl (a⁻¹ * (a * b) ≤ a⁻¹ * c ↔ a * b ≤ c)) (inv_mul_cancel_left a b)) this)
    (mul_le_mul_iff_left (a⁻¹))

@[simp] theorem inv_mul_le_iff_le_mul {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} : b⁻¹ * a ≤ c ↔ a ≤ b * c :=
  (fun (this : b⁻¹ * a ≤ b⁻¹ * (b * c) ↔ a ≤ b * c) =>
      eq.mp (Eq._oldrec (Eq.refl (b⁻¹ * a ≤ b⁻¹ * (b * c) ↔ a ≤ b * c)) (inv_mul_cancel_left b c)) this)
    (mul_le_mul_iff_left (b⁻¹))

theorem mul_inv_le_iff_le_mul {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} : a * (c⁻¹) ≤ b ↔ a ≤ b * c := sorry

@[simp] theorem mul_inv_le_iff_le_mul' {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} : a * (b⁻¹) ≤ c ↔ a ≤ b * c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (b⁻¹) ≤ c ↔ a ≤ b * c)) (Eq.symm (propext inv_mul_le_iff_le_mul))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (b⁻¹) ≤ c ↔ b⁻¹ * a ≤ c)) (mul_comm a (b⁻¹)))) (iff.refl (b⁻¹ * a ≤ c)))

theorem neg_add_le_iff_le_add' {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : -c + a ≤ b ↔ a ≤ b + c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-c + a ≤ b ↔ a ≤ b + c)) (propext neg_add_le_iff_le_add)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ c + b ↔ a ≤ b + c)) (add_comm c b))) (iff.refl (a ≤ b + c)))

@[simp] theorem lt_neg_add_iff_add_lt {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : b < -a + c ↔ a + b < c :=
  (fun (this : -a + (a + b) < -a + c ↔ a + b < c) =>
      eq.mp (Eq._oldrec (Eq.refl (-a + (a + b) < -a + c ↔ a + b < c)) (neg_add_cancel_left a b)) this)
    (add_lt_add_iff_left (-a))

@[simp] theorem inv_mul_lt_iff_lt_mul {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} : b⁻¹ * a < c ↔ a < b * c :=
  (fun (this : b⁻¹ * a < b⁻¹ * (b * c) ↔ a < b * c) =>
      eq.mp (Eq._oldrec (Eq.refl (b⁻¹ * a < b⁻¹ * (b * c) ↔ a < b * c)) (inv_mul_cancel_left b c)) this)
    (mul_lt_mul_iff_left (b⁻¹))

theorem inv_mul_lt_iff_lt_mul_right {α : Type u} [ordered_comm_group α] {a : α} {b : α} {c : α} : c⁻¹ * a < b ↔ a < b * c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (c⁻¹ * a < b ↔ a < b * c)) (propext inv_mul_lt_iff_lt_mul)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a < c * b ↔ a < b * c)) (mul_comm c b))) (iff.refl (a < b * c)))

theorem add_neg_le_add_neg_iff {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} {d : α} : a + -b ≤ c + -d ↔ a + d ≤ c + b := sorry

theorem sub_le_sub {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} {d : α} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c := sorry

theorem sub_lt_sub {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} {d : α} (hab : a < b) (hcd : c < d) : a - d < b - c := sorry

@[simp] theorem sub_le_self_iff {α : Type u} [ordered_add_comm_group α] (a : α) {b : α} : a - b ≤ a ↔ 0 ≤ b := sorry

theorem sub_le_self {α : Type u} [ordered_add_comm_group α] (a : α) {b : α} : 0 ≤ b → a - b ≤ a :=
  iff.mpr (sub_le_self_iff a)

@[simp] theorem sub_lt_self_iff {α : Type u} [ordered_add_comm_group α] (a : α) {b : α} : a - b < a ↔ 0 < b := sorry

theorem sub_lt_self {α : Type u} [ordered_add_comm_group α] (a : α) {b : α} : 0 < b → a - b < a :=
  iff.mpr (sub_lt_self_iff a)

theorem sub_le_sub_iff {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} {d : α} : a - b ≤ c - d ↔ a + d ≤ c + b := sorry

@[simp] theorem sub_le_sub_iff_left {α : Type u} [ordered_add_comm_group α] (a : α) {b : α} {c : α} : a - b ≤ a - c ↔ c ≤ b := sorry

theorem sub_le_sub_left {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} (h : a ≤ b) (c : α) : c - b ≤ c - a :=
  iff.mpr (sub_le_sub_iff_left c) h

@[simp] theorem sub_le_sub_iff_right {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} (c : α) : a - c ≤ b - c ↔ a ≤ b := sorry

theorem sub_le_sub_right {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} (h : a ≤ b) (c : α) : a - c ≤ b - c :=
  iff.mpr (sub_le_sub_iff_right c) h

@[simp] theorem sub_lt_sub_iff_left {α : Type u} [ordered_add_comm_group α] (a : α) {b : α} {c : α} : a - b < a - c ↔ c < b := sorry

theorem sub_lt_sub_left {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} (h : a < b) (c : α) : c - b < c - a :=
  iff.mpr (sub_lt_sub_iff_left c) h

@[simp] theorem sub_lt_sub_iff_right {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} (c : α) : a - c < b - c ↔ a < b := sorry

theorem sub_lt_sub_right {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} (h : a < b) (c : α) : a - c < b - c :=
  iff.mpr (sub_lt_sub_iff_right c) h

@[simp] theorem sub_nonneg {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : 0 ≤ a - b ↔ b ≤ a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ a - b ↔ b ≤ a)) (Eq.symm (sub_self a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - a ≤ a - b ↔ b ≤ a)) (propext (sub_le_sub_iff_left a)))) (iff.refl (b ≤ a)))

theorem sub_nonneg_of_le {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : b ≤ a → 0 ≤ a - b :=
  iff.mpr sub_nonneg

@[simp] theorem sub_nonpos {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : a - b ≤ 0 ↔ a ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b ≤ 0 ↔ a ≤ b)) (Eq.symm (sub_self b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - b ≤ b - b ↔ a ≤ b)) (propext (sub_le_sub_iff_right b)))) (iff.refl (a ≤ b)))

theorem le_of_sub_nonpos {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : a - b ≤ 0 → a ≤ b :=
  iff.mp sub_nonpos

@[simp] theorem sub_pos {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : 0 < a - b ↔ b < a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < a - b ↔ b < a)) (Eq.symm (sub_self a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - a < a - b ↔ b < a)) (propext (sub_lt_sub_iff_left a)))) (iff.refl (b < a)))

theorem lt_of_sub_pos {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : 0 < a - b → b < a :=
  iff.mp sub_pos

@[simp] theorem sub_lt_zero {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : a - b < 0 ↔ a < b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b < 0 ↔ a < b)) (Eq.symm (sub_self b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - b < b - b ↔ a < b)) (propext (sub_lt_sub_iff_right b)))) (iff.refl (a < b)))

theorem lt_of_sub_neg {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} : a - b < 0 → a < b :=
  iff.mp sub_lt_zero

theorem le_sub_iff_add_le' {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : b ≤ c - a ↔ a + b ≤ c := sorry

theorem le_sub_iff_add_le {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a ≤ c - b ↔ a + b ≤ c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ c - b ↔ a + b ≤ c)) (propext le_sub_iff_add_le')))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b + a ≤ c ↔ a + b ≤ c)) (add_comm b a))) (iff.refl (a + b ≤ c)))

theorem add_le_of_le_sub_right {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a ≤ c - b → a + b ≤ c :=
  iff.mp le_sub_iff_add_le

theorem sub_le_iff_le_add' {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a - b ≤ c ↔ a ≤ b + c := sorry

theorem le_sub_left_of_add_le {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a + b ≤ c → b ≤ c - a :=
  iff.mpr le_sub_iff_add_le'

theorem sub_le_iff_le_add {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a - c ≤ b ↔ a ≤ b + c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - c ≤ b ↔ a ≤ b + c)) (propext sub_le_iff_le_add')))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ c + b ↔ a ≤ b + c)) (add_comm c b))) (iff.refl (a ≤ b + c)))

@[simp] theorem neg_le_sub_iff_le_add {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : -b ≤ a - c ↔ c ≤ a + b :=
  iff.trans le_sub_iff_add_le neg_add_le_iff_le_add'

theorem neg_le_sub_iff_le_add' {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : -a ≤ b - c ↔ c ≤ a + b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-a ≤ b - c ↔ c ≤ a + b)) (propext neg_le_sub_iff_le_add)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (c ≤ b + a ↔ c ≤ a + b)) (add_comm b a))) (iff.refl (c ≤ a + b)))

theorem sub_le {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a - b ≤ c ↔ a - c ≤ b :=
  iff.trans sub_le_iff_le_add' (iff.symm sub_le_iff_le_add)

theorem le_sub {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a ≤ b - c ↔ c ≤ b - a :=
  iff.trans le_sub_iff_add_le' (iff.symm le_sub_iff_add_le)

theorem lt_sub_iff_add_lt' {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : b < c - a ↔ a + b < c := sorry

theorem add_lt_of_lt_sub_left {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : b < c - a → a + b < c :=
  iff.mp lt_sub_iff_add_lt'

theorem lt_sub_iff_add_lt {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a < c - b ↔ a + b < c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a < c - b ↔ a + b < c)) (propext lt_sub_iff_add_lt')))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b + a < c ↔ a + b < c)) (add_comm b a))) (iff.refl (a + b < c)))

theorem lt_sub_right_of_add_lt {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a + b < c → a < c - b :=
  iff.mpr lt_sub_iff_add_lt

theorem sub_lt_iff_lt_add' {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a - b < c ↔ a < b + c := sorry

theorem lt_add_of_sub_left_lt {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a - b < c → a < b + c :=
  iff.mp sub_lt_iff_lt_add'

theorem sub_lt_iff_lt_add {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a - c < b ↔ a < b + c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - c < b ↔ a < b + c)) (propext sub_lt_iff_lt_add')))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a < c + b ↔ a < b + c)) (add_comm c b))) (iff.refl (a < b + c)))

theorem sub_right_lt_of_lt_add {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a < b + c → a - c < b :=
  iff.mpr sub_lt_iff_lt_add

@[simp] theorem neg_lt_sub_iff_lt_add {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : -b < a - c ↔ c < a + b :=
  iff.trans lt_sub_iff_add_lt neg_add_lt_iff_lt_add_right

theorem neg_lt_sub_iff_lt_add' {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : -a < b - c ↔ c < a + b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-a < b - c ↔ c < a + b)) (propext neg_lt_sub_iff_lt_add)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (c < b + a ↔ c < a + b)) (add_comm b a))) (iff.refl (c < a + b)))

theorem sub_lt {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a - b < c ↔ a - c < b :=
  iff.trans sub_lt_iff_lt_add' (iff.symm sub_lt_iff_lt_add)

theorem lt_sub {α : Type u} [ordered_add_comm_group α] {a : α} {b : α} {c : α} : a < b - c ↔ c < b - a :=
  iff.trans lt_sub_iff_add_lt' (iff.symm lt_sub_iff_add_lt)

/-!

### Linearly ordered commutative groups

-/

/-- A linearly ordered additive commutative group is an
additive commutative group with a linear order in which
addition is monotone. -/
class linear_ordered_add_comm_group (α : Type u) 
extends add_comm_group α, linear_order α
where
  add_le_add_left : ∀ (a b : α), a ≤ b → ∀ (c : α), c + a ≤ c + b

/-- A linearly ordered commutative group is a
commutative group with a linear order in which
multiplication is monotone. -/
class linear_ordered_comm_group (α : Type u) 
extends linear_order α, comm_group α
where
  mul_le_mul_left : ∀ (a b : α), a ≤ b → ∀ (c : α), c * a ≤ c * b

protected instance linear_ordered_comm_group.to_ordered_comm_group (α : Type u) [s : linear_ordered_comm_group α] : ordered_comm_group α :=
  ordered_comm_group.mk linear_ordered_comm_group.mul linear_ordered_comm_group.mul_assoc linear_ordered_comm_group.one
    linear_ordered_comm_group.one_mul linear_ordered_comm_group.mul_one linear_ordered_comm_group.inv
    linear_ordered_comm_group.div linear_ordered_comm_group.mul_left_inv linear_ordered_comm_group.mul_comm
    linear_ordered_comm_group.le linear_ordered_comm_group.lt linear_ordered_comm_group.le_refl
    linear_ordered_comm_group.le_trans linear_ordered_comm_group.le_antisymm linear_ordered_comm_group.mul_le_mul_left

protected instance linear_ordered_add_comm_group.to_linear_ordered_cancel_add_comm_monoid {α : Type u} [linear_ordered_add_comm_group α] : linear_ordered_cancel_add_comm_monoid α :=
  linear_ordered_cancel_add_comm_monoid.mk linear_ordered_add_comm_group.add linear_ordered_add_comm_group.add_assoc sorry
    linear_ordered_add_comm_group.zero linear_ordered_add_comm_group.zero_add linear_ordered_add_comm_group.add_zero
    linear_ordered_add_comm_group.add_comm sorry linear_ordered_add_comm_group.le linear_ordered_add_comm_group.lt
    linear_ordered_add_comm_group.le_refl linear_ordered_add_comm_group.le_trans linear_ordered_add_comm_group.le_antisymm
    linear_ordered_add_comm_group.add_le_add_left sorry linear_ordered_add_comm_group.le_total
    linear_ordered_add_comm_group.decidable_le linear_ordered_add_comm_group.decidable_eq
    linear_ordered_add_comm_group.decidable_lt

theorem linear_ordered_add_comm_group.add_lt_add_left {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) (h : a < b) (c : α) : c + a < c + b :=
  ordered_add_comm_group.add_lt_add_left a b h c

theorem le_of_forall_pos_le_add {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} [densely_ordered α] (h : ∀ (ε : α), 0 < ε → a ≤ b + ε) : a ≤ b :=
  le_of_forall_le_of_dense
    fun (c : α) (hc : c > b) => trans_rel_left LessEq (h (c - b) (sub_pos_of_lt hc)) (add_sub_cancel'_right b c)

theorem min_neg_neg {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) : min (-a) (-b) = -max a b :=
  Eq.symm (monotone.map_max fun (a b : α) => neg_le_neg)

theorem max_neg_neg {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) : max (-a) (-b) = -min a b :=
  Eq.symm (monotone.map_min fun (a b : α) => neg_le_neg)

theorem min_sub_sub_right {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) (c : α) : min (a - c) (b - c) = min a b - c := sorry

theorem max_sub_sub_right {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) (c : α) : max (a - c) (b - c) = max a b - c := sorry

theorem min_sub_sub_left {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) (c : α) : min (a - b) (a - c) = a - max b c := sorry

theorem max_sub_sub_left {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) (c : α) : max (a - b) (a - c) = a - min b c := sorry

theorem max_zero_sub_eq_self {α : Type u} [linear_ordered_add_comm_group α] (a : α) : max a 0 - max (-a) 0 = a := sorry

/-- `abs a` is the absolute value of `a`. -/
def abs {α : Type u} [linear_ordered_add_comm_group α] (a : α) : α :=
  max a (-a)

theorem abs_of_nonneg {α : Type u} [linear_ordered_add_comm_group α] {a : α} (h : 0 ≤ a) : abs a = a :=
  max_eq_left (has_le.le.trans (iff.mpr neg_nonpos h) h)

theorem abs_of_pos {α : Type u} [linear_ordered_add_comm_group α] {a : α} (h : 0 < a) : abs a = a :=
  abs_of_nonneg (has_lt.lt.le h)

theorem abs_of_nonpos {α : Type u} [linear_ordered_add_comm_group α] {a : α} (h : a ≤ 0) : abs a = -a :=
  max_eq_right (has_le.le.trans h (iff.mpr neg_nonneg h))

theorem abs_of_neg {α : Type u} [linear_ordered_add_comm_group α] {a : α} (h : a < 0) : abs a = -a :=
  abs_of_nonpos (has_lt.lt.le h)

@[simp] theorem abs_zero {α : Type u} [linear_ordered_add_comm_group α] : abs 0 = 0 :=
  abs_of_nonneg le_rfl

@[simp] theorem abs_neg {α : Type u} [linear_ordered_add_comm_group α] (a : α) : abs (-a) = abs a := sorry

@[simp] theorem abs_pos {α : Type u} [linear_ordered_add_comm_group α] {a : α} : 0 < abs a ↔ a ≠ 0 := sorry

theorem abs_pos_of_pos {α : Type u} [linear_ordered_add_comm_group α] {a : α} (h : 0 < a) : 0 < abs a :=
  iff.mpr abs_pos (ne.symm (has_lt.lt.ne h))

theorem abs_pos_of_neg {α : Type u} [linear_ordered_add_comm_group α] {a : α} (h : a < 0) : 0 < abs a :=
  iff.mpr abs_pos (has_lt.lt.ne h)

theorem abs_sub {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) : abs (a - b) = abs (b - a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs (a - b) = abs (b - a))) (Eq.symm (neg_sub b a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (abs (-(b - a)) = abs (b - a))) (abs_neg (b - a)))) (Eq.refl (abs (b - a))))

theorem abs_le' {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} : abs a ≤ b ↔ a ≤ b ∧ -a ≤ b :=
  max_le_iff

theorem abs_le {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} : abs a ≤ b ↔ -b ≤ a ∧ a ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs a ≤ b ↔ -b ≤ a ∧ a ≤ b)) (propext abs_le')))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b ∧ -a ≤ b ↔ -b ≤ a ∧ a ≤ b)) (propext and.comm)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (-a ≤ b ∧ a ≤ b ↔ -b ≤ a ∧ a ≤ b)) (propext neg_le))) (iff.refl (-b ≤ a ∧ a ≤ b))))

theorem le_abs_self {α : Type u} [linear_ordered_add_comm_group α] (a : α) : a ≤ abs a :=
  le_max_left a (-a)

theorem neg_le_abs_self {α : Type u} [linear_ordered_add_comm_group α] (a : α) : -a ≤ abs a :=
  le_max_right a (-a)

theorem abs_nonneg {α : Type u} [linear_ordered_add_comm_group α] (a : α) : 0 ≤ abs a :=
  or.elim (le_total 0 a) (fun (h : 0 ≤ a) => has_le.le.trans h (le_abs_self a))
    fun (h : a ≤ 0) => has_le.le.trans (iff.mpr neg_nonneg h) (neg_le_abs_self a)

@[simp] theorem abs_abs {α : Type u} [linear_ordered_add_comm_group α] (a : α) : abs (abs a) = abs a :=
  abs_of_nonneg (abs_nonneg a)

@[simp] theorem abs_eq_zero {α : Type u} [linear_ordered_add_comm_group α] {a : α} : abs a = 0 ↔ a = 0 :=
  iff.mp not_iff_not (iff.trans ne_comm (iff.trans (iff.symm (has_le.le.lt_iff_ne (abs_nonneg a))) abs_pos))

@[simp] theorem abs_nonpos_iff {α : Type u} [linear_ordered_add_comm_group α] {a : α} : abs a ≤ 0 ↔ a = 0 :=
  iff.trans (has_le.le.le_iff_eq (abs_nonneg a)) abs_eq_zero

theorem abs_lt {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} : abs a < b ↔ -b < a ∧ a < b :=
  iff.trans max_lt_iff
    (iff.trans and.comm
      (eq.mpr (id (Eq._oldrec (Eq.refl (-a < b ∧ a < b ↔ -b < a ∧ a < b)) (propext neg_lt))) (iff.refl (-b < a ∧ a < b))))

theorem lt_abs {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} : a < abs b ↔ a < b ∨ a < -b :=
  lt_max_iff

theorem max_sub_min_eq_abs' {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) : max a b - min a b = abs (a - b) := sorry

theorem max_sub_min_eq_abs {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) : max a b - min a b = abs (b - a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (max a b - min a b = abs (b - a))) (abs_sub b a))) (max_sub_min_eq_abs' a b)

theorem abs_add {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) : abs (a + b) ≤ abs a + abs b := sorry

theorem abs_sub_le_iff {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} {c : α} : abs (a - b) ≤ c ↔ a - b ≤ c ∧ b - a ≤ c := sorry

theorem abs_sub_lt_iff {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} {c : α} : abs (a - b) < c ↔ a - b < c ∧ b - a < c := sorry

theorem sub_le_of_abs_sub_le_left {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : abs (a - b) ≤ c) : b - c ≤ a :=
  iff.mp sub_le (and.right (iff.mp abs_sub_le_iff h))

theorem sub_le_of_abs_sub_le_right {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : abs (a - b) ≤ c) : a - c ≤ b :=
  sub_le_of_abs_sub_le_left (abs_sub a b ▸ h)

theorem sub_lt_of_abs_sub_lt_left {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : abs (a - b) < c) : b - c < a :=
  iff.mp sub_lt (and.right (iff.mp abs_sub_lt_iff h))

theorem sub_lt_of_abs_sub_lt_right {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} {c : α} (h : abs (a - b) < c) : a - c < b :=
  sub_lt_of_abs_sub_lt_left (abs_sub a b ▸ h)

theorem abs_sub_abs_le_abs_sub {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) : abs a - abs b ≤ abs (a - b) := sorry

theorem abs_abs_sub_abs_le_abs_sub {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) : abs (abs a - abs b) ≤ abs (a - b) := sorry

theorem abs_eq {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} (hb : 0 ≤ b) : abs a = b ↔ a = b ∨ a = -b := sorry

theorem abs_le_max_abs_abs {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} {c : α} (hab : a ≤ b) (hbc : b ≤ c) : abs b ≤ max (abs a) (abs c) := sorry

theorem abs_le_abs {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} (h₀ : a ≤ b) (h₁ : -a ≤ b) : abs a ≤ abs b :=
  has_le.le.trans (iff.mpr abs_le' { left := h₀, right := h₁ }) (le_abs_self b)

theorem abs_max_sub_max_le_abs {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) (c : α) : abs (max a c - max b c) ≤ abs (a - b) := sorry

theorem eq_zero_of_neg_eq {α : Type u} [linear_ordered_add_comm_group α] {a : α} (h : -a = a) : a = 0 := sorry

theorem eq_of_abs_sub_eq_zero {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} (h : abs (a - b) = 0) : a = b :=
  iff.mp sub_eq_zero (iff.mp abs_eq_zero h)

theorem abs_by_cases {α : Type u} [linear_ordered_add_comm_group α] (P : α → Prop) {a : α} (h1 : P a) (h2 : P (-a)) : P (abs a) :=
  sup_ind a (-a) h1 h2

theorem abs_sub_le {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) (c : α) : abs (a - c) ≤ abs (a - b) + abs (b - c) := sorry

theorem abs_add_three {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) (c : α) : abs (a + b + c) ≤ abs a + abs b + abs c :=
  has_le.le.trans (abs_add (a + b) c) (add_le_add_right (abs_add a b) (abs c))

theorem dist_bdd_within_interval {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} {lb : α} {ub : α} (hal : lb ≤ a) (hau : a ≤ ub) (hbl : lb ≤ b) (hbu : b ≤ ub) : abs (a - b) ≤ ub - lb :=
  iff.mpr abs_sub_le_iff { left := sub_le_sub hau hbl, right := sub_le_sub hbu hal }

theorem eq_of_abs_sub_nonpos {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α} (h : abs (a - b) ≤ 0) : a = b :=
  eq_of_abs_sub_eq_zero (le_antisymm h (abs_nonneg (a - b)))

theorem exists_zero_lt {α : Type u} [linear_ordered_add_comm_group α] [nontrivial α] : ∃ (a : α), 0 < a := sorry

protected instance linear_ordered_add_comm_group.to_no_top_order {α : Type u} [linear_ordered_add_comm_group α] [nontrivial α] : no_top_order α :=
  no_top_order.mk
    (Exists.dcases_on exists_zero_lt fun (y : α) (hy : 0 < y) (a : α) => Exists.intro (a + y) (lt_add_of_pos_right a hy))

protected instance linear_ordered_add_comm_group.to_no_bot_order {α : Type u} [linear_ordered_add_comm_group α] [nontrivial α] : no_bot_order α :=
  no_bot_order.mk
    (Exists.dcases_on exists_zero_lt fun (y : α) (hy : 0 < y) (a : α) => Exists.intro (a - y) (sub_lt_self a hy))

/-- This is not so much a new structure as a construction mechanism
  for ordered groups, by specifying only the "positive cone" of the group. -/
class nonneg_add_comm_group (α : Type u_1) 
extends add_comm_group α
where
  nonneg : α → Prop
  pos : α → Prop
  pos_iff : autoParam (∀ (a : α), pos a ↔ nonneg a ∧ ¬nonneg (-a))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.order_laws_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "order_laws_tac") [])
  zero_nonneg : nonneg 0
  add_nonneg : ∀ {a b : α}, nonneg a → nonneg b → nonneg (a + b)
  nonneg_antisymm : ∀ {a : α}, nonneg a → nonneg (-a) → a = 0

namespace nonneg_add_comm_group


protected instance to_ordered_add_comm_group {α : Type u} [s : nonneg_add_comm_group α] : ordered_add_comm_group α :=
  ordered_add_comm_group.mk add add_assoc zero zero_add add_zero neg sub add_left_neg add_comm
    (fun (a b : α) => nonneg (b - a)) (fun (a b : α) => pos (b - a)) sorry sorry sorry sorry

theorem nonneg_def {α : Type u} [s : nonneg_add_comm_group α] {a : α} : nonneg a ↔ 0 ≤ a := sorry

theorem pos_def {α : Type u} [s : nonneg_add_comm_group α] {a : α} : pos a ↔ 0 < a := sorry

theorem not_zero_pos {α : Type u} [s : nonneg_add_comm_group α] : ¬pos 0 :=
  mt (iff.mp pos_def) (lt_irrefl 0)

theorem zero_lt_iff_nonneg_nonneg {α : Type u} [s : nonneg_add_comm_group α] {a : α} : 0 < a ↔ nonneg a ∧ ¬nonneg (-a) :=
  iff.trans (iff.symm pos_def) (pos_iff a)

theorem nonneg_total_iff {α : Type u} [s : nonneg_add_comm_group α] : (∀ (a : α), nonneg a ∨ nonneg (-a)) ↔ ∀ (a b : α), a ≤ b ∨ b ≤ a := sorry

/--
A `nonneg_add_comm_group` is a `linear_ordered_add_comm_group`
if `nonneg` is total and decidable.
-/
def to_linear_ordered_add_comm_group {α : Type u} [s : nonneg_add_comm_group α] [decidable_pred nonneg] (nonneg_total : ∀ (a : α), nonneg a ∨ nonneg (-a)) : linear_ordered_add_comm_group α :=
  linear_ordered_add_comm_group.mk ordered_add_comm_group.add sorry ordered_add_comm_group.zero sorry sorry
    ordered_add_comm_group.neg ordered_add_comm_group.sub sorry sorry LessEq Less sorry sorry sorry sorry
    (fun (a b : α) => _inst_1 (b - a))
    (linear_order.decidable_eq._default LessEq Less sorry sorry sorry fun (a b : α) => _inst_1 (b - a))
    (fun (a b : α) => Mathlib.decidable_lt_of_decidable_le a b) sorry

end nonneg_add_comm_group


namespace order_dual


protected instance ordered_add_comm_group {α : Type u} [ordered_add_comm_group α] : ordered_add_comm_group (order_dual α) :=
  ordered_add_comm_group.mk ordered_add_comm_monoid.add sorry ordered_add_comm_monoid.zero sorry sorry add_comm_group.neg
    (fun (a b : order_dual α) => a - b) sorry sorry ordered_add_comm_monoid.le ordered_add_comm_monoid.lt sorry sorry
    sorry sorry

protected instance linear_ordered_add_comm_group {α : Type u} [linear_ordered_add_comm_group α] : linear_ordered_add_comm_group (order_dual α) :=
  linear_ordered_add_comm_group.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg
    add_comm_group.sub sorry sorry linear_order.le linear_order.lt sorry sorry sorry sorry linear_order.decidable_le
    linear_order.decidable_eq linear_order.decidable_lt sorry

end order_dual


namespace prod


protected instance ordered_add_comm_group {G : Type u_1} {H : Type u_2} [ordered_add_comm_group G] [ordered_add_comm_group H] : ordered_add_comm_group (G × H) :=
  ordered_add_comm_group.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub
    sorry sorry partial_order.le partial_order.lt sorry sorry sorry sorry

end prod


protected instance multiplicative.ordered_comm_group {α : Type u} [ordered_add_comm_group α] : ordered_comm_group (multiplicative α) :=
  ordered_comm_group.mk comm_group.mul sorry comm_group.one sorry sorry comm_group.inv comm_group.div sorry sorry
    ordered_comm_monoid.le ordered_comm_monoid.lt sorry sorry sorry sorry

protected instance additive.ordered_add_comm_group {α : Type u} [ordered_comm_group α] : ordered_add_comm_group (additive α) :=
  ordered_add_comm_group.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub
    sorry sorry ordered_add_comm_monoid.le ordered_add_comm_monoid.lt sorry sorry sorry sorry

