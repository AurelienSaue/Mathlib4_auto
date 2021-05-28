/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.ordered_ring
import Mathlib.algebra.field
import Mathlib.tactic.monotonicity.basic
import Mathlib.PostPort

universes u_2 l u_1 

namespace Mathlib

/-!
  ### Linear ordered fields
  A linear ordered field is a field equipped with a linear order such that
  * addition respects the order: `a ≤ b → c + a ≤ c + b`;
  * multiplication of positives is positive: `0 < a → 0 < b → 0 < a * b`;
  * `0 < 1`.

  ### Main Definitions
  * `linear_ordered_field`: the class of linear ordered fields.
-/

/-- A linear ordered field is a field with a linear order respecting the operations. -/
class linear_ordered_field (α : Type u_2) 
extends linear_ordered_comm_ring α, field α
where

/-!
### Lemmas about pos, nonneg, nonpos, neg
-/

@[simp] theorem inv_pos {α : Type u_1} [linear_ordered_field α] {a : α} : 0 < (a⁻¹) ↔ 0 < a := sorry

@[simp] theorem inv_nonneg {α : Type u_1} [linear_ordered_field α] {a : α} : 0 ≤ (a⁻¹) ↔ 0 ≤ a := sorry

@[simp] theorem inv_lt_zero {α : Type u_1} [linear_ordered_field α] {a : α} : a⁻¹ < 0 ↔ a < 0 := sorry

@[simp] theorem inv_nonpos {α : Type u_1} [linear_ordered_field α] {a : α} : a⁻¹ ≤ 0 ↔ a ≤ 0 := sorry

theorem one_div_pos {α : Type u_1} [linear_ordered_field α] {a : α} : 0 < 1 / a ↔ 0 < a :=
  inv_eq_one_div a ▸ inv_pos

theorem one_div_neg {α : Type u_1} [linear_ordered_field α] {a : α} : 1 / a < 0 ↔ a < 0 :=
  inv_eq_one_div a ▸ inv_lt_zero

theorem one_div_nonneg {α : Type u_1} [linear_ordered_field α] {a : α} : 0 ≤ 1 / a ↔ 0 ≤ a :=
  inv_eq_one_div a ▸ inv_nonneg

theorem one_div_nonpos {α : Type u_1} [linear_ordered_field α] {a : α} : 1 / a ≤ 0 ↔ a ≤ 0 :=
  inv_eq_one_div a ▸ inv_nonpos

theorem div_pos_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} : 0 < a / b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := sorry

theorem div_neg_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} : a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := sorry

theorem div_nonneg_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} : 0 ≤ a / b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := sorry

theorem div_nonpos_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} : a / b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := sorry

theorem div_pos {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
  mul_pos ha (iff.mpr inv_pos hb)

theorem div_pos_of_neg_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : 0 < a / b :=
  mul_pos_of_neg_of_neg ha (iff.mpr inv_lt_zero hb)

theorem div_neg_of_neg_of_pos {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : 0 < b) : a / b < 0 :=
  mul_neg_of_neg_of_pos ha (iff.mpr inv_pos hb)

theorem div_neg_of_pos_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : b < 0) : a / b < 0 :=
  mul_neg_of_pos_of_neg ha (iff.mpr inv_lt_zero hb)

theorem div_nonneg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b :=
  mul_nonneg ha (iff.mpr inv_nonneg hb)

theorem div_nonneg_of_nonpos {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a / b :=
  mul_nonneg_of_nonpos_of_nonpos ha (iff.mpr inv_nonpos hb)

theorem div_nonpos_of_nonpos_of_nonneg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg ha (iff.mpr inv_nonneg hb)

theorem div_nonpos_of_nonneg_of_nonpos {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos ha (iff.mpr inv_nonpos hb)

/-!
### Relating one division with another term.
-/

theorem le_div_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := sorry

theorem le_div_iff' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b / c ↔ c * a ≤ b)) (mul_comm c a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b / c ↔ a * c ≤ b)) (propext (le_div_iff hc)))) (iff.refl (a * c ≤ b)))

theorem div_le_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := sorry

theorem div_le_iff' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b ≤ c ↔ a ≤ b * c)) (mul_comm b c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / b ≤ c ↔ a ≤ c * b)) (propext (div_le_iff hb)))) (iff.refl (a ≤ c * b)))

theorem lt_div_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : 0 < c) : a < b / c ↔ a * c < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff hc)

theorem lt_div_iff' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : 0 < c) : a < b / c ↔ c * a < b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a < b / c ↔ c * a < b)) (mul_comm c a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a < b / c ↔ a * c < b)) (propext (lt_div_iff hc)))) (iff.refl (a * c < b)))

theorem div_lt_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : 0 < c) : b / c < a ↔ b < a * c :=
  lt_iff_lt_of_le_iff_le (le_div_iff hc)

theorem div_lt_iff' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : 0 < c) : b / c < a ↔ b < c * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b / c < a ↔ b < c * a)) (mul_comm c a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b / c < a ↔ b < a * c)) (propext (div_lt_iff hc)))) (iff.refl (b < a * c)))

theorem inv_mul_le_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (h : 0 < b) : b⁻¹ * a ≤ c ↔ a ≤ b * c := sorry

theorem inv_mul_le_iff' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (h : 0 < b) : b⁻¹ * a ≤ c ↔ a ≤ c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b⁻¹ * a ≤ c ↔ a ≤ c * b)) (propext (inv_mul_le_iff h))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b * c ↔ a ≤ c * b)) (mul_comm b c))) (iff.refl (a ≤ c * b)))

theorem mul_inv_le_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (h : 0 < b) : a * (b⁻¹) ≤ c ↔ a ≤ b * c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (b⁻¹) ≤ c ↔ a ≤ b * c)) (mul_comm a (b⁻¹))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b⁻¹ * a ≤ c ↔ a ≤ b * c)) (propext (inv_mul_le_iff h)))) (iff.refl (a ≤ b * c)))

theorem mul_inv_le_iff' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (h : 0 < b) : a * (b⁻¹) ≤ c ↔ a ≤ c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (b⁻¹) ≤ c ↔ a ≤ c * b)) (mul_comm a (b⁻¹))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b⁻¹ * a ≤ c ↔ a ≤ c * b)) (propext (inv_mul_le_iff' h)))) (iff.refl (a ≤ c * b)))

theorem inv_mul_lt_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (h : 0 < b) : b⁻¹ * a < c ↔ a < b * c := sorry

theorem inv_mul_lt_iff' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (h : 0 < b) : b⁻¹ * a < c ↔ a < c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b⁻¹ * a < c ↔ a < c * b)) (propext (inv_mul_lt_iff h))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a < b * c ↔ a < c * b)) (mul_comm b c))) (iff.refl (a < c * b)))

theorem mul_inv_lt_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (h : 0 < b) : a * (b⁻¹) < c ↔ a < b * c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (b⁻¹) < c ↔ a < b * c)) (mul_comm a (b⁻¹))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b⁻¹ * a < c ↔ a < b * c)) (propext (inv_mul_lt_iff h)))) (iff.refl (a < b * c)))

theorem mul_inv_lt_iff' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (h : 0 < b) : a * (b⁻¹) < c ↔ a < c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (b⁻¹) < c ↔ a < c * b)) (mul_comm a (b⁻¹))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b⁻¹ * a < c ↔ a < c * b)) (propext (inv_mul_lt_iff' h)))) (iff.refl (a < c * b)))

theorem inv_pos_le_iff_one_le_mul {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ ≤ b ↔ 1 ≤ b * a)) (inv_eq_one_div a))) (div_le_iff ha)

theorem inv_pos_le_iff_one_le_mul' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ ≤ b ↔ 1 ≤ a * b)) (inv_eq_one_div a))) (div_le_iff' ha)

theorem inv_pos_lt_iff_one_lt_mul {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) : a⁻¹ < b ↔ 1 < b * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ < b ↔ 1 < b * a)) (inv_eq_one_div a))) (div_lt_iff ha)

theorem inv_pos_lt_iff_one_lt_mul' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) : a⁻¹ < b ↔ 1 < a * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ < b ↔ 1 < a * b)) (inv_eq_one_div a))) (div_lt_iff' ha)

theorem div_le_iff_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c < 0) : b / c ≤ a ↔ a * c ≤ b := sorry

theorem div_le_iff_of_neg' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c < 0) : b / c ≤ a ↔ c * a ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b / c ≤ a ↔ c * a ≤ b)) (mul_comm c a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b / c ≤ a ↔ a * c ≤ b)) (propext (div_le_iff_of_neg hc)))) (iff.refl (a * c ≤ b)))

theorem le_div_iff_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c < 0) : a ≤ b / c ↔ b ≤ a * c := sorry

theorem le_div_iff_of_neg' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c < 0) : a ≤ b / c ↔ b ≤ c * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b / c ↔ b ≤ c * a)) (mul_comm c a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b / c ↔ b ≤ a * c)) (propext (le_div_iff_of_neg hc)))) (iff.refl (b ≤ a * c)))

theorem div_lt_iff_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c < 0) : b / c < a ↔ a * c < b :=
  lt_iff_lt_of_le_iff_le (le_div_iff_of_neg hc)

theorem div_lt_iff_of_neg' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c < 0) : b / c < a ↔ c * a < b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b / c < a ↔ c * a < b)) (mul_comm c a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b / c < a ↔ a * c < b)) (propext (div_lt_iff_of_neg hc)))) (iff.refl (a * c < b)))

theorem lt_div_iff_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c < 0) : a < b / c ↔ b < a * c :=
  lt_iff_lt_of_le_iff_le (div_le_iff_of_neg hc)

theorem lt_div_iff_of_neg' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c < 0) : a < b / c ↔ b < c * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a < b / c ↔ b < c * a)) (mul_comm c a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a < b / c ↔ b < a * c)) (propext (lt_div_iff_of_neg hc)))) (iff.refl (b < a * c)))

/-- One direction of `div_le_iff` where `b` is allowed to be `0` (but `c` must be nonnegative) -/
theorem div_le_of_nonneg_of_le_mul {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a / b ≤ c := sorry

theorem div_le_one_of_le {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1 :=
  div_le_of_nonneg_of_le_mul hb zero_le_one (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ 1 * b)) (one_mul b))) h)

/-!
### Bi-implications of inequalities using inversions
-/

theorem inv_le_inv_of_le {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ (a⁻¹) := sorry

/-- See `inv_le_inv_of_le` for the implication from right-to-left with one fewer assumption. -/
theorem inv_le_inv {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ (b⁻¹) ↔ b ≤ a := sorry

theorem inv_le {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ ≤ b ↔ b⁻¹ ≤ a)) (Eq.symm (propext (inv_le_inv hb (iff.mpr inv_pos ha))))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b⁻¹ ≤ (a⁻¹⁻¹) ↔ b⁻¹ ≤ a)) (inv_inv' a))) (iff.refl (b⁻¹ ≤ a)))

theorem le_inv {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : a ≤ (b⁻¹) ↔ b ≤ (a⁻¹) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ (b⁻¹) ↔ b ≤ (a⁻¹))) (Eq.symm (propext (inv_le_inv (iff.mpr inv_pos hb) ha)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b⁻¹⁻¹ ≤ (a⁻¹) ↔ b ≤ (a⁻¹))) (inv_inv' b))) (iff.refl (b ≤ (a⁻¹))))

theorem inv_lt_inv {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : a⁻¹ < (b⁻¹) ↔ b < a :=
  lt_iff_lt_of_le_iff_le (inv_le_inv hb ha)

theorem inv_lt {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a :=
  lt_iff_lt_of_le_iff_le (le_inv hb ha)

theorem lt_inv {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : a < (b⁻¹) ↔ b < (a⁻¹) :=
  lt_iff_lt_of_le_iff_le (inv_le hb ha)

theorem inv_le_inv_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ (b⁻¹) ↔ b ≤ a := sorry

theorem inv_le_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (a⁻¹ ≤ b ↔ b⁻¹ ≤ a)) (Eq.symm (propext (inv_le_inv_of_neg hb (iff.mpr inv_lt_zero ha))))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b⁻¹ ≤ (a⁻¹⁻¹) ↔ b⁻¹ ≤ a)) (inv_inv' a))) (iff.refl (b⁻¹ ≤ a)))

theorem le_inv_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : a ≤ (b⁻¹) ↔ b ≤ (a⁻¹) := sorry

theorem inv_lt_inv_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : a⁻¹ < (b⁻¹) ↔ b < a :=
  lt_iff_lt_of_le_iff_le (inv_le_inv_of_neg hb ha)

theorem inv_lt_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : a⁻¹ < b ↔ b⁻¹ < a :=
  lt_iff_lt_of_le_iff_le (le_inv_of_neg hb ha)

theorem lt_inv_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : a < (b⁻¹) ↔ b < (a⁻¹) :=
  lt_iff_lt_of_le_iff_le (inv_le_of_neg hb ha)

theorem inv_lt_one {α : Type u_1} [linear_ordered_field α] {a : α} (ha : 1 < a) : a⁻¹ < 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ < 1)) (propext (inv_lt (has_lt.lt.trans zero_lt_one ha) zero_lt_one))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1⁻¹ < a)) inv_one)) ha)

theorem one_lt_inv {α : Type u_1} [linear_ordered_field α] {a : α} (h₁ : 0 < a) (h₂ : a < 1) : 1 < (a⁻¹) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 < (a⁻¹))) (propext (lt_inv zero_lt_one h₁))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a < (1⁻¹))) inv_one)) h₂)

theorem inv_le_one {α : Type u_1} [linear_ordered_field α] {a : α} (ha : 1 ≤ a) : a⁻¹ ≤ 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ ≤ 1)) (propext (inv_le (has_lt.lt.trans_le zero_lt_one ha) zero_lt_one))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1⁻¹ ≤ a)) inv_one)) ha)

theorem one_le_inv {α : Type u_1} [linear_ordered_field α] {a : α} (h₁ : 0 < a) (h₂ : a ≤ 1) : 1 ≤ (a⁻¹) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ (a⁻¹))) (propext (le_inv zero_lt_one h₁))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ (1⁻¹))) inv_one)) h₂)

theorem inv_lt_one_iff_of_pos {α : Type u_1} [linear_ordered_field α] {a : α} (h₀ : 0 < a) : a⁻¹ < 1 ↔ 1 < a :=
  { mp := fun (h₁ : a⁻¹ < 1) => inv_inv' a ▸ one_lt_inv (iff.mpr inv_pos h₀) h₁, mpr := inv_lt_one }

theorem inv_lt_one_iff {α : Type u_1} [linear_ordered_field α] {a : α} : a⁻¹ < 1 ↔ a ≤ 0 ∨ 1 < a := sorry

theorem one_lt_inv_iff {α : Type u_1} [linear_ordered_field α] {a : α} : 1 < (a⁻¹) ↔ 0 < a ∧ a < 1 := sorry

theorem inv_le_one_iff {α : Type u_1} [linear_ordered_field α] {a : α} : a⁻¹ ≤ 1 ↔ a ≤ 0 ∨ 1 ≤ a := sorry

theorem one_le_inv_iff {α : Type u_1} [linear_ordered_field α] {a : α} : 1 ≤ (a⁻¹) ↔ 0 < a ∧ a ≤ 1 := sorry

/-!
### Relating two divisions.
-/

theorem div_le_div_of_le {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : 0 ≤ c) (h : a ≤ b) : a / c ≤ b / c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / c ≤ b / c)) (div_eq_mul_one_div a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (1 / c) ≤ b / c)) (div_eq_mul_one_div b c)))
      (mul_le_mul_of_nonneg_right h (iff.mpr one_div_nonneg hc)))

theorem div_le_div_of_le_left {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b ≤ a / c)) (div_eq_mul_inv a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (b⁻¹) ≤ a / c)) (div_eq_mul_inv a c)))
      (mul_le_mul_of_nonneg_left (iff.mpr (inv_le_inv (has_lt.lt.trans_le hc h) hc) h) ha))

theorem div_le_div_of_le_of_nonneg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c :=
  div_le_div_of_le hc hab

theorem div_le_div_of_nonpos_of_le {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c ≤ 0) (h : b ≤ a) : a / c ≤ b / c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / c ≤ b / c)) (div_eq_mul_one_div a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (1 / c) ≤ b / c)) (div_eq_mul_one_div b c)))
      (mul_le_mul_of_nonpos_right h (iff.mpr one_div_nonpos hc)))

theorem div_lt_div_of_lt {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : 0 < c) (h : a < b) : a / c < b / c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / c < b / c)) (div_eq_mul_one_div a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (1 / c) < b / c)) (div_eq_mul_one_div b c)))
      (mul_lt_mul_of_pos_right h (iff.mpr one_div_pos hc)))

theorem div_lt_div_of_neg_of_lt {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c < 0) (h : b < a) : a / c < b / c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / c < b / c)) (div_eq_mul_one_div a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (1 / c) < b / c)) (div_eq_mul_one_div b c)))
      (mul_lt_mul_of_neg_right h (iff.mpr one_div_neg hc)))

theorem div_le_div_right {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b :=
  { mp := le_imp_le_of_lt_imp_lt (div_lt_div_of_lt hc), mpr := div_le_div_of_le (has_lt.lt.le hc) }

theorem div_le_div_right_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c < 0) : a / c ≤ b / c ↔ b ≤ a :=
  { mp := le_imp_le_of_lt_imp_lt (div_lt_div_of_neg_of_lt hc), mpr := div_le_div_of_nonpos_of_le (has_lt.lt.le hc) }

theorem div_lt_div_right {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : 0 < c) : a / c < b / c ↔ a < b :=
  lt_iff_lt_of_le_iff_le (div_le_div_right hc)

theorem div_lt_div_right_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hc : c < 0) : a / c < b / c ↔ b < a :=
  lt_iff_lt_of_le_iff_le (div_le_div_right_of_neg hc)

theorem div_lt_div_left {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b :=
  iff.trans (mul_lt_mul_left ha) (inv_lt_inv hb hc)

theorem div_le_div_left {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b ≤ a / c ↔ c ≤ b :=
  iff.mpr le_iff_le_iff_lt_iff_lt (div_lt_div_left ha hc hb)

theorem div_lt_div_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} {d : α} (b0 : 0 < b) (d0 : 0 < d) : a / b < c / d ↔ a * d < c * b := sorry

theorem div_le_div_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} {d : α} (b0 : 0 < b) (d0 : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b := sorry

theorem div_le_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} {d : α} (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hbd : d ≤ b) : a / b ≤ c / d :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b ≤ c / d)) (propext (div_le_div_iff (has_lt.lt.trans_le hd hbd) hd))))
    (mul_le_mul hac hbd (has_lt.lt.le hd) hc)

theorem div_lt_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} {d : α} (hac : a < c) (hbd : d ≤ b) (c0 : 0 ≤ c) (d0 : 0 < d) : a / b < c / d :=
  iff.mpr (div_lt_div_iff (has_lt.lt.trans_le d0 hbd) d0) (mul_lt_mul hac hbd d0 c0)

theorem div_lt_div' {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} {d : α} (hac : a ≤ c) (hbd : d < b) (c0 : 0 < c) (d0 : 0 < d) : a / b < c / d :=
  iff.mpr (div_lt_div_iff (has_lt.lt.trans d0 hbd) d0) (mul_lt_mul' hac hbd (has_lt.lt.le d0) c0)

theorem div_lt_div_of_lt_left {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} (hb : 0 < b) (h : b < a) (hc : 0 < c) : c / a < c / b :=
  iff.mpr (div_lt_div_left hc (has_lt.lt.trans hb h) hb) h

/-!
### Relating one division and involving `1`
-/

theorem one_le_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ a / b ↔ b ≤ a)) (propext (le_div_iff hb))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 * b ≤ a ↔ b ≤ a)) (one_mul b))) (iff.refl (b ≤ a)))

theorem div_le_one {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b ≤ 1 ↔ a ≤ b)) (propext (div_le_iff hb))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ 1 * b ↔ a ≤ b)) (one_mul b))) (iff.refl (a ≤ b)))

theorem one_lt_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : 0 < b) : 1 < a / b ↔ b < a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 < a / b ↔ b < a)) (propext (lt_div_iff hb))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 * b < a ↔ b < a)) (one_mul b))) (iff.refl (b < a)))

theorem div_lt_one {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : 0 < b) : a / b < 1 ↔ a < b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b < 1 ↔ a < b)) (propext (div_lt_iff hb))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a < 1 * b ↔ a < b)) (one_mul b))) (iff.refl (a < b)))

theorem one_le_div_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : b < 0) : 1 ≤ a / b ↔ a ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ a / b ↔ a ≤ b)) (propext (le_div_iff_of_neg hb))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ 1 * b ↔ a ≤ b)) (one_mul b))) (iff.refl (a ≤ b)))

theorem div_le_one_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : b < 0) : a / b ≤ 1 ↔ b ≤ a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b ≤ 1 ↔ b ≤ a)) (propext (div_le_iff_of_neg hb))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 * b ≤ a ↔ b ≤ a)) (one_mul b))) (iff.refl (b ≤ a)))

theorem one_lt_div_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : b < 0) : 1 < a / b ↔ a < b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 < a / b ↔ a < b)) (propext (lt_div_iff_of_neg hb))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a < 1 * b ↔ a < b)) (one_mul b))) (iff.refl (a < b)))

theorem div_lt_one_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : b < 0) : a / b < 1 ↔ b < a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b < 1 ↔ b < a)) (propext (div_lt_iff_of_neg hb))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 * b < a ↔ b < a)) (one_mul b))) (iff.refl (b < a)))

theorem one_div_le {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ b ↔ 1 / b ≤ a := sorry

theorem one_div_lt {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a := sorry

theorem le_one_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : a ≤ 1 / b ↔ b ≤ 1 / a := sorry

theorem lt_one_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : a < 1 / b ↔ b < 1 / a := sorry

theorem one_div_le_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : 1 / a ≤ b ↔ 1 / b ≤ a := sorry

theorem one_div_lt_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : 1 / a < b ↔ 1 / b < a := sorry

theorem le_one_div_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : a ≤ 1 / b ↔ b ≤ 1 / a := sorry

theorem lt_one_div_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : a < 1 / b ↔ b < 1 / a := sorry

theorem one_lt_div_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} : 1 < a / b ↔ 0 < b ∧ b < a ∨ b < 0 ∧ a < b := sorry

theorem one_le_div_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} : 1 ≤ a / b ↔ 0 < b ∧ b ≤ a ∨ b < 0 ∧ a ≤ b := sorry

theorem div_lt_one_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} : a / b < 1 ↔ 0 < b ∧ a < b ∨ b = 0 ∨ b < 0 ∧ b < a := sorry

theorem div_le_one_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} : a / b ≤ 1 ↔ 0 < b ∧ a ≤ b ∨ b = 0 ∨ b < 0 ∧ b ≤ a := sorry

/-!
### Relating two divisions, involving `1`
-/

theorem one_div_le_one_div_of_le {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a := sorry

theorem one_div_lt_one_div_of_lt {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (h : a < b) : 1 / b < 1 / a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 / b < 1 / a)) (propext (lt_div_iff' ha))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (1 / b) < 1)) (Eq.symm (div_eq_mul_one_div a b))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a / b < 1)) (propext (div_lt_one (has_lt.lt.trans ha h))))) h))

theorem one_div_le_one_div_of_neg_of_le {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 / b ≤ 1 / a)) (propext (div_le_iff_of_neg' hb))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * (1 / a) ≤ 1)) (Eq.symm (div_eq_mul_one_div b a))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b / a ≤ 1)) (propext (div_le_one_of_neg (has_le.le.trans_lt h hb))))) h))

theorem one_div_lt_one_div_of_neg_of_lt {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : b < 0) (h : a < b) : 1 / b < 1 / a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 / b < 1 / a)) (propext (div_lt_iff_of_neg' hb))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * (1 / a) < 1)) (Eq.symm (div_eq_mul_one_div b a))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b / a < 1)) (propext (div_lt_one_of_neg (has_lt.lt.trans h hb))))) h))

theorem le_of_one_div_le_one_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (h : 1 / a ≤ 1 / b) : b ≤ a :=
  le_imp_le_of_lt_imp_lt (one_div_lt_one_div_of_lt ha) h

theorem lt_of_one_div_lt_one_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (h : 1 / a < 1 / b) : b < a :=
  lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_le ha) h

theorem le_of_neg_of_one_div_le_one_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : b < 0) (h : 1 / a ≤ 1 / b) : b ≤ a :=
  le_imp_le_of_lt_imp_lt (one_div_lt_one_div_of_neg_of_lt hb) h

theorem lt_of_neg_of_one_div_lt_one_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (hb : b < 0) (h : 1 / a < 1 / b) : b < a :=
  lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_neg_of_le hb) h

/-- For the single implications with fewer assumptions, see `one_div_le_one_div_of_le` and
  `le_of_one_div_le_one_div` -/
theorem one_div_le_one_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ 1 / b ↔ b ≤ a :=
  div_le_div_left zero_lt_one ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_lt_one_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
  div_lt_div_left zero_lt_one ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_neg_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_le_one_div_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : 1 / a ≤ 1 / b ↔ b ≤ a := sorry

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_lt_one_div_of_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : 1 / a < 1 / b ↔ b < a :=
  lt_iff_lt_of_le_iff_le (one_div_le_one_div_of_neg hb ha)

theorem one_lt_one_div {α : Type u_1} [linear_ordered_field α] {a : α} (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 < 1 / a)) (propext (lt_one_div zero_lt_one h1))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a < 1 / 1)) one_div_one)) h2)

theorem one_le_one_div {α : Type u_1} [linear_ordered_field α] {a : α} (h1 : 0 < a) (h2 : a ≤ 1) : 1 ≤ 1 / a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ 1 / a)) (propext (le_one_div zero_lt_one h1))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ 1 / 1)) one_div_one)) h2)

theorem one_div_lt_neg_one {α : Type u_1} [linear_ordered_field α] {a : α} (h1 : a < 0) (h2 : -1 < a) : 1 / a < -1 :=
  (fun (this : 1 / a < 1 / -1) => eq.mp (Eq._oldrec (Eq.refl (1 / a < 1 / -1)) one_div_neg_one_eq_neg_one) this)
    (one_div_lt_one_div_of_neg_of_lt h1 h2)

theorem one_div_le_neg_one {α : Type u_1} [linear_ordered_field α] {a : α} (h1 : a < 0) (h2 : -1 ≤ a) : 1 / a ≤ -1 :=
  (fun (this : 1 / a ≤ 1 / -1) => eq.mp (Eq._oldrec (Eq.refl (1 / a ≤ 1 / -1)) one_div_neg_one_eq_neg_one) this)
    (one_div_le_one_div_of_neg_of_le h1 h2)

/-!
### Results about halving.

The equalities also hold in fields of characteristic `0`. -/

theorem add_halves {α : Type u_1} [linear_ordered_field α] (a : α) : a / bit0 1 + a / bit0 1 = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / bit0 1 + a / bit0 1 = a)) (div_add_div_same a a (bit0 1))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((a + a) / bit0 1 = a)) (Eq.symm (two_mul a))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (bit0 1 * a / bit0 1 = a)) (mul_div_cancel_left a two_ne_zero))) (Eq.refl a)))

theorem sub_self_div_two {α : Type u_1} [linear_ordered_field α] (a : α) : a - a / bit0 1 = a / bit0 1 := sorry

theorem div_two_sub_self {α : Type u_1} [linear_ordered_field α] (a : α) : a / bit0 1 - a = -(a / bit0 1) := sorry

theorem add_self_div_two {α : Type u_1} [linear_ordered_field α] (a : α) : (a + a) / bit0 1 = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a + a) / bit0 1 = a)) (Eq.symm (mul_two a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * bit0 1 / bit0 1 = a)) (mul_div_cancel a two_ne_zero))) (Eq.refl a))

theorem half_pos {α : Type u_1} [linear_ordered_field α] {a : α} (h : 0 < a) : 0 < a / bit0 1 :=
  div_pos h zero_lt_two

theorem one_half_pos {α : Type u_1} [linear_ordered_field α] : 0 < 1 / bit0 1 :=
  half_pos zero_lt_one

theorem div_two_lt_of_pos {α : Type u_1} [linear_ordered_field α] {a : α} (h : 0 < a) : a / bit0 1 < a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / bit0 1 < a)) (propext (div_lt_iff zero_lt_two))))
    (lt_mul_of_one_lt_right h one_lt_two)

theorem half_lt_self {α : Type u_1} [linear_ordered_field α] {a : α} : 0 < a → a / bit0 1 < a :=
  div_two_lt_of_pos

theorem one_half_lt_one {α : Type u_1} [linear_ordered_field α] : 1 / bit0 1 < 1 :=
  half_lt_self zero_lt_one

theorem add_sub_div_two_lt {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (h : a < b) : a + (b - a) / bit0 1 < b := sorry

/-!
### Miscellaneous lemmas
-/

theorem mul_sub_mul_div_mul_neg_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} {d : α} (hc : c ≠ 0) (hd : d ≠ 0) : (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d := sorry

theorem mul_sub_mul_div_mul_neg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} {d : α} (hc : c ≠ 0) (hd : d ≠ 0) : a / c < b / d → (a * d - b * c) / (c * d) < 0 :=
  iff.mpr (mul_sub_mul_div_mul_neg_iff hc hd)

theorem mul_sub_mul_div_mul_nonpos_iff {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} {d : α} (hc : c ≠ 0) (hd : d ≠ 0) : (a * d - b * c) / (c * d) ≤ 0 ↔ a / c ≤ b / d := sorry

theorem mul_sub_mul_div_mul_nonpos {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} {d : α} (hc : c ≠ 0) (hd : d ≠ 0) : a / c ≤ b / d → (a * d - b * c) / (c * d) ≤ 0 :=
  iff.mpr (mul_sub_mul_div_mul_nonpos_iff hc hd)

theorem mul_le_mul_of_mul_div_le {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} {d : α} (h : a * (b / c) ≤ d) (hc : 0 < c) : b * a ≤ d * c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b * a ≤ d * c)) (mul_comm b a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * b ≤ d * c)) (Eq.symm (propext (div_le_iff hc)))))
      (eq.mp (Eq._oldrec (Eq.refl (a * (b / c) ≤ d)) (Eq.symm mul_div_assoc)) h))

theorem div_mul_le_div_mul_of_div_le_div {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} {c : α} {d : α} {e : α} (h : a / b ≤ c / d) (he : 0 ≤ e) : a / (b * e) ≤ c / (d * e) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / (b * e) ≤ c / (d * e))) (div_mul_eq_div_mul_one_div a b e)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / b * (1 / e) ≤ c / (d * e))) (div_mul_eq_div_mul_one_div c d e)))
      (mul_le_mul_of_nonneg_right h (iff.mpr one_div_nonneg he)))

theorem exists_add_lt_and_pos_of_lt {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (h : b < a) : ∃ (c : α), b + c < a ∧ 0 < c :=
  Exists.intro ((a - b) / bit0 1) { left := add_sub_div_two_lt h, right := div_pos (sub_pos_of_lt h) zero_lt_two }

theorem le_of_forall_sub_le {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (h : ∀ (ε : α), ε > 0 → b - ε ≤ a) : b ≤ a := sorry

theorem monotone.div_const {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [preorder β] {f : β → α} (hf : monotone f) {c : α} (hc : 0 ≤ c) : monotone fun (x : β) => f x / c :=
  monotone.mul_const hf (iff.mpr inv_nonneg hc)

theorem strict_mono.div_const {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [preorder β] {f : β → α} (hf : strict_mono f) {c : α} (hc : 0 < c) : strict_mono fun (x : β) => f x / c :=
  strict_mono.mul_const hf (iff.mpr inv_pos hc)

protected instance linear_ordered_field.to_densely_ordered {α : Type u_1} [linear_ordered_field α] : densely_ordered α :=
  densely_ordered.mk
    fun (a₁ a₂ : α) (h : a₁ < a₂) =>
      Exists.intro ((a₁ + a₂) / bit0 1)
        { left :=
            trans_rel_right Less (Eq.symm (add_self_div_two a₁)) (div_lt_div_of_lt zero_lt_two (add_lt_add_left h a₁)),
          right := trans_rel_left Less (div_lt_div_of_lt zero_lt_two (add_lt_add_right h a₂)) (add_self_div_two a₂) }

theorem mul_self_inj_of_nonneg {α : Type u_1} [linear_ordered_field α] {a : α} {b : α} (a0 : 0 ≤ a) (b0 : 0 ≤ b) : a * a = b * b ↔ a = b := sorry

theorem min_div_div_right {α : Type u_1} [linear_ordered_field α] {c : α} (hc : 0 ≤ c) (a : α) (b : α) : min (a / c) (b / c) = min a b / c :=
  Eq.symm (monotone.map_min fun (x y : α) => div_le_div_of_le hc)

theorem max_div_div_right {α : Type u_1} [linear_ordered_field α] {c : α} (hc : 0 ≤ c) (a : α) (b : α) : max (a / c) (b / c) = max a b / c :=
  Eq.symm (monotone.map_max fun (x y : α) => div_le_div_of_le hc)

theorem min_div_div_right_of_nonpos {α : Type u_1} [linear_ordered_field α] {c : α} (hc : c ≤ 0) (a : α) (b : α) : min (a / c) (b / c) = max a b / c :=
  Eq.symm (monotone.map_max fun (x y : α) => div_le_div_of_nonpos_of_le hc)

theorem max_div_div_right_of_nonpos {α : Type u_1} [linear_ordered_field α] {c : α} (hc : c ≤ 0) (a : α) (b : α) : max (a / c) (b / c) = min a b / c :=
  Eq.symm (monotone.map_min fun (x y : α) => div_le_div_of_nonpos_of_le hc)

theorem abs_div {α : Type u_1} [linear_ordered_field α] (a : α) (b : α) : abs (a / b) = abs a / abs b :=
  monoid_with_zero_hom.map_div abs_hom a b

theorem abs_one_div {α : Type u_1} [linear_ordered_field α] (a : α) : abs (1 / a) = 1 / abs a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs (1 / a) = 1 / abs a)) (abs_div 1 a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (abs 1 / abs a = 1 / abs a)) abs_one)) (Eq.refl (1 / abs a)))

theorem abs_inv {α : Type u_1} [linear_ordered_field α] (a : α) : abs (a⁻¹) = (abs a⁻¹) :=
  monoid_with_zero_hom.map_inv' abs_hom a

