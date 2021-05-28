/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.ordered_group
import Mathlib.data.set.intervals.basic
import Mathlib.PostPort

universes u l u_1 

namespace Mathlib

/-- An `ordered_semiring α` is a semiring `α` with a partial order such that
multiplication with a positive number and addition are monotone. -/
class ordered_semiring (α : Type u) 
extends ordered_cancel_add_comm_monoid α, semiring α
where
  zero_le_one : 0 ≤ 1
  mul_lt_mul_of_pos_left : ∀ (a b c : α), a < b → 0 < c → c * a < c * b
  mul_lt_mul_of_pos_right : ∀ (a b c : α), a < b → 0 < c → a * c < b * c

theorem zero_le_one {α : Type u} [ordered_semiring α] : 0 ≤ 1 :=
  ordered_semiring.zero_le_one

theorem zero_le_two {α : Type u} [ordered_semiring α] : 0 ≤ bit0 1 :=
  add_nonneg zero_le_one zero_le_one

theorem zero_lt_one {α : Type u} [ordered_semiring α] [nontrivial α] : 0 < 1 :=
  lt_of_le_of_ne zero_le_one zero_ne_one

theorem zero_lt_two {α : Type u} [ordered_semiring α] [nontrivial α] : 0 < bit0 1 :=
  add_pos zero_lt_one zero_lt_one

theorem two_ne_zero {α : Type u} [ordered_semiring α] [nontrivial α] : bit0 1 ≠ 0 :=
  ne.symm (ne_of_lt zero_lt_two)

theorem one_lt_two {α : Type u} [ordered_semiring α] [nontrivial α] : 1 < bit0 1 :=
  trans_rel_left gt (trans_rel_right gt one_add_one_eq_two (add_lt_add_left zero_lt_one 1)) (add_zero 1)

theorem one_le_two {α : Type u} [ordered_semiring α] [nontrivial α] : 1 ≤ bit0 1 :=
  has_lt.lt.le one_lt_two

theorem zero_lt_three {α : Type u} [ordered_semiring α] [nontrivial α] : 0 < bit1 1 :=
  add_pos zero_lt_two zero_lt_one

theorem zero_lt_four {α : Type u} [ordered_semiring α] [nontrivial α] : 0 < bit0 (bit0 1) :=
  add_pos zero_lt_two zero_lt_two

theorem mul_lt_mul_of_pos_left {α : Type u} [ordered_semiring α] {a : α} {b : α} {c : α} (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
  ordered_semiring.mul_lt_mul_of_pos_left a b c h₁ h₂

theorem mul_lt_mul_of_pos_right {α : Type u} [ordered_semiring α] {a : α} {b : α} {c : α} (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
  ordered_semiring.mul_lt_mul_of_pos_right a b c h₁ h₂

theorem mul_le_mul_of_nonneg_left {α : Type u} [ordered_semiring α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b := sorry

theorem mul_le_mul_of_nonneg_right {α : Type u} [ordered_semiring α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c := sorry

-- TODO: there are four variations, depending on which variables we assume to be nonneg

theorem mul_le_mul {α : Type u} [ordered_semiring α] {a : α} {b : α} {c : α} {d : α} (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) : a * b ≤ c * d :=
  le_trans (mul_le_mul_of_nonneg_right hac nn_b) (mul_le_mul_of_nonneg_left hbd nn_c)

theorem mul_nonneg {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  (fun (h : 0 * b ≤ a * b) => eq.mp (Eq._oldrec (Eq.refl (0 * b ≤ a * b)) (zero_mul b)) h)
    (mul_le_mul_of_nonneg_right ha hb)

theorem mul_nonpos_of_nonneg_of_nonpos {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 :=
  (fun (h : a * b ≤ a * 0) => eq.mp (Eq._oldrec (Eq.refl (a * b ≤ a * 0)) (mul_zero a)) h)
    (mul_le_mul_of_nonneg_left hb ha)

theorem mul_nonpos_of_nonpos_of_nonneg {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 :=
  (fun (h : a * b ≤ 0 * b) => eq.mp (Eq._oldrec (Eq.refl (a * b ≤ 0 * b)) (zero_mul b)) h)
    (mul_le_mul_of_nonneg_right ha hb)

theorem mul_lt_mul {α : Type u} [ordered_semiring α] {a : α} {b : α} {c : α} {d : α} (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b) (nn_c : 0 ≤ c) : a * b < c * d :=
  lt_of_lt_of_le (mul_lt_mul_of_pos_right hac pos_b) (mul_le_mul_of_nonneg_left hbd nn_c)

theorem mul_lt_mul' {α : Type u} [ordered_semiring α] {a : α} {b : α} {c : α} {d : α} (h1 : a ≤ c) (h2 : b < d) (h3 : 0 ≤ b) (h4 : 0 < c) : a * b < c * d :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 h3) (mul_lt_mul_of_pos_left h2 h4)

theorem mul_pos {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  (fun (h : 0 * b < a * b) => eq.mp (Eq._oldrec (Eq.refl (0 * b < a * b)) (zero_mul b)) h) (mul_lt_mul_of_pos_right ha hb)

theorem mul_neg_of_pos_of_neg {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : 0 < a) (hb : b < 0) : a * b < 0 :=
  (fun (h : a * b < a * 0) => eq.mp (Eq._oldrec (Eq.refl (a * b < a * 0)) (mul_zero a)) h) (mul_lt_mul_of_pos_left hb ha)

theorem mul_neg_of_neg_of_pos {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : a < 0) (hb : 0 < b) : a * b < 0 :=
  (fun (h : a * b < 0 * b) => eq.mp (Eq._oldrec (Eq.refl (a * b < 0 * b)) (zero_mul b)) h) (mul_lt_mul_of_pos_right ha hb)

theorem mul_self_lt_mul_self {α : Type u} [ordered_semiring α] {a : α} {b : α} (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
  mul_lt_mul' (has_lt.lt.le h2) h2 h1 (has_le.le.trans_lt h1 h2)

theorem strict_mono_incr_on_mul_self {α : Type u} [ordered_semiring α] : strict_mono_incr_on (fun (x : α) => x * x) (set.Ici 0) :=
  fun (x : α) (hx : x ∈ set.Ici 0) (y : α) (hy : y ∈ set.Ici 0) (hxy : x < y) => mul_self_lt_mul_self hx hxy

theorem mul_self_le_mul_self {α : Type u} [ordered_semiring α] {a : α} {b : α} (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
  mul_le_mul h2 h2 h1 (has_le.le.trans h1 h2)

theorem mul_lt_mul'' {α : Type u} [ordered_semiring α] {a : α} {b : α} {c : α} {d : α} (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d := sorry

theorem le_mul_of_one_le_right {α : Type u} [ordered_semiring α] {a : α} {b : α} (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ b * a :=
  (fun (this : b * 1 ≤ b * a) => eq.mp (Eq._oldrec (Eq.refl (b * 1 ≤ b * a)) (mul_one b)) this)
    (mul_le_mul_of_nonneg_left h hb)

theorem le_mul_of_one_le_left {α : Type u} [ordered_semiring α] {a : α} {b : α} (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b :=
  (fun (this : 1 * b ≤ a * b) => eq.mp (Eq._oldrec (Eq.refl (1 * b ≤ a * b)) (one_mul b)) this)
    (mul_le_mul_of_nonneg_right h hb)

theorem bit1_pos {α : Type u} [ordered_semiring α] {a : α} [nontrivial α] (h : 0 ≤ a) : 0 < bit1 a :=
  lt_add_of_le_of_pos (add_nonneg h h) zero_lt_one

theorem lt_add_one {α : Type u} [ordered_semiring α] [nontrivial α] (a : α) : a < a + 1 :=
  lt_add_of_le_of_pos le_rfl zero_lt_one

theorem lt_one_add {α : Type u} [ordered_semiring α] [nontrivial α] (a : α) : a < 1 + a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a < 1 + a)) (add_comm 1 a))) (lt_add_one a)

theorem bit1_pos' {α : Type u} [ordered_semiring α] {a : α} (h : 0 < a) : 0 < bit1 a :=
  bit1_pos (has_lt.lt.le h)

theorem one_lt_mul {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
  one_mul 1 ▸ mul_lt_mul' ha hb zero_le_one (has_lt.lt.trans_le zero_lt_one ha)

theorem mul_le_one {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : a ≤ 1) (hb' : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b ≤ 1)) (Eq.symm (one_mul 1)))) (mul_le_mul ha hb hb' zero_le_one)

theorem one_lt_mul_of_le_of_lt {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
  trans_rel_right Less (eq.mpr (id (Eq._oldrec (Eq.refl (1 = 1 * 1)) (one_mul 1))) (Eq.refl 1))
    (mul_lt_mul' ha hb zero_le_one (has_lt.lt.trans_le zero_lt_one ha))

theorem one_lt_mul_of_lt_of_le {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
  trans_rel_right Less (eq.mpr (id (Eq._oldrec (Eq.refl (1 = 1 * 1)) (one_mul 1))) (Eq.refl 1))
    (mul_lt_mul ha hb zero_lt_one (has_le.le.trans zero_le_one (has_lt.lt.le ha)))

theorem mul_le_of_le_one_right {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : 0 ≤ a) (hb1 : b ≤ 1) : a * b ≤ a :=
  trans_rel_left LessEq (mul_le_mul_of_nonneg_left hb1 ha) (mul_one a)

theorem mul_le_of_le_one_left {α : Type u} [ordered_semiring α] {a : α} {b : α} (hb : 0 ≤ b) (ha1 : a ≤ 1) : a * b ≤ b :=
  trans_rel_left LessEq (mul_le_mul ha1 le_rfl hb zero_le_one) (one_mul b)

theorem mul_lt_one_of_nonneg_of_lt_one_left {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha0 : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
  lt_of_le_of_lt (mul_le_of_le_one_right ha0 hb) ha

theorem mul_lt_one_of_nonneg_of_lt_one_right {α : Type u} [ordered_semiring α] {a : α} {b : α} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b < 1) : a * b < 1 :=
  lt_of_le_of_lt (mul_le_of_le_one_left hb0 ha) hb

/-- An `ordered_comm_semiring α` is a commutative semiring `α` with a partial order such that
multiplication with a positive number and addition are monotone. -/
class ordered_comm_semiring (α : Type u) 
extends comm_semiring α, ordered_semiring α
where

/--
A `linear_ordered_semiring α` is a nontrivial semiring `α` with a linear order
such that multiplication with a positive number and addition are monotone.
-/
-- It's not entirely clear we should assume `nontrivial` at this point;

-- it would be reasonable to explore changing this,

-- but be warned that the instances involving `domain` may cause

-- typeclass search loops.

class linear_ordered_semiring (α : Type u) 
extends ordered_semiring α, nontrivial α, linear_order α
where

-- `norm_num` expects the lemma stating `0 < 1` to have a single typeclass argument

-- (see `norm_num.prove_pos_nat`).

-- Rather than working out how to relax that assumption,

-- we provide a synonym for `zero_lt_one` (which needs both `ordered_semiring α` and `nontrivial α`)

-- with only a `linear_ordered_semiring` typeclass argument.

theorem zero_lt_one' {α : Type u} [linear_ordered_semiring α] : 0 < 1 :=
  zero_lt_one

theorem lt_of_mul_lt_mul_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} {c : α} (h : c * a < c * b) (hc : 0 ≤ c) : a < b :=
  lt_of_not_ge fun (h1 : b ≤ a) => (fun (h2 : c * b ≤ c * a) => has_le.le.not_lt h2 h) (mul_le_mul_of_nonneg_left h1 hc)

theorem lt_of_mul_lt_mul_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} {c : α} (h : a * c < b * c) (hc : 0 ≤ c) : a < b :=
  lt_of_not_ge fun (h1 : b ≤ a) => (fun (h2 : b * c ≤ a * c) => has_le.le.not_lt h2 h) (mul_le_mul_of_nonneg_right h1 hc)

theorem le_of_mul_le_mul_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} {c : α} (h : c * a ≤ c * b) (hc : 0 < c) : a ≤ b :=
  le_of_not_gt fun (h1 : b < a) => (fun (h2 : c * b < c * a) => has_lt.lt.not_le h2 h) (mul_lt_mul_of_pos_left h1 hc)

theorem le_of_mul_le_mul_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} {c : α} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
  le_of_not_gt fun (h1 : b < a) => (fun (h2 : b * c < a * c) => has_lt.lt.not_le h2 h) (mul_lt_mul_of_pos_right h1 hc)

theorem pos_and_pos_or_neg_and_neg_of_mul_pos {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (hab : 0 < a * b) : 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := sorry

theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (hab : 0 ≤ a * b) : 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := sorry

theorem pos_of_mul_pos_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
  and.right
    (or.resolve_right (pos_and_pos_or_neg_and_neg_of_mul_pos h)
      fun (h : a < 0 ∧ b < 0) => has_lt.lt.not_le (and.left h) ha)

theorem pos_of_mul_pos_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
  and.left
    (or.resolve_right (pos_and_pos_or_neg_and_neg_of_mul_pos h)
      fun (h : a < 0 ∧ b < 0) => has_lt.lt.not_le (and.right h) hb)

theorem nonneg_of_mul_nonneg_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : 0 ≤ a * b) (h1 : 0 < a) : 0 ≤ b :=
  le_of_not_gt fun (h2 : b < 0) => has_lt.lt.not_le (mul_neg_of_pos_of_neg h1 h2) h

theorem nonneg_of_mul_nonneg_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : 0 ≤ a * b) (h1 : 0 < b) : 0 ≤ a :=
  le_of_not_gt fun (h2 : a < 0) => has_lt.lt.not_le (mul_neg_of_neg_of_pos h2 h1) h

theorem neg_of_mul_neg_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun (h2 : b ≥ 0) => has_le.le.not_lt (mul_nonneg h1 h2) h

theorem neg_of_mul_neg_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun (h2 : a ≥ 0) => has_le.le.not_lt (mul_nonneg h2 h1) h

theorem nonpos_of_mul_nonpos_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : a * b ≤ 0) (h1 : 0 < a) : b ≤ 0 :=
  le_of_not_gt fun (h2 : b > 0) => has_lt.lt.not_le (mul_pos h1 h2) h

theorem nonpos_of_mul_nonpos_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : a * b ≤ 0) (h1 : 0 < b) : a ≤ 0 :=
  le_of_not_gt fun (h2 : a > 0) => has_lt.lt.not_le (mul_pos h2 h1) h

@[simp] theorem mul_le_mul_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} {c : α} (h : 0 < c) : c * a ≤ c * b ↔ a ≤ b :=
  { mp := fun (h' : c * a ≤ c * b) => le_of_mul_le_mul_left h' h,
    mpr := fun (h' : a ≤ b) => mul_le_mul_of_nonneg_left h' (has_lt.lt.le h) }

@[simp] theorem mul_le_mul_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} {c : α} (h : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
  { mp := fun (h' : a * c ≤ b * c) => le_of_mul_le_mul_right h' h,
    mpr := fun (h' : a ≤ b) => mul_le_mul_of_nonneg_right h' (has_lt.lt.le h) }

@[simp] theorem mul_lt_mul_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} {c : α} (h : 0 < c) : c * a < c * b ↔ a < b :=
  { mp := lt_imp_lt_of_le_imp_le fun (h' : b ≤ a) => mul_le_mul_of_nonneg_left h' (has_lt.lt.le h),
    mpr := fun (h' : a < b) => mul_lt_mul_of_pos_left h' h }

@[simp] theorem mul_lt_mul_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} {c : α} (h : 0 < c) : a * c < b * c ↔ a < b :=
  { mp := lt_imp_lt_of_le_imp_le fun (h' : b ≤ a) => mul_le_mul_of_nonneg_right h' (has_lt.lt.le h),
    mpr := fun (h' : a < b) => mul_lt_mul_of_pos_right h' h }

@[simp] theorem zero_le_mul_left {α : Type u} [linear_ordered_semiring α] {b : α} {c : α} (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b := sorry

@[simp] theorem zero_le_mul_right {α : Type u} [linear_ordered_semiring α] {b : α} {c : α} (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b := sorry

@[simp] theorem zero_lt_mul_left {α : Type u} [linear_ordered_semiring α] {b : α} {c : α} (h : 0 < c) : 0 < c * b ↔ 0 < b := sorry

@[simp] theorem zero_lt_mul_right {α : Type u} [linear_ordered_semiring α] {b : α} {c : α} (h : 0 < c) : 0 < b * c ↔ 0 < b := sorry

@[simp] theorem bit0_le_bit0 {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} [nontrivial α] : bit0 a ≤ bit0 b ↔ a ≤ b := sorry

@[simp] theorem bit0_lt_bit0 {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} [nontrivial α] : bit0 a < bit0 b ↔ a < b := sorry

@[simp] theorem bit1_le_bit1 {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} [nontrivial α] : bit1 a ≤ bit1 b ↔ a ≤ b :=
  iff.trans (add_le_add_iff_right 1) bit0_le_bit0

@[simp] theorem bit1_lt_bit1 {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} [nontrivial α] : bit1 a < bit1 b ↔ a < b :=
  iff.trans (add_lt_add_iff_right 1) bit0_lt_bit0

@[simp] theorem one_le_bit1 {α : Type u} [linear_ordered_semiring α] {a : α} [nontrivial α] : 1 ≤ bit1 a ↔ 0 ≤ a := sorry

@[simp] theorem one_lt_bit1 {α : Type u} [linear_ordered_semiring α] {a : α} [nontrivial α] : 1 < bit1 a ↔ 0 < a := sorry

@[simp] theorem zero_le_bit0 {α : Type u} [linear_ordered_semiring α] {a : α} [nontrivial α] : 0 ≤ bit0 a ↔ 0 ≤ a := sorry

@[simp] theorem zero_lt_bit0 {α : Type u} [linear_ordered_semiring α] {a : α} [nontrivial α] : 0 < bit0 a ↔ 0 < a := sorry

theorem le_mul_iff_one_le_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (hb : 0 < b) : b ≤ a * b ↔ 1 ≤ a :=
  (fun (this : 1 * b ≤ a * b ↔ 1 ≤ a) => eq.mp (Eq._oldrec (Eq.refl (1 * b ≤ a * b ↔ 1 ≤ a)) (one_mul b)) this)
    (mul_le_mul_right hb)

theorem lt_mul_iff_one_lt_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (hb : 0 < b) : b < a * b ↔ 1 < a :=
  (fun (this : 1 * b < a * b ↔ 1 < a) => eq.mp (Eq._oldrec (Eq.refl (1 * b < a * b ↔ 1 < a)) (one_mul b)) this)
    (mul_lt_mul_right hb)

theorem le_mul_iff_one_le_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (hb : 0 < b) : b ≤ b * a ↔ 1 ≤ a :=
  (fun (this : b * 1 ≤ b * a ↔ 1 ≤ a) => eq.mp (Eq._oldrec (Eq.refl (b * 1 ≤ b * a ↔ 1 ≤ a)) (mul_one b)) this)
    (mul_le_mul_left hb)

theorem lt_mul_iff_one_lt_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (hb : 0 < b) : b < b * a ↔ 1 < a :=
  (fun (this : b * 1 < b * a ↔ 1 < a) => eq.mp (Eq._oldrec (Eq.refl (b * 1 < b * a ↔ 1 < a)) (mul_one b)) this)
    (mul_lt_mul_left hb)

theorem lt_mul_of_one_lt_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (hb : 0 < b) : 1 < a → b < b * a :=
  iff.mpr (lt_mul_iff_one_lt_right hb)

theorem mul_nonneg_iff_right_nonneg_of_pos {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : 0 < a) : 0 ≤ b * a ↔ 0 ≤ b :=
  { mp := fun (this : 0 ≤ b * a) => nonneg_of_mul_nonneg_right this h,
    mpr := fun (this : 0 ≤ b) => mul_nonneg this (has_lt.lt.le h) }

theorem mul_le_iff_le_one_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (hb : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  { mp := fun (h : a * b ≤ b) => le_of_not_lt (mt (iff.mpr (lt_mul_iff_one_lt_left hb)) (has_le.le.not_lt h)),
    mpr := fun (h : a ≤ 1) => le_of_not_lt (mt (iff.mp (lt_mul_iff_one_lt_left hb)) (has_le.le.not_lt h)) }

theorem mul_lt_iff_lt_one_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (hb : 0 < b) : a * b < b ↔ a < 1 :=
  { mp := fun (h : a * b < b) => lt_of_not_ge (mt (iff.mpr (le_mul_iff_one_le_left hb)) (has_lt.lt.not_le h)),
    mpr := fun (h : a < 1) => lt_of_not_ge (mt (iff.mp (le_mul_iff_one_le_left hb)) (has_lt.lt.not_le h)) }

theorem mul_le_iff_le_one_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (hb : 0 < b) : b * a ≤ b ↔ a ≤ 1 :=
  { mp := fun (h : b * a ≤ b) => le_of_not_lt (mt (iff.mpr (lt_mul_iff_one_lt_right hb)) (has_le.le.not_lt h)),
    mpr := fun (h : a ≤ 1) => le_of_not_lt (mt (iff.mp (lt_mul_iff_one_lt_right hb)) (has_le.le.not_lt h)) }

theorem mul_lt_iff_lt_one_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (hb : 0 < b) : b * a < b ↔ a < 1 :=
  { mp := fun (h : b * a < b) => lt_of_not_ge (mt (iff.mpr (le_mul_iff_one_le_right hb)) (has_lt.lt.not_le h)),
    mpr := fun (h : a < 1) => lt_of_not_ge (mt (iff.mp (le_mul_iff_one_le_right hb)) (has_lt.lt.not_le h)) }

theorem nonpos_of_mul_nonneg_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 :=
  le_of_not_gt fun (ha : a > 0) => absurd h (has_lt.lt.not_le (mul_neg_of_pos_of_neg ha hb))

theorem nonpos_of_mul_nonneg_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
  le_of_not_gt fun (hb : b > 0) => absurd h (has_lt.lt.not_le (mul_neg_of_neg_of_pos ha hb))

theorem neg_of_mul_pos_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : 0 < a * b) (hb : b ≤ 0) : a < 0 :=
  lt_of_not_ge fun (ha : a ≥ 0) => absurd h (has_le.le.not_lt (mul_nonpos_of_nonneg_of_nonpos ha hb))

theorem neg_of_mul_pos_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  lt_of_not_ge fun (hb : b ≥ 0) => absurd h (has_le.le.not_lt (mul_nonpos_of_nonpos_of_nonneg ha hb))

protected instance linear_ordered_semiring.to_no_top_order {α : Type u_1} [linear_ordered_semiring α] : no_top_order α :=
  no_top_order.mk fun (a : α) => Exists.intro (a + 1) (lt_add_of_pos_right a zero_lt_one)

theorem monotone_mul_left_of_nonneg {α : Type u} [linear_ordered_semiring α] {a : α} (ha : 0 ≤ a) : monotone fun (x : α) => a * x :=
  fun (b c : α) (b_le_c : b ≤ c) => mul_le_mul_of_nonneg_left b_le_c ha

theorem monotone_mul_right_of_nonneg {α : Type u} [linear_ordered_semiring α] {a : α} (ha : 0 ≤ a) : monotone fun (x : α) => x * a :=
  fun (b c : α) (b_le_c : b ≤ c) => mul_le_mul_of_nonneg_right b_le_c ha

theorem monotone.mul_const {α : Type u} {β : Type u_1} [linear_ordered_semiring α] [preorder β] {f : β → α} {a : α} (hf : monotone f) (ha : 0 ≤ a) : monotone fun (x : β) => f x * a :=
  monotone.comp (monotone_mul_right_of_nonneg ha) hf

theorem monotone.const_mul {α : Type u} {β : Type u_1} [linear_ordered_semiring α] [preorder β] {f : β → α} {a : α} (hf : monotone f) (ha : 0 ≤ a) : monotone fun (x : β) => a * f x :=
  monotone.comp (monotone_mul_left_of_nonneg ha) hf

theorem monotone.mul {α : Type u} {β : Type u_1} [linear_ordered_semiring α] [preorder β] {f : β → α} {g : β → α} (hf : monotone f) (hg : monotone g) (hf0 : ∀ (x : β), 0 ≤ f x) (hg0 : ∀ (x : β), 0 ≤ g x) : monotone fun (x : β) => f x * g x :=
  fun (x y : β) (h : x ≤ y) => mul_le_mul (hf h) (hg h) (hg0 x) (hf0 y)

theorem strict_mono_mul_left_of_pos {α : Type u} [linear_ordered_semiring α] {a : α} (ha : 0 < a) : strict_mono fun (x : α) => a * x :=
  fun (b c : α) (b_lt_c : b < c) => iff.mpr (mul_lt_mul_left ha) b_lt_c

theorem strict_mono_mul_right_of_pos {α : Type u} [linear_ordered_semiring α] {a : α} (ha : 0 < a) : strict_mono fun (x : α) => x * a :=
  fun (b c : α) (b_lt_c : b < c) => iff.mpr (mul_lt_mul_right ha) b_lt_c

theorem strict_mono.mul_const {α : Type u} {β : Type u_1} [linear_ordered_semiring α] [preorder β] {f : β → α} {a : α} (hf : strict_mono f) (ha : 0 < a) : strict_mono fun (x : β) => f x * a :=
  strict_mono.comp (strict_mono_mul_right_of_pos ha) hf

theorem strict_mono.const_mul {α : Type u} {β : Type u_1} [linear_ordered_semiring α] [preorder β] {f : β → α} {a : α} (hf : strict_mono f) (ha : 0 < a) : strict_mono fun (x : β) => a * f x :=
  strict_mono.comp (strict_mono_mul_left_of_pos ha) hf

theorem strict_mono.mul_monotone {α : Type u} {β : Type u_1} [linear_ordered_semiring α] [preorder β] {f : β → α} {g : β → α} (hf : strict_mono f) (hg : monotone g) (hf0 : ∀ (x : β), 0 ≤ f x) (hg0 : ∀ (x : β), 0 < g x) : strict_mono fun (x : β) => f x * g x :=
  fun (x y : β) (h : x < y) => mul_lt_mul (hf h) (hg (has_lt.lt.le h)) (hg0 x) (hf0 y)

theorem monotone.mul_strict_mono {α : Type u} {β : Type u_1} [linear_ordered_semiring α] [preorder β] {f : β → α} {g : β → α} (hf : monotone f) (hg : strict_mono g) (hf0 : ∀ (x : β), 0 < f x) (hg0 : ∀ (x : β), 0 ≤ g x) : strict_mono fun (x : β) => f x * g x :=
  fun (x y : β) (h : x < y) => mul_lt_mul' (hf (has_lt.lt.le h)) (hg h) (hg0 x) (hf0 y)

theorem strict_mono.mul {α : Type u} {β : Type u_1} [linear_ordered_semiring α] [preorder β] {f : β → α} {g : β → α} (hf : strict_mono f) (hg : strict_mono g) (hf0 : ∀ (x : β), 0 ≤ f x) (hg0 : ∀ (x : β), 0 ≤ g x) : strict_mono fun (x : β) => f x * g x :=
  fun (x y : β) (h : x < y) => mul_lt_mul'' (hf h) (hg h) (hf0 x) (hg0 x)

@[simp] theorem decidable.mul_le_mul_left {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} {c : α} (h : 0 < c) : c * a ≤ c * b ↔ a ≤ b :=
  iff.mpr decidable.le_iff_le_iff_lt_iff_lt (mul_lt_mul_left h)

@[simp] theorem decidable.mul_le_mul_right {α : Type u} [linear_ordered_semiring α] {a : α} {b : α} {c : α} (h : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
  iff.mpr decidable.le_iff_le_iff_lt_iff_lt (mul_lt_mul_right h)

theorem mul_max_of_nonneg {α : Type u} [linear_ordered_semiring α] {a : α} (b : α) (c : α) (ha : 0 ≤ a) : a * max b c = max (a * b) (a * c) :=
  monotone.map_max (monotone_mul_left_of_nonneg ha)

theorem mul_min_of_nonneg {α : Type u} [linear_ordered_semiring α] {a : α} (b : α) (c : α) (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) :=
  monotone.map_min (monotone_mul_left_of_nonneg ha)

theorem max_mul_of_nonneg {α : Type u} [linear_ordered_semiring α] {c : α} (a : α) (b : α) (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) :=
  monotone.map_max (monotone_mul_right_of_nonneg hc)

theorem min_mul_of_nonneg {α : Type u} [linear_ordered_semiring α] {c : α} (a : α) (b : α) (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) :=
  monotone.map_min (monotone_mul_right_of_nonneg hc)

/-- An `ordered_ring α` is a ring `α` with a partial order such that
multiplication with a positive number and addition are monotone. -/
class ordered_ring (α : Type u) 
extends ring α, ordered_add_comm_group α
where
  zero_le_one : 0 ≤ 1
  mul_pos : ∀ (a b : α), 0 < a → 0 < b → 0 < a * b

theorem ordered_ring.mul_nonneg {α : Type u} [ordered_ring α] (a : α) (b : α) (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ a * b := sorry

theorem ordered_ring.mul_le_mul_of_nonneg_left {α : Type u} [ordered_ring α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (c * a ≤ c * b)) (Eq.symm (propext sub_nonneg))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ c * b - c * a)) (Eq.symm (mul_sub c b a))))
      (ordered_ring.mul_nonneg c (b - a) h₂ (iff.mpr sub_nonneg h₁)))

theorem ordered_ring.mul_le_mul_of_nonneg_right {α : Type u} [ordered_ring α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * c ≤ b * c)) (Eq.symm (propext sub_nonneg))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ b * c - a * c)) (Eq.symm (sub_mul b a c))))
      (ordered_ring.mul_nonneg (b - a) c (iff.mpr sub_nonneg h₁) h₂))

theorem ordered_ring.mul_lt_mul_of_pos_left {α : Type u} [ordered_ring α] {a : α} {b : α} {c : α} (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (c * a < c * b)) (Eq.symm (propext sub_pos))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 < c * b - c * a)) (Eq.symm (mul_sub c b a))))
      (ordered_ring.mul_pos c (b - a) h₂ (iff.mpr sub_pos h₁)))

theorem ordered_ring.mul_lt_mul_of_pos_right {α : Type u} [ordered_ring α] {a : α} {b : α} {c : α} (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * c < b * c)) (Eq.symm (propext sub_pos))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 < b * c - a * c)) (Eq.symm (sub_mul b a c))))
      (ordered_ring.mul_pos (b - a) c (iff.mpr sub_pos h₁) h₂))

protected instance ordered_ring.to_ordered_semiring {α : Type u} [ordered_ring α] : ordered_semiring α :=
  ordered_semiring.mk ordered_ring.add ordered_ring.add_assoc ordered_ring.zero ordered_ring.zero_add
    ordered_ring.add_zero ordered_ring.add_comm ordered_ring.mul ordered_ring.mul_assoc ordered_ring.one
    ordered_ring.one_mul ordered_ring.mul_one sorry sorry ordered_ring.left_distrib ordered_ring.right_distrib sorry sorry
    ordered_ring.le ordered_ring.lt ordered_ring.le_refl ordered_ring.le_trans ordered_ring.le_antisymm
    ordered_ring.add_le_add_left sorry ordered_ring.zero_le_one ordered_ring.mul_lt_mul_of_pos_left
    ordered_ring.mul_lt_mul_of_pos_right

theorem mul_le_mul_of_nonpos_left {α : Type u} [ordered_ring α] {a : α} {b : α} {c : α} (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b := sorry

theorem mul_le_mul_of_nonpos_right {α : Type u} [ordered_ring α] {a : α} {b : α} {c : α} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := sorry

theorem mul_nonneg_of_nonpos_of_nonpos {α : Type u} [ordered_ring α] {a : α} {b : α} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b :=
  (fun (this : 0 * b ≤ a * b) => eq.mp (Eq._oldrec (Eq.refl (0 * b ≤ a * b)) (zero_mul b)) this)
    (mul_le_mul_of_nonpos_right ha hb)

theorem mul_lt_mul_of_neg_left {α : Type u} [ordered_ring α] {a : α} {b : α} {c : α} (h : b < a) (hc : c < 0) : c * a < c * b := sorry

theorem mul_lt_mul_of_neg_right {α : Type u} [ordered_ring α] {a : α} {b : α} {c : α} (h : b < a) (hc : c < 0) : a * c < b * c := sorry

theorem mul_pos_of_neg_of_neg {α : Type u} [ordered_ring α] {a : α} {b : α} (ha : a < 0) (hb : b < 0) : 0 < a * b :=
  (fun (this : 0 * b < a * b) => eq.mp (Eq._oldrec (Eq.refl (0 * b < a * b)) (zero_mul b)) this)
    (mul_lt_mul_of_neg_right ha hb)

/-- An `ordered_comm_ring α` is a commutative ring `α` with a partial order such that
multiplication with a positive number and addition are monotone. -/
class ordered_comm_ring (α : Type u) 
extends ordered_ring α, comm_ring α, ordered_comm_semiring α
where

/-- A `linear_ordered_ring α` is a ring `α` with a linear order such that
multiplication with a positive number and addition are monotone. -/
class linear_ordered_ring (α : Type u) 
extends nontrivial α, linear_order α, ordered_ring α
where

protected instance linear_ordered_ring.to_linear_ordered_add_comm_group {α : Type u} [s : linear_ordered_ring α] : linear_ordered_add_comm_group α :=
  linear_ordered_add_comm_group.mk linear_ordered_ring.add linear_ordered_ring.add_assoc linear_ordered_ring.zero
    linear_ordered_ring.zero_add linear_ordered_ring.add_zero linear_ordered_ring.neg linear_ordered_ring.sub
    linear_ordered_ring.add_left_neg linear_ordered_ring.add_comm linear_ordered_ring.le linear_ordered_ring.lt
    linear_ordered_ring.le_refl linear_ordered_ring.le_trans linear_ordered_ring.le_antisymm linear_ordered_ring.le_total
    linear_ordered_ring.decidable_le linear_ordered_ring.decidable_eq linear_ordered_ring.decidable_lt
    linear_ordered_ring.add_le_add_left

protected instance linear_ordered_ring.to_linear_ordered_semiring {α : Type u} [linear_ordered_ring α] : linear_ordered_semiring α :=
  linear_ordered_semiring.mk linear_ordered_ring.add linear_ordered_ring.add_assoc linear_ordered_ring.zero
    linear_ordered_ring.zero_add linear_ordered_ring.add_zero linear_ordered_ring.add_comm linear_ordered_ring.mul
    linear_ordered_ring.mul_assoc linear_ordered_ring.one linear_ordered_ring.one_mul linear_ordered_ring.mul_one sorry
    sorry linear_ordered_ring.left_distrib linear_ordered_ring.right_distrib sorry sorry linear_ordered_ring.le
    linear_ordered_ring.lt linear_ordered_ring.le_refl linear_ordered_ring.le_trans linear_ordered_ring.le_antisymm
    linear_ordered_ring.add_le_add_left sorry linear_ordered_ring.zero_le_one sorry sorry linear_ordered_ring.le_total
    linear_ordered_ring.decidable_le linear_ordered_ring.decidable_eq linear_ordered_ring.decidable_lt
    linear_ordered_ring.exists_pair_ne

protected instance linear_ordered_ring.to_domain {α : Type u} [linear_ordered_ring α] : domain α :=
  domain.mk linear_ordered_ring.add linear_ordered_ring.add_assoc linear_ordered_ring.zero linear_ordered_ring.zero_add
    linear_ordered_ring.add_zero linear_ordered_ring.neg linear_ordered_ring.sub linear_ordered_ring.add_left_neg
    linear_ordered_ring.add_comm linear_ordered_ring.mul linear_ordered_ring.mul_assoc linear_ordered_ring.one
    linear_ordered_ring.one_mul linear_ordered_ring.mul_one linear_ordered_ring.left_distrib
    linear_ordered_ring.right_distrib linear_ordered_ring.exists_pair_ne sorry

@[simp] theorem abs_one {α : Type u} [linear_ordered_ring α] : abs 1 = 1 :=
  abs_of_pos zero_lt_one

@[simp] theorem abs_two {α : Type u} [linear_ordered_ring α] : abs (bit0 1) = bit0 1 :=
  abs_of_pos zero_lt_two

theorem abs_mul {α : Type u} [linear_ordered_ring α] (a : α) (b : α) : abs (a * b) = abs a * abs b := sorry

/-- `abs` as a `monoid_with_zero_hom`. -/
def abs_hom {α : Type u} [linear_ordered_ring α] : monoid_with_zero_hom α α :=
  monoid_with_zero_hom.mk abs sorry abs_one abs_mul

@[simp] theorem abs_mul_abs_self {α : Type u} [linear_ordered_ring α] (a : α) : abs a * abs a = a * a :=
  abs_by_cases (fun (x : α) => x * x = a * a) rfl (neg_mul_neg a a)

@[simp] theorem abs_mul_self {α : Type u} [linear_ordered_ring α] (a : α) : abs (a * a) = a * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs (a * a) = a * a)) (abs_mul a a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (abs a * abs a = a * a)) (abs_mul_abs_self a))) (Eq.refl (a * a)))

theorem mul_pos_iff {α : Type u} [linear_ordered_ring α] {a : α} {b : α} : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := sorry

theorem mul_neg_iff {α : Type u} [linear_ordered_ring α] {a : α} {b : α} : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := sorry

theorem mul_nonneg_iff {α : Type u} [linear_ordered_ring α] {a : α} {b : α} : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := sorry

theorem mul_nonpos_iff {α : Type u} [linear_ordered_ring α] {a : α} {b : α} : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := sorry

theorem mul_self_nonneg {α : Type u} [linear_ordered_ring α] (a : α) : 0 ≤ a * a :=
  abs_mul_self a ▸ abs_nonneg (a * a)

@[simp] theorem neg_le_self_iff {α : Type u} [linear_ordered_ring α] {a : α} : -a ≤ a ↔ 0 ≤ a := sorry

@[simp] theorem neg_lt_self_iff {α : Type u} [linear_ordered_ring α] {a : α} : -a < a ↔ 0 < a := sorry

@[simp] theorem le_neg_self_iff {α : Type u} [linear_ordered_ring α] {a : α} : a ≤ -a ↔ a ≤ 0 :=
  iff.trans
    (iff.trans (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ -a ↔ --a ≤ -a)) (neg_neg a))) (iff.refl (a ≤ -a))) neg_le_self_iff)
    neg_nonneg

@[simp] theorem lt_neg_self_iff {α : Type u} [linear_ordered_ring α] {a : α} : a < -a ↔ a < 0 :=
  iff.trans
    (iff.trans (eq.mpr (id (Eq._oldrec (Eq.refl (a < -a ↔ --a < -a)) (neg_neg a))) (iff.refl (a < -a))) neg_lt_self_iff)
    neg_pos

@[simp] theorem abs_eq_self {α : Type u} [linear_ordered_ring α] {a : α} : abs a = a ↔ 0 ≤ a := sorry

@[simp] theorem abs_eq_neg_self {α : Type u} [linear_ordered_ring α] {a : α} : abs a = -a ↔ a ≤ 0 := sorry

theorem gt_of_mul_lt_mul_neg_left {α : Type u} [linear_ordered_ring α] {a : α} {b : α} {c : α} (h : c * a < c * b) (hc : c ≤ 0) : b < a := sorry

theorem neg_one_lt_zero {α : Type u} [linear_ordered_ring α] : -1 < 0 :=
  iff.mpr neg_lt_zero zero_lt_one

theorem le_of_mul_le_of_one_le {α : Type u} [linear_ordered_ring α] {a : α} {b : α} {c : α} (h : a * c ≤ b) (hb : 0 ≤ b) (hc : 1 ≤ c) : a ≤ b :=
  (fun (h' : a * c ≤ b * c) => le_of_mul_le_mul_right h' (has_lt.lt.trans_le zero_lt_one hc))
    (le_trans (trans_rel_left LessEq h (eq.mpr (id (Eq._oldrec (Eq.refl (b = b * 1)) (mul_one b))) (Eq.refl b)))
      (mul_le_mul_of_nonneg_left hc hb))

theorem nonneg_le_nonneg_of_squares_le {α : Type u} [linear_ordered_ring α] {a : α} {b : α} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b :=
  le_of_not_gt fun (hab : a > b) => has_lt.lt.not_le (mul_self_lt_mul_self hb hab) h

theorem mul_self_le_mul_self_iff {α : Type u} [linear_ordered_ring α] {a : α} {b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b :=
  { mp := mul_self_le_mul_self h1, mpr := nonneg_le_nonneg_of_squares_le h2 }

theorem mul_self_lt_mul_self_iff {α : Type u} [linear_ordered_ring α] {a : α} {b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b :=
  iff.symm (strict_mono_incr_on.lt_iff_lt strict_mono_incr_on_mul_self h1 h2)

theorem mul_self_inj {α : Type u} [linear_ordered_ring α] {a : α} {b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a * a = b * b ↔ a = b :=
  set.inj_on.eq_iff (strict_mono_incr_on.inj_on strict_mono_incr_on_mul_self) h1 h2

@[simp] theorem mul_le_mul_left_of_neg {α : Type u} [linear_ordered_ring α] {a : α} {b : α} {c : α} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
  { mp := le_imp_le_of_lt_imp_lt fun (h' : a < b) => mul_lt_mul_of_neg_left h' h,
    mpr := fun (h' : b ≤ a) => mul_le_mul_of_nonpos_left h' (has_lt.lt.le h) }

@[simp] theorem mul_le_mul_right_of_neg {α : Type u} [linear_ordered_ring α] {a : α} {b : α} {c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
  { mp := le_imp_le_of_lt_imp_lt fun (h' : a < b) => mul_lt_mul_of_neg_right h' h,
    mpr := fun (h' : b ≤ a) => mul_le_mul_of_nonpos_right h' (has_lt.lt.le h) }

@[simp] theorem mul_lt_mul_left_of_neg {α : Type u} [linear_ordered_ring α] {a : α} {b : α} {c : α} (h : c < 0) : c * a < c * b ↔ b < a :=
  lt_iff_lt_of_le_iff_le (mul_le_mul_left_of_neg h)

@[simp] theorem mul_lt_mul_right_of_neg {α : Type u} [linear_ordered_ring α] {a : α} {b : α} {c : α} (h : c < 0) : a * c < b * c ↔ b < a :=
  lt_iff_lt_of_le_iff_le (mul_le_mul_right_of_neg h)

theorem sub_one_lt {α : Type u} [linear_ordered_ring α] (a : α) : a - 1 < a :=
  iff.mpr sub_lt_iff_lt_add (lt_add_one a)

theorem mul_self_pos {α : Type u} [linear_ordered_ring α] {a : α} (ha : a ≠ 0) : 0 < a * a :=
  or.dcases_on (lt_trichotomy a 0) (fun (h : a < 0) => mul_pos_of_neg_of_neg h h)
    fun (h : a = 0 ∨ 0 < a) => or.dcases_on h (fun (h : a = 0) => false.elim (ha h)) fun (h : 0 < a) => mul_pos h h

theorem mul_self_le_mul_self_of_le_of_neg_le {α : Type u} [linear_ordered_ring α] {x : α} {y : α} (h₁ : x ≤ y) (h₂ : -x ≤ y) : x * x ≤ y * y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x * x ≤ y * y)) (Eq.symm (abs_mul_abs_self x))))
    (mul_self_le_mul_self (abs_nonneg x) (iff.mpr abs_le { left := iff.mpr neg_le h₂, right := h₁ }))

theorem nonneg_of_mul_nonpos_left {α : Type u} [linear_ordered_ring α] {a : α} {b : α} (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
  le_of_not_gt fun (ha : 0 > a) => absurd h (has_lt.lt.not_le (mul_pos_of_neg_of_neg ha hb))

theorem nonneg_of_mul_nonpos_right {α : Type u} [linear_ordered_ring α] {a : α} {b : α} (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
  le_of_not_gt fun (hb : 0 > b) => absurd h (has_lt.lt.not_le (mul_pos_of_neg_of_neg ha hb))

theorem pos_of_mul_neg_left {α : Type u} [linear_ordered_ring α] {a : α} {b : α} (h : a * b < 0) (hb : b ≤ 0) : 0 < a :=
  lt_of_not_ge fun (ha : 0 ≥ a) => absurd h (has_le.le.not_lt (mul_nonneg_of_nonpos_of_nonpos ha hb))

theorem pos_of_mul_neg_right {α : Type u} [linear_ordered_ring α] {a : α} {b : α} (h : a * b < 0) (ha : a ≤ 0) : 0 < b :=
  lt_of_not_ge fun (hb : 0 ≥ b) => absurd h (has_le.le.not_lt (mul_nonneg_of_nonpos_of_nonpos ha hb))

/-- The sum of two squares is zero iff both elements are zero. -/
theorem mul_self_add_mul_self_eq_zero {α : Type u} [linear_ordered_ring α] {x : α} {y : α} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 := sorry

theorem eq_zero_of_mul_self_add_mul_self_eq_zero {α : Type u} [linear_ordered_ring α] {a : α} {b : α} (h : a * a + b * b = 0) : a = 0 :=
  and.left (iff.mp mul_self_add_mul_self_eq_zero h)

theorem abs_eq_iff_mul_self_eq {α : Type u} [linear_ordered_ring α] {a : α} {b : α} : abs a = abs b ↔ a * a = b * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs a = abs b ↔ a * a = b * b)) (Eq.symm (abs_mul_abs_self a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (abs a = abs b ↔ abs a * abs a = b * b)) (Eq.symm (abs_mul_abs_self b))))
      (iff.symm (mul_self_inj (abs_nonneg a) (abs_nonneg b))))

theorem abs_lt_iff_mul_self_lt {α : Type u} [linear_ordered_ring α] {a : α} {b : α} : abs a < abs b ↔ a * a < b * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs a < abs b ↔ a * a < b * b)) (Eq.symm (abs_mul_abs_self a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (abs a < abs b ↔ abs a * abs a < b * b)) (Eq.symm (abs_mul_abs_self b))))
      (mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)))

theorem abs_le_iff_mul_self_le {α : Type u} [linear_ordered_ring α] {a : α} {b : α} : abs a ≤ abs b ↔ a * a ≤ b * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs a ≤ abs b ↔ a * a ≤ b * b)) (Eq.symm (abs_mul_abs_self a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (abs a ≤ abs b ↔ abs a * abs a ≤ b * b)) (Eq.symm (abs_mul_abs_self b))))
      (mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)))

theorem abs_le_one_iff_mul_self_le_one {α : Type u} [linear_ordered_ring α] {a : α} : abs a ≤ 1 ↔ a * a ≤ 1 := sorry

/-- A `linear_ordered_comm_ring α` is a commutative ring `α` with a linear order
such that multiplication with a positive number and addition are monotone. -/
class linear_ordered_comm_ring (α : Type u) 
extends linear_ordered_ring α, comm_monoid α
where

protected instance linear_ordered_comm_ring.to_ordered_comm_ring {α : Type u} [d : linear_ordered_comm_ring α] : ordered_comm_ring α := sorry

-- One might hope that `{ ..linear_ordered_ring.to_linear_ordered_semiring, ..d }`

-- achieved the same result here.

-- Unfortunately with that definition we see mismatched instances in `algebra.star.chsh`.

protected instance linear_ordered_comm_ring.to_integral_domain {α : Type u} [s : linear_ordered_comm_ring α] : integral_domain α :=
  integral_domain.mk domain.add sorry domain.zero sorry sorry domain.neg domain.sub sorry sorry domain.mul sorry
    domain.one sorry sorry sorry sorry linear_ordered_comm_ring.mul_comm sorry sorry

protected instance linear_ordered_comm_ring.to_linear_ordered_semiring {α : Type u} [d : linear_ordered_comm_ring α] : linear_ordered_semiring α := sorry

theorem max_mul_mul_le_max_mul_max {α : Type u} [linear_ordered_comm_ring α] {a : α} {d : α} (b : α) (c : α) (ha : 0 ≤ a) (hd : 0 ≤ d) : max (a * b) (d * c) ≤ max a c * max d b := sorry

theorem abs_sub_square {α : Type u} [linear_ordered_comm_ring α] (a : α) (b : α) : abs (a - b) * abs (a - b) = a * a + b * b - (1 + 1) * a * b := sorry

/-- Extend `nonneg_add_comm_group` to support ordered rings
  specified by their nonnegative elements -/
class nonneg_ring (α : Type u_1) 
extends nonneg_add_comm_group α, ring α
where
  one_nonneg : nonneg 1
  mul_nonneg : ∀ {a b : α}, nonneg a → nonneg b → nonneg (a * b)
  mul_pos : ∀ {a b : α}, pos a → pos b → pos (a * b)

/-- Extend `nonneg_add_comm_group` to support linearly ordered rings
  specified by their nonnegative elements -/
class linear_nonneg_ring (α : Type u_1) 
extends nonneg_add_comm_group α, domain α
where
  one_pos : pos 1
  mul_nonneg : ∀ {a b : α}, nonneg a → nonneg b → nonneg (a * b)
  nonneg_total : ∀ (a : α), nonneg a ∨ nonneg (-a)

namespace nonneg_ring


/-- `to_linear_nonneg_ring` shows that a `nonneg_ring` with a total order is a `domain`,
hence a `linear_nonneg_ring`. -/
def to_linear_nonneg_ring {α : Type u} [nonneg_ring α] [nontrivial α] (nonneg_total : ∀ (a : α), nonneg a ∨ nonneg (-a)) : linear_nonneg_ring α :=
  linear_nonneg_ring.mk add add_assoc zero zero_add add_zero neg sub add_left_neg add_comm mul mul_assoc one one_mul
    mul_one left_distrib right_distrib nontrivial.exists_pair_ne sorry nonneg pos zero_nonneg add_nonneg nonneg_antisymm
    sorry mul_nonneg nonneg_total

end nonneg_ring


namespace linear_nonneg_ring


protected instance to_nonneg_ring {α : Type u} [linear_nonneg_ring α] : nonneg_ring α :=
  nonneg_ring.mk add add_assoc zero zero_add add_zero neg sub add_left_neg add_comm mul mul_assoc one one_mul mul_one
    left_distrib right_distrib nonneg pos zero_nonneg add_nonneg nonneg_antisymm sorry mul_nonneg sorry

/-- Construct `linear_order` from `linear_nonneg_ring`. This is not an instance
because we don't use it in `mathlib`. -/
def to_linear_order {α : Type u} [linear_nonneg_ring α] [decidable_pred nonneg] : linear_order α :=
  linear_order.mk ordered_add_comm_group.le ordered_add_comm_group.lt sorry sorry sorry sorry
    (fun (a b : α) => _inst_2 (b - a)) Mathlib.decidable_eq_of_decidable_le
    fun (a b : α) => Mathlib.decidable_lt_of_decidable_le a b

/-- Construct `linear_ordered_ring` from `linear_nonneg_ring`.
This is not an instance because we don't use it in `mathlib`. -/
def to_linear_ordered_ring {α : Type u} [linear_nonneg_ring α] [decidable_pred nonneg] : linear_ordered_ring α :=
  linear_ordered_ring.mk add add_assoc zero zero_add add_zero neg sub add_left_neg add_comm mul mul_assoc one one_mul
    mul_one left_distrib right_distrib ordered_add_comm_group.le ordered_add_comm_group.lt sorry sorry sorry sorry sorry
    sorry sorry linear_order.decidable_le linear_order.decidable_eq linear_order.decidable_lt exists_pair_ne

/-- Convert a `linear_nonneg_ring` with a commutative multiplication and
decidable non-negativity into a `linear_ordered_comm_ring` -/
def to_linear_ordered_comm_ring {α : Type u} [linear_nonneg_ring α] [decidable_pred nonneg] [comm : is_commutative α Mul.mul] : linear_ordered_comm_ring α :=
  linear_ordered_comm_ring.mk linear_ordered_ring.add sorry linear_ordered_ring.zero sorry sorry linear_ordered_ring.neg
    linear_ordered_ring.sub sorry sorry linear_ordered_ring.mul sorry linear_ordered_ring.one sorry sorry sorry sorry
    linear_ordered_ring.le linear_ordered_ring.lt sorry sorry sorry sorry sorry sorry sorry
    linear_ordered_ring.decidable_le linear_ordered_ring.decidable_eq linear_ordered_ring.decidable_lt sorry sorry

end linear_nonneg_ring


/-- A canonically ordered commutative semiring is an ordered, commutative semiring
in which `a ≤ b` iff there exists `c` with `b = a + c`. This is satisfied by the
natural numbers, for example, but not the integers or other ordered groups. -/
class canonically_ordered_comm_semiring (α : Type u_1) 
extends comm_semiring α, canonically_ordered_add_monoid α
where
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (a b : α), a * b = 0 → a = 0 ∨ b = 0

namespace canonically_ordered_semiring


protected instance canonically_ordered_comm_semiring.to_no_zero_divisors {α : Type u} [canonically_ordered_comm_semiring α] : no_zero_divisors α :=
  no_zero_divisors.mk canonically_ordered_comm_semiring.eq_zero_or_eq_zero_of_mul_eq_zero

theorem mul_le_mul {α : Type u} [canonically_ordered_comm_semiring α] {a : α} {b : α} {c : α} {d : α} (hab : a ≤ b) (hcd : c ≤ d) : a * c ≤ b * d := sorry

theorem mul_le_mul_left' {α : Type u} [canonically_ordered_comm_semiring α] {b : α} {c : α} (h : b ≤ c) (a : α) : a * b ≤ a * c :=
  mul_le_mul le_rfl h

theorem mul_le_mul_right' {α : Type u} [canonically_ordered_comm_semiring α] {b : α} {c : α} (h : b ≤ c) (a : α) : b * a ≤ c * a :=
  mul_le_mul h le_rfl

/-- A version of `zero_lt_one : 0 < 1` for a `canonically_ordered_comm_semiring`. -/
theorem zero_lt_one {α : Type u} [canonically_ordered_comm_semiring α] [nontrivial α] : 0 < 1 :=
  has_le.le.lt_of_ne (zero_le 1) zero_ne_one

theorem mul_pos {α : Type u} [canonically_ordered_comm_semiring α] {a : α} {b : α} : 0 < a * b ↔ 0 < a ∧ 0 < b := sorry

end canonically_ordered_semiring


namespace with_top


protected instance nontrivial {α : Type u} [Nonempty α] : nontrivial (with_top α) :=
  option.nontrivial

protected instance mul_zero_class {α : Type u} [DecidableEq α] [HasZero α] [Mul α] : mul_zero_class (with_top α) :=
  mul_zero_class.mk
    (fun (m n : with_top α) => ite (m = 0 ∨ n = 0) 0 (option.bind m fun (a : α) => option.bind n fun (b : α) => ↑(a * b)))
    0 sorry sorry

theorem mul_def {α : Type u} [DecidableEq α] [HasZero α] [Mul α] {a : with_top α} {b : with_top α} : a * b = ite (a = 0 ∨ b = 0) 0 (option.bind a fun (a : α) => option.bind b fun (b : α) => ↑(a * b)) :=
  rfl

@[simp] theorem mul_top {α : Type u} [DecidableEq α] [HasZero α] [Mul α] {a : with_top α} (h : a ≠ 0) : a * ⊤ = ⊤ := sorry

@[simp] theorem top_mul {α : Type u} [DecidableEq α] [HasZero α] [Mul α] {a : with_top α} (h : a ≠ 0) : ⊤ * a = ⊤ := sorry

@[simp] theorem top_mul_top {α : Type u} [DecidableEq α] [HasZero α] [Mul α] : ⊤ * ⊤ = ⊤ :=
  top_mul top_ne_zero

theorem coe_mul {α : Type u} [DecidableEq α] [mul_zero_class α] {a : α} {b : α} : ↑(a * b) = ↑a * ↑b := sorry

theorem mul_coe {α : Type u} [DecidableEq α] [mul_zero_class α] {b : α} (hb : b ≠ 0) {a : with_top α} : a * ↑b = option.bind a fun (a : α) => ↑(a * b) := sorry

@[simp] theorem mul_eq_top_iff {α : Type u} [DecidableEq α] [mul_zero_class α] {a : with_top α} {b : with_top α} : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := sorry

protected instance no_zero_divisors {α : Type u} [DecidableEq α] [mul_zero_class α] [no_zero_divisors α] : no_zero_divisors (with_top α) := sorry

-- `nontrivial α` is needed here as otherwise

-- we have `1 * ⊤ = ⊤` but also `= 0 * ⊤ = 0`.

protected instance canonically_ordered_comm_semiring {α : Type u} [DecidableEq α] [canonically_ordered_comm_semiring α] [nontrivial α] : canonically_ordered_comm_semiring (with_top α) :=
  canonically_ordered_comm_semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry
    canonically_ordered_add_monoid.le canonically_ordered_add_monoid.lt sorry sorry sorry sorry sorry
    canonically_ordered_add_monoid.bot sorry sorry mul_zero_class.mul sorry ↑1 sorry sorry sorry sorry sorry sorry sorry
    sorry

theorem mul_lt_top {α : Type u} [DecidableEq α] [canonically_ordered_comm_semiring α] [nontrivial α] {a : with_top α} {b : with_top α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤ := sorry

