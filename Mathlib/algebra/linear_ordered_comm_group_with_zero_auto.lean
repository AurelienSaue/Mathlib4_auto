/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.ordered_group
import Mathlib.algebra.group_with_zero.default
import Mathlib.algebra.group_with_zero.power
import Mathlib.tactic.abel
import PostPort

universes u_1 l u_2 

namespace Mathlib

/-!
# Linearly ordered commutative groups and monoids with a zero element adjoined

This file sets up a special class of linearly ordered commutative monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative group Γ and formally adjoining a zero element: Γ ∪ {0}.

The disadvantage is that a type such as `nnreal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.

Note that to avoid issues with import cycles, `linear_ordered_comm_monoid_with_zero` is defined
in another file. However, the lemmas about it are stated here.
-/

/-- A linearly ordered commutative group with a zero element. -/
class linear_ordered_comm_group_with_zero (α : Type u_1) 
extends comm_group_with_zero α, linear_ordered_comm_monoid_with_zero α
where

/-
The following facts are true more generally in a (linearly) ordered commutative monoid.
-/

theorem one_le_pow_of_one_le' {α : Type u_1} {x : α} [linear_ordered_comm_monoid_with_zero α] {n : ℕ} (H : 1 ≤ x) : 1 ≤ x ^ n :=
  Nat.rec (le_refl 1) (fun (n : ℕ) (ih : 1 ≤ x ^ n) => one_le_mul H ih) n

theorem pow_le_one_of_le_one {α : Type u_1} {x : α} [linear_ordered_comm_monoid_with_zero α] {n : ℕ} (H : x ≤ 1) : x ^ n ≤ 1 :=
  Nat.rec (le_refl 1) (fun (n : ℕ) (ih : x ^ n ≤ 1) => mul_le_one' H ih) n

theorem eq_one_of_pow_eq_one {α : Type u_1} {x : α} [linear_ordered_comm_monoid_with_zero α] {n : ℕ} (hn : n ≠ 0) (H : x ^ n = 1) : x = 1 := sorry

theorem pow_eq_one_iff {α : Type u_1} {x : α} [linear_ordered_comm_monoid_with_zero α] {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 :=
  { mp := eq_one_of_pow_eq_one hn, mpr := fun (ᾰ : x = 1) => Eq._oldrec (one_pow n) (Eq.symm ᾰ) }

theorem one_le_pow_iff {α : Type u_1} {x : α} [linear_ordered_comm_monoid_with_zero α] {n : ℕ} (hn : n ≠ 0) : 1 ≤ x ^ n ↔ 1 ≤ x := sorry

theorem pow_le_one_iff {α : Type u_1} {x : α} [linear_ordered_comm_monoid_with_zero α] {n : ℕ} (hn : n ≠ 0) : x ^ n ≤ 1 ↔ x ≤ 1 := sorry

theorem zero_le_one' {α : Type u_1} [linear_ordered_comm_monoid_with_zero α] : 0 ≤ 1 :=
  linear_ordered_comm_monoid_with_zero.zero_le_one

@[simp] theorem zero_le' {α : Type u_1} {a : α} [linear_ordered_comm_monoid_with_zero α] : 0 ≤ a := sorry

@[simp] theorem not_lt_zero' {α : Type u_1} {a : α} [linear_ordered_comm_monoid_with_zero α] : ¬a < 0 :=
  not_lt_of_le zero_le'

@[simp] theorem le_zero_iff {α : Type u_1} {a : α} [linear_ordered_comm_monoid_with_zero α] : a ≤ 0 ↔ a = 0 :=
  { mp := fun (h : a ≤ 0) => le_antisymm h zero_le', mpr := fun (h : a = 0) => h ▸ le_refl a }

theorem zero_lt_iff {α : Type u_1} {a : α} [linear_ordered_comm_monoid_with_zero α] : 0 < a ↔ a ≠ 0 :=
  { mp := ne_of_gt, mpr := fun (h : a ≠ 0) => lt_of_le_of_ne zero_le' (ne.symm h) }

theorem ne_zero_of_lt {α : Type u_1} {a : α} {b : α} [linear_ordered_comm_monoid_with_zero α] (h : b < a) : a ≠ 0 :=
  fun (h1 : a = 0) => not_lt_zero' ((fun (this : b < 0) => this) (h1 ▸ h))

theorem zero_lt_one'' {α : Type u_1} [linear_ordered_comm_group_with_zero α] : 0 < 1 :=
  lt_of_le_of_ne zero_le_one' zero_ne_one

theorem le_of_le_mul_right {α : Type u_1} {a : α} {b : α} {c : α} [linear_ordered_comm_group_with_zero α] (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b := sorry

theorem le_mul_inv_of_mul_le {α : Type u_1} {a : α} {b : α} {c : α} [linear_ordered_comm_group_with_zero α] (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * (c⁻¹) := sorry

theorem mul_inv_le_of_le_mul {α : Type u_1} {a : α} {b : α} {c : α} [linear_ordered_comm_group_with_zero α] (h : c ≠ 0) (hab : a ≤ b * c) : a * (c⁻¹) ≤ b := sorry

theorem div_le_div' {α : Type u_1} [linear_ordered_comm_group_with_zero α] (a : α) (b : α) (c : α) (d : α) (hb : b ≠ 0) (hd : d ≠ 0) : a * (b⁻¹) ≤ c * (d⁻¹) ↔ a * d ≤ c * b := sorry

@[simp] theorem units.zero_lt {α : Type u_1} [linear_ordered_comm_group_with_zero α] (u : units α) : 0 < ↑u :=
  iff.mpr zero_lt_iff (units.ne_zero u)

theorem mul_lt_mul'''' {α : Type u_1} {a : α} {b : α} {c : α} {d : α} [linear_ordered_comm_group_with_zero α] (hab : a < b) (hcd : c < d) : a * c < b * d := sorry

theorem mul_inv_lt_of_lt_mul' {α : Type u_1} {x : α} {y : α} {z : α} [linear_ordered_comm_group_with_zero α] (h : x < y * z) : x * (z⁻¹) < y := sorry

theorem mul_lt_right' {α : Type u_1} {a : α} {b : α} [linear_ordered_comm_group_with_zero α] (c : α) (h : a < b) (hc : c ≠ 0) : a * c < b * c := sorry

theorem pow_lt_pow_succ {α : Type u_1} [linear_ordered_comm_group_with_zero α] {x : α} {n : ℕ} (hx : 1 < x) : x ^ n < x ^ Nat.succ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ^ n < x ^ Nat.succ n)) (Eq.symm (one_mul (x ^ n)))))
    (mul_lt_right' (x ^ n) hx (pow_ne_zero n (ne_of_gt (lt_trans zero_lt_one'' hx))))

theorem pow_lt_pow' {α : Type u_1} [linear_ordered_comm_group_with_zero α] {x : α} {m : ℕ} {n : ℕ} (hx : 1 < x) (hmn : m < n) : x ^ m < x ^ n :=
  nat.less_than_or_equal.drec (pow_lt_pow_succ hx)
    (fun {n : ℕ} (hmn : nat.less_than_or_equal (Nat.succ m) n) (ih : x ^ m < x ^ n) => lt_trans ih (pow_lt_pow_succ hx))
    hmn

theorem inv_lt_inv'' {α : Type u_1} {a : α} {b : α} [linear_ordered_comm_group_with_zero α] (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ < (b⁻¹) ↔ b < a :=
  inv_lt_inv_iff

theorem inv_le_inv'' {α : Type u_1} {a : α} {b : α} [linear_ordered_comm_group_with_zero α] (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ ≤ (b⁻¹) ↔ b ≤ a :=
  inv_le_inv_iff

namespace monoid_hom


theorem map_neg_one {α : Type u_1} [linear_ordered_comm_group_with_zero α] {R : Type u_2} [ring R] (f : R →* α) : coe_fn f (-1) = 1 := sorry

@[simp] theorem map_neg {α : Type u_1} [linear_ordered_comm_group_with_zero α] {R : Type u_2} [ring R] (f : R →* α) (x : R) : coe_fn f (-x) = coe_fn f x := sorry

theorem map_sub_swap {α : Type u_1} [linear_ordered_comm_group_with_zero α] {R : Type u_2} [ring R] (f : R →* α) (x : R) (y : R) : coe_fn f (x - y) = coe_fn f (y - x) := sorry

