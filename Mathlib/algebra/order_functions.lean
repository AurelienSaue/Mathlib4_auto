/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.order
import Mathlib.order.lattice
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# `max` and `min`

This file proves basic properties about maxima and minima on a `linear_order`.

## Tags

min, max
-/

-- translate from lattices to linear orders (sup → max, inf → min)

@[simp] theorem le_min_iff {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : c ≤ min a b ↔ c ≤ a ∧ c ≤ b :=
  le_inf_iff

@[simp] theorem max_le_iff {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  sup_le_iff

theorem max_le_max {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} : a ≤ c → b ≤ d → max a b ≤ max c d :=
  sup_le_sup

theorem min_le_min {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} : a ≤ c → b ≤ d → min a b ≤ min c d :=
  inf_le_inf

theorem le_max_left_of_le {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : a ≤ b → a ≤ max b c :=
  le_sup_left_of_le

theorem le_max_right_of_le {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : a ≤ c → a ≤ max b c :=
  le_sup_right_of_le

theorem min_le_left_of_le {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : a ≤ c → min a b ≤ c :=
  inf_le_left_of_le

theorem min_le_right_of_le {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : b ≤ c → min a b ≤ c :=
  inf_le_right_of_le

theorem max_min_distrib_left {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : max a (min b c) = min (max a b) (max a c) :=
  sup_inf_left

theorem max_min_distrib_right {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : max (min a b) c = min (max a c) (max b c) :=
  sup_inf_right

theorem min_max_distrib_left {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : min a (max b c) = max (min a b) (min a c) :=
  inf_sup_left

theorem min_max_distrib_right {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : min (max a b) c = max (min a c) (min b c) :=
  inf_sup_right

theorem min_le_max {α : Type u} [linear_order α] {a : α} {b : α} : min a b ≤ max a b :=
  le_trans (min_le_left a b) (le_max_left a b)

@[simp] theorem min_eq_left_iff {α : Type u} [linear_order α] {a : α} {b : α} : min a b = a ↔ a ≤ b :=
  inf_eq_left

@[simp] theorem min_eq_right_iff {α : Type u} [linear_order α] {a : α} {b : α} : min a b = b ↔ b ≤ a :=
  inf_eq_right

@[simp] theorem max_eq_left_iff {α : Type u} [linear_order α] {a : α} {b : α} : max a b = a ↔ b ≤ a :=
  sup_eq_left

@[simp] theorem max_eq_right_iff {α : Type u} [linear_order α] {a : α} {b : α} : max a b = b ↔ a ≤ b :=
  sup_eq_right

/-- An instance asserting that `max a a = a` -/
protected instance max_idem {α : Type u} [linear_order α] : is_idempotent α max :=
  Mathlib.sup_is_idempotent

/-- An instance asserting that `min a a = a` -/
protected instance min_idem {α : Type u} [linear_order α] : is_idempotent α min :=
  Mathlib.inf_is_idempotent

@[simp] theorem max_lt_iff {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : max a b < c ↔ a < c ∧ b < c :=
  sup_lt_iff

@[simp] theorem lt_min_iff {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : a < min b c ↔ a < b ∧ a < c :=
  lt_inf_iff

@[simp] theorem lt_max_iff {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : a < max b c ↔ a < b ∨ a < c :=
  lt_sup_iff

@[simp] theorem min_lt_iff {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : min a b < c ↔ a < c ∨ b < c :=
  lt_max_iff

@[simp] theorem min_le_iff {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : min a b ≤ c ↔ a ≤ c ∨ b ≤ c :=
  inf_le_iff

@[simp] theorem le_max_iff {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
  min_le_iff

theorem max_lt_max {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} (h₁ : a < c) (h₂ : b < d) : max a b < max c d := sorry

theorem min_lt_min {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} (h₁ : a < c) (h₂ : b < d) : min a b < min c d :=
  max_lt_max h₁ h₂

theorem min_right_comm {α : Type u} [linear_order α] (a : α) (b : α) (c : α) : min (min a b) c = min (min a c) b :=
  right_comm min min_comm min_assoc a b c

theorem max.left_comm {α : Type u} [linear_order α] (a : α) (b : α) (c : α) : max a (max b c) = max b (max a c) :=
  left_comm max max_comm max_assoc a b c

theorem max.right_comm {α : Type u} [linear_order α] (a : α) (b : α) (c : α) : max (max a b) c = max (max a c) b :=
  right_comm max max_comm max_assoc a b c

theorem monotone.map_max {α : Type u} {β : Type v} [linear_order α] [linear_order β] {f : α → β} {a : α} {b : α} (hf : monotone f) : f (max a b) = max (f a) (f b) := sorry

theorem monotone.map_min {α : Type u} {β : Type v} [linear_order α] [linear_order β] {f : α → β} {a : α} {b : α} (hf : monotone f) : f (min a b) = min (f a) (f b) :=
  monotone.map_max (monotone.order_dual hf)

theorem min_choice {α : Type u} [linear_order α] (a : α) (b : α) : min a b = a ∨ min a b = b := sorry

theorem max_choice {α : Type u} [linear_order α] (a : α) (b : α) : max a b = a ∨ max a b = b :=
  min_choice a b

theorem le_of_max_le_left {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h : max a b ≤ c) : a ≤ c :=
  le_trans (le_max_left a b) h

theorem le_of_max_le_right {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h : max a b ≤ c) : b ≤ c :=
  le_trans (le_max_right a b) h

