/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.algebra.order
import Mathlib.Lean3Lib.init.meta.default
 

universes u 

namespace Mathlib

def min {α : Type u} [linear_order α] (a : α) (b : α) : α :=
  ite (a ≤ b) a b

def max {α : Type u} [linear_order α] (a : α) (b : α) : α :=
  ite (b ≤ a) a b

theorem min_le_left {α : Type u} [linear_order α] (a : α) (b : α) : min a b ≤ a := sorry

theorem min_le_right {α : Type u} [linear_order α] (a : α) (b : α) : min a b ≤ b := sorry

theorem le_min {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b := sorry

theorem le_max_left {α : Type u} [linear_order α] (a : α) (b : α) : a ≤ max a b := sorry

theorem le_max_right {α : Type u} [linear_order α] (a : α) (b : α) : b ≤ max a b := sorry

theorem max_le {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c := sorry

theorem eq_min {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀ {d : α}, d ≤ a → d ≤ b → d ≤ c) : c = min a b :=
  le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

theorem min_comm {α : Type u} [linear_order α] (a : α) (b : α) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) fun (c : α) (h₁ : c ≤ b) (h₂ : c ≤ a) => le_min h₂ h₁

theorem min_assoc {α : Type u} [linear_order α] (a : α) (b : α) (c : α) : min (min a b) c = min a (min b c) := sorry

theorem min_left_comm {α : Type u} [linear_order α] (a : α) (b : α) (c : α) : min a (min b c) = min b (min a c) :=
  left_comm min min_comm min_assoc

@[simp] theorem min_self {α : Type u} [linear_order α] (a : α) : min a a = a := sorry

theorem min_eq_left {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) : min a b = a :=
  Eq.symm (eq_min (le_refl a) h fun (d : α) (ᾰ : d ≤ a) (ᾰ_1 : d ≤ b) => ᾰ)

theorem min_eq_right {α : Type u} [linear_order α] {a : α} {b : α} (h : b ≤ a) : min a b = b :=
  min_comm b a ▸ min_eq_left h

theorem eq_max {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) (h₃ : ∀ {d : α}, a ≤ d → b ≤ d → c ≤ d) : c = max a b :=
  le_antisymm (h₃ (le_max_left a b) (le_max_right a b)) (max_le h₁ h₂)

theorem max_comm {α : Type u} [linear_order α] (a : α) (b : α) : max a b = max b a :=
  eq_max (le_max_right a b) (le_max_left a b) fun (c : α) (h₁ : b ≤ c) (h₂ : a ≤ c) => max_le h₂ h₁

theorem max_assoc {α : Type u} [linear_order α] (a : α) (b : α) (c : α) : max (max a b) c = max a (max b c) := sorry

theorem max_left_comm {α : Type u} [linear_order α] (a : α) (b : α) (c : α) : max a (max b c) = max b (max a c) :=
  left_comm max max_comm max_assoc

@[simp] theorem max_self {α : Type u} [linear_order α] (a : α) : max a a = a := sorry

theorem max_eq_left {α : Type u} [linear_order α] {a : α} {b : α} (h : b ≤ a) : max a b = a :=
  Eq.symm (eq_max (le_refl a) h fun (d : α) (ᾰ : a ≤ d) (ᾰ_1 : b ≤ d) => ᾰ)

theorem max_eq_right {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) : max a b = b :=
  max_comm b a ▸ max_eq_left h

/- these rely on lt_of_lt -/

theorem min_eq_left_of_lt {α : Type u} [linear_order α] {a : α} {b : α} (h : a < b) : min a b = a :=
  min_eq_left (le_of_lt h)

theorem min_eq_right_of_lt {α : Type u} [linear_order α] {a : α} {b : α} (h : b < a) : min a b = b :=
  min_eq_right (le_of_lt h)

theorem max_eq_left_of_lt {α : Type u} [linear_order α] {a : α} {b : α} (h : b < a) : max a b = a :=
  max_eq_left (le_of_lt h)

theorem max_eq_right_of_lt {α : Type u} [linear_order α] {a : α} {b : α} (h : a < b) : max a b = b :=
  max_eq_right (le_of_lt h)

/- these use the fact that it is a linear ordering -/

theorem lt_min {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a < b) (h₂ : a < c) : a < min b c := sorry

theorem max_lt {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a < c) (h₂ : b < c) : max a b < c := sorry

