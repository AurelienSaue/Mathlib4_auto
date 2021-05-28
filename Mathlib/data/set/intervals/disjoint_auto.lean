/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.set.lattice
import PostPort

universes u 

namespace Mathlib

/-!
# Extra lemmas about intervals

This file contains lemmas about intervals that cannot be included into `data.set.intervals.basic`
because this would create an `import` cycle. Namely, lemmas in this file can use definitions
from `data.set.lattice`, including `disjoint`.
-/

namespace set


@[simp] theorem Iic_disjoint_Ioi {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) : disjoint (Iic a) (Ioi b) := sorry

@[simp] theorem Iic_disjoint_Ioc {α : Type u} [preorder α] {a : α} {b : α} {c : α} (h : a ≤ b) : disjoint (Iic a) (Ioc b c) :=
  disjoint.mono (le_refl (Iic a)) (fun (_x : α) => and.left) (Iic_disjoint_Ioi h)

@[simp] theorem Ioc_disjoint_Ioc_same {α : Type u} [preorder α] {a : α} {b : α} {c : α} : disjoint (Ioc a b) (Ioc b c) :=
  disjoint.mono (fun (_x : α) => and.right) (le_refl (Ioc b c)) (Iic_disjoint_Ioc (le_refl b))

@[simp] theorem Ico_disjoint_Ico_same {α : Type u} [preorder α] {a : α} {b : α} {c : α} : disjoint (Ico a b) (Ico b c) :=
  fun (x : α) (hx : x ∈ Ico a b ⊓ Ico b c) => not_le_of_lt (and.right (and.left hx)) (and.left (and.right hx))

@[simp] theorem Ico_disjoint_Ico {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} : disjoint (Ico a₁ a₂) (Ico b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := sorry

@[simp] theorem Ioc_disjoint_Ioc {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} : disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := sorry

/-- If two half-open intervals are disjoint and the endpoint of one lies in the other,
  then it must be equal to the endpoint of the other. -/
theorem eq_of_Ico_disjoint {α : Type u} [linear_order α] {x₁ : α} {x₂ : α} {y₁ : α} {y₂ : α} (h : disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂) (h2 : x₂ ∈ Ico y₁ y₂) : y₁ = x₂ := sorry

