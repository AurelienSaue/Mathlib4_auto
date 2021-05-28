/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.set.lattice
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Accumulate

The function `accumulate` takes a set `s` and returns `⋃ y ≤ x, s y`.
-/

namespace set


/-- `accumulate s` is the union of `s y` for `y ≤ x`. -/
def accumulate {α : Type u_1} {β : Type u_2} [HasLessEq α] (s : α → set β) (x : α) : set β :=
  Union fun (y : α) => Union fun (H : y ≤ x) => s y

theorem accumulate_def {α : Type u_1} {β : Type u_2} {s : α → set β} [HasLessEq α] {x : α} : accumulate s x = Union fun (y : α) => Union fun (H : y ≤ x) => s y :=
  rfl

@[simp] theorem mem_accumulate {α : Type u_1} {β : Type u_2} {s : α → set β} [HasLessEq α] {x : α} {z : β} : z ∈ accumulate s x ↔ ∃ (y : α), ∃ (H : y ≤ x), z ∈ s y :=
  mem_bUnion_iff

theorem subset_accumulate {α : Type u_1} {β : Type u_2} {s : α → set β} [preorder α] {x : α} : s x ⊆ accumulate s x :=
  fun (z : β) => mem_bUnion le_rfl

theorem monotone_accumulate {α : Type u_1} {β : Type u_2} {s : α → set β} [preorder α] : monotone (accumulate s) :=
  fun (x y : α) (hxy : x ≤ y) =>
    bUnion_subset_bUnion_left fun (z : α) (hz : z ∈ fun (y : α) => preorder.le y x) => le_trans hz hxy

theorem bUnion_accumulate {α : Type u_1} {β : Type u_2} {s : α → set β} [preorder α] (x : α) : (Union fun (y : α) => Union fun (H : y ≤ x) => accumulate s y) = Union fun (y : α) => Union fun (H : y ≤ x) => s y :=
  subset.antisymm (bUnion_subset fun (x_1 : α) (hx : x_1 ∈ fun (y : α) => preorder.le y x) => monotone_accumulate hx)
    (bUnion_subset_bUnion_right fun (x_1 : α) (hx : x_1 ∈ fun (y : α) => preorder.le y x) => subset_accumulate)

theorem Union_accumulate {α : Type u_1} {β : Type u_2} {s : α → set β} [preorder α] : (Union fun (x : α) => accumulate s x) = Union fun (x : α) => s x := sorry

