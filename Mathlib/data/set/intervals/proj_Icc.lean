/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.intervals.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Projection of a line onto a closed interval

Given a linearly ordered type `α`, in this file we define

* `set.proj_Icc (a b : α) (h : a ≤ b)` to be the map `α → [a, b]` sending `(-∞, a]` to `a`, `[b, ∞)`
  to `b`, and each point `x ∈ [a, b]` to itself;
* `set.Icc_extend {a b : α} (h : a ≤ b) (f : Icc a b → β)` to be the extension of `f` to `α` defined
  as `f ∘ proj_Icc a b h`.

We also prove some trivial properties of these maps.
-/

namespace set


/-- Projection of `α` to the closed interval `[a, b]`. -/
def proj_Icc {α : Type u_1} [linear_order α] (a : α) (b : α) (h : a ≤ b) (x : α) : ↥(Icc a b) :=
  { val := max a (min b x), property := sorry }

theorem proj_Icc_of_le_left {α : Type u_1} [linear_order α] {a : α} {b : α} (h : a ≤ b) {x : α} (hx : x ≤ a) : proj_Icc a b h x = { val := a, property := iff.mpr left_mem_Icc h } := sorry

@[simp] theorem proj_Icc_left {α : Type u_1} [linear_order α] {a : α} {b : α} (h : a ≤ b) : proj_Icc a b h a = { val := a, property := iff.mpr left_mem_Icc h } :=
  proj_Icc_of_le_left h le_rfl

theorem proj_Icc_of_right_le {α : Type u_1} [linear_order α] {a : α} {b : α} (h : a ≤ b) {x : α} (hx : b ≤ x) : proj_Icc a b h x = { val := b, property := iff.mpr right_mem_Icc h } := sorry

@[simp] theorem proj_Icc_right {α : Type u_1} [linear_order α] {a : α} {b : α} (h : a ≤ b) : proj_Icc a b h b = { val := b, property := iff.mpr right_mem_Icc h } :=
  proj_Icc_of_right_le h le_rfl

theorem proj_Icc_of_mem {α : Type u_1} [linear_order α] {a : α} {b : α} (h : a ≤ b) {x : α} (hx : x ∈ Icc a b) : proj_Icc a b h x = { val := x, property := hx } := sorry

@[simp] theorem proj_Icc_coe {α : Type u_1} [linear_order α] {a : α} {b : α} (h : a ≤ b) (x : ↥(Icc a b)) : proj_Icc a b h ↑x = x :=
  subtype.cases_on x fun (x_val : α) (x_property : x_val ∈ Icc a b) => proj_Icc_of_mem h x_property

theorem proj_Icc_surj_on {α : Type u_1} [linear_order α] {a : α} {b : α} (h : a ≤ b) : surj_on (proj_Icc a b h) (Icc a b) univ :=
  fun (x : ↥(Icc a b)) (_x : x ∈ univ) => Exists.intro ↑x { left := subtype.property x, right := proj_Icc_coe h x }

theorem proj_Icc_surjective {α : Type u_1} [linear_order α] {a : α} {b : α} (h : a ≤ b) : function.surjective (proj_Icc a b h) :=
  fun (x : ↥(Icc a b)) => Exists.intro (↑x) (proj_Icc_coe h x)

@[simp] theorem range_proj_Icc {α : Type u_1} [linear_order α] {a : α} {b : α} (h : a ≤ b) : range (proj_Icc a b h) = univ :=
  function.surjective.range_eq (proj_Icc_surjective h)

theorem monotone_proj_Icc {α : Type u_1} [linear_order α] {a : α} {b : α} (h : a ≤ b) : monotone (proj_Icc a b h) :=
  fun (x y : α) (hxy : x ≤ y) => max_le_max le_rfl (min_le_min le_rfl hxy)

theorem strict_mono_incr_on_proj_Icc {α : Type u_1} [linear_order α] {a : α} {b : α} (h : a ≤ b) : strict_mono_incr_on (proj_Icc a b h) (Icc a b) := sorry

/-- Extend a function `[a, b] → β` to a map `α → β`. -/
def Icc_extend {α : Type u_1} {β : Type u_2} [linear_order α] {a : α} {b : α} (h : a ≤ b) (f : ↥(Icc a b) → β) : α → β :=
  f ∘ proj_Icc a b h

@[simp] theorem Icc_extend_range {α : Type u_1} {β : Type u_2} [linear_order α] {a : α} {b : α} (h : a ≤ b) (f : ↥(Icc a b) → β) : range (Icc_extend h f) = range f := sorry

theorem Icc_extend_of_le_left {α : Type u_1} {β : Type u_2} [linear_order α] {a : α} {b : α} (h : a ≤ b) {x : α} (f : ↥(Icc a b) → β) (hx : x ≤ a) : Icc_extend h f x = f { val := a, property := iff.mpr left_mem_Icc h } :=
  congr_arg f (proj_Icc_of_le_left h hx)

@[simp] theorem Icc_extend_left {α : Type u_1} {β : Type u_2} [linear_order α] {a : α} {b : α} (h : a ≤ b) (f : ↥(Icc a b) → β) : Icc_extend h f a = f { val := a, property := iff.mpr left_mem_Icc h } :=
  Icc_extend_of_le_left h f le_rfl

theorem Icc_extend_of_right_le {α : Type u_1} {β : Type u_2} [linear_order α] {a : α} {b : α} (h : a ≤ b) {x : α} (f : ↥(Icc a b) → β) (hx : b ≤ x) : Icc_extend h f x = f { val := b, property := iff.mpr right_mem_Icc h } :=
  congr_arg f (proj_Icc_of_right_le h hx)

@[simp] theorem Icc_extend_right {α : Type u_1} {β : Type u_2} [linear_order α] {a : α} {b : α} (h : a ≤ b) (f : ↥(Icc a b) → β) : Icc_extend h f b = f { val := b, property := iff.mpr right_mem_Icc h } :=
  Icc_extend_of_right_le h f le_rfl

theorem Icc_extend_of_mem {α : Type u_1} {β : Type u_2} [linear_order α] {a : α} {b : α} (h : a ≤ b) {x : α} (f : ↥(Icc a b) → β) (hx : x ∈ Icc a b) : Icc_extend h f x = f { val := x, property := hx } :=
  congr_arg f (proj_Icc_of_mem h hx)

@[simp] theorem Icc_extend_coe {α : Type u_1} {β : Type u_2} [linear_order α] {a : α} {b : α} (h : a ≤ b) (f : ↥(Icc a b) → β) (x : ↥(Icc a b)) : Icc_extend h f ↑x = f x :=
  congr_arg f (proj_Icc_coe h x)

end set


theorem monotone.Icc_extend {α : Type u_1} {β : Type u_2} [linear_order α] [preorder β] {a : α} {b : α} (h : a ≤ b) {f : ↥(set.Icc a b) → β} (hf : monotone f) : monotone (set.Icc_extend h f) :=
  monotone.comp hf (set.monotone_proj_Icc h)

theorem strict_mono.strict_mono_incr_on_Icc_extend {α : Type u_1} {β : Type u_2} [linear_order α] [preorder β] {a : α} {b : α} (h : a ≤ b) {f : ↥(set.Icc a b) → β} (hf : strict_mono f) : strict_mono_incr_on (set.Icc_extend h f) (set.Icc a b) :=
  strict_mono.comp_strict_mono_incr_on hf (set.strict_mono_incr_on_proj_Icc h)

