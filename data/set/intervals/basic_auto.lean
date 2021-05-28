/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.ordered_group
import Mathlib.data.set.basic
import PostPort

universes u 

namespace Mathlib

/-!
# Intervals

In any preorder `α`, we define intervals (which on each side can be either infinite, open, or
closed) using the following naming conventions:
- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side. For instance,
`Ioc a b` denotes the inverval `(a, b]`.

This file contains these definitions, and basic facts on inclusion, intersection, difference of
intervals (where the precise statements may depend on the properties of the order, in particular
for some statements it should be `linear_order` or `densely_ordered`).

TODO: This is just the beginning; a lot of rules are missing
-/

namespace set


/-- Left-open right-open interval -/
def Ioo {α : Type u} [preorder α] (a : α) (b : α) : set α :=
  set_of fun (x : α) => a < x ∧ x < b

/-- Left-closed right-open interval -/
def Ico {α : Type u} [preorder α] (a : α) (b : α) : set α :=
  set_of fun (x : α) => a ≤ x ∧ x < b

/-- Left-infinite right-open interval -/
def Iio {α : Type u} [preorder α] (a : α) : set α :=
  set_of fun (x : α) => x < a

/-- Left-closed right-closed interval -/
def Icc {α : Type u} [preorder α] (a : α) (b : α) : set α :=
  set_of fun (x : α) => a ≤ x ∧ x ≤ b

/-- Left-infinite right-closed interval -/
def Iic {α : Type u} [preorder α] (b : α) : set α :=
  set_of fun (x : α) => x ≤ b

/-- Left-open right-closed interval -/
def Ioc {α : Type u} [preorder α] (a : α) (b : α) : set α :=
  set_of fun (x : α) => a < x ∧ x ≤ b

/-- Left-closed right-infinite interval -/
def Ici {α : Type u} [preorder α] (a : α) : set α :=
  set_of fun (x : α) => a ≤ x

/-- Left-open right-infinite interval -/
def Ioi {α : Type u} [preorder α] (a : α) : set α :=
  set_of fun (x : α) => a < x

theorem Ioo_def {α : Type u} [preorder α] (a : α) (b : α) : (set_of fun (x : α) => a < x ∧ x < b) = Ioo a b :=
  rfl

theorem Ico_def {α : Type u} [preorder α] (a : α) (b : α) : (set_of fun (x : α) => a ≤ x ∧ x < b) = Ico a b :=
  rfl

theorem Iio_def {α : Type u} [preorder α] (a : α) : (set_of fun (x : α) => x < a) = Iio a :=
  rfl

theorem Icc_def {α : Type u} [preorder α] (a : α) (b : α) : (set_of fun (x : α) => a ≤ x ∧ x ≤ b) = Icc a b :=
  rfl

theorem Iic_def {α : Type u} [preorder α] (b : α) : (set_of fun (x : α) => x ≤ b) = Iic b :=
  rfl

theorem Ioc_def {α : Type u} [preorder α] (a : α) (b : α) : (set_of fun (x : α) => a < x ∧ x ≤ b) = Ioc a b :=
  rfl

theorem Ici_def {α : Type u} [preorder α] (a : α) : (set_of fun (x : α) => a ≤ x) = Ici a :=
  rfl

theorem Ioi_def {α : Type u} [preorder α] (a : α) : (set_of fun (x : α) => a < x) = Ioi a :=
  rfl

@[simp] theorem mem_Ioo {α : Type u} [preorder α] {a : α} {b : α} {x : α} : x ∈ Ioo a b ↔ a < x ∧ x < b :=
  iff.rfl

@[simp] theorem mem_Ico {α : Type u} [preorder α] {a : α} {b : α} {x : α} : x ∈ Ico a b ↔ a ≤ x ∧ x < b :=
  iff.rfl

@[simp] theorem mem_Iio {α : Type u} [preorder α] {b : α} {x : α} : x ∈ Iio b ↔ x < b :=
  iff.rfl

@[simp] theorem mem_Icc {α : Type u} [preorder α] {a : α} {b : α} {x : α} : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
  iff.rfl

@[simp] theorem mem_Iic {α : Type u} [preorder α] {b : α} {x : α} : x ∈ Iic b ↔ x ≤ b :=
  iff.rfl

@[simp] theorem mem_Ioc {α : Type u} [preorder α] {a : α} {b : α} {x : α} : x ∈ Ioc a b ↔ a < x ∧ x ≤ b :=
  iff.rfl

@[simp] theorem mem_Ici {α : Type u} [preorder α] {a : α} {x : α} : x ∈ Ici a ↔ a ≤ x :=
  iff.rfl

@[simp] theorem mem_Ioi {α : Type u} [preorder α] {a : α} {x : α} : x ∈ Ioi a ↔ a < x :=
  iff.rfl

@[simp] theorem left_mem_Ioo {α : Type u} [preorder α] {a : α} {b : α} : a ∈ Ioo a b ↔ False := sorry

@[simp] theorem left_mem_Ico {α : Type u} [preorder α] {a : α} {b : α} : a ∈ Ico a b ↔ a < b := sorry

@[simp] theorem left_mem_Icc {α : Type u} [preorder α] {a : α} {b : α} : a ∈ Icc a b ↔ a ≤ b := sorry

@[simp] theorem left_mem_Ioc {α : Type u} [preorder α] {a : α} {b : α} : a ∈ Ioc a b ↔ False := sorry

theorem left_mem_Ici {α : Type u} [preorder α] {a : α} : a ∈ Ici a :=
  eq.mpr (id (propext mem_Ici)) (le_refl a)

@[simp] theorem right_mem_Ioo {α : Type u} [preorder α] {a : α} {b : α} : b ∈ Ioo a b ↔ False := sorry

@[simp] theorem right_mem_Ico {α : Type u} [preorder α] {a : α} {b : α} : b ∈ Ico a b ↔ False := sorry

@[simp] theorem right_mem_Icc {α : Type u} [preorder α] {a : α} {b : α} : b ∈ Icc a b ↔ a ≤ b := sorry

@[simp] theorem right_mem_Ioc {α : Type u} [preorder α] {a : α} {b : α} : b ∈ Ioc a b ↔ a < b := sorry

theorem right_mem_Iic {α : Type u} [preorder α] {a : α} : a ∈ Iic a :=
  eq.mpr (id (propext mem_Iic)) (le_refl a)

@[simp] theorem dual_Ici {α : Type u} [preorder α] {a : α} : Ici a = Iic a :=
  rfl

@[simp] theorem dual_Iic {α : Type u} [preorder α] {a : α} : Iic a = Ici a :=
  rfl

@[simp] theorem dual_Ioi {α : Type u} [preorder α] {a : α} : Ioi a = Iio a :=
  rfl

@[simp] theorem dual_Iio {α : Type u} [preorder α] {a : α} : Iio a = Ioi a :=
  rfl

@[simp] theorem dual_Icc {α : Type u} [preorder α] {a : α} {b : α} : Icc a b = Icc b a :=
  ext fun (x : order_dual α) => and_comm (a ≤ x) (x ≤ b)

@[simp] theorem dual_Ioc {α : Type u} [preorder α] {a : α} {b : α} : Ioc a b = Ico b a :=
  ext fun (x : order_dual α) => and_comm (a < x) (x ≤ b)

@[simp] theorem dual_Ico {α : Type u} [preorder α] {a : α} {b : α} : Ico a b = Ioc b a :=
  ext fun (x : order_dual α) => and_comm (a ≤ x) (x < b)

@[simp] theorem dual_Ioo {α : Type u} [preorder α] {a : α} {b : α} : Ioo a b = Ioo b a :=
  ext fun (x : order_dual α) => and_comm (a < x) (x < b)

@[simp] theorem nonempty_Icc {α : Type u} [preorder α] {a : α} {b : α} : set.nonempty (Icc a b) ↔ a ≤ b := sorry

@[simp] theorem nonempty_Ico {α : Type u} [preorder α] {a : α} {b : α} : set.nonempty (Ico a b) ↔ a < b := sorry

@[simp] theorem nonempty_Ioc {α : Type u} [preorder α] {a : α} {b : α} : set.nonempty (Ioc a b) ↔ a < b := sorry

@[simp] theorem nonempty_Ici {α : Type u} [preorder α] {a : α} : set.nonempty (Ici a) :=
  Exists.intro a left_mem_Ici

@[simp] theorem nonempty_Iic {α : Type u} [preorder α] {a : α} : set.nonempty (Iic a) :=
  Exists.intro a right_mem_Iic

@[simp] theorem nonempty_Ioo {α : Type u} [preorder α] {a : α} {b : α} [densely_ordered α] : set.nonempty (Ioo a b) ↔ a < b := sorry

@[simp] theorem nonempty_Ioi {α : Type u} [preorder α] {a : α} [no_top_order α] : set.nonempty (Ioi a) :=
  no_top a

@[simp] theorem nonempty_Iio {α : Type u} [preorder α] {a : α} [no_bot_order α] : set.nonempty (Iio a) :=
  no_bot a

theorem nonempty_Icc_subtype {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) : Nonempty ↥(Icc a b) :=
  nonempty.to_subtype (iff.mpr nonempty_Icc h)

theorem nonempty_Ico_subtype {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) : Nonempty ↥(Ico a b) :=
  nonempty.to_subtype (iff.mpr nonempty_Ico h)

theorem nonempty_Ioc_subtype {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) : Nonempty ↥(Ioc a b) :=
  nonempty.to_subtype (iff.mpr nonempty_Ioc h)

/-- An interval `Ici a` is nonempty. -/
protected instance nonempty_Ici_subtype {α : Type u} [preorder α] {a : α} : Nonempty ↥(Ici a) :=
  nonempty.to_subtype nonempty_Ici

/-- An interval `Iic a` is nonempty. -/
protected instance nonempty_Iic_subtype {α : Type u} [preorder α] {a : α} : Nonempty ↥(Iic a) :=
  nonempty.to_subtype nonempty_Iic

theorem nonempty_Ioo_subtype {α : Type u} [preorder α] {a : α} {b : α} [densely_ordered α] (h : a < b) : Nonempty ↥(Ioo a b) :=
  nonempty.to_subtype (iff.mpr nonempty_Ioo h)

/-- In a `no_top_order`, the intervals `Ioi` are nonempty. -/
protected instance nonempty_Ioi_subtype {α : Type u} [preorder α] {a : α} [no_top_order α] : Nonempty ↥(Ioi a) :=
  nonempty.to_subtype nonempty_Ioi

/-- In a `no_bot_order`, the intervals `Iio` are nonempty. -/
protected instance nonempty_Iio_subtype {α : Type u} [preorder α] {a : α} [no_bot_order α] : Nonempty ↥(Iio a) :=
  nonempty.to_subtype nonempty_Iio

@[simp] theorem Ioo_eq_empty {α : Type u} [preorder α] {a : α} {b : α} (h : b ≤ a) : Ioo a b = ∅ := sorry

@[simp] theorem Ico_eq_empty {α : Type u} [preorder α] {a : α} {b : α} (h : b ≤ a) : Ico a b = ∅ := sorry

@[simp] theorem Icc_eq_empty {α : Type u} [preorder α] {a : α} {b : α} (h : b < a) : Icc a b = ∅ := sorry

@[simp] theorem Ioc_eq_empty {α : Type u} [preorder α] {a : α} {b : α} (h : b ≤ a) : Ioc a b = ∅ := sorry

@[simp] theorem Ioo_self {α : Type u} [preorder α] (a : α) : Ioo a a = ∅ :=
  Ioo_eq_empty (le_refl a)

@[simp] theorem Ico_self {α : Type u} [preorder α] (a : α) : Ico a a = ∅ :=
  Ico_eq_empty (le_refl a)

@[simp] theorem Ioc_self {α : Type u} [preorder α] (a : α) : Ioc a a = ∅ :=
  Ioc_eq_empty (le_refl a)

theorem Ici_subset_Ici {α : Type u} [preorder α] {a : α} {b : α} : Ici a ⊆ Ici b ↔ b ≤ a :=
  { mp := fun (h : Ici a ⊆ Ici b) => h left_mem_Ici, mpr := fun (h : b ≤ a) (x : α) (hx : x ∈ Ici a) => le_trans h hx }

theorem Iic_subset_Iic {α : Type u} [preorder α] {a : α} {b : α} : Iic a ⊆ Iic b ↔ a ≤ b :=
  Ici_subset_Ici

theorem Ici_subset_Ioi {α : Type u} [preorder α] {a : α} {b : α} : Ici a ⊆ Ioi b ↔ b < a :=
  { mp := fun (h : Ici a ⊆ Ioi b) => h left_mem_Ici,
    mpr := fun (h : b < a) (x : α) (hx : x ∈ Ici a) => lt_of_lt_of_le h hx }

theorem Iic_subset_Iio {α : Type u} [preorder α] {a : α} {b : α} : Iic a ⊆ Iio b ↔ a < b :=
  { mp := fun (h : Iic a ⊆ Iio b) => h right_mem_Iic,
    mpr := fun (h : a < b) (x : α) (hx : x ∈ Iic a) => lt_of_le_of_lt hx h }

theorem Ioo_subset_Ioo {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ := sorry

theorem Ioo_subset_Ioo_left {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b : α} (h : a₁ ≤ a₂) : Ioo a₂ b ⊆ Ioo a₁ b :=
  Ioo_subset_Ioo h (le_refl b)

theorem Ioo_subset_Ioo_right {α : Type u} [preorder α] {a : α} {b₁ : α} {b₂ : α} (h : b₁ ≤ b₂) : Ioo a b₁ ⊆ Ioo a b₂ :=
  Ioo_subset_Ioo (le_refl a) h

theorem Ico_subset_Ico {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ico a₂ b₂ := sorry

theorem Ico_subset_Ico_left {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b : α} (h : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b :=
  Ico_subset_Ico h (le_refl b)

theorem Ico_subset_Ico_right {α : Type u} [preorder α] {a : α} {b₁ : α} {b₂ : α} (h : b₁ ≤ b₂) : Ico a b₁ ⊆ Ico a b₂ :=
  Ico_subset_Ico (le_refl a) h

theorem Icc_subset_Icc {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : Icc a₁ b₁ ⊆ Icc a₂ b₂ := sorry

theorem Icc_subset_Icc_left {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b : α} (h : a₁ ≤ a₂) : Icc a₂ b ⊆ Icc a₁ b :=
  Icc_subset_Icc h (le_refl b)

theorem Icc_subset_Icc_right {α : Type u} [preorder α] {a : α} {b₁ : α} {b₂ : α} (h : b₁ ≤ b₂) : Icc a b₁ ⊆ Icc a b₂ :=
  Icc_subset_Icc (le_refl a) h

theorem Icc_subset_Ioo {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (ha : a₂ < a₁) (hb : b₁ < b₂) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ :=
  fun (x : α) (hx : x ∈ Icc a₁ b₁) =>
    { left := lt_of_lt_of_le ha (and.left hx), right := lt_of_le_of_lt (and.right hx) hb }

theorem Icc_subset_Ici_self {α : Type u} [preorder α] {a : α} {b : α} : Icc a b ⊆ Ici a :=
  fun (x : α) => and.left

theorem Icc_subset_Iic_self {α : Type u} [preorder α] {a : α} {b : α} : Icc a b ⊆ Iic b :=
  fun (x : α) => and.right

theorem Ioc_subset_Iic_self {α : Type u} [preorder α] {a : α} {b : α} : Ioc a b ⊆ Iic b :=
  fun (x : α) => and.right

theorem Ioc_subset_Ioc {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : Ioc a₁ b₁ ⊆ Ioc a₂ b₂ := sorry

theorem Ioc_subset_Ioc_left {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b : α} (h : a₁ ≤ a₂) : Ioc a₂ b ⊆ Ioc a₁ b :=
  Ioc_subset_Ioc h (le_refl b)

theorem Ioc_subset_Ioc_right {α : Type u} [preorder α] {a : α} {b₁ : α} {b₂ : α} (h : b₁ ≤ b₂) : Ioc a b₁ ⊆ Ioc a b₂ :=
  Ioc_subset_Ioc (le_refl a) h

theorem Ico_subset_Ioo_left {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b : α} (h₁ : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b :=
  fun (x : α) => and.imp_left (lt_of_lt_of_le h₁)

theorem Ioc_subset_Ioo_right {α : Type u} [preorder α] {a : α} {b₁ : α} {b₂ : α} (h : b₁ < b₂) : Ioc a b₁ ⊆ Ioo a b₂ :=
  fun (x : α) => and.imp_right fun (h' : x ≤ b₁) => lt_of_le_of_lt h' h

theorem Icc_subset_Ico_right {α : Type u} [preorder α] {a : α} {b₁ : α} {b₂ : α} (h₁ : b₁ < b₂) : Icc a b₁ ⊆ Ico a b₂ :=
  fun (x : α) => and.imp_right fun (h₂ : x ≤ b₁) => lt_of_le_of_lt h₂ h₁

theorem Ioo_subset_Ico_self {α : Type u} [preorder α] {a : α} {b : α} : Ioo a b ⊆ Ico a b :=
  fun (x : α) => and.imp_left le_of_lt

theorem Ioo_subset_Ioc_self {α : Type u} [preorder α] {a : α} {b : α} : Ioo a b ⊆ Ioc a b :=
  fun (x : α) => and.imp_right le_of_lt

theorem Ico_subset_Icc_self {α : Type u} [preorder α] {a : α} {b : α} : Ico a b ⊆ Icc a b :=
  fun (x : α) => and.imp_right le_of_lt

theorem Ioc_subset_Icc_self {α : Type u} [preorder α] {a : α} {b : α} : Ioc a b ⊆ Icc a b :=
  fun (x : α) => and.imp_left le_of_lt

theorem Ioo_subset_Icc_self {α : Type u} [preorder α] {a : α} {b : α} : Ioo a b ⊆ Icc a b :=
  subset.trans Ioo_subset_Ico_self Ico_subset_Icc_self

theorem Ico_subset_Iio_self {α : Type u} [preorder α] {a : α} {b : α} : Ico a b ⊆ Iio b :=
  fun (x : α) => and.right

theorem Ioo_subset_Iio_self {α : Type u} [preorder α] {a : α} {b : α} : Ioo a b ⊆ Iio b :=
  fun (x : α) => and.right

theorem Ioc_subset_Ioi_self {α : Type u} [preorder α] {a : α} {b : α} : Ioc a b ⊆ Ioi a :=
  fun (x : α) => and.left

theorem Ioo_subset_Ioi_self {α : Type u} [preorder α] {a : α} {b : α} : Ioo a b ⊆ Ioi a :=
  fun (x : α) => and.left

theorem Ioi_subset_Ici_self {α : Type u} [preorder α] {a : α} : Ioi a ⊆ Ici a :=
  fun (x : α) (hx : x ∈ Ioi a) => le_of_lt hx

theorem Iio_subset_Iic_self {α : Type u} [preorder α] {a : α} : Iio a ⊆ Iic a :=
  fun (x : α) (hx : x ∈ Iio a) => le_of_lt hx

theorem Ico_subset_Ici_self {α : Type u} [preorder α] {a : α} {b : α} : Ico a b ⊆ Ici a :=
  fun (x : α) => and.left

theorem Icc_subset_Icc_iff {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := sorry

theorem Icc_subset_Ioo_iff {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ := sorry

theorem Icc_subset_Ico_iff {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ := sorry

theorem Icc_subset_Ioc_iff {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ := sorry

theorem Icc_subset_Iio_iff {α : Type u} [preorder α] {a₁ : α} {b₁ : α} {b₂ : α} (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Iio b₂ ↔ b₁ < b₂ := sorry

theorem Icc_subset_Ioi_iff {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioi a₂ ↔ a₂ < a₁ := sorry

theorem Icc_subset_Iic_iff {α : Type u} [preorder α] {a₁ : α} {b₁ : α} {b₂ : α} (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Iic b₂ ↔ b₁ ≤ b₂ := sorry

theorem Icc_subset_Ici_iff {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ici a₂ ↔ a₂ ≤ a₁ := sorry

theorem Icc_ssubset_Icc_left {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊂ Icc a₂ b₂ := sorry

theorem Icc_ssubset_Icc_right {α : Type u} [preorder α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (hI : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ < b₂) : Icc a₁ b₁ ⊂ Icc a₂ b₂ := sorry

/-- If `a ≤ b`, then `(b, +∞) ⊆ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_subset_Ioi_iff`. -/
theorem Ioi_subset_Ioi {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) : Ioi b ⊆ Ioi a :=
  fun (x : α) (hx : x ∈ Ioi b) => lt_of_le_of_lt h hx

/-- If `a ≤ b`, then `(b, +∞) ⊆ [a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Ioi_subset_Ici_iff`. -/
theorem Ioi_subset_Ici {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) : Ioi b ⊆ Ici a :=
  subset.trans (Ioi_subset_Ioi h) Ioi_subset_Ici_self

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_subset_Iio_iff`. -/
theorem Iio_subset_Iio {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) : Iio a ⊆ Iio b :=
  fun (x : α) (hx : x ∈ Iio a) => lt_of_lt_of_le hx h

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b]`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Iio_subset_Iic_iff`. -/
theorem Iio_subset_Iic {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) : Iio a ⊆ Iic b :=
  subset.trans (Iio_subset_Iio h) Iio_subset_Iic_self

theorem Ici_inter_Iic {α : Type u} [preorder α] {a : α} {b : α} : Ici a ∩ Iic b = Icc a b :=
  rfl

theorem Ici_inter_Iio {α : Type u} [preorder α] {a : α} {b : α} : Ici a ∩ Iio b = Ico a b :=
  rfl

theorem Ioi_inter_Iic {α : Type u} [preorder α] {a : α} {b : α} : Ioi a ∩ Iic b = Ioc a b :=
  rfl

theorem Ioi_inter_Iio {α : Type u} [preorder α] {a : α} {b : α} : Ioi a ∩ Iio b = Ioo a b :=
  rfl

theorem mem_Icc_of_Ioo {α : Type u} [preorder α] {a : α} {b : α} {x : α} (h : x ∈ Ioo a b) : x ∈ Icc a b :=
  Ioo_subset_Icc_self h

theorem mem_Ico_of_Ioo {α : Type u} [preorder α] {a : α} {b : α} {x : α} (h : x ∈ Ioo a b) : x ∈ Ico a b :=
  Ioo_subset_Ico_self h

theorem mem_Ioc_of_Ioo {α : Type u} [preorder α] {a : α} {b : α} {x : α} (h : x ∈ Ioo a b) : x ∈ Ioc a b :=
  Ioo_subset_Ioc_self h

theorem mem_Icc_of_Ico {α : Type u} [preorder α] {a : α} {b : α} {x : α} (h : x ∈ Ico a b) : x ∈ Icc a b :=
  Ico_subset_Icc_self h

theorem mem_Icc_of_Ioc {α : Type u} [preorder α] {a : α} {b : α} {x : α} (h : x ∈ Ioc a b) : x ∈ Icc a b :=
  Ioc_subset_Icc_self h

theorem mem_Ici_of_Ioi {α : Type u} [preorder α] {a : α} {x : α} (h : x ∈ Ioi a) : x ∈ Ici a :=
  Ioi_subset_Ici_self h

theorem mem_Iic_of_Iio {α : Type u} [preorder α] {a : α} {x : α} (h : x ∈ Iio a) : x ∈ Iic a :=
  Iio_subset_Iic_self h

@[simp] theorem Icc_self {α : Type u} [partial_order α] (a : α) : Icc a a = singleton a := sorry

@[simp] theorem Icc_diff_left {α : Type u} [partial_order α] {a : α} {b : α} : Icc a b \ singleton a = Ioc a b := sorry

@[simp] theorem Icc_diff_right {α : Type u} [partial_order α] {a : α} {b : α} : Icc a b \ singleton b = Ico a b := sorry

@[simp] theorem Ico_diff_left {α : Type u} [partial_order α] {a : α} {b : α} : Ico a b \ singleton a = Ioo a b := sorry

@[simp] theorem Ioc_diff_right {α : Type u} [partial_order α] {a : α} {b : α} : Ioc a b \ singleton b = Ioo a b := sorry

@[simp] theorem Icc_diff_both {α : Type u} [partial_order α] {a : α} {b : α} : Icc a b \ insert a (singleton b) = Ioo a b := sorry

@[simp] theorem Ici_diff_left {α : Type u} [partial_order α] {a : α} : Ici a \ singleton a = Ioi a := sorry

@[simp] theorem Iic_diff_right {α : Type u} [partial_order α] {a : α} : Iic a \ singleton a = Iio a := sorry

@[simp] theorem Ico_diff_Ioo_same {α : Type u} [partial_order α] {a : α} {b : α} (h : a < b) : Ico a b \ Ioo a b = singleton a := sorry

@[simp] theorem Ioc_diff_Ioo_same {α : Type u} [partial_order α] {a : α} {b : α} (h : a < b) : Ioc a b \ Ioo a b = singleton b := sorry

@[simp] theorem Icc_diff_Ico_same {α : Type u} [partial_order α] {a : α} {b : α} (h : a ≤ b) : Icc a b \ Ico a b = singleton b := sorry

@[simp] theorem Icc_diff_Ioc_same {α : Type u} [partial_order α] {a : α} {b : α} (h : a ≤ b) : Icc a b \ Ioc a b = singleton a := sorry

@[simp] theorem Icc_diff_Ioo_same {α : Type u} [partial_order α] {a : α} {b : α} (h : a ≤ b) : Icc a b \ Ioo a b = insert a (singleton b) := sorry

@[simp] theorem Ici_diff_Ioi_same {α : Type u} [partial_order α] {a : α} : Ici a \ Ioi a = singleton a := sorry

@[simp] theorem Iic_diff_Iio_same {α : Type u} [partial_order α] {a : α} : Iic a \ Iio a = singleton a := sorry

@[simp] theorem Ioi_union_left {α : Type u} [partial_order α] {a : α} : Ioi a ∪ singleton a = Ici a := sorry

@[simp] theorem Iio_union_right {α : Type u} [partial_order α] {a : α} : Iio a ∪ singleton a = Iic a :=
  ext fun (x : α) => iff.symm le_iff_lt_or_eq

theorem Ioo_union_left {α : Type u} [partial_order α] {a : α} {b : α} (hab : a < b) : Ioo a b ∪ singleton a = Ico a b := sorry

theorem Ioo_union_right {α : Type u} [partial_order α] {a : α} {b : α} (hab : a < b) : Ioo a b ∪ singleton b = Ioc a b := sorry

theorem Ioc_union_left {α : Type u} [partial_order α] {a : α} {b : α} (hab : a ≤ b) : Ioc a b ∪ singleton a = Icc a b := sorry

theorem Ico_union_right {α : Type u} [partial_order α] {a : α} {b : α} (hab : a ≤ b) : Ico a b ∪ singleton b = Icc a b := sorry

theorem mem_Ici_Ioi_of_subset_of_subset {α : Type u} [partial_order α] {a : α} {s : set α} (ho : Ioi a ⊆ s) (hc : s ⊆ Ici a) : s ∈ insert (Ici a) (singleton (Ioi a)) := sorry

theorem mem_Iic_Iio_of_subset_of_subset {α : Type u} [partial_order α] {a : α} {s : set α} (ho : Iio a ⊆ s) (hc : s ⊆ Iic a) : s ∈ insert (Iic a) (singleton (Iio a)) :=
  mem_Ici_Ioi_of_subset_of_subset ho hc

theorem mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset {α : Type u} [partial_order α] {a : α} {b : α} {s : set α} (ho : Ioo a b ⊆ s) (hc : s ⊆ Icc a b) : s ∈ insert (Icc a b) (insert (Ico a b) (insert (Ioc a b) (singleton (Ioo a b)))) := sorry

theorem mem_Ioo_or_eq_endpoints_of_mem_Icc {α : Type u} [partial_order α] {a : α} {b : α} {x : α} (hmem : x ∈ Icc a b) : x = a ∨ x = b ∨ x ∈ Ioo a b := sorry

theorem mem_Ioo_or_eq_left_of_mem_Ico {α : Type u} [partial_order α] {a : α} {b : α} {x : α} (hmem : x ∈ Ico a b) : x = a ∨ x ∈ Ioo a b := sorry

theorem mem_Ioo_or_eq_right_of_mem_Ioc {α : Type u} [partial_order α] {a : α} {b : α} {x : α} (hmem : x ∈ Ioc a b) : x = b ∨ x ∈ Ioo a b :=
  eq.mp (Eq._oldrec (Eq.refl (x ∈ Ico b a → x = b ∨ x ∈ Ioo a b)) dual_Ico)
    (eq.mp (Eq._oldrec (Eq.refl (x ∈ Ico b a → x = b ∨ x ∈ Ioo b a)) dual_Ioo) mem_Ioo_or_eq_left_of_mem_Ico) hmem

theorem Ici_singleton_of_top {α : Type u} [partial_order α] {a : α} (h_top : ∀ (x : α), x ≤ a) : Ici a = singleton a :=
  ext
    fun (x : α) =>
      { mp := fun (h : x ∈ Ici a) => le_antisymm (h_top x) h, mpr := fun (h : x ∈ singleton a) => le_of_eq (Eq.symm h) }

theorem Iic_singleton_of_bot {α : Type u} [partial_order α] {a : α} (h_bot : ∀ (x : α), a ≤ x) : Iic a = singleton a :=
  Ici_singleton_of_top h_bot

@[simp] theorem Ici_top {α : Type u} [order_top α] : Ici ⊤ = singleton ⊤ :=
  Ici_singleton_of_top fun (_x : α) => le_top

@[simp] theorem Iic_top {α : Type u} [order_top α] : Iic ⊤ = univ :=
  eq_univ_of_forall fun (x : α) => le_top

@[simp] theorem Icc_top {α : Type u} [order_top α] {a : α} : Icc a ⊤ = Ici a := sorry

@[simp] theorem Ioc_top {α : Type u} [order_top α] {a : α} : Ioc a ⊤ = Ioi a := sorry

@[simp] theorem Iic_bot {α : Type u} [order_bot α] : Iic ⊥ = singleton ⊥ :=
  Iic_singleton_of_bot fun (_x : α) => bot_le

@[simp] theorem Ici_bot {α : Type u} [order_bot α] : Ici ⊥ = univ :=
  Iic_top

@[simp] theorem Icc_bot {α : Type u} [order_bot α] {a : α} : Icc ⊥ a = Iic a := sorry

@[simp] theorem Ico_bot {α : Type u} [order_bot α] {a : α} : Ico ⊥ a = Iio a := sorry

@[simp] theorem compl_Iic {α : Type u} [linear_order α] {a : α} : Iic aᶜ = Ioi a :=
  ext fun (_x : α) => not_le

@[simp] theorem compl_Ici {α : Type u} [linear_order α] {a : α} : Ici aᶜ = Iio a :=
  ext fun (_x : α) => not_le

@[simp] theorem compl_Iio {α : Type u} [linear_order α] {a : α} : Iio aᶜ = Ici a :=
  ext fun (_x : α) => not_lt

@[simp] theorem compl_Ioi {α : Type u} [linear_order α] {a : α} : Ioi aᶜ = Iic a :=
  ext fun (_x : α) => not_lt

@[simp] theorem Ici_diff_Ici {α : Type u} [linear_order α] {a : α} {b : α} : Ici a \ Ici b = Ico a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Ici a \ Ici b = Ico a b)) (diff_eq (Ici a) (Ici b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Ici a ∩ (Ici bᶜ) = Ico a b)) compl_Ici))
      (eq.mpr (id (Eq._oldrec (Eq.refl (Ici a ∩ Iio b = Ico a b)) Ici_inter_Iio)) (Eq.refl (Ico a b))))

@[simp] theorem Ici_diff_Ioi {α : Type u} [linear_order α] {a : α} {b : α} : Ici a \ Ioi b = Icc a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Ici a \ Ioi b = Icc a b)) (diff_eq (Ici a) (Ioi b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Ici a ∩ (Ioi bᶜ) = Icc a b)) compl_Ioi))
      (eq.mpr (id (Eq._oldrec (Eq.refl (Ici a ∩ Iic b = Icc a b)) Ici_inter_Iic)) (Eq.refl (Icc a b))))

@[simp] theorem Ioi_diff_Ioi {α : Type u} [linear_order α] {a : α} {b : α} : Ioi a \ Ioi b = Ioc a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Ioi a \ Ioi b = Ioc a b)) (diff_eq (Ioi a) (Ioi b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Ioi a ∩ (Ioi bᶜ) = Ioc a b)) compl_Ioi))
      (eq.mpr (id (Eq._oldrec (Eq.refl (Ioi a ∩ Iic b = Ioc a b)) Ioi_inter_Iic)) (Eq.refl (Ioc a b))))

@[simp] theorem Ioi_diff_Ici {α : Type u} [linear_order α] {a : α} {b : α} : Ioi a \ Ici b = Ioo a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Ioi a \ Ici b = Ioo a b)) (diff_eq (Ioi a) (Ici b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Ioi a ∩ (Ici bᶜ) = Ioo a b)) compl_Ici))
      (eq.mpr (id (Eq._oldrec (Eq.refl (Ioi a ∩ Iio b = Ioo a b)) Ioi_inter_Iio)) (Eq.refl (Ioo a b))))

@[simp] theorem Iic_diff_Iic {α : Type u} [linear_order α] {a : α} {b : α} : Iic b \ Iic a = Ioc a b := sorry

@[simp] theorem Iio_diff_Iic {α : Type u} [linear_order α] {a : α} {b : α} : Iio b \ Iic a = Ioo a b := sorry

@[simp] theorem Iic_diff_Iio {α : Type u} [linear_order α] {a : α} {b : α} : Iic b \ Iio a = Icc a b := sorry

@[simp] theorem Iio_diff_Iio {α : Type u} [linear_order α] {a : α} {b : α} : Iio b \ Iio a = Ico a b := sorry

theorem Ioo_eq_empty_iff {α : Type u} [linear_order α] {a : α} {b : α} [densely_ordered α] : Ioo a b = ∅ ↔ b ≤ a := sorry

theorem Ico_eq_empty_iff {α : Type u} [linear_order α] {a : α} {b : α} : Ico a b = ∅ ↔ b ≤ a := sorry

theorem Icc_eq_empty_iff {α : Type u} [linear_order α] {a : α} {b : α} : Icc a b = ∅ ↔ b < a := sorry

theorem Ico_subset_Ico_iff {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h₁ : a₁ < b₁) : Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := sorry

theorem Ioo_subset_Ioo_iff {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} [densely_ordered α] (h₁ : a₁ < b₁) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := sorry

theorem Ico_eq_Ico_iff {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h : a₁ < b₁ ∨ a₂ < b₂) : Ico a₁ b₁ = Ico a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := sorry

@[simp] theorem Ioi_subset_Ioi_iff {α : Type u} [linear_order α] {a : α} {b : α} : Ioi b ⊆ Ioi a ↔ a ≤ b :=
  { mp := fun (h : Ioi b ⊆ Ioi a) => decidable.by_contradiction fun (ba : ¬a ≤ b) => lt_irrefl a (h (iff.mp not_le ba)),
    mpr := fun (h : a ≤ b) => Ioi_subset_Ioi h }

@[simp] theorem Ioi_subset_Ici_iff {α : Type u} [linear_order α] {a : α} {b : α} [densely_ordered α] : Ioi b ⊆ Ici a ↔ a ≤ b := sorry

@[simp] theorem Iio_subset_Iio_iff {α : Type u} [linear_order α] {a : α} {b : α} : Iio a ⊆ Iio b ↔ a ≤ b :=
  { mp := fun (h : Iio a ⊆ Iio b) => decidable.by_contradiction fun (ab : ¬a ≤ b) => lt_irrefl b (h (iff.mp not_le ab)),
    mpr := fun (h : a ≤ b) => Iio_subset_Iio h }

@[simp] theorem Iio_subset_Iic_iff {α : Type u} [linear_order α] {a : α} {b : α} [densely_ordered α] : Iio a ⊆ Iic b ↔ a ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Iio a ⊆ Iic b ↔ a ≤ b)) (Eq.symm (propext diff_eq_empty))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Iio a \ Iic b = ∅ ↔ a ≤ b)) Iio_diff_Iic))
      (eq.mpr (id (Eq._oldrec (Eq.refl (Ioo b a = ∅ ↔ a ≤ b)) (propext Ioo_eq_empty_iff))) (iff.refl (a ≤ b))))

/-! ### Unions of adjacent intervals -/

/-! #### Two infinite intervals -/

@[simp] theorem Iic_union_Ici {α : Type u} [linear_order α] {a : α} : Iic a ∪ Ici a = univ :=
  eq_univ_of_forall fun (x : α) => le_total x a

@[simp] theorem Iio_union_Ici {α : Type u} [linear_order α] {a : α} : Iio a ∪ Ici a = univ :=
  eq_univ_of_forall fun (x : α) => lt_or_le x a

@[simp] theorem Iic_union_Ioi {α : Type u} [linear_order α] {a : α} : Iic a ∪ Ioi a = univ :=
  eq_univ_of_forall fun (x : α) => le_or_lt x a

/-! #### A finite and an infinite interval -/

theorem Ioo_union_Ioi' {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : c < b) : Ioo a b ∪ Ioi c = Ioi (min a c) := sorry

theorem Ioo_union_Ioi {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h : c < max a b) : Ioo a b ∪ Ioi c = Ioi (min a c) := sorry

theorem Ioi_subset_Ioo_union_Ici {α : Type u} [linear_order α] {a : α} {b : α} : Ioi a ⊆ Ioo a b ∪ Ici b :=
  fun (x : α) (hx : x ∈ Ioi a) =>
    or.elim (lt_or_le x b) (fun (hxb : x < b) => Or.inl { left := hx, right := hxb }) fun (hxb : b ≤ x) => Or.inr hxb

@[simp] theorem Ioo_union_Ici_eq_Ioi {α : Type u} [linear_order α] {a : α} {b : α} (h : a < b) : Ioo a b ∪ Ici b = Ioi a :=
  subset.antisymm (fun (x : α) (hx : x ∈ Ioo a b ∪ Ici b) => or.elim hx and.left (lt_of_lt_of_le h))
    Ioi_subset_Ioo_union_Ici

theorem Ici_subset_Ico_union_Ici {α : Type u} [linear_order α] {a : α} {b : α} : Ici a ⊆ Ico a b ∪ Ici b :=
  fun (x : α) (hx : x ∈ Ici a) =>
    or.elim (lt_or_le x b) (fun (hxb : x < b) => Or.inl { left := hx, right := hxb }) fun (hxb : b ≤ x) => Or.inr hxb

@[simp] theorem Ico_union_Ici_eq_Ici {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) : Ico a b ∪ Ici b = Ici a :=
  subset.antisymm (fun (x : α) (hx : x ∈ Ico a b ∪ Ici b) => or.elim hx and.left (le_trans h)) Ici_subset_Ico_union_Ici

theorem Ico_union_Ici' {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : c ≤ b) : Ico a b ∪ Ici c = Ici (min a c) := sorry

theorem Ico_union_Ici {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h : c ≤ max a b) : Ico a b ∪ Ici c = Ici (min a c) := sorry

theorem Ioi_subset_Ioc_union_Ioi {α : Type u} [linear_order α] {a : α} {b : α} : Ioi a ⊆ Ioc a b ∪ Ioi b :=
  fun (x : α) (hx : x ∈ Ioi a) =>
    or.elim (le_or_lt x b) (fun (hxb : x ≤ b) => Or.inl { left := hx, right := hxb }) fun (hxb : b < x) => Or.inr hxb

@[simp] theorem Ioc_union_Ioi_eq_Ioi {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) : Ioc a b ∪ Ioi b = Ioi a :=
  subset.antisymm (fun (x : α) (hx : x ∈ Ioc a b ∪ Ioi b) => or.elim hx and.left (lt_of_le_of_lt h))
    Ioi_subset_Ioc_union_Ioi

theorem Ioc_union_Ioi' {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : c ≤ b) : Ioc a b ∪ Ioi c = Ioi (min a c) := sorry

theorem Ioc_union_Ioi {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h : c ≤ max a b) : Ioc a b ∪ Ioi c = Ioi (min a c) := sorry

theorem Ici_subset_Icc_union_Ioi {α : Type u} [linear_order α] {a : α} {b : α} : Ici a ⊆ Icc a b ∪ Ioi b :=
  fun (x : α) (hx : x ∈ Ici a) =>
    or.elim (le_or_lt x b) (fun (hxb : x ≤ b) => Or.inl { left := hx, right := hxb }) fun (hxb : b < x) => Or.inr hxb

@[simp] theorem Icc_union_Ioi_eq_Ici {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) : Icc a b ∪ Ioi b = Ici a :=
  subset.antisymm
    (fun (x : α) (hx : x ∈ Icc a b ∪ Ioi b) => or.elim hx and.left fun (hx : x ∈ Ioi b) => le_trans h (le_of_lt hx))
    Ici_subset_Icc_union_Ioi

theorem Ioi_subset_Ioc_union_Ici {α : Type u} [linear_order α] {a : α} {b : α} : Ioi a ⊆ Ioc a b ∪ Ici b :=
  subset.trans Ioi_subset_Ioo_union_Ici (union_subset_union_left (Ici b) Ioo_subset_Ioc_self)

@[simp] theorem Ioc_union_Ici_eq_Ioi {α : Type u} [linear_order α] {a : α} {b : α} (h : a < b) : Ioc a b ∪ Ici b = Ioi a :=
  subset.antisymm (fun (x : α) (hx : x ∈ Ioc a b ∪ Ici b) => or.elim hx and.left (lt_of_lt_of_le h))
    Ioi_subset_Ioc_union_Ici

theorem Ici_subset_Icc_union_Ici {α : Type u} [linear_order α] {a : α} {b : α} : Ici a ⊆ Icc a b ∪ Ici b :=
  subset.trans Ici_subset_Ico_union_Ici (union_subset_union_left (Ici b) Ico_subset_Icc_self)

@[simp] theorem Icc_union_Ici_eq_Ici {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) : Icc a b ∪ Ici b = Ici a :=
  subset.antisymm (fun (x : α) (hx : x ∈ Icc a b ∪ Ici b) => or.elim hx and.left (le_trans h)) Ici_subset_Icc_union_Ici

theorem Icc_union_Ici' {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : c ≤ b) : Icc a b ∪ Ici c = Ici (min a c) := sorry

theorem Icc_union_Ici {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h : c ≤ max a b) : Icc a b ∪ Ici c = Ici (min a c) := sorry

/-! #### An infinite and a finite interval -/

theorem Iic_subset_Iio_union_Icc {α : Type u} [linear_order α] {a : α} {b : α} : Iic b ⊆ Iio a ∪ Icc a b :=
  fun (x : α) (hx : x ∈ Iic b) =>
    or.elim (lt_or_le x a) (fun (hxa : x < a) => Or.inl hxa) fun (hxa : a ≤ x) => Or.inr { left := hxa, right := hx }

@[simp] theorem Iio_union_Icc_eq_Iic {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) : Iio a ∪ Icc a b = Iic b :=
  subset.antisymm
    (fun (x : α) (hx : x ∈ Iio a ∪ Icc a b) => or.elim hx (fun (hx : x ∈ Iio a) => le_trans (le_of_lt hx) h) and.right)
    Iic_subset_Iio_union_Icc

theorem Iio_subset_Iio_union_Ico {α : Type u} [linear_order α] {a : α} {b : α} : Iio b ⊆ Iio a ∪ Ico a b :=
  fun (x : α) (hx : x ∈ Iio b) =>
    or.elim (lt_or_le x a) (fun (hxa : x < a) => Or.inl hxa) fun (hxa : a ≤ x) => Or.inr { left := hxa, right := hx }

@[simp] theorem Iio_union_Ico_eq_Iio {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) : Iio a ∪ Ico a b = Iio b :=
  subset.antisymm
    (fun (x : α) (hx : x ∈ Iio a ∪ Ico a b) => or.elim hx (fun (hx : x ∈ Iio a) => lt_of_lt_of_le hx h) and.right)
    Iio_subset_Iio_union_Ico

theorem Iio_union_Ico' {α : Type u} [linear_order α] {b : α} {c : α} {d : α} (h₁ : c ≤ b) : Iio b ∪ Ico c d = Iio (max b d) := sorry

theorem Iio_union_Ico {α : Type u} [linear_order α] {b : α} {c : α} {d : α} (h : min c d ≤ b) : Iio b ∪ Ico c d = Iio (max b d) := sorry

theorem Iic_subset_Iic_union_Ioc {α : Type u} [linear_order α] {a : α} {b : α} : Iic b ⊆ Iic a ∪ Ioc a b :=
  fun (x : α) (hx : x ∈ Iic b) =>
    or.elim (le_or_lt x a) (fun (hxa : x ≤ a) => Or.inl hxa) fun (hxa : a < x) => Or.inr { left := hxa, right := hx }

@[simp] theorem Iic_union_Ioc_eq_Iic {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) : Iic a ∪ Ioc a b = Iic b :=
  subset.antisymm (fun (x : α) (hx : x ∈ Iic a ∪ Ioc a b) => or.elim hx (fun (hx : x ∈ Iic a) => le_trans hx h) and.right)
    Iic_subset_Iic_union_Ioc

theorem Iic_union_Ioc' {α : Type u} [linear_order α] {b : α} {c : α} {d : α} (h₁ : c < b) : Iic b ∪ Ioc c d = Iic (max b d) := sorry

theorem Iic_union_Ioc {α : Type u} [linear_order α] {b : α} {c : α} {d : α} (h : min c d < b) : Iic b ∪ Ioc c d = Iic (max b d) := sorry

theorem Iio_subset_Iic_union_Ioo {α : Type u} [linear_order α] {a : α} {b : α} : Iio b ⊆ Iic a ∪ Ioo a b :=
  fun (x : α) (hx : x ∈ Iio b) =>
    or.elim (le_or_lt x a) (fun (hxa : x ≤ a) => Or.inl hxa) fun (hxa : a < x) => Or.inr { left := hxa, right := hx }

@[simp] theorem Iic_union_Ioo_eq_Iio {α : Type u} [linear_order α] {a : α} {b : α} (h : a < b) : Iic a ∪ Ioo a b = Iio b :=
  subset.antisymm
    (fun (x : α) (hx : x ∈ Iic a ∪ Ioo a b) => or.elim hx (fun (hx : x ∈ Iic a) => lt_of_le_of_lt hx h) and.right)
    Iio_subset_Iic_union_Ioo

theorem Iio_union_Ioo' {α : Type u} [linear_order α] {b : α} {c : α} {d : α} (h₁ : c < b) : Iio b ∪ Ioo c d = Iio (max b d) := sorry

theorem Iio_union_Ioo {α : Type u} [linear_order α] {b : α} {c : α} {d : α} (h : min c d < b) : Iio b ∪ Ioo c d = Iio (max b d) := sorry

theorem Iic_subset_Iic_union_Icc {α : Type u} [linear_order α] {a : α} {b : α} : Iic b ⊆ Iic a ∪ Icc a b :=
  subset.trans Iic_subset_Iic_union_Ioc (union_subset_union_right (Iic a) Ioc_subset_Icc_self)

@[simp] theorem Iic_union_Icc_eq_Iic {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) : Iic a ∪ Icc a b = Iic b :=
  subset.antisymm (fun (x : α) (hx : x ∈ Iic a ∪ Icc a b) => or.elim hx (fun (hx : x ∈ Iic a) => le_trans hx h) and.right)
    Iic_subset_Iic_union_Icc

theorem Iic_union_Icc' {α : Type u} [linear_order α] {b : α} {c : α} {d : α} (h₁ : c ≤ b) : Iic b ∪ Icc c d = Iic (max b d) := sorry

theorem Iic_union_Icc {α : Type u} [linear_order α] {b : α} {c : α} {d : α} (h : min c d ≤ b) : Iic b ∪ Icc c d = Iic (max b d) := sorry

theorem Iio_subset_Iic_union_Ico {α : Type u} [linear_order α] {a : α} {b : α} : Iio b ⊆ Iic a ∪ Ico a b :=
  subset.trans Iio_subset_Iic_union_Ioo (union_subset_union_right (Iic a) Ioo_subset_Ico_self)

@[simp] theorem Iic_union_Ico_eq_Iio {α : Type u} [linear_order α] {a : α} {b : α} (h : a < b) : Iic a ∪ Ico a b = Iio b :=
  subset.antisymm
    (fun (x : α) (hx : x ∈ Iic a ∪ Ico a b) => or.elim hx (fun (hx : x ∈ Iic a) => lt_of_le_of_lt hx h) and.right)
    Iio_subset_Iic_union_Ico

/-! #### Two finite intervals, `I?o` and `Ic?` -/

theorem Ioo_subset_Ioo_union_Ico {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ioo a c ⊆ Ioo a b ∪ Ico b c :=
  fun (x : α) (hx : x ∈ Ioo a c) =>
    or.elim (lt_or_le x b) (fun (hxb : x < b) => Or.inl { left := and.left hx, right := hxb })
      fun (hxb : b ≤ x) => Or.inr { left := hxb, right := and.right hx }

@[simp] theorem Ioo_union_Ico_eq_Ioo {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a < b) (h₂ : b ≤ c) : Ioo a b ∪ Ico b c = Ioo a c := sorry

theorem Ico_subset_Ico_union_Ico {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ico a c ⊆ Ico a b ∪ Ico b c :=
  fun (x : α) (hx : x ∈ Ico a c) =>
    or.elim (lt_or_le x b) (fun (hxb : x < b) => Or.inl { left := and.left hx, right := hxb })
      fun (hxb : b ≤ x) => Or.inr { left := hxb, right := and.right hx }

@[simp] theorem Ico_union_Ico_eq_Ico {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : Ico a b ∪ Ico b c = Ico a c := sorry

theorem Ico_union_Ico' {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} (h₁ : c ≤ b) (h₂ : a ≤ d) : Ico a b ∪ Ico c d = Ico (min a c) (max b d) := sorry

theorem Ico_union_Ico {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) : Ico a b ∪ Ico c d = Ico (min a c) (max b d) := sorry

theorem Icc_subset_Ico_union_Icc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Icc a c ⊆ Ico a b ∪ Icc b c :=
  fun (x : α) (hx : x ∈ Icc a c) =>
    or.elim (lt_or_le x b) (fun (hxb : x < b) => Or.inl { left := and.left hx, right := hxb })
      fun (hxb : b ≤ x) => Or.inr { left := hxb, right := and.right hx }

@[simp] theorem Ico_union_Icc_eq_Icc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : Ico a b ∪ Icc b c = Icc a c := sorry

theorem Ioc_subset_Ioo_union_Icc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ioc a c ⊆ Ioo a b ∪ Icc b c :=
  fun (x : α) (hx : x ∈ Ioc a c) =>
    or.elim (lt_or_le x b) (fun (hxb : x < b) => Or.inl { left := and.left hx, right := hxb })
      fun (hxb : b ≤ x) => Or.inr { left := hxb, right := and.right hx }

@[simp] theorem Ioo_union_Icc_eq_Ioc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a < b) (h₂ : b ≤ c) : Ioo a b ∪ Icc b c = Ioc a c := sorry

/-! #### Two finite intervals, `I?c` and `Io?` -/

theorem Ioo_subset_Ioc_union_Ioo {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ioo a c ⊆ Ioc a b ∪ Ioo b c :=
  fun (x : α) (hx : x ∈ Ioo a c) =>
    or.elim (le_or_lt x b) (fun (hxb : x ≤ b) => Or.inl { left := and.left hx, right := hxb })
      fun (hxb : b < x) => Or.inr { left := hxb, right := and.right hx }

@[simp] theorem Ioc_union_Ioo_eq_Ioo {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : b < c) : Ioc a b ∪ Ioo b c = Ioo a c := sorry

theorem Ico_subset_Icc_union_Ioo {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ico a c ⊆ Icc a b ∪ Ioo b c :=
  fun (x : α) (hx : x ∈ Ico a c) =>
    or.elim (le_or_lt x b) (fun (hxb : x ≤ b) => Or.inl { left := and.left hx, right := hxb })
      fun (hxb : b < x) => Or.inr { left := hxb, right := and.right hx }

@[simp] theorem Icc_union_Ioo_eq_Ico {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : b < c) : Icc a b ∪ Ioo b c = Ico a c := sorry

theorem Icc_subset_Icc_union_Ioc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Icc a c ⊆ Icc a b ∪ Ioc b c :=
  fun (x : α) (hx : x ∈ Icc a c) =>
    or.elim (le_or_lt x b) (fun (hxb : x ≤ b) => Or.inl { left := and.left hx, right := hxb })
      fun (hxb : b < x) => Or.inr { left := hxb, right := and.right hx }

@[simp] theorem Icc_union_Ioc_eq_Icc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : Icc a b ∪ Ioc b c = Icc a c := sorry

theorem Ioc_subset_Ioc_union_Ioc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ioc a c ⊆ Ioc a b ∪ Ioc b c :=
  fun (x : α) (hx : x ∈ Ioc a c) =>
    or.elim (le_or_lt x b) (fun (hxb : x ≤ b) => Or.inl { left := and.left hx, right := hxb })
      fun (hxb : b < x) => Or.inr { left := hxb, right := and.right hx }

@[simp] theorem Ioc_union_Ioc_eq_Ioc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : Ioc a b ∪ Ioc b c = Ioc a c := sorry

theorem Ioc_union_Ioc' {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} (h₁ : c ≤ b) (h₂ : a ≤ d) : Ioc a b ∪ Ioc c d = Ioc (min a c) (max b d) := sorry

theorem Ioc_union_Ioc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) : Ioc a b ∪ Ioc c d = Ioc (min a c) (max b d) := sorry

/-! #### Two finite intervals with a common point -/

theorem Ioo_subset_Ioc_union_Ico {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ioo a c ⊆ Ioc a b ∪ Ico b c :=
  subset.trans Ioo_subset_Ioc_union_Ioo (union_subset_union_right (Ioc a b) Ioo_subset_Ico_self)

@[simp] theorem Ioc_union_Ico_eq_Ioo {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a < b) (h₂ : b < c) : Ioc a b ∪ Ico b c = Ioo a c := sorry

theorem Ico_subset_Icc_union_Ico {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ico a c ⊆ Icc a b ∪ Ico b c :=
  subset.trans Ico_subset_Icc_union_Ioo (union_subset_union_right (Icc a b) Ioo_subset_Ico_self)

@[simp] theorem Icc_union_Ico_eq_Ico {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : b < c) : Icc a b ∪ Ico b c = Ico a c := sorry

theorem Icc_subset_Icc_union_Icc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Icc a c ⊆ Icc a b ∪ Icc b c :=
  subset.trans Icc_subset_Icc_union_Ioc (union_subset_union_right (Icc a b) Ioc_subset_Icc_self)

@[simp] theorem Icc_union_Icc_eq_Icc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : Icc a b ∪ Icc b c = Icc a c := sorry

theorem Icc_union_Icc' {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} (h₁ : c ≤ b) (h₂ : a ≤ d) : Icc a b ∪ Icc c d = Icc (min a c) (max b d) := sorry

/--
We cannot replace `<` by `≤` in the hypotheses.
Otherwise for `b < a = d < c` the l.h.s. is `∅` and the r.h.s. is `{a}`.
-/
theorem Icc_union_Icc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} (h₁ : min a b < max c d) (h₂ : min c d < max a b) : Icc a b ∪ Icc c d = Icc (min a c) (max b d) := sorry

theorem Ioc_subset_Ioc_union_Icc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ioc a c ⊆ Ioc a b ∪ Icc b c :=
  subset.trans Ioc_subset_Ioc_union_Ioc (union_subset_union_right (Ioc a b) Ioc_subset_Icc_self)

@[simp] theorem Ioc_union_Icc_eq_Ioc {α : Type u} [linear_order α] {a : α} {b : α} {c : α} (h₁ : a < b) (h₂ : b ≤ c) : Ioc a b ∪ Icc b c = Ioc a c := sorry

theorem Ioo_union_Ioo' {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} (h₁ : c < b) (h₂ : a < d) : Ioo a b ∪ Ioo c d = Ioo (min a c) (max b d) := sorry

theorem Ioo_union_Ioo {α : Type u} [linear_order α] {a : α} {b : α} {c : α} {d : α} (h₁ : min a b < max c d) (h₂ : min c d < max a b) : Ioo a b ∪ Ioo c d = Ioo (min a c) (max b d) := sorry

@[simp] theorem Iic_inter_Iic {α : Type u} [semilattice_inf α] {a : α} {b : α} : Iic a ∩ Iic b = Iic (a ⊓ b) := sorry

@[simp] theorem Iio_inter_Iio {α : Type u} [semilattice_inf α] [is_total α LessEq] {a : α} {b : α} : Iio a ∩ Iio b = Iio (a ⊓ b) := sorry

@[simp] theorem Ici_inter_Ici {α : Type u} [semilattice_sup α] {a : α} {b : α} : Ici a ∩ Ici b = Ici (a ⊔ b) := sorry

@[simp] theorem Ioi_inter_Ioi {α : Type u} [semilattice_sup α] [is_total α LessEq] {a : α} {b : α} : Ioi a ∩ Ioi b = Ioi (a ⊔ b) := sorry

theorem Icc_inter_Icc {α : Type u} [lattice α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} : Icc a₁ b₁ ∩ Icc a₂ b₂ = Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂) := sorry

@[simp] theorem Icc_inter_Icc_eq_singleton {α : Type u} [lattice α] {a : α} {b : α} {c : α} (hab : a ≤ b) (hbc : b ≤ c) : Icc a b ∩ Icc b c = singleton b := sorry

theorem Ico_inter_Ico {α : Type u} [lattice α] [ht : is_total α LessEq] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} : Ico a₁ b₁ ∩ Ico a₂ b₂ = Ico (a₁ ⊔ a₂) (b₁ ⊓ b₂) := sorry

theorem Ioc_inter_Ioc {α : Type u} [lattice α] [ht : is_total α LessEq] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} : Ioc a₁ b₁ ∩ Ioc a₂ b₂ = Ioc (a₁ ⊔ a₂) (b₁ ⊓ b₂) := sorry

theorem Ioo_inter_Ioo {α : Type u} [lattice α] [ht : is_total α LessEq] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} : Ioo a₁ b₁ ∩ Ioo a₂ b₂ = Ioo (a₁ ⊔ a₂) (b₁ ⊓ b₂) := sorry

theorem Ioc_inter_Ioo_of_left_lt {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h : b₁ < b₂) : Ioc a₁ b₁ ∩ Ioo a₂ b₂ = Ioc (max a₁ a₂) b₁ := sorry

theorem Ioc_inter_Ioo_of_right_le {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h : b₂ ≤ b₁) : Ioc a₁ b₁ ∩ Ioo a₂ b₂ = Ioo (max a₁ a₂) b₂ := sorry

theorem Ioo_inter_Ioc_of_left_le {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h : b₁ ≤ b₂) : Ioo a₁ b₁ ∩ Ioc a₂ b₂ = Ioo (max a₁ a₂) b₁ := sorry

theorem Ioo_inter_Ioc_of_right_lt {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α} (h : b₂ < b₁) : Ioo a₁ b₁ ∩ Ioc a₂ b₂ = Ioc (max a₁ a₂) b₂ := sorry

@[simp] theorem Ico_diff_Iio {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ico a b \ Iio c = Ico (max a c) b := sorry

@[simp] theorem Ico_inter_Iio {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ico a b ∩ Iio c = Ico a (min b c) := sorry

@[simp] theorem Ioc_union_Ioc_right {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ioc a b ∪ Ioc a c = Ioc a (max b c) := sorry

@[simp] theorem Ioc_union_Ioc_left {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ioc a c ∪ Ioc b c = Ioc (min a b) c := sorry

@[simp] theorem Ioc_union_Ioc_symm {α : Type u} [linear_order α] {a : α} {b : α} : Ioc a b ∪ Ioc b a = Ioc (min a b) (max a b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Ioc a b ∪ Ioc b a = Ioc (min a b) (max a b))) (max_comm a b)))
    (Ioc_union_Ioc (eq.mpr (id (Eq._oldrec (Eq.refl (min a b ≤ max b a)) (max_comm b a))) min_le_max)
      (eq.mpr (id (Eq._oldrec (Eq.refl (min b a ≤ max a b)) (max_comm a b))) min_le_max))

@[simp] theorem Ioc_union_Ioc_union_Ioc_cycle {α : Type u} [linear_order α] {a : α} {b : α} {c : α} : Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc (min a (min b c)) (max a (max b c)) := sorry

/-- If we remove a smaller interval from a larger, the result is nonempty -/
theorem nonempty_Ico_sdiff {α : Type u} [linear_ordered_add_comm_group α] {x : α} {dx : α} {y : α} {dy : α} (h : dy < dx) (hx : 0 < dx) : Nonempty ↥(Ico x (x + dx) \ Ico y (y + dy)) := sorry

