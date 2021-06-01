/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.bounds
import Mathlib.data.set.intervals.image_preimage
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Intervals without endpoints ordering

In any decidable linear order `α`, we define the set of elements lying between two elements `a` and
`b` as `Icc (min a b) (max a b)`.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. The
interval as defined in this file is always the set of things lying between `a` and `b`, regardless
of the relative order of `a` and `b`.

For real numbers, `Icc (min a b) (max a b)` is the same as `segment a b`.

## Notation

We use the localized notation `[a, b]` for `interval a b`. One can open the locale `interval` to
make the notation available.

-/

namespace set


/-- `interval a b` is the set of elements lying between `a` and `b`, with `a` and `b` included. -/
def interval {α : Type u} [linear_order α] (a : α) (b : α) : set α := Icc (min a b) (max a b)

@[simp] theorem interval_of_le {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) :
    interval a b = Icc a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (interval a b = Icc a b)) (interval.equations._eqn_1 a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Icc (min a b) (max a b) = Icc a b)) (min_eq_left h)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (Icc a (max a b) = Icc a b)) (max_eq_right h)))
        (Eq.refl (Icc a b))))

@[simp] theorem interval_of_ge {α : Type u} [linear_order α] {a : α} {b : α} (h : b ≤ a) :
    interval a b = Icc b a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (interval a b = Icc b a)) (interval.equations._eqn_1 a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Icc (min a b) (max a b) = Icc b a)) (min_eq_right h)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (Icc b (max a b) = Icc b a)) (max_eq_left h)))
        (Eq.refl (Icc b a))))

theorem interval_swap {α : Type u} [linear_order α] (a : α) (b : α) : interval a b = interval b a :=
  sorry

theorem interval_of_lt {α : Type u} [linear_order α] {a : α} {b : α} (h : a < b) :
    interval a b = Icc a b :=
  interval_of_le (le_of_lt h)

theorem interval_of_gt {α : Type u} [linear_order α] {a : α} {b : α} (h : b < a) :
    interval a b = Icc b a :=
  interval_of_ge (le_of_lt h)

theorem interval_of_not_le {α : Type u} [linear_order α] {a : α} {b : α} (h : ¬a ≤ b) :
    interval a b = Icc b a :=
  interval_of_gt (lt_of_not_ge h)

theorem interval_of_not_ge {α : Type u} [linear_order α] {a : α} {b : α} (h : ¬b ≤ a) :
    interval a b = Icc a b :=
  interval_of_lt (lt_of_not_ge h)

@[simp] theorem interval_self {α : Type u} [linear_order α] {a : α} : interval a a = singleton a :=
  sorry

@[simp] theorem nonempty_interval {α : Type u} [linear_order α] {a : α} {b : α} :
    set.nonempty (interval a b) :=
  sorry

@[simp] theorem left_mem_interval {α : Type u} [linear_order α] {a : α} {b : α} :
    a ∈ interval a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ interval a b)) (interval.equations._eqn_1 a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ Icc (min a b) (max a b))) (propext mem_Icc)))
      { left := min_le_left a b, right := le_max_left a b })

@[simp] theorem right_mem_interval {α : Type u} [linear_order α] {a : α} {b : α} :
    b ∈ interval a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b ∈ interval a b)) (interval_swap a b))) left_mem_interval

theorem Icc_subset_interval {α : Type u} [linear_order α] {a : α} {b : α} :
    Icc a b ⊆ interval a b :=
  id
    fun (x : α) (h : x ∈ Icc a b) =>
      eq.mpr
        (id
          (Eq._oldrec (Eq.refl (x ∈ interval a b))
            (interval_of_le (le_trans (and.left h) (and.right h)))))
        h

theorem Icc_subset_interval' {α : Type u} [linear_order α] {a : α} {b : α} :
    Icc b a ⊆ interval a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Icc b a ⊆ interval a b)) (interval_swap a b)))
    Icc_subset_interval

theorem mem_interval_of_le {α : Type u} [linear_order α] {a : α} {b : α} {x : α} (ha : a ≤ x)
    (hb : x ≤ b) : x ∈ interval a b :=
  Icc_subset_interval { left := ha, right := hb }

theorem mem_interval_of_ge {α : Type u} [linear_order α] {a : α} {b : α} {x : α} (hb : b ≤ x)
    (ha : x ≤ a) : x ∈ interval a b :=
  Icc_subset_interval' { left := hb, right := ha }

theorem interval_subset_interval {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}
    (h₁ : a₁ ∈ interval a₂ b₂) (h₂ : b₁ ∈ interval a₂ b₂) : interval a₁ b₁ ⊆ interval a₂ b₂ :=
  Icc_subset_Icc (le_min (and.left h₁) (and.left h₂)) (max_le (and.right h₁) (and.right h₂))

theorem interval_subset_interval_iff_mem {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α}
    {b₂ : α} : interval a₁ b₁ ⊆ interval a₂ b₂ ↔ a₁ ∈ interval a₂ b₂ ∧ b₁ ∈ interval a₂ b₂ :=
  { mp :=
      fun (h : interval a₁ b₁ ⊆ interval a₂ b₂) =>
        { left := h left_mem_interval, right := h right_mem_interval },
    mpr :=
      fun (h : a₁ ∈ interval a₂ b₂ ∧ b₁ ∈ interval a₂ b₂) =>
        interval_subset_interval (and.left h) (and.right h) }

theorem interval_subset_interval_iff_le {α : Type u} [linear_order α] {a₁ : α} {a₂ : α} {b₁ : α}
    {b₂ : α} : interval a₁ b₁ ⊆ interval a₂ b₂ ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
  sorry

theorem interval_subset_interval_right {α : Type u} [linear_order α] {a : α} {b : α} {x : α}
    (h : x ∈ interval a b) : interval x b ⊆ interval a b :=
  interval_subset_interval h right_mem_interval

theorem interval_subset_interval_left {α : Type u} [linear_order α] {a : α} {b : α} {x : α}
    (h : x ∈ interval a b) : interval a x ⊆ interval a b :=
  interval_subset_interval left_mem_interval h

theorem bdd_below_bdd_above_iff_subset_interval {α : Type u} [linear_order α] (s : set α) :
    bdd_below s ∧ bdd_above s ↔ ∃ (a : α), ∃ (b : α), s ⊆ interval a b :=
  sorry

@[simp] theorem preimage_const_add_interval {α : Type u} [linear_ordered_add_comm_group α] (a : α)
    (b : α) (c : α) : (fun (x : α) => a + x) ⁻¹' interval b c = interval (b - a) (c - a) :=
  sorry

@[simp] theorem preimage_add_const_interval {α : Type u} [linear_ordered_add_comm_group α] (a : α)
    (b : α) (c : α) : (fun (x : α) => x + a) ⁻¹' interval b c = interval (b - a) (c - a) :=
  sorry

@[simp] theorem preimage_neg_interval {α : Type u} [linear_ordered_add_comm_group α] (a : α)
    (b : α) : -interval a b = interval (-a) (-b) :=
  sorry

@[simp] theorem preimage_sub_const_interval {α : Type u} [linear_ordered_add_comm_group α] (a : α)
    (b : α) (c : α) : (fun (x : α) => x - a) ⁻¹' interval b c = interval (b + a) (c + a) :=
  sorry

@[simp] theorem preimage_const_sub_interval {α : Type u} [linear_ordered_add_comm_group α] (a : α)
    (b : α) (c : α) : (fun (x : α) => a - x) ⁻¹' interval b c = interval (a - b) (a - c) :=
  sorry

@[simp] theorem image_const_add_interval {α : Type u} [linear_ordered_add_comm_group α] (a : α)
    (b : α) (c : α) : (fun (x : α) => a + x) '' interval b c = interval (a + b) (a + c) :=
  sorry

@[simp] theorem image_add_const_interval {α : Type u} [linear_ordered_add_comm_group α] (a : α)
    (b : α) (c : α) : (fun (x : α) => x + a) '' interval b c = interval (b + a) (c + a) :=
  sorry

@[simp] theorem image_const_sub_interval {α : Type u} [linear_ordered_add_comm_group α] (a : α)
    (b : α) (c : α) : (fun (x : α) => a - x) '' interval b c = interval (a - b) (a - c) :=
  sorry

@[simp] theorem image_sub_const_interval {α : Type u} [linear_ordered_add_comm_group α] (a : α)
    (b : α) (c : α) : (fun (x : α) => x - a) '' interval b c = interval (b - a) (c - a) :=
  sorry

theorem image_neg_interval {α : Type u} [linear_ordered_add_comm_group α] (a : α) (b : α) :
    Neg.neg '' interval a b = interval (-a) (-b) :=
  sorry

/-- If `[x, y]` is a subinterval of `[a, b]`, then the distance between `x` and `y`
is less than or equal to that of `a` and `b` -/
theorem abs_sub_le_of_subinterval {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α}
    {x : α} {y : α} (h : interval x y ⊆ interval a b) : abs (y - x) ≤ abs (b - a) :=
  sorry

/-- If `x ∈ [a, b]`, then the distance between `a` and `x` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_left_of_mem_interval {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α}
    {x : α} (h : x ∈ interval a b) : abs (x - a) ≤ abs (b - a) :=
  abs_sub_le_of_subinterval (interval_subset_interval_left h)

/-- If `x ∈ [a, b]`, then the distance between `x` and `b` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_right_of_mem_interval {α : Type u} [linear_ordered_add_comm_group α] {a : α} {b : α}
    {x : α} (h : x ∈ interval a b) : abs (b - x) ≤ abs (b - a) :=
  abs_sub_le_of_subinterval (interval_subset_interval_right h)

@[simp] theorem preimage_mul_const_interval {k : Type u} [linear_ordered_field k] {a : k}
    (ha : a ≠ 0) (b : k) (c : k) :
    (fun (x : k) => x * a) ⁻¹' interval b c = interval (b / a) (c / a) :=
  sorry

@[simp] theorem preimage_const_mul_interval {k : Type u} [linear_ordered_field k] {a : k}
    (ha : a ≠ 0) (b : k) (c : k) :
    (fun (x : k) => a * x) ⁻¹' interval b c = interval (b / a) (c / a) :=
  sorry

@[simp] theorem preimage_div_const_interval {k : Type u} [linear_ordered_field k] {a : k}
    (ha : a ≠ 0) (b : k) (c : k) :
    (fun (x : k) => x / a) ⁻¹' interval b c = interval (b * a) (c * a) :=
  sorry

@[simp] theorem image_mul_const_interval {k : Type u} [linear_ordered_field k] (a : k) (b : k)
    (c : k) : (fun (x : k) => x * a) '' interval b c = interval (b * a) (c * a) :=
  sorry

@[simp] theorem image_const_mul_interval {k : Type u} [linear_ordered_field k] (a : k) (b : k)
    (c : k) : (fun (x : k) => a * x) '' interval b c = interval (a * b) (a * c) :=
  sorry

@[simp] theorem image_div_const_interval {k : Type u} [linear_ordered_field k] (a : k) (b : k)
    (c : k) : (fun (x : k) => x / a) '' interval b c = interval (b / a) (c / a) :=
  image_mul_const_interval (a⁻¹) b c

end Mathlib