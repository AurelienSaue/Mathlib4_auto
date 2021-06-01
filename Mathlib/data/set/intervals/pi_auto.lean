/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.intervals.basic
import Mathlib.data.set.lattice
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Intervals in `pi`-space

In this we prove various simple lemmas about intervals in `Π i, α i`. Closed intervals (`Ici x`,
`Iic x`, `Icc x y`) are equal to products of their projections to `α i`, while (semi-)open intervals
usually include the corresponding products as proper subsets.
-/

namespace set


@[simp] theorem pi_univ_Ici {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)]
    (x : (i : ι) → α i) : (pi univ fun (i : ι) => Ici (x i)) = Ici x :=
  sorry

@[simp] theorem pi_univ_Iic {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)]
    (x : (i : ι) → α i) : (pi univ fun (i : ι) => Iic (x i)) = Iic x :=
  sorry

@[simp] theorem pi_univ_Icc {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)]
    (x : (i : ι) → α i) (y : (i : ι) → α i) : (pi univ fun (i : ι) => Icc (x i) (y i)) = Icc x y :=
  sorry

theorem pi_univ_Ioi_subset {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)]
    (x : (i : ι) → α i) [Nonempty ι] : (pi univ fun (i : ι) => Ioi (x i)) ⊆ Ioi x :=
  sorry

theorem pi_univ_Iio_subset {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)]
    (x : (i : ι) → α i) [Nonempty ι] : (pi univ fun (i : ι) => Iio (x i)) ⊆ Iio x :=
  pi_univ_Ioi_subset x

theorem pi_univ_Ioo_subset {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)]
    (x : (i : ι) → α i) (y : (i : ι) → α i) [Nonempty ι] :
    (pi univ fun (i : ι) => Ioo (x i) (y i)) ⊆ Ioo x y :=
  fun (x_1 : (i : ι) → α i) (hx : x_1 ∈ pi univ fun (i : ι) => Ioo (x i) (y i)) =>
    { left :=
        pi_univ_Ioi_subset (fun (i : ι) => x i) fun (i : ι) (hi : i ∈ univ) => and.left (hx i hi),
      right :=
        pi_univ_Iio_subset (fun (i : ι) => y i) fun (i : ι) (hi : i ∈ univ) => and.right (hx i hi) }

theorem pi_univ_Ioc_subset {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)]
    (x : (i : ι) → α i) (y : (i : ι) → α i) [Nonempty ι] :
    (pi univ fun (i : ι) => Ioc (x i) (y i)) ⊆ Ioc x y :=
  fun (x_1 : (i : ι) → α i) (hx : x_1 ∈ pi univ fun (i : ι) => Ioc (x i) (y i)) =>
    { left :=
        pi_univ_Ioi_subset (fun (i : ι) => x i) fun (i : ι) (hi : i ∈ univ) => and.left (hx i hi),
      right := fun (i : ι) => and.right (hx i trivial) }

theorem pi_univ_Ico_subset {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)]
    (x : (i : ι) → α i) (y : (i : ι) → α i) [Nonempty ι] :
    (pi univ fun (i : ι) => Ico (x i) (y i)) ⊆ Ico x y :=
  fun (x_1 : (i : ι) → α i) (hx : x_1 ∈ pi univ fun (i : ι) => Ico (x i) (y i)) =>
    { left := fun (i : ι) => and.left (hx i trivial),
      right :=
        pi_univ_Iio_subset (fun (i : ι) => y i) fun (i : ι) (hi : i ∈ univ) => and.right (hx i hi) }

theorem pi_univ_Ioc_update_left {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)]
    [DecidableEq ι] {x : (i : ι) → α i} {y : (i : ι) → α i} {i₀ : ι} {m : α i₀} (hm : x i₀ ≤ m) :
    (pi univ fun (i : ι) => Ioc (function.update x i₀ m i) (y i)) =
        (set_of fun (z : (i : ι) → α i) => m < z i₀) ∩ pi univ fun (i : ι) => Ioc (x i) (y i) :=
  sorry

theorem pi_univ_Ioc_update_right {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)]
    [DecidableEq ι] {x : (i : ι) → α i} {y : (i : ι) → α i} {i₀ : ι} {m : α i₀} (hm : m ≤ y i₀) :
    (pi univ fun (i : ι) => Ioc (x i) (function.update y i₀ m i)) =
        (set_of fun (z : (i : ι) → α i) => z i₀ ≤ m) ∩ pi univ fun (i : ι) => Ioc (x i) (y i) :=
  sorry

theorem disjoint_pi_univ_Ioc_update_left_right {ι : Type u_1} {α : ι → Type u_2}
    [(i : ι) → preorder (α i)] [DecidableEq ι] {x : (i : ι) → α i} {y : (i : ι) → α i} {i₀ : ι}
    {m : α i₀} :
    disjoint (pi univ fun (i : ι) => Ioc (x i) (function.update y i₀ m i))
        (pi univ fun (i : ι) => Ioc (function.update x i₀ m i) (y i)) :=
  sorry

theorem pi_univ_Ioc_update_union {ι : Type u_1} {α : ι → Type u_2} [DecidableEq ι]
    [(i : ι) → linear_order (α i)] (x : (i : ι) → α i) (y : (i : ι) → α i) (i₀ : ι) (m : α i₀)
    (hm : m ∈ Icc (x i₀) (y i₀)) :
    ((pi univ fun (i : ι) => Ioc (x i) (function.update y i₀ m i)) ∪
          pi univ fun (i : ι) => Ioc (function.update x i₀ m i) (y i)) =
        pi univ fun (i : ι) => Ioc (x i) (y i) :=
  sorry

/-- If `x`, `y`, `x'`, and `y'` are functions `Π i : ι, α i`, then
the set difference between the box `[x, y]` and the product of the open intervals `(x' i, y' i)`
is covered by the union of the following boxes: for each `i : ι`, we take
`[x, update y i (x' i)]` and `[update x i (y' i), y]`.

E.g., if `x' = x` and `y' = y`, then this lemma states that the difference between a closed box
`[x, y]` and the corresponding open box `{z | ∀ i, x i < z i < y i}` is covered by the union
of the faces of `[x, y]`. -/
theorem Icc_diff_pi_univ_Ioo_subset {ι : Type u_1} {α : ι → Type u_2} [DecidableEq ι]
    [(i : ι) → linear_order (α i)] (x : (i : ι) → α i) (y : (i : ι) → α i) (x' : (i : ι) → α i)
    (y' : (i : ι) → α i) :
    (Icc x y \ pi univ fun (i : ι) => Ioo (x' i) (y' i)) ⊆
        (Union fun (i : ι) => Icc x (function.update y i (x' i))) ∪
          Union fun (i : ι) => Icc (function.update x i (y' i)) y :=
  sorry

/-- If `x`, `y`, `z` are functions `Π i : ι, α i`, then
the set difference between the box `[x, z]` and the product of the intervals `(y i, z i]`
is covered by the union of the boxes `[x, update z i (y i)]`.

E.g., if `x = y`, then this lemma states that the difference between a closed box
`[x, y]` and the product of half-open intervals `{z | ∀ i, x i < z i ≤ y i}` is covered by the union
of the faces of `[x, y]` adjacent to `x`. -/
theorem Icc_diff_pi_univ_Ioc_subset {ι : Type u_1} {α : ι → Type u_2} [DecidableEq ι]
    [(i : ι) → linear_order (α i)] (x : (i : ι) → α i) (y : (i : ι) → α i) (z : (i : ι) → α i) :
    (Icc x z \ pi univ fun (i : ι) => Ioc (y i) (z i)) ⊆
        Union fun (i : ι) => Icc x (function.update z i (y i)) :=
  sorry

end Mathlib