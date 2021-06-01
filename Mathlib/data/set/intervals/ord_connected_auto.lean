/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.intervals.unordered_interval
import Mathlib.data.set.lattice
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Order-connected sets

We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α = ℝ`, then
this condition is also equivalent to `convex s`.

In this file we prove that intersection of a family of `ord_connected` sets is `ord_connected` and
that all standard intervals are `ord_connected`.
-/

namespace set


/--
We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α = ℝ`, then
this condition is also equivalent to `convex s`.
-/
def ord_connected {α : Type u_1} [preorder α] (s : set α) :=
  ∀ {x : α}, x ∈ s → ∀ {y : α}, y ∈ s → Icc x y ⊆ s

/-- It suffices to prove `[x, y] ⊆ s` for `x y ∈ s`, `x ≤ y`. -/
theorem ord_connected_iff {α : Type u_1} [preorder α] {s : set α} :
    ord_connected s ↔ ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → x ≤ y → Icc x y ⊆ s :=
  sorry

theorem ord_connected_of_Ioo {α : Type u_1} [partial_order α] {s : set α}
    (hs : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → x < y → Ioo x y ⊆ s) : ord_connected s :=
  sorry

protected theorem Icc_subset {α : Type u_1} [preorder α] (s : set α) [hs : ord_connected s] {x : α}
    {y : α} (hx : x ∈ s) (hy : y ∈ s) : Icc x y ⊆ s :=
  hs hx hy

theorem ord_connected.inter {α : Type u_1} [preorder α] {s : set α} {t : set α}
    (hs : ord_connected s) (ht : ord_connected t) : ord_connected (s ∩ t) :=
  fun (x : α) (hx : x ∈ s ∩ t) (y : α) (hy : y ∈ s ∩ t) =>
    subset_inter (hs (and.left hx) (and.left hy)) (ht (and.right hx) (and.right hy))

protected instance ord_connected.inter' {α : Type u_1} [preorder α] {s : set α} {t : set α}
    [ord_connected s] [ord_connected t] : ord_connected (s ∩ t) :=
  ord_connected.inter _inst_2 _inst_3

theorem ord_connected.dual {α : Type u_1} [preorder α] {s : set α} (hs : ord_connected s) :
    ord_connected s :=
  fun (x : order_dual α) (hx : x ∈ s) (y : order_dual α) (hy : y ∈ s) (z : order_dual α)
    (hz : z ∈ Icc x y) => hs hy hx { left := and.right hz, right := and.left hz }

theorem ord_connected_dual {α : Type u_1} [preorder α] {s : set α} :
    ord_connected s ↔ ord_connected s :=
  { mp := fun (h : ord_connected s) => ord_connected.dual h,
    mpr := fun (h : ord_connected s) => ord_connected.dual h }

theorem ord_connected_sInter {α : Type u_1} [preorder α] {S : set (set α)}
    (hS : ∀ (s : set α), s ∈ S → ord_connected s) : ord_connected (⋂₀S) :=
  fun (x : α) (hx : x ∈ ⋂₀S) (y : α) (hy : y ∈ ⋂₀S) =>
    subset_sInter fun (s : set α) (hs : s ∈ S) => hS s hs (hx s hs) (hy s hs)

theorem ord_connected_Inter {α : Type u_1} [preorder α] {ι : Sort u_2} {s : ι → set α}
    (hs : ∀ (i : ι), ord_connected (s i)) : ord_connected (Inter fun (i : ι) => s i) :=
  ord_connected_sInter (iff.mpr forall_range_iff hs)

protected instance ord_connected_Inter' {α : Type u_1} [preorder α] {ι : Sort u_2} {s : ι → set α}
    [∀ (i : ι), ord_connected (s i)] : ord_connected (Inter fun (i : ι) => s i) :=
  ord_connected_Inter _inst_2

theorem ord_connected_bInter {α : Type u_1} [preorder α] {ι : Sort u_2} {p : ι → Prop}
    {s : (i : ι) → p i → set α} (hs : ∀ (i : ι) (hi : p i), ord_connected (s i hi)) :
    ord_connected (Inter fun (i : ι) => Inter fun (hi : p i) => s i hi) :=
  ord_connected_Inter fun (i : ι) => ord_connected_Inter (hs i)

theorem ord_connected_pi {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)] {s : set ι}
    {t : (i : ι) → set (α i)} (h : ∀ (i : ι), i ∈ s → ord_connected (t i)) :
    ord_connected (pi s t) :=
  fun (x : (i : ι) → α i) (hx : x ∈ pi s t) (y : (i : ι) → α i) (hy : y ∈ pi s t)
    (z : (i : ι) → α i) (hz : z ∈ Icc x y) (i : ι) (hi : i ∈ s) =>
    h i hi (hx i hi) (hy i hi) { left := and.left hz i, right := and.right hz i }

protected instance ord_connected_pi' {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → preorder (α i)]
    {s : set ι} {t : (i : ι) → set (α i)} [h : ∀ (i : ι), ord_connected (t i)] :
    ord_connected (pi s t) :=
  ord_connected_pi fun (i : ι) (hi : i ∈ s) => h i

instance ord_connected_Ici {α : Type u_1} [preorder α] {a : α} : ord_connected (Ici a) :=
  fun (x : α) (hx : x ∈ Ici a) (y : α) (hy : y ∈ Ici a) (z : α) (hz : z ∈ Icc x y) =>
    le_trans hx (and.left hz)

instance ord_connected_Iic {α : Type u_1} [preorder α] {a : α} : ord_connected (Iic a) :=
  fun (x : α) (hx : x ∈ Iic a) (y : α) (hy : y ∈ Iic a) (z : α) (hz : z ∈ Icc x y) =>
    le_trans (and.right hz) hy

instance ord_connected_Ioi {α : Type u_1} [preorder α] {a : α} : ord_connected (Ioi a) :=
  fun (x : α) (hx : x ∈ Ioi a) (y : α) (hy : y ∈ Ioi a) (z : α) (hz : z ∈ Icc x y) =>
    lt_of_lt_of_le hx (and.left hz)

instance ord_connected_Iio {α : Type u_1} [preorder α] {a : α} : ord_connected (Iio a) :=
  fun (x : α) (hx : x ∈ Iio a) (y : α) (hy : y ∈ Iio a) (z : α) (hz : z ∈ Icc x y) =>
    lt_of_le_of_lt (and.right hz) hy

instance ord_connected_Icc {α : Type u_1} [preorder α] {a : α} {b : α} : ord_connected (Icc a b) :=
  ord_connected.inter ord_connected_Ici ord_connected_Iic

instance ord_connected_Ico {α : Type u_1} [preorder α] {a : α} {b : α} : ord_connected (Ico a b) :=
  ord_connected.inter ord_connected_Ici ord_connected_Iio

instance ord_connected_Ioc {α : Type u_1} [preorder α] {a : α} {b : α} : ord_connected (Ioc a b) :=
  ord_connected.inter ord_connected_Ioi ord_connected_Iic

instance ord_connected_Ioo {α : Type u_1} [preorder α] {a : α} {b : α} : ord_connected (Ioo a b) :=
  ord_connected.inter ord_connected_Ioi ord_connected_Iio

instance ord_connected_singleton {α : Type u_1} [partial_order α] {a : α} :
    ord_connected (singleton a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ord_connected (singleton a))) (Eq.symm (Icc_self a))))
    ord_connected_Icc

instance ord_connected_empty {α : Type u_1} [preorder α] : ord_connected ∅ :=
  fun (x : α) => false.elim

instance ord_connected_univ {α : Type u_1} [preorder α] : ord_connected univ :=
  fun (_x : α) (_x_1 : _x ∈ univ) (_x_2 : α) (_x_3 : _x_2 ∈ univ) => subset_univ (Icc _x _x_2)

/-- In a dense order `α`, the subtype from an `ord_connected` set is also densely ordered. -/
protected instance densely_ordered {α : Type u_1} [preorder α] [densely_ordered α] {s : set α}
    [hs : ord_connected s] : densely_ordered ↥s :=
  densely_ordered.mk
    fun (a₁ a₂ : ↥s) (ha : a₁ < a₂) =>
      Exists.dcases_on (exists_between ha)
        fun (x : α) (h : ↑a₁ < x ∧ x < ↑a₂) =>
          and.dcases_on h
            fun (ha₁x : ↑a₁ < x) (hxa₂ : x < ↑a₂) =>
              Exists.intro
                { val := x,
                  property :=
                    hs (subtype.property a₁) (subtype.property a₂)
                      (Ioo_subset_Icc_self { left := ha₁x, right := hxa₂ }) }
                { left := ha₁x, right := hxa₂ }

instance ord_connected_interval {β : Type u_2} [linear_order β] {a : β} {b : β} :
    ord_connected (interval a b) :=
  ord_connected_Icc

theorem ord_connected.interval_subset {β : Type u_2} [linear_order β] {s : set β}
    (hs : ord_connected s) {x : β} (hx : x ∈ s) {y : β} (hy : y ∈ s) : interval x y ⊆ s :=
  sorry

theorem ord_connected_iff_interval_subset {β : Type u_2} [linear_order β] {s : set β} :
    ord_connected s ↔ ∀ {x : β}, x ∈ s → ∀ {y : β}, y ∈ s → interval x y ⊆ s :=
  sorry

end Mathlib