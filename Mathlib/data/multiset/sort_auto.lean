/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.sort
import Mathlib.data.multiset.basic
import Mathlib.data.string.basic
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Construct a sorted list from a multiset.
-/

namespace multiset


/-- `sort s` constructs a sorted list from the multiset `s`.
  (Uses merge sort algorithm.) -/
def sort {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r] [is_antisymm α r]
    [is_total α r] (s : multiset α) : List α :=
  quot.lift_on s (list.merge_sort r) sorry

@[simp] theorem coe_sort {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r]
    [is_antisymm α r] [is_total α r] (l : List α) : sort r ↑l = list.merge_sort r l :=
  rfl

@[simp] theorem sort_sorted {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r]
    [is_antisymm α r] [is_total α r] (s : multiset α) : list.sorted r (sort r s) :=
  quot.induction_on s fun (l : List α) => list.sorted_merge_sort r l

@[simp] theorem sort_eq {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r]
    [is_antisymm α r] [is_total α r] (s : multiset α) : ↑(sort r s) = s :=
  quot.induction_on s fun (l : List α) => quot.sound (list.perm_merge_sort r l)

@[simp] theorem mem_sort {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r]
    [is_antisymm α r] [is_total α r] {s : multiset α} {a : α} : a ∈ sort r s ↔ a ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ sort r s ↔ a ∈ s)) (Eq.symm (propext mem_coe))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ ↑(sort r s) ↔ a ∈ s)) (sort_eq r s))) (iff.refl (a ∈ s)))

@[simp] theorem length_sort {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r]
    [is_antisymm α r] [is_total α r] {s : multiset α} : list.length (sort r s) = coe_fn card s :=
  quot.induction_on s (list.length_merge_sort r)

protected instance has_repr {α : Type u_1} [has_repr α] : has_repr (multiset α) :=
  has_repr.mk
    fun (s : multiset α) =>
      string.str string.empty (char.of_nat (bit1 (bit1 (bit0 (bit1 (bit1 (bit1 1))))))) ++
          string.intercalate
            (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit0 1)))))))
              (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
            (sort LessEq (map repr s)) ++
        string.str string.empty (char.of_nat (bit1 (bit0 (bit1 (bit1 (bit1 (bit1 1)))))))

end Mathlib