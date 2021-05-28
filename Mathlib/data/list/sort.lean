/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.perm
import Mathlib.data.list.chain
import Mathlib.PostPort

universes u_1 uu 

namespace Mathlib

/-!
# Sorting algorithms on lists

In this file we define `list.sorted r l` to be an alias for `pairwise r l`. This alias is preferred
in the case that `r` is a `<` or `≤`-like relation. Then we define two sorting algorithms:
`list.insertion_sort` and `list.merge_sort`, and prove their correctness.
-/

namespace list


/-!
### The predicate `list.sorted`
-/

/-- `sorted r l` is the same as `pairwise r l`, preferred in the case that `r`
  is a `<` or `≤`-like relation (transitive and antisymmetric or asymmetric) -/
def sorted {α : Type u_1} (R : α → α → Prop) : List α → Prop :=
  pairwise

protected instance decidable_sorted {α : Type uu} {r : α → α → Prop} [DecidableRel r] (l : List α) : Decidable (sorted r l) :=
  list.decidable_pairwise l

@[simp] theorem sorted_nil {α : Type uu} {r : α → α → Prop} : sorted r [] :=
  pairwise.nil

theorem sorted_of_sorted_cons {α : Type uu} {r : α → α → Prop} {a : α} {l : List α} : sorted r (a :: l) → sorted r l :=
  pairwise_of_pairwise_cons

theorem sorted.tail {α : Type uu} {r : α → α → Prop} {l : List α} (h : sorted r l) : sorted r (tail l) :=
  pairwise.tail h

theorem rel_of_sorted_cons {α : Type uu} {r : α → α → Prop} {a : α} {l : List α} : sorted r (a :: l) → ∀ (b : α), b ∈ l → r a b :=
  rel_of_pairwise_cons

@[simp] theorem sorted_cons {α : Type uu} {r : α → α → Prop} {a : α} {l : List α} : sorted r (a :: l) ↔ (∀ (b : α), b ∈ l → r a b) ∧ sorted r l :=
  pairwise_cons

protected theorem sorted.nodup {α : Type uu} {r : α → α → Prop} [is_irrefl α r] {l : List α} (h : sorted r l) : nodup l :=
  pairwise.nodup h

theorem eq_of_perm_of_sorted {α : Type uu} {r : α → α → Prop} [is_antisymm α r] {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) (s₁ : sorted r l₁) (s₂ : sorted r l₂) : l₁ = l₂ := sorry

@[simp] theorem sorted_singleton {α : Type uu} {r : α → α → Prop} (a : α) : sorted r [a] :=
  pairwise_singleton r a

theorem nth_le_of_sorted_of_le {α : Type uu} {r : α → α → Prop} [is_refl α r] {l : List α} (h : sorted r l) {a : ℕ} {b : ℕ} {ha : a < length l} {hb : b < length l} (hab : a ≤ b) : r (nth_le l a ha) (nth_le l b hb) :=
  or.dcases_on (eq_or_lt_of_le hab) (fun (H : a = b) => eq.drec (fun (hab : a ≤ a) => refl (nth_le l a ha)) H hb hab)
    fun (H : a < b) => iff.mp pairwise_iff_nth_le h a b hb H

/-! ### Insertion sort -/

/-- `ordered_insert a l` inserts `a` into `l` at such that
  `ordered_insert a l` is sorted if `l` is. -/
@[simp] def ordered_insert {α : Type uu} (r : α → α → Prop) [DecidableRel r] (a : α) : List α → List α :=
  sorry

/-- `insertion_sort l` returns `l` sorted using the insertion sort algorithm. -/
@[simp] def insertion_sort {α : Type uu} (r : α → α → Prop) [DecidableRel r] : List α → List α :=
  sorry

@[simp] theorem ordered_insert_nil {α : Type uu} (r : α → α → Prop) [DecidableRel r] (a : α) : ordered_insert r a [] = [a] :=
  rfl

theorem ordered_insert_length {α : Type uu} (r : α → α → Prop) [DecidableRel r] (L : List α) (a : α) : length (ordered_insert r a L) = length L + 1 := sorry

/-- An alternative definition of `ordered_insert` using `take_while` and `drop_while`. -/
theorem ordered_insert_eq_take_drop {α : Type uu} (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) : ordered_insert r a l = take_while (fun (b : α) => ¬r a b) l ++ a :: drop_while (fun (b : α) => ¬r a b) l := sorry

theorem insertion_sort_cons_eq_take_drop {α : Type uu} (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) : insertion_sort r (a :: l) =
  take_while (fun (b : α) => ¬r a b) (insertion_sort r l) ++
    a :: drop_while (fun (b : α) => ¬r a b) (insertion_sort r l) :=
  ordered_insert_eq_take_drop r a (insertion_sort r l)

theorem perm_ordered_insert {α : Type uu} (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) : ordered_insert r a l ~ a :: l := sorry

theorem ordered_insert_count {α : Type uu} (r : α → α → Prop) [DecidableRel r] [DecidableEq α] (L : List α) (a : α) (b : α) : count a (ordered_insert r b L) = count a L + ite (a = b) 1 0 := sorry

theorem perm_insertion_sort {α : Type uu} (r : α → α → Prop) [DecidableRel r] (l : List α) : insertion_sort r l ~ l := sorry

/-- If `l` is already `list.sorted` with respect to `r`, then `insertion_sort` does not change
it. -/
theorem sorted.insertion_sort_eq {α : Type uu} {r : α → α → Prop} [DecidableRel r] {l : List α} (h : sorted r l) : insertion_sort r l = l := sorry

theorem sorted.ordered_insert {α : Type uu} {r : α → α → Prop} [DecidableRel r] [is_total α r] [is_trans α r] (a : α) (l : List α) : sorted r l → sorted r (ordered_insert r a l) := sorry

/-- The list `list.insertion_sort r l` is `list.sorted` with respect to `r`. -/
theorem sorted_insertion_sort {α : Type uu} (r : α → α → Prop) [DecidableRel r] [is_total α r] [is_trans α r] (l : List α) : sorted r (insertion_sort r l) := sorry

/-! ### Merge sort -/

-- TODO(Jeremy): observation: if instead we write (a :: (split l).1, b :: (split l).2), the

-- equation compiler can't prove the third equation

/-- Split `l` into two lists of approximately equal length.

     split [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) -/
@[simp] def split {α : Type uu} : List α → List α × List α :=
  sorry

theorem split_cons_of_eq {α : Type uu} (a : α) {l : List α} {l₁ : List α} {l₂ : List α} (h : split l = (l₁, l₂)) : split (a :: l) = (a :: l₂, l₁) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (split (a :: l) = (a :: l₂, l₁))) (split.equations._eqn_2 a l)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (split._match_1 a (split l) = (a :: l₂, l₁))) h))
      (Eq.refl (split._match_1 a (l₁, l₂))))

theorem length_split_le {α : Type uu} {l : List α} {l₁ : List α} {l₂ : List α} : split l = (l₁, l₂) → length l₁ ≤ length l ∧ length l₂ ≤ length l := sorry

theorem length_split_lt {α : Type uu} {a : α} {b : α} {l : List α} {l₁ : List α} {l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) : length l₁ < length (a :: b :: l) ∧ length l₂ < length (a :: b :: l) := sorry

theorem perm_split {α : Type uu} {l : List α} {l₁ : List α} {l₂ : List α} : split l = (l₁, l₂) → l ~ l₁ ++ l₂ := sorry

/-- Merge two sorted lists into one in linear time.

     merge [1, 2, 4, 5] [0, 1, 3, 4] = [0, 1, 1, 2, 3, 4, 4, 5] -/
def merge {α : Type uu} (r : α → α → Prop) [DecidableRel r] : List α → List α → List α :=
  sorry

/-- Implementation of a merge sort algorithm to sort a list. -/
def merge_sort {α : Type uu} (r : α → α → Prop) [DecidableRel r] : List α → List α :=
  sorry

theorem merge_sort_cons_cons {α : Type uu} (r : α → α → Prop) [DecidableRel r] {a : α} {b : α} {l : List α} {l₁ : List α} {l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) : merge_sort r (a :: b :: l) = merge r (merge_sort r l₁) (merge_sort r l₂) := sorry

theorem perm_merge {α : Type uu} (r : α → α → Prop) [DecidableRel r] (l : List α) (l' : List α) : merge r l l' ~ l ++ l' := sorry

theorem perm_merge_sort {α : Type uu} (r : α → α → Prop) [DecidableRel r] (l : List α) : merge_sort r l ~ l := sorry

@[simp] theorem length_merge_sort {α : Type uu} (r : α → α → Prop) [DecidableRel r] (l : List α) : length (merge_sort r l) = length l :=
  perm.length_eq (perm_merge_sort r l)

theorem sorted.merge {α : Type uu} {r : α → α → Prop} [DecidableRel r] [is_total α r] [is_trans α r] {l : List α} {l' : List α} : sorted r l → sorted r l' → sorted r (merge r l l') := sorry

theorem sorted_merge_sort {α : Type uu} (r : α → α → Prop) [DecidableRel r] [is_total α r] [is_trans α r] (l : List α) : sorted r (merge_sort r l) := sorry

theorem merge_sort_eq_self {α : Type uu} (r : α → α → Prop) [DecidableRel r] [is_total α r] [is_trans α r] [is_antisymm α r] {l : List α} : sorted r l → merge_sort r l = l :=
  eq_of_perm_of_sorted (perm_merge_sort r l) (sorted_merge_sort r l)

theorem merge_sort_eq_insertion_sort {α : Type uu} (r : α → α → Prop) [DecidableRel r] [is_total α r] [is_trans α r] [is_antisymm α r] (l : List α) : merge_sort r l = insertion_sort r l :=
  eq_of_perm_of_sorted (perm.trans (perm_merge_sort r l) (perm.symm (perm_insertion_sort r l))) (sorted_merge_sort r l)
    (sorted_insertion_sort r l)

