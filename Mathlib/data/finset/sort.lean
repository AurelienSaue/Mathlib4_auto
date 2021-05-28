/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finset.lattice
import Mathlib.data.multiset.sort
import Mathlib.data.list.nodup_equiv_fin
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Construct a sorted list from a finset.
-/

namespace finset


/-! ### sort -/

/-- `sort s` constructs a sorted list from the unordered set `s`.
  (Uses merge sort algorithm.) -/
def sort {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r] [is_antisymm α r] [is_total α r] (s : finset α) : List α :=
  multiset.sort r (val s)

@[simp] theorem sort_sorted {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r] [is_antisymm α r] [is_total α r] (s : finset α) : list.sorted r (sort r s) :=
  multiset.sort_sorted r (val s)

@[simp] theorem sort_eq {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r] [is_antisymm α r] [is_total α r] (s : finset α) : ↑(sort r s) = val s :=
  multiset.sort_eq r (val s)

@[simp] theorem sort_nodup {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r] [is_antisymm α r] [is_total α r] (s : finset α) : list.nodup (sort r s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (multiset.nodup ↑(sort r s))) (sort_eq r s))) (nodup s)

@[simp] theorem sort_to_finset {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r] [is_antisymm α r] [is_total α r] [DecidableEq α] (s : finset α) : list.to_finset (sort r s) = s :=
  list.to_finset_eq (sort_nodup r s) ▸ eq_of_veq (sort_eq r s)

@[simp] theorem mem_sort {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r] [is_antisymm α r] [is_total α r] {s : finset α} {a : α} : a ∈ sort r s ↔ a ∈ s :=
  multiset.mem_sort r

@[simp] theorem length_sort {α : Type u_1} (r : α → α → Prop) [DecidableRel r] [is_trans α r] [is_antisymm α r] [is_total α r] {s : finset α} : list.length (sort r s) = card s :=
  multiset.length_sort r

theorem sort_sorted_lt {α : Type u_1} [linear_order α] (s : finset α) : list.sorted Less (sort LessEq s) :=
  list.pairwise.imp₂ lt_of_le_of_ne (sort_sorted LessEq s) (sort_nodup LessEq s)

theorem sorted_zero_eq_min'_aux {α : Type u_1} [linear_order α] (s : finset α) (h : 0 < list.length (sort LessEq s)) (H : finset.nonempty s) : list.nth_le (sort LessEq s) 0 h = min' s H := sorry

theorem sorted_zero_eq_min' {α : Type u_1} [linear_order α] {s : finset α} {h : 0 < list.length (sort LessEq s)} : list.nth_le (sort LessEq s) 0 h =
  min' s (iff.mp card_pos (eq.mp (Eq._oldrec (Eq.refl (0 < list.length (sort LessEq s))) (length_sort LessEq)) h)) :=
  sorted_zero_eq_min'_aux s h
    (iff.mp card_pos (eq.mp (Eq._oldrec (Eq.refl (0 < list.length (sort LessEq s))) (length_sort LessEq)) h))

theorem min'_eq_sorted_zero {α : Type u_1} [linear_order α] {s : finset α} {h : finset.nonempty s} : min' s h =
  list.nth_le (sort LessEq s) 0
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 < list.length (sort LessEq s))) (length_sort LessEq))) (iff.mpr card_pos h)) :=
  Eq.symm
    (sorted_zero_eq_min'_aux s
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 < list.length (sort LessEq s))) (length_sort LessEq))) (iff.mpr card_pos h)) h)

theorem sorted_last_eq_max'_aux {α : Type u_1} [linear_order α] (s : finset α) (h : list.length (sort LessEq s) - 1 < list.length (sort LessEq s)) (H : finset.nonempty s) : list.nth_le (sort LessEq s) (list.length (sort LessEq s) - 1) h = max' s H := sorry

theorem sorted_last_eq_max' {α : Type u_1} [linear_order α] {s : finset α} {h : list.length (sort LessEq s) - 1 < list.length (sort LessEq s)} : list.nth_le (sort LessEq s) (list.length (sort LessEq s) - 1) h =
  max' s
    (iff.mp card_pos
      (lt_of_le_of_lt bot_le
        (eq.mp
          (Eq._oldrec (Eq.refl (list.length (sort LessEq s) - 1 < list.length (sort LessEq s))) (length_sort LessEq))
          h))) := sorry

theorem max'_eq_sorted_last {α : Type u_1} [linear_order α] {s : finset α} {h : finset.nonempty s} : max' s h =
  list.nth_le (sort LessEq s) (list.length (sort LessEq s) - 1)
    (eq.mpr
      (id
        ((fun (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℕ) (e_3 : ᾰ_2 = ᾰ_3) => congr (congr_arg Less e_2) e_3)
          (list.length (sort LessEq s) - 1) (card s - 1)
          ((fun (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℕ) (e_3 : ᾰ_2 = ᾰ_3) => congr (congr_arg Sub.sub e_2) e_3)
            (list.length (sort LessEq s)) (card s) (length_sort LessEq) 1 1 (Eq.refl 1))
          (list.length (sort LessEq s)) (card s) (length_sort LessEq)))
      (eq.mp (Eq.refl (card s - 1 < card s)) (nat.sub_lt (iff.mpr card_pos h) zero_lt_one))) := sorry

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `order_iso_of_fin s h`
is the increasing bijection between `fin k` and `s` as an `order_iso`. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of an iso `fin s.card ≃o s` to avoid
casting issues in further uses of this function. -/
def order_iso_of_fin {α : Type u_1} [linear_order α] (s : finset α) {k : ℕ} (h : card s = k) : fin k ≃o ↥↑s :=
  order_iso.trans (fin.cast sorry)
    (order_iso.trans (list.sorted.nth_le_iso (sort LessEq s) (sort_sorted_lt s))
      (order_iso.set_congr (fun (x : α) => list.mem x (sort LessEq s)) ↑s sorry))

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `order_emb_of_fin s h` is
the increasing bijection between `fin k` and `s` as an order embedding into `α`. Here, `h` is a
proof that the cardinality of `s` is `k`. We use this instead of an embedding `fin s.card ↪o α` to
avoid casting issues in further uses of this function. -/
def order_emb_of_fin {α : Type u_1} [linear_order α] (s : finset α) {k : ℕ} (h : card s = k) : fin k ↪o α :=
  rel_embedding.trans (order_iso.to_order_embedding (order_iso_of_fin s h))
    (order_embedding.subtype fun (x : α) => x ∈ ↑s)

@[simp] theorem coe_order_iso_of_fin_apply {α : Type u_1} [linear_order α] (s : finset α) {k : ℕ} (h : card s = k) (i : fin k) : ↑(coe_fn (order_iso_of_fin s h) i) = coe_fn (order_emb_of_fin s h) i :=
  rfl

theorem order_iso_of_fin_symm_apply {α : Type u_1} [linear_order α] (s : finset α) {k : ℕ} (h : card s = k) (x : ↥↑s) : ↑(coe_fn (order_iso.symm (order_iso_of_fin s h)) x) = list.index_of (↑x) (sort LessEq s) :=
  rfl

theorem order_emb_of_fin_apply {α : Type u_1} [linear_order α] (s : finset α) {k : ℕ} (h : card s = k) (i : fin k) : coe_fn (order_emb_of_fin s h) i =
  list.nth_le (sort LessEq s) (↑i)
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑i < list.length (sort LessEq s))) (length_sort LessEq)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑i < card s)) h)) (subtype.property i))) :=
  rfl

@[simp] theorem order_emb_of_fin_mem {α : Type u_1} [linear_order α] (s : finset α) {k : ℕ} (h : card s = k) (i : fin k) : coe_fn (order_emb_of_fin s h) i ∈ s :=
  subtype.property (coe_fn (order_iso_of_fin s h) i)

@[simp] theorem range_order_emb_of_fin {α : Type u_1} [linear_order α] (s : finset α) {k : ℕ} (h : card s = k) : set.range ⇑(order_emb_of_fin s h) = ↑s := sorry

/-- The bijection `order_emb_of_fin s h` sends `0` to the minimum of `s`. -/
theorem order_emb_of_fin_zero {α : Type u_1} [linear_order α] {s : finset α} {k : ℕ} (h : card s = k) (hz : 0 < k) : coe_fn (order_emb_of_fin s h) { val := 0, property := hz } = min' s (iff.mp card_pos (Eq.symm h ▸ hz)) := sorry

/-- The bijection `order_emb_of_fin s h` sends `k-1` to the maximum of `s`. -/
theorem order_emb_of_fin_last {α : Type u_1} [linear_order α] {s : finset α} {k : ℕ} (h : card s = k) (hz : 0 < k) : coe_fn (order_emb_of_fin s h) { val := k - 1, property := buffer.lt_aux_2 hz } =
  max' s (iff.mp card_pos (Eq.symm h ▸ hz)) := sorry

/-- `order_emb_of_fin {a} h` sends any argument to `a`. -/
@[simp] theorem order_emb_of_fin_singleton {α : Type u_1} [linear_order α] (a : α) (i : fin 1) : coe_fn (order_emb_of_fin (singleton a) (card_singleton a)) i = a := sorry

/-- Any increasing map `f` from `fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `order_emb_of_fin s h`. -/
theorem order_emb_of_fin_unique {α : Type u_1} [linear_order α] {s : finset α} {k : ℕ} (h : card s = k) {f : fin k → α} (hfs : ∀ (x : fin k), f x ∈ s) (hmono : strict_mono f) : f = ⇑(order_emb_of_fin s h) := sorry

/-- An order embedding `f` from `fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `order_emb_of_fin s h`. -/
theorem order_emb_of_fin_unique' {α : Type u_1} [linear_order α] {s : finset α} {k : ℕ} (h : card s = k) {f : fin k ↪o α} (hfs : ∀ (x : fin k), coe_fn f x ∈ s) : f = order_emb_of_fin s h :=
  rel_embedding.ext (iff.mp function.funext_iff (order_emb_of_fin_unique h hfs (order_embedding.strict_mono f)))

/-- Two parametrizations `order_emb_of_fin` of the same set take the same value on `i` and `j` if
and only if `i = j`. Since they can be defined on a priori not defeq types `fin k` and `fin l`
(although necessarily `k = l`), the conclusion is rather written `(i : ℕ) = (j : ℕ)`. -/
@[simp] theorem order_emb_of_fin_eq_order_emb_of_fin_iff {α : Type u_1} [linear_order α] {k : ℕ} {l : ℕ} {s : finset α} {i : fin k} {j : fin l} {h : card s = k} {h' : card s = l} : coe_fn (order_emb_of_fin s h) i = coe_fn (order_emb_of_fin s h') j ↔ ↑i = ↑j := sorry

protected instance has_repr {α : Type u_1} [has_repr α] : has_repr (finset α) :=
  has_repr.mk fun (s : finset α) => repr (val s)

