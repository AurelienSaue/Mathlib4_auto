/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.list.sort
import Mathlib.data.fin
import PostPort

universes u_1 

namespace Mathlib

/-!
# Isomorphism between `fin (length l)` and `{x // x ∈ l}`

Given a list `l,

* if `l` has no duplicates, then `list.nodup.nth_le_equiv` is the bijection between `fin (length l)`
  and `{x // x ∈ l}` sending `⟨i, hi⟩` to `⟨nth_le l i hi, _⟩` with the inverse sending `⟨x, hx⟩` to
  `⟨index_of x l, _⟩`;

* if `l` is sorted w.r.t. `(<)`, then `list.sorted.nth_le_iso` is the same bijection reinterpreted
  as an `order_iso`.

-/

namespace list


namespace nodup


/-- If `l` has no duplicates, then `list.nth_le` defines a bijection between `fin (length l)` and
the set of elements of `l`. -/
def nth_le_equiv {α : Type u_1} [DecidableEq α] (l : List α) (H : nodup l) : fin (length l) ≃ Subtype fun (x : α) => x ∈ l :=
  equiv.mk (fun (i : fin (length l)) => { val := nth_le l ↑i sorry, property := sorry })
    (fun (x : Subtype fun (x : α) => x ∈ l) => { val := index_of (↑x) l, property := sorry }) sorry sorry

@[simp] theorem coe_nth_le_equiv_apply {α : Type u_1} [DecidableEq α] {l : List α} (H : nodup l) (i : fin (length l)) : ↑(coe_fn (nth_le_equiv l H) i) = nth_le l (↑i) (subtype.property i) :=
  rfl

@[simp] theorem coe_nth_le_equiv_symm_apply {α : Type u_1} [DecidableEq α] {l : List α} (H : nodup l) (x : Subtype fun (x : α) => x ∈ l) : ↑(coe_fn (equiv.symm (nth_le_equiv l H)) x) = index_of (↑x) l :=
  rfl

end nodup


namespace sorted


theorem nth_le_mono {α : Type u_1} [preorder α] {l : List α} (h : sorted LessEq l) : monotone fun (i : fin (length l)) => nth_le l (↑i) (subtype.property i) :=
  fun (i j : fin (length l)) => nth_le_of_sorted_of_le h

theorem nth_le_strict_mono {α : Type u_1} [preorder α] {l : List α} (h : sorted Less l) : strict_mono fun (i : fin (length l)) => nth_le l (↑i) (subtype.property i) :=
  fun (i j : fin (length l)) => iff.mp pairwise_iff_nth_le h (↑i) (↑j) (subtype.property j)

/-- If `l` is a list sorted w.r.t. `(<)`, then `list.nth_le` defines an order isomorphism between
`fin (length l)` and the set of elements of `l`. -/
def nth_le_iso {α : Type u_1} [preorder α] [DecidableEq α] (l : List α) (H : sorted Less l) : fin (length l) ≃o Subtype fun (x : α) => x ∈ l :=
  rel_iso.mk (nodup.nth_le_equiv l sorry) sorry

@[simp] theorem coe_nth_le_iso_apply {α : Type u_1} [preorder α] {l : List α} [DecidableEq α] (H : sorted Less l) {i : fin (length l)} : ↑(coe_fn (nth_le_iso l H) i) = nth_le l (↑i) (subtype.property i) :=
  rfl

@[simp] theorem coe_nth_le_iso_symm_apply {α : Type u_1} [preorder α] {l : List α} [DecidableEq α] (H : sorted Less l) {x : Subtype fun (x : α) => x ∈ l} : ↑(coe_fn (order_iso.symm (nth_le_iso l H)) x) = index_of (↑x) l :=
  rfl

