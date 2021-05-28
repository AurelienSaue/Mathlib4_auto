/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.finset.basic
import PostPort

universes u_1 

namespace Mathlib

/-!
# The powerset of a finset
-/

namespace finset


/-! ### powerset -/

/-- When `s` is a finset, `s.powerset` is the finset of all subsets of `s` (seen as finsets). -/
def powerset {α : Type u_1} (s : finset α) : finset (finset α) :=
  mk (multiset.pmap mk (multiset.powerset (val s)) sorry) sorry

@[simp] theorem mem_powerset {α : Type u_1} {s : finset α} {t : finset α} : s ∈ powerset t ↔ s ⊆ t := sorry

@[simp] theorem empty_mem_powerset {α : Type u_1} (s : finset α) : ∅ ∈ powerset s :=
  iff.mpr mem_powerset (empty_subset s)

@[simp] theorem mem_powerset_self {α : Type u_1} (s : finset α) : s ∈ powerset s :=
  iff.mpr mem_powerset (subset.refl s)

@[simp] theorem powerset_empty {α : Type u_1} : powerset ∅ = singleton ∅ :=
  rfl

@[simp] theorem powerset_mono {α : Type u_1} {s : finset α} {t : finset α} : powerset s ⊆ powerset t ↔ s ⊆ t := sorry

@[simp] theorem card_powerset {α : Type u_1} (s : finset α) : card (powerset s) = bit0 1 ^ card s :=
  Eq.trans (multiset.card_pmap mk (multiset.powerset (val s)) (powerset._proof_1 s)) (multiset.card_powerset (val s))

theorem not_mem_of_mem_powerset_of_not_mem {α : Type u_1} {s : finset α} {t : finset α} {a : α} (ht : t ∈ powerset s) (h : ¬a ∈ s) : ¬a ∈ t :=
  mt (iff.mp mem_powerset ht a) h

theorem powerset_insert {α : Type u_1} [DecidableEq α] (s : finset α) (a : α) : powerset (insert a s) = powerset s ∪ image (insert a) (powerset s) := sorry

/-- Given an integer `n` and a finset `s`, then `powerset_len n s` is the finset of subsets of `s`
of cardinality `n`.-/
def powerset_len {α : Type u_1} (n : ℕ) (s : finset α) : finset (finset α) :=
  mk (multiset.pmap mk (multiset.powerset_len n (val s)) sorry) sorry

theorem mem_powerset_len {α : Type u_1} {n : ℕ} {s : finset α} {t : finset α} : s ∈ powerset_len n t ↔ s ⊆ t ∧ card s = n := sorry

@[simp] theorem powerset_len_mono {α : Type u_1} {n : ℕ} {s : finset α} {t : finset α} (h : s ⊆ t) : powerset_len n s ⊆ powerset_len n t :=
  fun (u : finset α) (h' : u ∈ powerset_len n s) =>
    iff.mpr mem_powerset_len (and.imp (fun (h₂ : u ⊆ s) => subset.trans h₂ h) id (iff.mp mem_powerset_len h'))

@[simp] theorem card_powerset_len {α : Type u_1} (n : ℕ) (s : finset α) : card (powerset_len n s) = nat.choose (card s) n :=
  Eq.trans (multiset.card_pmap mk (multiset.powerset_len n (val s)) (powerset_len._proof_1 n s))
    (multiset.card_powerset_len n (val s))

@[simp] theorem powerset_len_zero {α : Type u_1} (s : finset α) : powerset_len 0 s = singleton ∅ := sorry

theorem powerset_len_eq_filter {α : Type u_1} {n : ℕ} {s : finset α} : powerset_len n s = filter (fun (x : finset α) => card x = n) (powerset s) := sorry

