/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Parallel computation of a computable sequence of computations by
a diagonal enumeration.
The important theorems of this operation are proven as
terminates_parallel and exists_of_mem_parallel.
(This operation is nondeterministic in the sense that it does not
honor sequence equivalence (irrelevance of computation time).)
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.seq.wseq
import Mathlib.PostPort

universes u v 

namespace Mathlib

namespace computation


def parallel.aux2 {α : Type u} : List (computation α) → α ⊕ List (computation α) :=
  list.foldr (fun (c : computation α) (o : α ⊕ List (computation α)) => sorry) (sum.inr [])

def parallel.aux1 {α : Type u} : List (computation α) × wseq (computation α) → α ⊕ List (computation α) × wseq (computation α) :=
  sorry

/-- Parallel computation of an infinite stream of computations,
  taking the first result -/
def parallel {α : Type u} (S : wseq (computation α)) : computation α :=
  corec sorry ([], S)

theorem terminates_parallel.aux {α : Type u} {l : List (computation α)} {S : wseq (computation α)} {c : computation α} : c ∈ l → terminates c → terminates (corec parallel.aux1 (l, S)) := sorry

theorem terminates_parallel {α : Type u} {S : wseq (computation α)} {c : computation α} (h : c ∈ S) [T : terminates c] : terminates (parallel S) := sorry

theorem exists_of_mem_parallel {α : Type u} {S : wseq (computation α)} {a : α} (h : a ∈ parallel S) : ∃ (c : computation α), ∃ (H : c ∈ S), a ∈ c := sorry

theorem map_parallel {α : Type u} {β : Type v} (f : α → β) (S : wseq (computation α)) : map f (parallel S) = parallel (wseq.map (map f) S) := sorry

theorem parallel_empty {α : Type u} (S : wseq (computation α)) (h : wseq.head S ~> none) : parallel S = empty α := sorry

-- The reason this isn't trivial from exists_of_mem_parallel is because it eliminates to Sort

def parallel_rec {α : Type u} {S : wseq (computation α)} (C : α → Sort v) (H : (s : computation α) → s ∈ S → (a : α) → a ∈ s → C a) {a : α} (h : a ∈ parallel S) : C a :=
  let T : wseq (computation (α × computation α)) := wseq.map (fun (c : computation α) => map (fun (a : α) => (a, c)) c) S;
  (fun (_x : α × computation α) (e : get (parallel T) = _x) =>
      Prod.rec
        (fun (a' : α) (c : computation α) (e : get (parallel T) = (a', c)) =>
          and.dcases_on sorry fun (ac : a ∈ c) (cs : c ∈ S) => H c cs a ac)
        _x e)
    (get (parallel T)) sorry

theorem parallel_promises {α : Type u} {S : wseq (computation α)} {a : α} (H : ∀ (s : computation α), s ∈ S → s ~> a) : parallel S ~> a := sorry

theorem mem_parallel {α : Type u} {S : wseq (computation α)} {a : α} (H : ∀ (s : computation α), s ∈ S → s ~> a) {c : computation α} (cs : c ∈ S) (ac : a ∈ c) : a ∈ parallel S :=
  mem_of_promises (parallel S) (parallel_promises H)

theorem parallel_congr_lem {α : Type u} {S : wseq (computation α)} {T : wseq (computation α)} {a : α} (H : wseq.lift_rel equiv S T) : (∀ (s : computation α), s ∈ S → s ~> a) ↔ ∀ (t : computation α), t ∈ T → t ~> a := sorry

-- The parallel operation is only deterministic when all computation paths lead to the same value

theorem parallel_congr_left {α : Type u} {S : wseq (computation α)} {T : wseq (computation α)} {a : α} (h1 : ∀ (s : computation α), s ∈ S → s ~> a) (H : wseq.lift_rel equiv S T) : parallel S ~ parallel T := sorry

theorem parallel_congr_right {α : Type u} {S : wseq (computation α)} {T : wseq (computation α)} {a : α} (h2 : ∀ (t : computation α), t ∈ T → t ~> a) (H : wseq.lift_rel equiv S T) : parallel S ~ parallel T :=
  parallel_congr_left (iff.mpr (parallel_congr_lem H) h2) H

