/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.encodable.basic
import Mathlib.data.finset.basic
import Mathlib.data.set.disjointed
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Lattice operations on encodable types

Lemmas about lattice and set operations on encodable types

## Implementation Notes

This is a separate file, to avoid unnecessary imports in basic files.

Previously some of these results were in the `measure_theory` folder.
-/

namespace encodable


theorem supr_decode2 {α : Type u_1} {β : Type u_2} [encodable β] [complete_lattice α] (f : β → α) : (supr fun (i : ℕ) => supr fun (b : β) => supr fun (H : b ∈ decode2 β i) => f b) = supr fun (b : β) => f b := sorry

theorem Union_decode2 {α : Type u_1} {β : Type u_2} [encodable β] (f : β → set α) : (set.Union fun (i : ℕ) => set.Union fun (b : β) => set.Union fun (H : b ∈ decode2 β i) => f b) =
  set.Union fun (b : β) => f b :=
  supr_decode2 f

theorem Union_decode2_cases {α : Type u_1} {β : Type u_2} [encodable β] {f : β → set α} {C : set α → Prop} (H0 : C ∅) (H1 : ∀ (b : β), C (f b)) {n : ℕ} : C (set.Union fun (b : β) => set.Union fun (H : b ∈ decode2 β n) => f b) := sorry

theorem Union_decode2_disjoint_on {α : Type u_1} {β : Type u_2} [encodable β] {f : β → set α} (hd : pairwise (disjoint on f)) : pairwise (disjoint on fun (i : ℕ) => set.Union fun (b : β) => set.Union fun (H : b ∈ decode2 β i) => f b) := sorry

end encodable


namespace finset


theorem nonempty_encodable {α : Type u_1} (t : finset α) : Nonempty (encodable (Subtype fun (i : α) => i ∈ t)) := sorry

