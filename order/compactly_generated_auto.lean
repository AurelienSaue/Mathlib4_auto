/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.well_founded
import Mathlib.order.order_iso_nat
import Mathlib.data.set.finite
import Mathlib.tactic.tfae
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Compactness properties for complete lattices

For complete lattices, there are numerous equivalent ways to express the fact that the relation `>`
is well-founded. In this file we define three especially-useful characterisations and provide
proofs that they are indeed equivalent to well-foundedness.

## Main definitions
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `complete_lattice.is_compact_element`
 * `complete_lattice.is_compactly_generated`

## Main results
The main result is that the following four conditions are equivalent for a complete lattice:
 * `well_founded (>)`
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `∀ k, complete_lattice.is_compact_element k`

This is demonstrated by means of the following four lemmas:
 * `complete_lattice.well_founded.is_Sup_finite_compact`
 * `complete_lattice.is_Sup_finite_compact.is_sup_closed_compact`
 * `complete_lattice.is_sup_closed_compact.well_founded`
 * `complete_lattice.is_Sup_finite_compact_iff_all_elements_compact`

 We also show well-founded lattices are compactly generated
 (`complete_lattice.compactly_generated_of_well_founded`).

## Tags

complete lattice, well-founded, compact
-/

namespace complete_lattice


/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `Sup`. -/
def is_sup_closed_compact (α : Type u_1) [complete_lattice α]  :=
  ∀ (s : set α), set.nonempty s → (∀ (a b : α), a ∈ s → b ∈ s → a ⊔ b ∈ s) → Sup s ∈ s

/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `Sup`. -/
def is_Sup_finite_compact (α : Type u_1) [complete_lattice α]  :=
  ∀ (s : set α), ∃ (t : finset α), ↑t ⊆ s ∧ Sup s = finset.sup t id

/-- An element `k` of a complete lattice is said to be compact if any set with `Sup`
above `k` has a finite subset with `Sup` above `k`.  Such an element is also called
"finite" or "S-compact". -/
def is_compact_element {α : Type u_1} [complete_lattice α] (k : α)  :=
  ∀ (s : set α), k ≤ Sup s → ∃ (t : finset α), ↑t ⊆ s ∧ k ≤ finset.sup t id

/-- A complete lattice is said to be compactly generated if any
element is the `Sup` of compact elements. -/
def is_compactly_generated (α : Type u_1) [complete_lattice α]  :=
  ∀ (x : α), ∃ (s : set α), (∀ (x : α), x ∈ s → is_compact_element x) ∧ Sup s = x

/-- An element `k` is compact if and only if any directed set with `Sup` above
`k` already got above `k` at some point in the set. -/
theorem is_compact_element_iff_le_of_directed_Sup_le (α : Type u_1) [complete_lattice α] (k : α) : is_compact_element k ↔ ∀ (s : set α), set.nonempty s → directed_on LessEq s → k ≤ Sup s → ∃ (x : α), x ∈ s ∧ k ≤ x := sorry

theorem finset_sup_compact_of_compact {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} (s : finset β) (h : ∀ (x : β), x ∈ s → is_compact_element (f x)) : is_compact_element (finset.sup s f) := sorry

theorem well_founded.is_Sup_finite_compact (α : Type u_1) [complete_lattice α] (h : well_founded gt) : is_Sup_finite_compact α := sorry

theorem is_Sup_finite_compact.is_sup_closed_compact (α : Type u_1) [complete_lattice α] (h : is_Sup_finite_compact α) : is_sup_closed_compact α := sorry

theorem is_sup_closed_compact.well_founded (α : Type u_1) [complete_lattice α] (h : is_sup_closed_compact α) : well_founded gt := sorry

theorem is_Sup_finite_compact_iff_all_elements_compact (α : Type u_1) [complete_lattice α] : is_Sup_finite_compact α ↔ ∀ (k : α), is_compact_element k := sorry

theorem well_founded_characterisations (α : Type u_1) [complete_lattice α] : tfae [well_founded gt, is_Sup_finite_compact α, is_sup_closed_compact α, ∀ (k : α), is_compact_element k] := sorry

theorem well_founded_iff_is_Sup_finite_compact (α : Type u_1) [complete_lattice α] : well_founded gt ↔ is_Sup_finite_compact α :=
  list.tfae.out (well_founded_characterisations α) 0 1

theorem is_Sup_finite_compact_iff_is_sup_closed_compact (α : Type u_1) [complete_lattice α] : is_Sup_finite_compact α ↔ is_sup_closed_compact α :=
  list.tfae.out (well_founded_characterisations α) 1 (bit0 1)

theorem is_sup_closed_compact_iff_well_founded (α : Type u_1) [complete_lattice α] : is_sup_closed_compact α ↔ well_founded gt :=
  list.tfae.out (well_founded_characterisations α) (bit0 1) 0

theorem Mathlib.is_Sup_finite_compact.well_founded (α : Type u_1) [complete_lattice α] : is_Sup_finite_compact α → well_founded gt :=
  iff.mpr (well_founded_iff_is_Sup_finite_compact α)

theorem Mathlib.is_sup_closed_compact.is_Sup_finite_compact (α : Type u_1) [complete_lattice α] : is_sup_closed_compact α → is_Sup_finite_compact α :=
  iff.mpr (is_Sup_finite_compact_iff_is_sup_closed_compact α)

theorem Mathlib.well_founded.is_sup_closed_compact (α : Type u_1) [complete_lattice α] : well_founded gt → is_sup_closed_compact α :=
  iff.mpr (is_sup_closed_compact_iff_well_founded α)

theorem compactly_generated_of_well_founded (α : Type u_1) [complete_lattice α] (h : well_founded gt) : is_compactly_generated α := sorry

