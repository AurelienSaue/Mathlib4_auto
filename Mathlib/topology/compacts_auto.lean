/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.homeomorph
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Compact sets

## Summary

We define the subtype of compact sets in a topological space.

## Main Definitions

- `closeds α` is the type of closed subsets of a topological space `α`.
- `compacts α` is the type of compact subsets of a topological space `α`.
- `nonempty_compacts α` is the type of non-empty compact subsets.
- `positive_compacts α` is the type of compact subsets with non-empty interior.
-/

namespace topological_space


/-- The type of closed subsets of a topological space. -/
def closeds (α : Type u_1) [topological_space α] := Subtype fun (s : set α) => is_closed s

/-- The type of closed subsets is inhabited, with default element the empty set. -/
protected instance closeds.inhabited (α : Type u_1) [topological_space α] : Inhabited (closeds α) :=
  { default := { val := ∅, property := is_closed_empty } }

/-- The compact sets of a topological space. See also `nonempty_compacts`. -/
def compacts (α : Type u_1) [topological_space α] := Subtype fun (s : set α) => is_compact s

/-- The type of non-empty compact subsets of a topological space. The
non-emptiness will be useful in metric spaces, as we will be able to put
a distance (and not merely an edistance) on this space. -/
def nonempty_compacts (α : Type u_1) [topological_space α] :=
  Subtype fun (s : set α) => set.nonempty s ∧ is_compact s

/-- In an inhabited space, the type of nonempty compact subsets is also inhabited, with
default element the singleton set containing the default element. -/
protected instance nonempty_compacts_inhabited (α : Type u_1) [topological_space α] [Inhabited α] :
    Inhabited (nonempty_compacts α) :=
  { default := { val := singleton Inhabited.default, property := sorry } }

/-- The compact sets with nonempty interior of a topological space. See also `compacts` and
  `nonempty_compacts`. -/
def positive_compacts (α : Type u_1) [topological_space α] :=
  Subtype fun (s : set α) => is_compact s ∧ set.nonempty (interior s)

namespace compacts


protected instance semilattice_sup_bot {α : Type u_1} [topological_space α] :
    semilattice_sup_bot (compacts α) :=
  subtype.semilattice_sup_bot compact_empty sorry

protected instance semilattice_inf_bot {α : Type u_1} [topological_space α] [t2_space α] :
    semilattice_inf_bot (compacts α) :=
  subtype.semilattice_inf_bot compact_empty sorry

protected instance lattice {α : Type u_1} [topological_space α] [t2_space α] :
    lattice (compacts α) :=
  subtype.lattice sorry sorry

@[simp] theorem bot_val {α : Type u_1} [topological_space α] : subtype.val ⊥ = ∅ := rfl

@[simp] theorem sup_val {α : Type u_1} [topological_space α] {K₁ : compacts α} {K₂ : compacts α} :
    subtype.val (K₁ ⊔ K₂) = subtype.val K₁ ∪ subtype.val K₂ :=
  rfl

protected theorem ext {α : Type u_1} [topological_space α] {K₁ : compacts α} {K₂ : compacts α}
    (h : subtype.val K₁ = subtype.val K₂) : K₁ = K₂ :=
  subtype.eq h

@[simp] theorem finset_sup_val {α : Type u_1} [topological_space α] {β : Type u_2}
    {K : β → compacts α} {s : finset β} :
    subtype.val (finset.sup s K) = finset.sup s fun (x : β) => subtype.val (K x) :=
  finset.sup_coe s K

protected instance inhabited {α : Type u_1} [topological_space α] : Inhabited (compacts α) :=
  { default := ⊥ }

/-- The image of a compact set under a continuous function. -/
protected def map {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (f : α → β) (hf : continuous f) (K : compacts α) : compacts β :=
  { val := f '' subtype.val K, property := sorry }

@[simp] theorem map_val {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {f : α → β} (hf : continuous f) (K : compacts α) :
    subtype.val (compacts.map f hf K) = f '' subtype.val K :=
  rfl

/-- A homeomorphism induces an equivalence on compact sets, by taking the image. -/
@[simp] protected def equiv {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] (f : α ≃ₜ β) : compacts α ≃ compacts β :=
  equiv.mk (compacts.map (⇑f) (homeomorph.continuous f)) (compacts.map ⇑(homeomorph.symm f) sorry)
    sorry sorry

/-- The image of a compact set under a homeomorphism can also be expressed as a preimage. -/
theorem equiv_to_fun_val {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (f : α ≃ₜ β) (K : compacts α) :
    subtype.val (coe_fn (compacts.equiv f) K) = ⇑(homeomorph.symm f) ⁻¹' subtype.val K :=
  congr_fun
    (set.image_eq_preimage_of_inverse (equiv.left_inv (homeomorph.to_equiv f))
      (equiv.right_inv (homeomorph.to_equiv f)))
    (subtype.val K)

end compacts


protected instance nonempty_compacts.to_compact_space {α : Type u_1} [topological_space α]
    {p : nonempty_compacts α} : compact_space ↥(subtype.val p) :=
  compact_space.mk (iff.mp compact_iff_compact_univ (and.right (subtype.property p)))

protected instance nonempty_compacts.to_nonempty {α : Type u_1} [topological_space α]
    {p : nonempty_compacts α} : Nonempty ↥(subtype.val p) :=
  set.nonempty.to_subtype (and.left (subtype.property p))

/-- Associate to a nonempty compact subset the corresponding closed subset -/
def nonempty_compacts.to_closeds {α : Type u_1} [topological_space α] [t2_space α] :
    nonempty_compacts α → closeds α :=
  set.inclusion sorry

end Mathlib