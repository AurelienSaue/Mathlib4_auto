/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.complete_boolean_algebra
import Mathlib.order.modular_lattice
import Mathlib.data.fintype.basic
import Mathlib.PostPort

universes u_1 l u_2 

namespace Mathlib

/-!
# Atoms, Coatoms, and Simple Lattices

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
  * `is_atom a` indicates that the only element below `a` is `⊥`.
  * `is_coatom a` indicates that the only element above `a` is `⊤`.

### Atomic and Atomistic Lattices
  * `is_atomic` indicates that every element other than `⊥` is above an atom.
  * `is_coatomic` indicates that every element other than `⊤` is below a coatom.
  * `is_atomistic` indicates that every element is the `Sup` of a set of atoms.
  * `is_coatomistic` indicates that every element is the `Inf` of a set of coatoms.

### Simple Lattices
  * `is_simple_lattice` indicates that a bounded lattice has only two elements, `⊥` and `⊤`.
  * `is_simple_lattice.bounded_distrib_lattice`
  * Given an instance of `is_simple_lattice`, we provide the following definitions. These are not
    made global instances as they contain data :
    * `is_simple_lattice.boolean_algebra`
    * `is_simple_lattice.complete_lattice`
    * `is_simple_lattice.complete_boolean_algebra`

## Main results
  * `is_atom_dual_iff_is_coatom` and `is_coatom_dual_iff_is_atom` express the (definitional) duality
   of `is_atom` and `is_coatom`.
  * `is_simple_lattice_iff_is_atom_top` and `is_simple_lattice_iff_is_coatom_bot` express the
  connection between atoms, coatoms, and simple lattices

-/

/-- An atom of an `order_bot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def is_atom {α : Type u_1} [order_bot α] (a : α)  :=
  a ≠ ⊥ ∧ ∀ (b : α), b < a → b = ⊥

theorem eq_bot_or_eq_of_le_atom {α : Type u_1} [order_bot α] {a : α} {b : α} (ha : is_atom a) (hab : b ≤ a) : b = ⊥ ∨ b = a :=
  or.imp_left (and.right ha b) (has_le.le.lt_or_eq hab)

theorem is_atom.Iic {α : Type u_1} [order_bot α] {x : α} {a : α} (ha : is_atom a) (hax : a ≤ x) : is_atom { val := a, property := hax } := sorry

theorem is_atom.of_is_atom_coe_Iic {α : Type u_1} [order_bot α] {x : α} {a : ↥(set.Iic x)} (ha : is_atom a) : is_atom ↑a := sorry

/-- A coatom of an `order_top` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
def is_coatom {α : Type u_1} [order_top α] (a : α)  :=
  a ≠ ⊤ ∧ ∀ (b : α), a < b → b = ⊤

theorem eq_top_or_eq_of_coatom_le {α : Type u_1} [order_top α] {a : α} {b : α} (ha : is_coatom a) (hab : a ≤ b) : b = ⊤ ∨ b = a :=
  or.imp (and.right ha b) (iff.mpr eq_comm) (has_le.le.lt_or_eq hab)

theorem is_coatom.Ici {α : Type u_1} [order_top α] {x : α} {a : α} (ha : is_coatom a) (hax : x ≤ a) : is_coatom { val := a, property := hax } := sorry

theorem is_coatom.of_is_coatom_coe_Ici {α : Type u_1} [order_top α] {x : α} {a : ↥(set.Ici x)} (ha : is_coatom a) : is_coatom ↑a := sorry

theorem is_atom.inf_eq_bot_of_ne {α : Type u_1} [semilattice_inf_bot α] {a : α} {b : α} (ha : is_atom a) (hb : is_atom b) (hab : a ≠ b) : a ⊓ b = ⊥ := sorry

theorem is_atom.disjoint_of_ne {α : Type u_1} [semilattice_inf_bot α] {a : α} {b : α} (ha : is_atom a) (hb : is_atom b) (hab : a ≠ b) : disjoint a b :=
  iff.mpr disjoint_iff (is_atom.inf_eq_bot_of_ne ha hb hab)

theorem is_coatom.sup_eq_top_of_ne {α : Type u_1} [semilattice_sup_top α] {a : α} {b : α} (ha : is_coatom a) (hb : is_coatom b) (hab : a ≠ b) : a ⊔ b = ⊤ := sorry

@[simp] theorem is_coatom_dual_iff_is_atom {α : Type u_1} [bounded_lattice α] {a : α} : is_coatom (coe_fn order_dual.to_dual a) ↔ is_atom a :=
  iff.refl (is_coatom (coe_fn order_dual.to_dual a))

@[simp] theorem is_atom_dual_iff_is_coatom {α : Type u_1} [bounded_lattice α] {a : α} : is_atom (coe_fn order_dual.to_dual a) ↔ is_coatom a :=
  iff.refl (is_atom (coe_fn order_dual.to_dual a))

/-- A lattice is atomic iff every element other than `⊥` has an atom below it. -/
class is_atomic (α : Type u_1) [bounded_lattice α] 
where
  eq_bot_or_exists_atom_le : ∀ (b : α), b = ⊥ ∨ ∃ (a : α), is_atom a ∧ a ≤ b

/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
class is_coatomic (α : Type u_1) [bounded_lattice α] 
where
  eq_top_or_exists_le_coatom : ∀ (b : α), b = ⊤ ∨ ∃ (a : α), is_coatom a ∧ b ≤ a

@[simp] theorem is_coatomic_dual_iff_is_atomic {α : Type u_1} [bounded_lattice α] : is_coatomic (order_dual α) ↔ is_atomic α :=
  { mp := fun (h : is_coatomic (order_dual α)) => is_atomic.mk fun (b : α) => eq_top_or_exists_le_coatom b,
    mpr := fun (h : is_atomic α) => is_coatomic.mk fun (b : order_dual α) => eq_bot_or_exists_atom_le b }

@[simp] theorem is_atomic_dual_iff_is_coatomic {α : Type u_1} [bounded_lattice α] : is_atomic (order_dual α) ↔ is_coatomic α :=
  { mp := fun (h : is_atomic (order_dual α)) => is_coatomic.mk fun (b : α) => eq_bot_or_exists_atom_le b,
    mpr := fun (h : is_coatomic α) => is_atomic.mk fun (b : order_dual α) => eq_top_or_exists_le_coatom b }

namespace is_atomic


protected instance is_coatomic_dual {α : Type u_1} [bounded_lattice α] [h : is_atomic α] : is_coatomic (order_dual α) :=
  iff.mpr is_coatomic_dual_iff_is_atomic h

protected instance set.Iic.is_atomic {α : Type u_1} [bounded_lattice α] [is_atomic α] {x : α} : is_atomic ↥(set.Iic x) :=
  mk fun (_x : ↥(set.Iic x)) => sorry

end is_atomic


namespace is_coatomic


protected instance is_coatomic {α : Type u_1} [bounded_lattice α] [h : is_coatomic α] : is_atomic (order_dual α) :=
  iff.mpr is_atomic_dual_iff_is_coatomic h

protected instance set.Ici.is_coatomic {α : Type u_1} [bounded_lattice α] [is_coatomic α] {x : α} : is_coatomic ↥(set.Ici x) :=
  mk fun (_x : ↥(set.Ici x)) => sorry

end is_coatomic


theorem is_atomic_iff_forall_is_atomic_Iic {α : Type u_1} [bounded_lattice α] : is_atomic α ↔ ∀ (x : α), is_atomic ↥(set.Iic x) := sorry

theorem is_coatomic_iff_forall_is_coatomic_Ici {α : Type u_1} [bounded_lattice α] : is_coatomic α ↔ ∀ (x : α), is_coatomic ↥(set.Ici x) :=
  iff.trans (iff.symm is_atomic_dual_iff_is_coatomic)
    (iff.trans is_atomic_iff_forall_is_atomic_Iic
      (forall_congr fun (x : order_dual α) => iff.trans (iff.symm is_coatomic_dual_iff_is_atomic) iff.rfl))

/-- A lattice is atomistic iff every element is a `Sup` of a set of atoms. -/
class is_atomistic (α : Type u_1) [complete_lattice α] 
where
  eq_Sup_atoms : ∀ (b : α), ∃ (s : set α), b = Sup s ∧ ∀ (a : α), a ∈ s → is_atom a

/-- A lattice is coatomistic iff every element is an `Inf` of a set of coatoms. -/
class is_coatomistic (α : Type u_1) [complete_lattice α] 
where
  eq_Inf_coatoms : ∀ (b : α), ∃ (s : set α), b = Inf s ∧ ∀ (a : α), a ∈ s → is_coatom a

@[simp] theorem is_coatomistic_dual_iff_is_atomistic {α : Type u_1} [complete_lattice α] : is_coatomistic (order_dual α) ↔ is_atomistic α :=
  { mp := fun (h : is_coatomistic (order_dual α)) => is_atomistic.mk fun (b : α) => eq_Inf_coatoms b,
    mpr := fun (h : is_atomistic α) => is_coatomistic.mk fun (b : order_dual α) => eq_Sup_atoms b }

@[simp] theorem is_atomistic_dual_iff_is_coatomistic {α : Type u_1} [complete_lattice α] : is_atomistic (order_dual α) ↔ is_coatomistic α :=
  { mp := fun (h : is_atomistic (order_dual α)) => is_coatomistic.mk fun (b : α) => eq_Sup_atoms b,
    mpr := fun (h : is_coatomistic α) => is_atomistic.mk fun (b : order_dual α) => eq_Inf_coatoms b }

namespace is_atomistic


protected instance is_coatomistic_dual {α : Type u_1} [complete_lattice α] [h : is_atomistic α] : is_coatomistic (order_dual α) :=
  iff.mpr is_coatomistic_dual_iff_is_atomistic h

protected instance is_atomic {α : Type u_1} [complete_lattice α] [is_atomistic α] : is_atomic α := sorry

end is_atomistic


namespace is_coatomistic


protected instance is_atomistic_dual {α : Type u_1} [complete_lattice α] [h : is_coatomistic α] : is_atomistic (order_dual α) :=
  iff.mpr is_atomistic_dual_iff_is_coatomistic h

protected instance is_coatomic {α : Type u_1} [complete_lattice α] [is_coatomistic α] : is_coatomic α := sorry

end is_coatomistic


/-- A lattice is simple iff it has only two elements, `⊥` and `⊤`. -/
class is_simple_lattice (α : Type u_2) [bounded_lattice α] 
extends nontrivial α
where
  eq_bot_or_eq_top : ∀ (a : α), a = ⊥ ∨ a = ⊤

theorem is_simple_lattice_iff_is_simple_lattice_order_dual {α : Type u_1} [bounded_lattice α] : is_simple_lattice α ↔ is_simple_lattice (order_dual α) := sorry

protected instance order_dual.is_simple_lattice {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] : is_simple_lattice (order_dual α) :=
  iff.mp is_simple_lattice_iff_is_simple_lattice_order_dual _inst_2

@[simp] theorem is_atom_top {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] : is_atom ⊤ :=
  { left := top_ne_bot, right := fun (a : α) (ha : a < ⊤) => or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha) }

@[simp] theorem is_coatom_bot {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] : is_coatom ⊥ :=
  iff.mp is_atom_dual_iff_is_coatom is_atom_top

namespace is_simple_lattice


/-- A simple `bounded_lattice` is also distributive. -/
protected instance bounded_distrib_lattice {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] : bounded_distrib_lattice α :=
  bounded_distrib_lattice.mk bounded_lattice.sup bounded_lattice.le bounded_lattice.lt sorry sorry sorry sorry sorry sorry
    bounded_lattice.inf sorry sorry sorry sorry bounded_lattice.top sorry bounded_lattice.bot sorry

protected instance is_atomic {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] : is_atomic α :=
  is_atomic.mk
    fun (b : α) =>
      or.imp_right (fun (h : b = ⊤) => Exists.intro ⊤ { left := is_atom_top, right := ge_of_eq h }) (eq_bot_or_eq_top b)

protected instance is_coatomic {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] : is_coatomic α :=
  iff.mp is_atomic_dual_iff_is_coatomic is_simple_lattice.is_atomic

/-- Every simple lattice is order-isomorphic to `bool`. -/
def order_iso_bool {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] [DecidableEq α] : α ≃o Bool :=
  rel_iso.mk (equiv.mk (fun (x : α) => to_bool (x = ⊤)) (fun (x : Bool) => cond x ⊤ ⊥) sorry sorry) sorry

protected instance fintype {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] [DecidableEq α] : fintype α :=
  fintype.of_equiv Bool (equiv.symm (rel_iso.to_equiv order_iso_bool))

/-- A simple `bounded_lattice` is also a `boolean_algebra`. -/
protected def boolean_algebra {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] [DecidableEq α] : boolean_algebra α :=
  boolean_algebra.mk bounded_distrib_lattice.sup bounded_distrib_lattice.le bounded_distrib_lattice.lt sorry sorry sorry
    sorry sorry sorry bounded_distrib_lattice.inf sorry sorry sorry sorry bounded_distrib_lattice.top sorry
    bounded_distrib_lattice.bot sorry (fun (x : α) => ite (x = ⊥) ⊤ ⊥) (fun (x y : α) => ite (x = ⊤ ∧ y = ⊥) ⊤ ⊥) sorry
    sorry sorry

/-- A simple `bounded_lattice` is also complete. -/
protected def complete_lattice {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] : complete_lattice α :=
  complete_lattice.mk bounded_lattice.sup bounded_lattice.le bounded_lattice.lt sorry sorry sorry sorry sorry sorry
    bounded_lattice.inf sorry sorry sorry bounded_lattice.top sorry bounded_lattice.bot sorry
    (fun (s : set α) => ite (⊤ ∈ s) ⊤ ⊥) (fun (s : set α) => ite (⊥ ∈ s) ⊥ ⊤) sorry sorry sorry sorry

/-- A simple `bounded_lattice` is also a `complete_boolean_algebra`. -/
protected def complete_boolean_algebra {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] : complete_boolean_algebra α :=
  complete_boolean_algebra.mk complete_lattice.sup complete_lattice.le complete_lattice.lt sorry sorry sorry sorry sorry
    sorry complete_lattice.inf sorry sorry sorry sorry complete_lattice.top sorry complete_lattice.bot sorry
    boolean_algebra.compl boolean_algebra.sdiff sorry sorry sorry complete_lattice.Sup complete_lattice.Inf sorry sorry
    sorry sorry sorry sorry

end is_simple_lattice


namespace is_simple_lattice


protected instance is_atomistic {α : Type u_1} [complete_lattice α] [is_simple_lattice α] : is_atomistic α :=
  is_atomistic.mk
    fun (b : α) =>
      or.elim (eq_bot_or_eq_top b)
        (fun (h : b = ⊥) =>
          Exists.intro ∅
            { left := Eq.trans h (Eq.symm Sup_empty),
              right := fun (a : α) (ha : a ∈ ∅) => false.elim (set.not_mem_empty a ha) })
        fun (h : b = ⊤) =>
          Exists.intro (singleton ⊤)
            { left := Eq.trans h (Eq.symm Sup_singleton),
              right := fun (a : α) (ha : a ∈ singleton ⊤) => Eq.symm (iff.mp set.mem_singleton_iff ha) ▸ is_atom_top }

protected instance is_coatomistic {α : Type u_1} [complete_lattice α] [is_simple_lattice α] : is_coatomistic α :=
  iff.mp is_atomistic_dual_iff_is_coatomistic is_simple_lattice.is_atomistic

end is_simple_lattice


namespace fintype


namespace is_simple_lattice


theorem univ {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] [DecidableEq α] : finset.univ = insert ⊤ (singleton ⊥) := sorry

theorem card {α : Type u_1} [bounded_lattice α] [is_simple_lattice α] [DecidableEq α] : card α = bit0 1 :=
  Eq.trans (of_equiv_card (equiv.symm (rel_iso.to_equiv is_simple_lattice.order_iso_bool))) card_bool

end is_simple_lattice


end fintype


namespace bool


protected instance is_simple_lattice : is_simple_lattice Bool :=
  is_simple_lattice.mk
    fun (a : Bool) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (a = ⊥ ∨ a = ⊤)) (Eq.symm (propext finset.mem_singleton))))
        (eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ singleton ⊥ ∨ a = ⊤)) (propext or.comm)))
          (eq.mpr (id (Eq._oldrec (Eq.refl (a = ⊤ ∨ a ∈ singleton ⊥)) (Eq.symm (propext finset.mem_insert))))
            (eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ insert ⊤ (singleton ⊥))) top_eq_tt))
              (eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ insert tt (singleton ⊥))) bot_eq_ff))
                (eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ insert tt (singleton false))) (Eq.symm fintype.univ_bool)))
                  (finset.mem_univ a))))))

end bool


theorem is_simple_lattice_iff_is_atom_top {α : Type u_1} [bounded_lattice α] : is_simple_lattice α ↔ is_atom ⊤ := sorry

theorem is_simple_lattice_iff_is_coatom_bot {α : Type u_1} [bounded_lattice α] : is_simple_lattice α ↔ is_coatom ⊥ :=
  iff.trans is_simple_lattice_iff_is_simple_lattice_order_dual is_simple_lattice_iff_is_atom_top

namespace set


theorem is_simple_lattice_Iic_iff_is_atom {α : Type u_1} [bounded_lattice α] {a : α} : is_simple_lattice ↥(Iic a) ↔ is_atom a := sorry

theorem is_simple_lattice_Ici_iff_is_coatom {α : Type u_1} [bounded_lattice α] {a : α} : is_simple_lattice ↥(Ici a) ↔ is_coatom a := sorry

end set


namespace order_iso


@[simp] theorem is_atom_iff {α : Type u_1} [bounded_lattice α] {β : Type u_2} [bounded_lattice β] (f : α ≃o β) (a : α) : is_atom (coe_fn f a) ↔ is_atom a := sorry

@[simp] theorem is_coatom_iff {α : Type u_1} [bounded_lattice α] {β : Type u_2} [bounded_lattice β] (f : α ≃o β) (a : α) : is_coatom (coe_fn f a) ↔ is_coatom a :=
  is_atom_iff (order_iso.dual f) a

theorem is_simple_lattice_iff {α : Type u_1} [bounded_lattice α] {β : Type u_2} [bounded_lattice β] (f : α ≃o β) : is_simple_lattice α ↔ is_simple_lattice β := sorry

theorem is_simple_lattice {α : Type u_1} [bounded_lattice α] {β : Type u_2} [bounded_lattice β] [h : is_simple_lattice β] (f : α ≃o β) : is_simple_lattice α :=
  iff.mpr (is_simple_lattice_iff f) h

end order_iso


namespace is_compl


theorem is_atom_iff_is_coatom {α : Type u_1} [bounded_lattice α] [is_modular_lattice α] {a : α} {b : α} (hc : is_compl a b) : is_atom a ↔ is_coatom b :=
  iff.trans (iff.symm set.is_simple_lattice_Iic_iff_is_atom)
    (iff.trans (order_iso.is_simple_lattice_iff (Iic_order_iso_Ici hc)) set.is_simple_lattice_Ici_iff_is_coatom)

theorem is_coatom_iff_is_atom {α : Type u_1} [bounded_lattice α] [is_modular_lattice α] {a : α} {b : α} (hc : is_compl a b) : is_coatom a ↔ is_atom b :=
  iff.symm (is_atom_iff_is_coatom (is_compl.symm hc))

