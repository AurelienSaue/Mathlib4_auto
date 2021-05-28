/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.rel_iso
import Mathlib.order.lattice_intervals
import Mathlib.order.order_dual
import PostPort

universes u_2 l u_1 

namespace Mathlib

/-!
# Modular Lattices
This file defines Modular Lattices, a kind of lattice useful in algebra.
For examples, look to the subobject lattices of abelian groups, submodules, and ideals, or consider
any distributive lattice.

## Main Definitions
- `is_modular_lattice` defines a modular lattice to be one such that
  `x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z)`
- `inf_Icc_order_iso_Icc_sup` gives an order isomorphism between the intervals
  `[a ⊓ b, a]` and `[b, a ⊔ b]`.
  This corresponds to the diamond (or second) isomorphism theorems of algebra.

## Main Results
- `is_modular_lattice_iff_sup_inf_sup_assoc`:
  Modularity is equivalent to the `sup_inf_sup_assoc`: `(x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z`
- `distrib_lattice.is_modular_lattice`: Distributive lattices are modular.

## To do
- Relate atoms and coatoms in modular lattices

-/

/-- A modular lattice is one with a limited associativity between `⊓` and `⊔`. -/
class is_modular_lattice (α : Type u_2) [lattice α] 
where
  sup_inf_le_assoc_of_le : ∀ {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z

theorem sup_inf_assoc_of_le {α : Type u_1} [lattice α] [is_modular_lattice α] {x : α} (y : α) {z : α} (h : x ≤ z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z :=
  le_antisymm (is_modular_lattice.sup_inf_le_assoc_of_le y h)
    (le_inf (sup_le_sup_left inf_le_left x) (sup_le h inf_le_right))

theorem is_modular_lattice.sup_inf_sup_assoc {α : Type u_1} [lattice α] [is_modular_lattice α] {x : α} {y : α} {z : α} : x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z :=
  Eq.symm (sup_inf_assoc_of_le y inf_le_right)

theorem inf_sup_assoc_of_le {α : Type u_1} [lattice α] [is_modular_lattice α] {x : α} (y : α) {z : α} (h : z ≤ x) : x ⊓ y ⊔ z = x ⊓ (y ⊔ z) := sorry

protected instance order_dual.is_modular_lattice {α : Type u_1} [lattice α] [is_modular_lattice α] : is_modular_lattice (order_dual α) :=
  is_modular_lattice.mk
    fun (x y z : order_dual α) (xz : x ≤ z) =>
      le_of_eq
        (eq.mpr (id (Eq._oldrec (Eq.refl ((x ⊔ y) ⊓ z = x ⊔ y ⊓ z)) inf_comm))
          (eq.mpr (id (Eq._oldrec (Eq.refl (z ⊓ (x ⊔ y) = x ⊔ y ⊓ z)) sup_comm))
            (eq.mpr (id (Eq._oldrec (Eq.refl (z ⊓ (y ⊔ x) = x ⊔ y ⊓ z)) (propext eq_comm)))
              (eq.mpr (id (Eq._oldrec (Eq.refl (x ⊔ y ⊓ z = z ⊓ (y ⊔ x))) inf_comm))
                (eq.mpr (id (Eq._oldrec (Eq.refl (x ⊔ z ⊓ y = z ⊓ (y ⊔ x))) sup_comm))
                  (eq.mpr
                    ((fun (a a_1 : order_dual α) (e_1 : a = a_1) (ᾰ ᾰ_1 : order_dual α) (e_2 : ᾰ = ᾰ_1) =>
                        congr (congr_arg Eq e_1) e_2)
                      (z ⊓ y ⊔ x) ((z ⊔ coe_fn order_dual.of_dual y) ⊓ x) (Eq.refl (z ⊓ y ⊔ x)) (z ⊓ (y ⊔ x))
                      (z ⊔ coe_fn order_dual.of_dual y ⊓ x) (Eq.refl (z ⊓ (y ⊔ x))))
                    (sup_inf_assoc_of_le (coe_fn order_dual.of_dual y) (iff.mpr order_dual.dual_le xz))))))))

/-- The diamond isomorphism between the intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` -/
def inf_Icc_order_iso_Icc_sup {α : Type u_1} [lattice α] [is_modular_lattice α] (a : α) (b : α) : ↥(set.Icc (a ⊓ b) a) ≃o ↥(set.Icc b (a ⊔ b)) :=
  rel_iso.mk
    (equiv.mk (fun (x : ↥(set.Icc (a ⊓ b) a)) => { val := ↑x ⊔ b, property := sorry })
      (fun (x : ↥(set.Icc b (a ⊔ b))) => { val := a ⊓ ↑x, property := sorry }) sorry sorry)
    sorry

namespace is_compl


/-- The diamond isomorphism between the intervals `set.Iic a` and `set.Ici b`. -/
def Iic_order_iso_Ici {α : Type u_1} [bounded_lattice α] [is_modular_lattice α] {a : α} {b : α} (h : is_compl a b) : ↥(set.Iic a) ≃o ↥(set.Ici b) :=
  order_iso.trans (order_iso.set_congr (set.Iic a) (set.Icc (a ⊓ b) a) sorry)
    (order_iso.trans (inf_Icc_order_iso_Icc_sup a b) (order_iso.set_congr (set.Icc b (a ⊔ b)) (set.Ici b) sorry))

end is_compl


theorem is_modular_lattice_iff_sup_inf_sup_assoc {α : Type u_1} [lattice α] : is_modular_lattice α ↔ ∀ (x y z : α), x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z := sorry

namespace distrib_lattice


protected instance is_modular_lattice {α : Type u_1} [distrib_lattice α] : is_modular_lattice α :=
  is_modular_lattice.mk
    fun (x y z : α) (xz : x ≤ z) =>
      eq.mpr (id (Eq._oldrec (Eq.refl ((x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z)) inf_sup_right))
        (eq.mpr (id (Eq._oldrec (Eq.refl (x ⊓ z ⊔ y ⊓ z ≤ x ⊔ y ⊓ z)) (iff.mpr inf_eq_left xz))) (le_refl (x ⊔ y ⊓ z)))

end distrib_lattice


namespace is_modular_lattice


protected instance is_modular_lattice_Iic {α : Type u_1} [bounded_lattice α] [is_modular_lattice α] {a : α} : is_modular_lattice ↥(set.Iic a) :=
  mk fun (x y z : ↥(set.Iic a)) (xz : x ≤ z) => sup_inf_le_assoc_of_le (↑y) xz

protected instance is_modular_lattice_Ici {α : Type u_1} [bounded_lattice α] [is_modular_lattice α] {a : α} : is_modular_lattice ↥(set.Ici a) :=
  mk fun (x y z : ↥(set.Ici a)) (xz : x ≤ z) => sup_inf_le_assoc_of_le (↑y) xz

