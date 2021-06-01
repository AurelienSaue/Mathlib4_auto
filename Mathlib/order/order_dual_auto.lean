/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.basic
import Mathlib.data.equiv.basic
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Initial lemmas to work with the `order_dual`

## Definitions
`to_dual` and `of_dual` the order reversing identity maps, bundled as equivalences.

## Basic Lemmas to convert between an order and its dual

This file is similar to algebra/group/type_tags.lean
-/

namespace order_dual


protected instance nontrivial {α : Type u} [nontrivial α] : nontrivial (order_dual α) := id _inst_1

/-- `to_dual` is the identity function to the `order_dual` of a linear order.  -/
def to_dual {α : Type u} : α ≃ order_dual α := equiv.mk id id sorry sorry

/-- `of_dual` is the identity function from the `order_dual` of a linear order.  -/
def of_dual {α : Type u} : order_dual α ≃ α := equiv.symm to_dual

@[simp] theorem to_dual_symm_eq {α : Type u} : equiv.symm to_dual = of_dual := rfl

@[simp] theorem of_dual_symm_eq {α : Type u} : equiv.symm of_dual = to_dual := rfl

@[simp] theorem to_dual_of_dual {α : Type u} (a : order_dual α) :
    coe_fn to_dual (coe_fn of_dual a) = a :=
  rfl

@[simp] theorem of_dual_to_dual {α : Type u} (a : α) : coe_fn of_dual (coe_fn to_dual a) = a := rfl

@[simp] theorem to_dual_inj {α : Type u} {a : α} {b : α} :
    coe_fn to_dual a = coe_fn to_dual b ↔ a = b :=
  iff.rfl

@[simp] theorem to_dual_le_to_dual {α : Type u} [HasLessEq α] {a : α} {b : α} :
    coe_fn to_dual a ≤ coe_fn to_dual b ↔ b ≤ a :=
  iff.rfl

@[simp] theorem to_dual_lt_to_dual {α : Type u} [HasLess α] {a : α} {b : α} :
    coe_fn to_dual a < coe_fn to_dual b ↔ b < a :=
  iff.rfl

@[simp] theorem of_dual_inj {α : Type u} {a : order_dual α} {b : order_dual α} :
    coe_fn of_dual a = coe_fn of_dual b ↔ a = b :=
  iff.rfl

@[simp] theorem of_dual_le_of_dual {α : Type u} [HasLessEq α] {a : order_dual α}
    {b : order_dual α} : coe_fn of_dual a ≤ coe_fn of_dual b ↔ b ≤ a :=
  iff.rfl

@[simp] theorem of_dual_lt_of_dual {α : Type u} [HasLess α] {a : order_dual α} {b : order_dual α} :
    coe_fn of_dual a < coe_fn of_dual b ↔ b < a :=
  iff.rfl

theorem le_to_dual {α : Type u} [HasLessEq α] {a : order_dual α} {b : α} :
    a ≤ coe_fn to_dual b ↔ b ≤ coe_fn of_dual a :=
  iff.rfl

theorem lt_to_dual {α : Type u} [HasLess α] {a : order_dual α} {b : α} :
    a < coe_fn to_dual b ↔ b < coe_fn of_dual a :=
  iff.rfl

theorem to_dual_le {α : Type u} [HasLessEq α] {a : α} {b : order_dual α} :
    coe_fn to_dual a ≤ b ↔ coe_fn of_dual b ≤ a :=
  iff.rfl

theorem to_dual_lt {α : Type u} [HasLess α] {a : α} {b : order_dual α} :
    coe_fn to_dual a < b ↔ coe_fn of_dual b < a :=
  iff.rfl

end Mathlib