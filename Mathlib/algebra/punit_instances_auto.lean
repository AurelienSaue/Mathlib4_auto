/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Instances on punit.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.module.basic
import PostPort

universes u_1 u 

namespace Mathlib

namespace punit


protected instance comm_group : comm_group PUnit :=
  comm_group.mk (fun (_x _x : PUnit) => PUnit.unit) sorry PUnit.unit sorry sorry (fun (_x : PUnit) => PUnit.unit)
    (fun (_x _x : PUnit) => PUnit.unit) sorry sorry

protected instance comm_ring : comm_ring PUnit :=
  comm_ring.mk add_comm_group.add add_comm_group.add_assoc add_comm_group.zero add_comm_group.zero_add
    add_comm_group.add_zero add_comm_group.neg add_comm_group.sub add_comm_group.add_left_neg add_comm_group.add_comm
    comm_group.mul comm_group.mul_assoc comm_group.one comm_group.one_mul comm_group.mul_one sorry sorry
    comm_group.mul_comm

protected instance complete_boolean_algebra : complete_boolean_algebra PUnit :=
  complete_boolean_algebra.mk (fun (_x _x : PUnit) => PUnit.unit) (fun (_x _x : PUnit) => True)
    (fun (_x _x : PUnit) => False) sorry sorry sorry sorry sorry sorry (fun (_x _x : PUnit) => PUnit.unit) sorry sorry
    sorry sorry PUnit.unit sorry PUnit.unit sorry (fun (_x : PUnit) => PUnit.unit) (fun (_x _x : PUnit) => PUnit.unit)
    sorry sorry sorry (fun (_x : set PUnit) => PUnit.unit) (fun (_x : set PUnit) => PUnit.unit) sorry sorry sorry sorry
    sorry sorry

protected instance canonically_ordered_add_monoid : canonically_ordered_add_monoid PUnit :=
  canonically_ordered_add_monoid.mk comm_ring.add comm_ring.add_assoc comm_ring.zero comm_ring.zero_add comm_ring.add_zero
    comm_ring.add_comm complete_boolean_algebra.le complete_boolean_algebra.lt complete_boolean_algebra.le_refl
    complete_boolean_algebra.le_trans complete_boolean_algebra.le_antisymm sorry sorry complete_boolean_algebra.bot
    complete_boolean_algebra.bot_le sorry

protected instance linear_ordered_cancel_add_comm_monoid : linear_ordered_cancel_add_comm_monoid PUnit :=
  linear_ordered_cancel_add_comm_monoid.mk canonically_ordered_add_monoid.add canonically_ordered_add_monoid.add_assoc
    sorry canonically_ordered_add_monoid.zero canonically_ordered_add_monoid.zero_add
    canonically_ordered_add_monoid.add_zero canonically_ordered_add_monoid.add_comm sorry
    canonically_ordered_add_monoid.le canonically_ordered_add_monoid.lt canonically_ordered_add_monoid.le_refl
    canonically_ordered_add_monoid.le_trans canonically_ordered_add_monoid.le_antisymm
    canonically_ordered_add_monoid.add_le_add_left sorry sorry (fun (_x _x : PUnit) => decidable.true) punit.decidable_eq
    fun (_x _x : PUnit) => decidable.false

protected instance semimodule (R : Type u) [semiring R] : semimodule R PUnit :=
  semimodule.of_core (semimodule.core.mk (has_scalar.mk fun (_x : R) (_x : PUnit) => PUnit.unit) sorry sorry sorry sorry)

@[simp] theorem zero_eq : 0 = PUnit.unit :=
  rfl

@[simp] theorem one_eq : 1 = PUnit.unit :=
  rfl

@[simp] theorem add_eq (x : PUnit) (y : PUnit) : x + y = PUnit.unit :=
  rfl

@[simp] theorem mul_eq (x : PUnit) (y : PUnit) : x * y = PUnit.unit :=
  rfl

@[simp] theorem sub_eq (x : PUnit) (y : PUnit) : x - y = PUnit.unit :=
  rfl

@[simp] theorem neg_eq (x : PUnit) : -x = PUnit.unit :=
  rfl

@[simp] theorem inv_eq (x : PUnit) : x⁻¹ = PUnit.unit :=
  rfl

theorem smul_eq (x : PUnit) (y : PUnit) : x • y = PUnit.unit :=
  rfl

@[simp] theorem top_eq : ⊤ = PUnit.unit :=
  rfl

@[simp] theorem bot_eq : ⊥ = PUnit.unit :=
  rfl

@[simp] theorem sup_eq (x : PUnit) (y : PUnit) : x ⊔ y = PUnit.unit :=
  rfl

@[simp] theorem inf_eq (x : PUnit) (y : PUnit) : x ⊓ y = PUnit.unit :=
  rfl

@[simp] theorem Sup_eq (s : set PUnit) : Sup s = PUnit.unit :=
  rfl

@[simp] theorem Inf_eq (s : set PUnit) : Inf s = PUnit.unit :=
  rfl

@[simp] protected theorem le (x : PUnit) (y : PUnit) : x ≤ y :=
  trivial

@[simp] theorem not_lt (x : PUnit) (y : PUnit) : ¬x < y :=
  not_false

