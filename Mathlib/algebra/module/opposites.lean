/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.module.linear_map
import Mathlib.algebra.opposites
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Module operations on `Mᵒᵖ`

This file contains definitions that could not be placed into `algebra.opposites` due to import
cycles.
-/

namespace opposite


/-- `opposite.distrib_mul_action` extends to a `semimodule` -/
protected instance semimodule (R : Type u) {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : semimodule R (Mᵒᵖ) :=
  semimodule.mk sorry sorry

/-- The function `op` is a linear equivalence. -/
def op_linear_equiv (R : Type u) {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : linear_equiv R M (Mᵒᵖ) :=
  linear_equiv.mk (add_equiv.to_fun op_add_equiv) sorry sorry (add_equiv.inv_fun op_add_equiv) sorry sorry

@[simp] theorem coe_op_linear_equiv (R : Type u) {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : ⇑(op_linear_equiv R) = op :=
  rfl

@[simp] theorem coe_op_linear_equiv_symm (R : Type u) {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : ⇑(linear_equiv.symm (op_linear_equiv R)) = unop :=
  rfl

@[simp] theorem coe_op_linear_equiv_to_linear_map (R : Type u) {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : ⇑(linear_equiv.to_linear_map (op_linear_equiv R)) = op :=
  rfl

@[simp] theorem coe_op_linear_equiv_symm_to_linear_map (R : Type u) {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : ⇑(linear_equiv.to_linear_map (linear_equiv.symm (op_linear_equiv R))) = unop :=
  rfl

@[simp] theorem op_linear_equiv_to_add_equiv (R : Type u) {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : linear_equiv.to_add_equiv (op_linear_equiv R) = op_add_equiv :=
  rfl

@[simp] theorem op_linear_equiv_symm_to_add_equiv (R : Type u) {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : linear_equiv.to_add_equiv (linear_equiv.symm (op_linear_equiv R)) = add_equiv.symm op_add_equiv :=
  rfl

