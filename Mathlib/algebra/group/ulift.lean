/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.mul_add
import Mathlib.PostPort

universes u u_1 v 

namespace Mathlib

/-!
# `ulift` instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We use `tactic.pi_instance_derive_field`, even though it wasn't intended for this purpose,
which seems to work fine.

We also provide `ulift.mul_equiv : ulift R ≃* R` (and its additive analogue).
-/

namespace ulift


protected instance has_one {α : Type u} [HasOne α] : HasOne (ulift α) :=
  { one := up 1 }

@[simp] theorem one_down {α : Type u} [HasOne α] : down 1 = 1 :=
  rfl

protected instance has_mul {α : Type u} [Mul α] : Mul (ulift α) :=
  { mul := fun (f g : ulift α) => up (down f * down g) }

@[simp] theorem add_down {α : Type u} {x : ulift α} {y : ulift α} [Add α] : down (x + y) = down x + down y :=
  rfl

protected instance has_sub {α : Type u} [Sub α] : Sub (ulift α) :=
  { sub := fun (f g : ulift α) => up (down f - down g) }

@[simp] theorem sub_down {α : Type u} {x : ulift α} {y : ulift α} [Sub α] : down (x - y) = down x - down y :=
  rfl

protected instance has_inv {α : Type u} [has_inv α] : has_inv (ulift α) :=
  has_inv.mk fun (f : ulift α) => up (down f⁻¹)

@[simp] theorem neg_down {α : Type u} {x : ulift α} [Neg α] : down (-x) = -down x :=
  rfl

protected instance add_semigroup {α : Type u} [add_semigroup α] : add_semigroup (ulift α) :=
  add_semigroup.mk Add.add sorry

/--
The multiplicative equivalence between `ulift α` and `α`.
-/
def mul_equiv {α : Type u} [semigroup α] : ulift α ≃* α :=
  mul_equiv.mk down up sorry sorry sorry

protected instance add_comm_semigroup {α : Type u} [add_comm_semigroup α] : add_comm_semigroup (ulift α) :=
  add_comm_semigroup.mk Add.add sorry sorry

protected instance monoid {α : Type u} [monoid α] : monoid (ulift α) :=
  monoid.mk Mul.mul sorry 1 sorry sorry

protected instance comm_monoid {α : Type u} [comm_monoid α] : comm_monoid (ulift α) :=
  comm_monoid.mk Mul.mul sorry 1 sorry sorry sorry

protected instance group {α : Type u} [group α] : group (ulift α) :=
  group.mk Mul.mul sorry 1 sorry sorry has_inv.inv Div.div sorry

protected instance comm_group {α : Type u} [comm_group α] : comm_group (ulift α) :=
  comm_group.mk Mul.mul sorry 1 sorry sorry has_inv.inv Div.div sorry sorry

protected instance left_cancel_semigroup {α : Type u} [left_cancel_semigroup α] : left_cancel_semigroup (ulift α) :=
  left_cancel_semigroup.mk Mul.mul sorry sorry

protected instance right_cancel_semigroup {α : Type u} [right_cancel_semigroup α] : right_cancel_semigroup (ulift α) :=
  right_cancel_semigroup.mk Mul.mul sorry sorry

