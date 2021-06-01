/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.ulift
import Mathlib.data.equiv.ring
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# `ulift` instances for ring

This file defines instances for ring, semiring and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.ring_equiv : ulift R ≃+* R`.
-/

namespace ulift


protected instance mul_zero_class {α : Type u} [mul_zero_class α] : mul_zero_class (ulift α) :=
  mul_zero_class.mk Mul.mul 0 sorry sorry

protected instance distrib {α : Type u} [distrib α] : distrib (ulift α) :=
  distrib.mk Mul.mul Add.add sorry sorry

protected instance semiring {α : Type u} [semiring α] : semiring (ulift α) :=
  semiring.mk Add.add sorry 0 sorry sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry sorry sorry

/--
The ring equivalence between `ulift α` and `α`.
-/
def ring_equiv {α : Type u} [semiring α] : ulift α ≃+* α :=
  ring_equiv.mk down up sorry sorry sorry sorry

protected instance comm_semiring {α : Type u} [comm_semiring α] : comm_semiring (ulift α) :=
  comm_semiring.mk Add.add sorry 0 sorry sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry sorry
    sorry sorry

protected instance ring {α : Type u} [ring α] : ring (ulift α) :=
  ring.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry Mul.mul sorry 1 sorry sorry sorry
    sorry

protected instance comm_ring {α : Type u} [comm_ring α] : comm_ring (ulift α) :=
  comm_ring.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry Mul.mul sorry 1 sorry sorry
    sorry sorry sorry

end Mathlib