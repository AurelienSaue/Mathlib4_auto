/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.module.basic
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Prod instances for module and multiplicative actions

This file defines instances for binary product of modules
-/

namespace prod


protected instance has_scalar {α : Type u_1} {β : Type u_2} {γ : Type u_3} [has_scalar α β]
    [has_scalar α γ] : has_scalar α (β × γ) :=
  has_scalar.mk fun (a : α) (p : β × γ) => (a • fst p, a • snd p)

@[simp] theorem smul_fst {α : Type u_1} {β : Type u_2} {γ : Type u_3} [has_scalar α β]
    [has_scalar α γ] (a : α) (x : β × γ) : fst (a • x) = a • fst x :=
  rfl

@[simp] theorem smul_snd {α : Type u_1} {β : Type u_2} {γ : Type u_3} [has_scalar α β]
    [has_scalar α γ] (a : α) (x : β × γ) : snd (a • x) = a • snd x :=
  rfl

@[simp] theorem smul_mk {α : Type u_1} {β : Type u_2} {γ : Type u_3} [has_scalar α β]
    [has_scalar α γ] (a : α) (b : β) (c : γ) : a • (b, c) = (a • b, a • c) :=
  rfl

protected instance semimodule {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : semiring α}
    [add_comm_monoid β] [add_comm_monoid γ] [semimodule α β] [semimodule α γ] :
    semimodule α (β × γ) :=
  semimodule.mk sorry sorry

end Mathlib