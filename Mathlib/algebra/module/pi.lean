/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.module.basic
import Mathlib.algebra.ring.pi
import Mathlib.PostPort

universes u v u_1 u_2 

namespace Mathlib

/-!
# Pi instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on Pi Types
-/

namespace pi


protected instance has_scalar {I : Type u} {f : I → Type v} {α : Type u_1} [(i : I) → has_scalar α (f i)] : has_scalar α ((i : I) → f i) :=
  has_scalar.mk fun (s : α) (x : (i : I) → f i) (i : I) => s • x i

@[simp] theorem smul_apply {I : Type u} {f : I → Type v} (x : (i : I) → f i) (i : I) {α : Type u_1} [(i : I) → has_scalar α (f i)] (s : α) : has_scalar.smul s x i = s • x i :=
  rfl

protected instance has_scalar' {I : Type u} {f : I → Type v} {g : I → Type u_1} [(i : I) → has_scalar (f i) (g i)] : has_scalar ((i : I) → f i) ((i : I) → g i) :=
  has_scalar.mk fun (s : (i : I) → f i) (x : (i : I) → g i) (i : I) => s i • x i

@[simp] theorem smul_apply' {I : Type u} {f : I → Type v} (i : I) {g : I → Type u_1} [(i : I) → has_scalar (f i) (g i)] (s : (i : I) → f i) (x : (i : I) → g i) : has_scalar.smul s x i = s i • x i :=
  rfl

protected instance is_scalar_tower {I : Type u} {f : I → Type v} {α : Type u_1} {β : Type u_2} [has_scalar α β] [(i : I) → has_scalar β (f i)] [(i : I) → has_scalar α (f i)] [∀ (i : I), is_scalar_tower α β (f i)] : is_scalar_tower α β ((i : I) → f i) :=
  is_scalar_tower.mk fun (x : α) (y : β) (z : (i : I) → f i) => funext fun (i : I) => smul_assoc x y (z i)

protected instance is_scalar_tower' {I : Type u} {f : I → Type v} {g : I → Type u_1} {α : Type u_2} [(i : I) → has_scalar α (f i)] [(i : I) → has_scalar (f i) (g i)] [(i : I) → has_scalar α (g i)] [∀ (i : I), is_scalar_tower α (f i) (g i)] : is_scalar_tower α ((i : I) → f i) ((i : I) → g i) :=
  is_scalar_tower.mk fun (x : α) (y : (i : I) → f i) (z : (i : I) → g i) => funext fun (i : I) => smul_assoc x (y i) (z i)

protected instance is_scalar_tower'' {I : Type u} {f : I → Type v} {g : I → Type u_1} {h : I → Type u_2} [(i : I) → has_scalar (f i) (g i)] [(i : I) → has_scalar (g i) (h i)] [(i : I) → has_scalar (f i) (h i)] [∀ (i : I), is_scalar_tower (f i) (g i) (h i)] : is_scalar_tower ((i : I) → f i) ((i : I) → g i) ((i : I) → h i) :=
  is_scalar_tower.mk
    fun (x : (i : I) → f i) (y : (i : I) → g i) (z : (i : I) → h i) => funext fun (i : I) => smul_assoc (x i) (y i) (z i)

protected instance mul_action {I : Type u} {f : I → Type v} (α : Type u_1) {m : monoid α} [(i : I) → mul_action α (f i)] : mul_action α ((i : I) → f i) :=
  mul_action.mk sorry sorry

protected instance mul_action' {I : Type u} {f : I → Type v} {g : I → Type u_1} {m : (i : I) → monoid (f i)} [(i : I) → mul_action (f i) (g i)] : mul_action ((i : I) → f i) ((i : I) → g i) :=
  mul_action.mk sorry sorry

protected instance distrib_mul_action {I : Type u} {f : I → Type v} (α : Type u_1) {m : monoid α} {n : (i : I) → add_monoid (f i)} [(i : I) → distrib_mul_action α (f i)] : distrib_mul_action α ((i : I) → f i) :=
  distrib_mul_action.mk sorry sorry

protected instance distrib_mul_action' {I : Type u} {f : I → Type v} {g : I → Type u_1} {m : (i : I) → monoid (f i)} {n : (i : I) → add_monoid (g i)} [(i : I) → distrib_mul_action (f i) (g i)] : distrib_mul_action ((i : I) → f i) ((i : I) → g i) :=
  distrib_mul_action.mk sorry sorry

protected instance semimodule (I : Type u) (f : I → Type v) (α : Type u_1) {r : semiring α} {m : (i : I) → add_comm_monoid (f i)} [(i : I) → semimodule α (f i)] : semimodule α ((i : I) → f i) :=
  semimodule.mk sorry sorry

protected instance semimodule' {I : Type u} {f : I → Type v} {g : I → Type u_1} {r : (i : I) → semiring (f i)} {m : (i : I) → add_comm_monoid (g i)} [(i : I) → semimodule (f i) (g i)] : semimodule ((i : I) → f i) ((i : I) → g i) :=
  semimodule.mk sorry sorry

