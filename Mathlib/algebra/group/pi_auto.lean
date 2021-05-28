/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.pi
import Mathlib.tactic.pi_instances
import Mathlib.algebra.group.defs
import Mathlib.algebra.group.hom
import PostPort

universes u v u_1 u_2 u_3 

namespace Mathlib

/-!
# Pi instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/

namespace pi


protected instance semigroup {I : Type u} {f : I → Type v} [(i : I) → semigroup (f i)] : semigroup ((i : I) → f i) :=
  semigroup.mk Mul.mul sorry

protected instance add_comm_semigroup {I : Type u} {f : I → Type v} [(i : I) → add_comm_semigroup (f i)] : add_comm_semigroup ((i : I) → f i) :=
  add_comm_semigroup.mk Add.add sorry sorry

protected instance monoid {I : Type u} {f : I → Type v} [(i : I) → monoid (f i)] : monoid ((i : I) → f i) :=
  monoid.mk Mul.mul sorry 1 sorry sorry

protected instance add_comm_monoid {I : Type u} {f : I → Type v} [(i : I) → add_comm_monoid (f i)] : add_comm_monoid ((i : I) → f i) :=
  add_comm_monoid.mk Add.add sorry 0 sorry sorry sorry

protected instance sub_neg_add_monoid {I : Type u} {f : I → Type v} [(i : I) → sub_neg_monoid (f i)] : sub_neg_monoid ((i : I) → f i) :=
  sub_neg_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry Neg.neg Sub.sub

protected instance group {I : Type u} {f : I → Type v} [(i : I) → group (f i)] : group ((i : I) → f i) :=
  group.mk Mul.mul sorry 1 sorry sorry has_inv.inv Div.div sorry

protected instance comm_group {I : Type u} {f : I → Type v} [(i : I) → comm_group (f i)] : comm_group ((i : I) → f i) :=
  comm_group.mk Mul.mul sorry 1 sorry sorry has_inv.inv Div.div sorry sorry

protected instance left_cancel_semigroup {I : Type u} {f : I → Type v} [(i : I) → left_cancel_semigroup (f i)] : left_cancel_semigroup ((i : I) → f i) :=
  left_cancel_semigroup.mk Mul.mul sorry sorry

protected instance right_cancel_semigroup {I : Type u} {f : I → Type v} [(i : I) → right_cancel_semigroup (f i)] : right_cancel_semigroup ((i : I) → f i) :=
  right_cancel_semigroup.mk Mul.mul sorry sorry

protected instance mul_zero_class {I : Type u} {f : I → Type v} [(i : I) → mul_zero_class (f i)] : mul_zero_class ((i : I) → f i) :=
  mul_zero_class.mk Mul.mul 0 sorry sorry

protected instance comm_monoid_with_zero {I : Type u} {f : I → Type v} [(i : I) → comm_monoid_with_zero (f i)] : comm_monoid_with_zero ((i : I) → f i) :=
  comm_monoid_with_zero.mk Mul.mul sorry 1 sorry sorry sorry 0 sorry sorry

@[simp] theorem const_zero {α : Type u_1} {β : Type u_2} [HasZero β] : function.const α 0 = 0 :=
  rfl

@[simp] theorem comp_one {α : Type u_1} {β : Type u_2} {γ : Type u_3} [HasOne β] {f : β → γ} : f ∘ 1 = function.const α (f 1) :=
  rfl

@[simp] theorem one_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [HasOne γ] {f : α → β} : 1 ∘ f = 1 :=
  rfl

end pi


/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism. -/
def add_monoid_hom.apply {I : Type u} (f : I → Type v) [(i : I) → add_monoid (f i)] (i : I) : ((i : I) → f i) →+ f i :=
  add_monoid_hom.mk (fun (g : (i : I) → f i) => g i) sorry sorry

@[simp] theorem add_monoid_hom.apply_apply {I : Type u} (f : I → Type v) [(i : I) → add_monoid (f i)] (i : I) (g : (i : I) → f i) : coe_fn (add_monoid_hom.apply f i) g = g i :=
  rfl

/-- Coercion of a `monoid_hom` into a function is itself a `monoid_hom`.

See also `monoid_hom.eval`. -/
@[simp] theorem monoid_hom.coe_fn_apply (α : Type u_1) (β : Type u_2) [monoid α] [comm_monoid β] (g : α →* β) : ∀ (ᾰ : α), coe_fn (monoid_hom.coe_fn α β) g ᾰ = coe_fn g ᾰ :=
  fun (ᾰ : α) => Eq.refl (coe_fn (monoid_hom.coe_fn α β) g ᾰ)

/-- The additive monoid homomorphism including a single additive monoid
into a dependent family of additive monoids, as functions supported at a point. -/
def add_monoid_hom.single {I : Type u} (f : I → Type v) [DecidableEq I] [(i : I) → add_monoid (f i)] (i : I) : f i →+ (i : I) → f i :=
  add_monoid_hom.mk (fun (x : f i) => pi.single i x) sorry sorry

@[simp] theorem add_monoid_hom.single_apply {I : Type u} (f : I → Type v) [DecidableEq I] [(i : I) → add_monoid (f i)] {i : I} (x : f i) : coe_fn (add_monoid_hom.single f i) x = pi.single i x :=
  rfl

