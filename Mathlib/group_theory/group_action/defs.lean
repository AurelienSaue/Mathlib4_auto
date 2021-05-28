/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.basic
import Mathlib.algebra.group.defs
import Mathlib.algebra.group.hom
import Mathlib.logic.embedding
import Mathlib.PostPort

universes u v l u_1 u_2 u_3 w 

namespace Mathlib

/-!
# Definitions of group actions

This file defines a hierarchy of group action type-classes:

* `has_scalar α β`
* `mul_action α β`
* `distrib_mul_action α β`

The hierarchy is extended further by `semimodule`, defined elsewhere.

Also provided are type-classes regarding the interaction of different group actions,

* `smul_comm_class M N α`
* `is_scalar_tower M N α`

## Notation

`a • b` is used as notation for `smul a b`.

## Implementation details

This file should avoid depending on other parts of `group_theory`, to avoid import cycles.
More sophisticated lemmas belong in `group_theory.group_action`.
-/

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) 
where
  smul : α → γ → γ

infixr:73 " • " => Mathlib.has_scalar.smul

/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
class mul_action (α : Type u) (β : Type v) [monoid α] 
extends has_scalar α β
where
  one_smul : ∀ (b : β), 1 • b = b
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

/-- A typeclass mixin saying that two actions on the same space commute. -/
class smul_comm_class (M : Type u_1) (N : Type u_2) (α : Type u_3) [has_scalar M α] [has_scalar N α] 
where
  smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a

/-- Commutativity of actions is a symmetric relation. This lemma can't be an instance because this
would cause a loop in the instance search graph. -/
theorem smul_comm_class.symm (M : Type u_1) (N : Type u_2) (α : Type u_3) [has_scalar M α] [has_scalar N α] [smul_comm_class M N α] : smul_comm_class N M α :=
  smul_comm_class.mk fun (a' : N) (a : M) (b : α) => Eq.symm (smul_comm a a' b)

protected instance smul_comm_class_self (M : Type u_1) (α : Type u_2) [comm_monoid M] [mul_action M α] : smul_comm_class M M α :=
  smul_comm_class.mk
    fun (a a' : M) (b : α) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (a • a' • b = a' • a • b)) (Eq.symm (mul_smul a a' b))))
        (eq.mpr (id (Eq._oldrec (Eq.refl ((a * a') • b = a' • a • b)) (mul_comm a a')))
          (eq.mpr (id (Eq._oldrec (Eq.refl ((a' * a) • b = a' • a • b)) (mul_smul a' a b))) (Eq.refl (a' • a • b))))

/-- An instance of `is_scalar_tower M N α` states that the multiplicative
action of `M` on `α` is determined by the multiplicative actions of `M` on `N`
and `N` on `α`. -/
class is_scalar_tower (M : Type u_1) (N : Type u_2) (α : Type u_3) [has_scalar M N] [has_scalar N α] [has_scalar M α] 
where
  smul_assoc : ∀ (x : M) (y : N) (z : α), (x • y) • z = x • y • z

@[simp] theorem smul_assoc {α : Type u} {M : Type u_1} {N : Type u_2} [has_scalar M N] [has_scalar N α] [has_scalar M α] [is_scalar_tower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z :=
  is_scalar_tower.smul_assoc x y z

theorem smul_smul {α : Type u} {β : Type v} [monoid α] [mul_action α β] (a₁ : α) (a₂ : α) (b : β) : a₁ • a₂ • b = (a₁ * a₂) • b :=
  Eq.symm (mul_smul a₁ a₂ b)

@[simp] theorem one_smul (α : Type u) {β : Type v} [monoid α] [mul_action α β] (b : β) : 1 • b = b :=
  mul_action.one_smul b

/-- Pullback a multiplicative action along an injective map respecting `•`. -/
protected def function.injective.mul_action {α : Type u} {β : Type v} {γ : Type w} [monoid α] [mul_action α β] [has_scalar α γ] (f : γ → β) (hf : function.injective f) (smul : ∀ (c : α) (x : γ), f (c • x) = c • f x) : mul_action α γ :=
  mul_action.mk sorry sorry

/-- Pushforward a multiplicative action along a surjective map respecting `•`. -/
protected def function.surjective.mul_action {α : Type u} {β : Type v} {γ : Type w} [monoid α] [mul_action α β] [has_scalar α γ] (f : β → γ) (hf : function.surjective f) (smul : ∀ (c : α) (x : β), f (c • x) = c • f x) : mul_action α γ :=
  mul_action.mk sorry sorry

theorem ite_smul {α : Type u} {β : Type v} [monoid α] [mul_action α β] (p : Prop) [Decidable p] (a₁ : α) (a₂ : α) (b : β) : ite p a₁ a₂ • b = ite p (a₁ • b) (a₂ • b) := sorry

theorem smul_ite {α : Type u} {β : Type v} [monoid α] [mul_action α β] (p : Prop) [Decidable p] (a : α) (b₁ : β) (b₂ : β) : a • ite p b₁ b₂ = ite p (a • b₁) (a • b₂) := sorry

namespace mul_action


/-- The regular action of a monoid on itself by left multiplication. -/
def regular (α : Type u) [monoid α] : mul_action α α :=
  mk sorry sorry

protected instance is_scalar_tower.left (α : Type u) {β : Type v} [monoid α] [mul_action α β] : is_scalar_tower α α β :=
  is_scalar_tower.mk fun (x y : α) (z : β) => mul_smul x y z

/-- Embedding induced by action. -/
def to_fun (α : Type u) (β : Type v) [monoid α] [mul_action α β] : β ↪ α → β :=
  function.embedding.mk (fun (y : β) (x : α) => x • y) sorry

@[simp] theorem to_fun_apply {α : Type u} {β : Type v} [monoid α] [mul_action α β] (x : α) (y : β) : coe_fn (to_fun α β) y x = x • y :=
  rfl

/-- An action of `α` on `β` and a monoid homomorphism `γ → α` induce an action of `γ` on `β`. -/
def comp_hom {α : Type u} (β : Type v) {γ : Type w} [monoid α] [mul_action α β] [monoid γ] (g : γ →* α) : mul_action γ β :=
  mk sorry sorry

end mul_action


@[simp] theorem smul_one_smul {α : Type u} {M : Type u_1} (N : Type u_2) [monoid N] [has_scalar M N] [mul_action N α] [has_scalar M α] [is_scalar_tower M N α] (x : M) (y : α) : (x • 1) • y = x • y :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((x • 1) • y = x • y)) (smul_assoc x 1 y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x • 1 • y = x • y)) (one_smul N y))) (Eq.refl (x • y)))

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
class distrib_mul_action (α : Type u) (β : Type v) [monoid α] [add_monoid β] 
extends mul_action α β
where
  smul_add : ∀ (r : α) (x y : β), r • (x + y) = r • x + r • y
  smul_zero : ∀ (r : α), r • 0 = 0

theorem smul_add {α : Type u} {β : Type v} [monoid α] [add_monoid β] [distrib_mul_action α β] (a : α) (b₁ : β) (b₂ : β) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
  distrib_mul_action.smul_add a b₁ b₂

@[simp] theorem smul_zero {α : Type u} {β : Type v} [monoid α] [add_monoid β] [distrib_mul_action α β] (a : α) : a • 0 = 0 :=
  distrib_mul_action.smul_zero a

/-- Pullback a distributive multiplicative action along an injective additive monoid
homomorphism. -/
protected def function.injective.distrib_mul_action {α : Type u} {β : Type v} {γ : Type w} [monoid α] [add_monoid β] [distrib_mul_action α β] [add_monoid γ] [has_scalar α γ] (f : γ →+ β) (hf : function.injective ⇑f) (smul : ∀ (c : α) (x : γ), coe_fn f (c • x) = c • coe_fn f x) : distrib_mul_action α γ :=
  distrib_mul_action.mk sorry sorry

/-- Pushforward a distributive multiplicative action along a surjective additive monoid
homomorphism.-/
protected def function.surjective.distrib_mul_action {α : Type u} {β : Type v} {γ : Type w} [monoid α] [add_monoid β] [distrib_mul_action α β] [add_monoid γ] [has_scalar α γ] (f : β →+ γ) (hf : function.surjective ⇑f) (smul : ∀ (c : α) (x : β), coe_fn f (c • x) = c • coe_fn f x) : distrib_mul_action α γ :=
  distrib_mul_action.mk sorry sorry

/-- Scalar multiplication by `r` as an `add_monoid_hom`. -/
def const_smul_hom {α : Type u} (β : Type v) [monoid α] [add_monoid β] [distrib_mul_action α β] (r : α) : β →+ β :=
  add_monoid_hom.mk (has_scalar.smul r) (smul_zero r) (smul_add r)

@[simp] theorem const_smul_hom_apply {α : Type u} {β : Type v} [monoid α] [add_monoid β] [distrib_mul_action α β] (r : α) (x : β) : coe_fn (const_smul_hom β r) x = r • x :=
  rfl

@[simp] theorem smul_neg {α : Type u} {β : Type v} [monoid α] [add_group β] [distrib_mul_action α β] (r : α) (x : β) : r • -x = -(r • x) := sorry

theorem smul_sub {α : Type u} {β : Type v} [monoid α] [add_group β] [distrib_mul_action α β] (r : α) (x : β) (y : β) : r • (x - y) = r • x - r • y := sorry

