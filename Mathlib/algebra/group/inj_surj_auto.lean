/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.defs
import Mathlib.logic.function.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Lifting algebraic data classes along injective/surjective maps

This file provides definitions that are meant to deal with
situations such as the following:

Suppose that `G` is a group, and `H` is a type endowed with
`has_one H`, `has_mul H`, and `has_inv H`.
Suppose furthermore, that `f : G → H` is a surjective map
that respects the multiplication, and the unit elements.
Then `H` satisfies the group axioms.

The relevant definition in this case is `function.surjective.group`.
Dually, there is also `function.injective.group`.
And there are versions for (additive) (commutative) semigroups/monoids.
-/

namespace function


/-!
### Injective
-/

namespace injective


/-- A type endowed with `*` is a semigroup,
if it admits an injective map that preserves `*` to a semigroup. -/
protected def add_semigroup {M₁ : Type u_1} {M₂ : Type u_2} [Add M₁] [add_semigroup M₂]
    (f : M₁ → M₂) (hf : injective f) (mul : ∀ (x y : M₁), f (x + y) = f x + f y) :
    add_semigroup M₁ :=
  add_semigroup.mk Add.add sorry

/-- A type endowed with `*` is a commutative semigroup,
if it admits an injective map that preserves `*` to a commutative semigroup. -/
protected def comm_semigroup {M₁ : Type u_1} {M₂ : Type u_2} [Mul M₁] [comm_semigroup M₂]
    (f : M₁ → M₂) (hf : injective f) (mul : ∀ (x y : M₁), f (x * y) = f x * f y) :
    comm_semigroup M₁ :=
  comm_semigroup.mk semigroup.mul sorry sorry

/-- A type endowed with `*` is a left cancel semigroup,
if it admits an injective map that preserves `*` to a left cancel semigroup. -/
protected def add_left_cancel_semigroup {M₁ : Type u_1} {M₂ : Type u_2} [Add M₁]
    [add_left_cancel_semigroup M₂] (f : M₁ → M₂) (hf : injective f)
    (mul : ∀ (x y : M₁), f (x + y) = f x + f y) : add_left_cancel_semigroup M₁ :=
  add_left_cancel_semigroup.mk Add.add sorry sorry

/-- A type endowed with `*` is a right cancel semigroup,
if it admits an injective map that preserves `*` to a right cancel semigroup. -/
protected def right_cancel_semigroup {M₁ : Type u_1} {M₂ : Type u_2} [Mul M₁]
    [right_cancel_semigroup M₂] (f : M₁ → M₂) (hf : injective f)
    (mul : ∀ (x y : M₁), f (x * y) = f x * f y) : right_cancel_semigroup M₁ :=
  right_cancel_semigroup.mk Mul.mul sorry sorry

/-- A type endowed with `1` and `*` is a monoid,
if it admits an injective map that preserves `1` and `*` to a monoid. -/
protected def add_monoid {M₁ : Type u_1} {M₂ : Type u_2} [Add M₁] [HasZero M₁] [add_monoid M₂]
    (f : M₁ → M₂) (hf : injective f) (one : f 0 = 0) (mul : ∀ (x y : M₁), f (x + y) = f x + f y) :
    add_monoid M₁ :=
  add_monoid.mk add_semigroup.add sorry 0 sorry sorry

/-- A type endowed with `1` and `*` is a left cancel monoid,
if it admits an injective map that preserves `1` and `*` to a left cancel monoid. -/
protected def add_left_cancel_monoid {M₁ : Type u_1} {M₂ : Type u_2} [Add M₁] [HasZero M₁]
    [add_left_cancel_monoid M₂] (f : M₁ → M₂) (hf : injective f) (one : f 0 = 0)
    (mul : ∀ (x y : M₁), f (x + y) = f x + f y) : add_left_cancel_monoid M₁ :=
  add_left_cancel_monoid.mk add_left_cancel_semigroup.add sorry sorry add_monoid.zero sorry sorry

/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits an injective map that preserves `1` and `*` to a commutative monoid. -/
protected def add_comm_monoid {M₁ : Type u_1} {M₂ : Type u_2} [Add M₁] [HasZero M₁]
    [add_comm_monoid M₂] (f : M₁ → M₂) (hf : injective f) (one : f 0 = 0)
    (mul : ∀ (x y : M₁), f (x + y) = f x + f y) : add_comm_monoid M₁ :=
  add_comm_monoid.mk add_comm_semigroup.add sorry add_monoid.zero sorry sorry sorry

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`
if it admits an injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `div_inv_monoid`. -/
protected def div_inv_monoid {M₁ : Type u_1} {M₂ : Type u_2} [Mul M₁] [HasOne M₁] [has_inv M₁]
    [Div M₁] [div_inv_monoid M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
    (mul : ∀ (x y : M₁), f (x * y) = f x * f y) (inv : ∀ (x : M₁), f (x⁻¹) = (f x⁻¹))
    (div : ∀ (x y : M₁), f (x / y) = f x / f y) : div_inv_monoid M₁ :=
  div_inv_monoid.mk monoid.mul sorry monoid.one sorry sorry has_inv.inv Div.div

/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a group. -/
protected def group {M₁ : Type u_1} {M₂ : Type u_2} [Mul M₁] [HasOne M₁] [has_inv M₁] [group M₂]
    (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1) (mul : ∀ (x y : M₁), f (x * y) = f x * f y)
    (inv : ∀ (x : M₁), f (x⁻¹) = (f x⁻¹)) : group M₁ :=
  group.mk monoid.mul sorry monoid.one sorry sorry has_inv.inv
    (div_inv_monoid.div._default monoid.mul sorry monoid.one sorry sorry has_inv.inv) sorry

/-- A type endowed with `1`, `*`, `⁻¹` and `/` is a group,
if it admits an injective map to a group that preserves these operations.

This version of `injective.group` makes sure that the `/` operation is defeq
to the specified division operator.
-/
protected def add_group_sub {M₁ : Type u_1} {M₂ : Type u_2} [Add M₁] [HasZero M₁] [Neg M₁] [Sub M₁]
    [add_group M₂] (f : M₁ → M₂) (hf : injective f) (one : f 0 = 0)
    (mul : ∀ (x y : M₁), f (x + y) = f x + f y) (inv : ∀ (x : M₁), f (-x) = -f x)
    (div : ∀ (x y : M₁), f (x - y) = f x - f y) : add_group M₁ :=
  add_group.mk sub_neg_monoid.add sorry sub_neg_monoid.zero sorry sorry sub_neg_monoid.neg
    sub_neg_monoid.sub sorry

/-- A type endowed with `1`, `*` and `⁻¹` is a commutative group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a commutative group. -/
protected def comm_group {M₁ : Type u_1} {M₂ : Type u_2} [Mul M₁] [HasOne M₁] [has_inv M₁]
    [comm_group M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
    (mul : ∀ (x y : M₁), f (x * y) = f x * f y) (inv : ∀ (x : M₁), f (x⁻¹) = (f x⁻¹)) :
    comm_group M₁ :=
  comm_group.mk comm_monoid.mul sorry comm_monoid.one sorry sorry group.inv group.div sorry sorry

/-- A type endowed with `1`, `*`, `⁻¹` and `/` is a commutative group,
if it admits an injective map to a commutative group that preserves these operations.

This version of `injective.comm_group` makes sure that the `/` operation is defeq
to the specified division operator.
-/
protected def comm_group_div {M₁ : Type u_1} {M₂ : Type u_2} [Mul M₁] [HasOne M₁] [has_inv M₁]
    [Div M₁] [comm_group M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
    (mul : ∀ (x y : M₁), f (x * y) = f x * f y) (inv : ∀ (x : M₁), f (x⁻¹) = (f x⁻¹))
    (div : ∀ (x y : M₁), f (x / y) = f x / f y) : comm_group M₁ :=
  comm_group.mk comm_monoid.mul sorry comm_monoid.one sorry sorry group.inv group.div sorry sorry

end injective


/-!
### Surjective
-/

namespace surjective


/-- A type endowed with `*` is a semigroup,
if it admits a surjective map that preserves `*` from a semigroup. -/
protected def add_semigroup {M₁ : Type u_1} {M₂ : Type u_2} [Add M₂] [add_semigroup M₁]
    (f : M₁ → M₂) (hf : surjective f) (mul : ∀ (x y : M₁), f (x + y) = f x + f y) :
    add_semigroup M₂ :=
  add_semigroup.mk Add.add sorry

/-- A type endowed with `*` is a commutative semigroup,
if it admits a surjective map that preserves `*` from a commutative semigroup. -/
protected def add_comm_semigroup {M₁ : Type u_1} {M₂ : Type u_2} [Add M₂] [add_comm_semigroup M₁]
    (f : M₁ → M₂) (hf : surjective f) (mul : ∀ (x y : M₁), f (x + y) = f x + f y) :
    add_comm_semigroup M₂ :=
  add_comm_semigroup.mk add_semigroup.add sorry sorry

/-- A type endowed with `1` and `*` is a monoid,
if it admits a surjective map that preserves `1` and `*` from a monoid. -/
protected def add_monoid {M₁ : Type u_1} {M₂ : Type u_2} [Add M₂] [HasZero M₂] [add_monoid M₁]
    (f : M₁ → M₂) (hf : surjective f) (one : f 0 = 0) (mul : ∀ (x y : M₁), f (x + y) = f x + f y) :
    add_monoid M₂ :=
  add_monoid.mk add_semigroup.add sorry 0 sorry sorry

/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits a surjective map that preserves `1` and `*` from a commutative monoid. -/
protected def add_comm_monoid {M₁ : Type u_1} {M₂ : Type u_2} [Add M₂] [HasZero M₂]
    [add_comm_monoid M₁] (f : M₁ → M₂) (hf : surjective f) (one : f 0 = 0)
    (mul : ∀ (x y : M₁), f (x + y) = f x + f y) : add_comm_monoid M₂ :=
  add_comm_monoid.mk add_comm_semigroup.add sorry add_monoid.zero sorry sorry sorry

/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits a surjective map that preserves `1`, `*` and `⁻¹` from a group. -/
protected def group {M₁ : Type u_1} {M₂ : Type u_2} [Mul M₂] [HasOne M₂] [has_inv M₂] [group M₁]
    (f : M₁ → M₂) (hf : surjective f) (one : f 1 = 1) (mul : ∀ (x y : M₁), f (x * y) = f x * f y)
    (inv : ∀ (x : M₁), f (x⁻¹) = (f x⁻¹)) : group M₂ :=
  group.mk monoid.mul sorry monoid.one sorry sorry has_inv.inv
    (div_inv_monoid.div._default monoid.mul sorry monoid.one sorry sorry has_inv.inv) sorry

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`,
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` from a `div_inv_monoid` -/
protected def sub_neg_add_monoid {M₁ : Type u_1} {M₂ : Type u_2} [Add M₂] [HasZero M₂] [Neg M₂]
    [Sub M₂] [sub_neg_monoid M₁] (f : M₁ → M₂) (hf : surjective f) (one : f 0 = 0)
    (mul : ∀ (x y : M₁), f (x + y) = f x + f y) (inv : ∀ (x : M₁), f (-x) = -f x)
    (div : ∀ (x y : M₁), f (x - y) = f x - f y) : sub_neg_monoid M₂ :=
  sub_neg_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry Neg.neg Sub.sub

/-- A type endowed with `1`, `*`, `⁻¹` and `/` is a group,
if it admits an surjective map from a group that preserves these operations.

This version of `surjective.group` makes sure that the `/` operation is defeq
to the specified division operator.
-/
protected def add_group_sub {M₁ : Type u_1} {M₂ : Type u_2} [Add M₂] [HasZero M₂] [Neg M₂] [Sub M₂]
    [add_group M₁] (f : M₁ → M₂) (hf : surjective f) (one : f 0 = 0)
    (mul : ∀ (x y : M₁), f (x + y) = f x + f y) (inv : ∀ (x : M₁), f (-x) = -f x)
    (div : ∀ (x y : M₁), f (x - y) = f x - f y) : add_group M₂ :=
  add_group.mk sub_neg_monoid.add sorry sub_neg_monoid.zero sorry sorry sub_neg_monoid.neg
    sub_neg_monoid.sub sorry

/-- A type endowed with `1`, `*` and `⁻¹` is a commutative group,
if it admits a surjective map that preserves `1`, `*` and `⁻¹` from a commutative group. -/
protected def comm_group {M₁ : Type u_1} {M₂ : Type u_2} [Mul M₂] [HasOne M₂] [has_inv M₂]
    [comm_group M₁] (f : M₁ → M₂) (hf : surjective f) (one : f 1 = 1)
    (mul : ∀ (x y : M₁), f (x * y) = f x * f y) (inv : ∀ (x : M₁), f (x⁻¹) = (f x⁻¹)) :
    comm_group M₂ :=
  comm_group.mk comm_monoid.mul sorry comm_monoid.one sorry sorry group.inv group.div sorry sorry

/-- A type endowed with `1`, `*`, `⁻¹` and `/` is a commutative group,
if it admits an surjective map from a commutative group that preserves these operations.

This version of `surjective.comm_group` makes sure that the `/` operation is defeq
to the specified division operator.
-/
protected def add_comm_group_sub {M₁ : Type u_1} {M₂ : Type u_2} [Add M₂] [HasZero M₂] [Neg M₂]
    [Sub M₂] [add_comm_group M₁] (f : M₁ → M₂) (hf : surjective f) (one : f 0 = 0)
    (mul : ∀ (x y : M₁), f (x + y) = f x + f y) (inv : ∀ (x : M₁), f (-x) = -f x)
    (div : ∀ (x y : M₁), f (x - y) = f x - f y) : add_comm_group M₂ :=
  add_comm_group.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry add_group.neg
    add_group.sub sorry sorry

end Mathlib