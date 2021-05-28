/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.ring.basic
import Mathlib.data.equiv.basic
import PostPort

universes u_1 u v 

namespace Mathlib

/-- Add an extra element `1` to a type -/
def with_one (α : Type u_1)  :=
  Option α

namespace with_one


protected instance Mathlib.with_zero.monad : Monad with_zero :=
  option.monad

protected instance has_one {α : Type u} : HasOne (with_one α) :=
  { one := none }

protected instance Mathlib.with_zero.inhabited {α : Type u} : Inhabited (with_zero α) :=
  { default := 0 }

protected instance Mathlib.with_zero.nontrivial {α : Type u} [Nonempty α] : nontrivial (with_zero α) :=
  option.nontrivial

protected instance Mathlib.with_zero.has_coe_t {α : Type u} : has_coe_t α (with_zero α) :=
  has_coe_t.mk some

theorem Mathlib.with_zero.some_eq_coe {α : Type u} {a : α} : some a = ↑a :=
  rfl

@[simp] theorem coe_ne_one {α : Type u} {a : α} : ↑a ≠ 1 :=
  option.some_ne_none a

@[simp] theorem one_ne_coe {α : Type u} {a : α} : 1 ≠ ↑a :=
  ne.symm coe_ne_one

theorem Mathlib.with_zero.ne_zero_iff_exists {α : Type u} {x : with_zero α} : x ≠ 0 ↔ ∃ (a : α), ↑a = x :=
  option.ne_none_iff_exists

-- `to_additive` fails to generate some meta info around eqn lemmas, so `lift` doesn't work

-- unless we explicitly define this instance

protected instance can_lift {α : Type u} : can_lift (with_one α) α :=
  can_lift.mk coe (fun (a : with_one α) => a ≠ 1) sorry

@[simp] theorem Mathlib.with_zero.coe_inj {α : Type u} {a : α} {b : α} : ↑a = ↑b ↔ a = b :=
  option.some_inj

protected theorem Mathlib.with_zero.cases_on {α : Type u} {P : with_zero α → Prop} (x : with_zero α) : P 0 → (∀ (a : α), P ↑a) → P x :=
  option.cases_on

protected instance Mathlib.with_zero.has_add {α : Type u} [Add α] : Add (with_zero α) :=
  { add := option.lift_or_get Add.add }

protected instance monoid {α : Type u} [semigroup α] : monoid (with_one α) :=
  monoid.mk Mul.mul sorry 1 sorry sorry

protected instance Mathlib.with_zero.add_comm_monoid {α : Type u} [add_comm_semigroup α] : add_comm_monoid (with_zero α) :=
  add_comm_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry sorry

/-- `coe` as a bundled morphism -/
def coe_mul_hom {α : Type u} [Mul α] : mul_hom α (with_one α) :=
  mul_hom.mk coe sorry

/-- Lift a semigroup homomorphism `f` to a bundled monoid homorphism. -/
def Mathlib.with_zero.lift {α : Type u} [add_semigroup α] {β : Type v} [add_monoid β] : add_hom α β ≃ (with_zero α →+ β) :=
  equiv.mk (fun (f : add_hom α β) => add_monoid_hom.mk (fun (x : with_zero α) => option.cases_on x 0 ⇑f) sorry sorry)
    (fun (F : with_zero α →+ β) => add_hom.comp (add_monoid_hom.to_add_hom F) with_zero.coe_add_hom) sorry sorry

@[simp] theorem Mathlib.with_zero.lift_coe {α : Type u} [add_semigroup α] {β : Type v} [add_monoid β] (f : add_hom α β) (x : α) : coe_fn (coe_fn with_zero.lift f) ↑x = coe_fn f x :=
  rfl

@[simp] theorem lift_one {α : Type u} [semigroup α] {β : Type v} [monoid β] (f : mul_hom α β) : coe_fn (coe_fn lift f) 1 = 1 :=
  rfl

theorem Mathlib.with_zero.lift_unique {α : Type u} [add_semigroup α] {β : Type v} [add_monoid β] (f : with_zero α →+ β) : f = coe_fn with_zero.lift (add_hom.comp (add_monoid_hom.to_add_hom f) with_zero.coe_add_hom) :=
  Eq.symm (equiv.apply_symm_apply with_zero.lift f)

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `with_one α` to `with_one β` -/
def Mathlib.with_zero.map {α : Type u} {β : Type v} [add_semigroup α] [add_semigroup β] (f : add_hom α β) : with_zero α →+ with_zero β :=
  coe_fn with_zero.lift (add_hom.comp with_zero.coe_add_hom f)

@[simp] theorem Mathlib.with_zero.coe_add {α : Type u} [Add α] (a : α) (b : α) : ↑(a + b) = ↑a + ↑b :=
  rfl

end with_one


namespace with_zero


-- `to_additive` fails to generate some meta info around eqn lemmas, so `lift` doesn't work

-- unless we explicitly define this instance

protected instance can_lift {α : Type u} : can_lift (with_zero α) α :=
  can_lift.mk coe (fun (a : with_zero α) => a ≠ 0) sorry

protected instance has_one {α : Type u} [one : HasOne α] : HasOne (with_zero α) :=
  { one := ↑1 }

@[simp] theorem coe_one {α : Type u} [HasOne α] : ↑1 = 1 :=
  rfl

protected instance mul_zero_class {α : Type u} [Mul α] : mul_zero_class (with_zero α) :=
  mul_zero_class.mk (fun (o₁ o₂ : with_zero α) => option.bind o₁ fun (a : α) => option.map (fun (b : α) => a * b) o₂) 0
    sorry sorry

@[simp] theorem coe_mul {α : Type u} [Mul α] {a : α} {b : α} : ↑(a * b) = ↑a * ↑b :=
  rfl

@[simp] theorem zero_mul {α : Type u} [Mul α] (a : with_zero α) : 0 * a = 0 :=
  rfl

@[simp] theorem mul_zero {α : Type u} [Mul α] (a : with_zero α) : a * 0 = 0 :=
  option.cases_on a (Eq.refl (none * 0)) fun (a : α) => Eq.refl (some a * 0)

protected instance semigroup {α : Type u} [semigroup α] : semigroup (with_zero α) :=
  semigroup.mk mul_zero_class.mul sorry

protected instance comm_semigroup {α : Type u} [comm_semigroup α] : comm_semigroup (with_zero α) :=
  comm_semigroup.mk semigroup.mul sorry sorry

protected instance monoid_with_zero {α : Type u} [monoid α] : monoid_with_zero (with_zero α) :=
  monoid_with_zero.mk mul_zero_class.mul sorry 1 sorry sorry mul_zero_class.zero sorry sorry

protected instance comm_monoid_with_zero {α : Type u} [comm_monoid α] : comm_monoid_with_zero (with_zero α) :=
  comm_monoid_with_zero.mk monoid_with_zero.mul sorry monoid_with_zero.one sorry sorry sorry monoid_with_zero.zero sorry
    sorry

/-- Given an inverse operation on `α` there is an inverse operation
  on `with_zero α` sending `0` to `0`-/
def inv {α : Type u} [has_inv α] (x : with_zero α) : with_zero α :=
  do 
    let a ← x 
    return (a⁻¹)

protected instance has_inv {α : Type u} [has_inv α] : has_inv (with_zero α) :=
  has_inv.mk inv

@[simp] theorem coe_inv {α : Type u} [has_inv α] (a : α) : ↑(a⁻¹) = (↑a⁻¹) :=
  rfl

@[simp] theorem inv_zero {α : Type u} [has_inv α] : 0⁻¹ = 0 :=
  rfl

@[simp] theorem inv_one {α : Type u} [group α] : 1⁻¹ = 1 := sorry

/-- if `G` is a group then `with_zero G` is a group with zero. -/
protected instance group_with_zero {α : Type u} [group α] : group_with_zero (with_zero α) :=
  group_with_zero.mk monoid_with_zero.mul sorry monoid_with_zero.one sorry sorry monoid_with_zero.zero sorry sorry
    has_inv.inv (div_inv_monoid.div._default monoid_with_zero.mul sorry monoid_with_zero.one sorry sorry has_inv.inv)
    sorry sorry sorry

theorem div_coe {α : Type u} [group α] (a : α) (b : α) : ↑a / ↑b = ↑(a * (b⁻¹)) :=
  rfl

protected instance comm_group_with_zero {α : Type u} [comm_group α] : comm_group_with_zero (with_zero α) :=
  comm_group_with_zero.mk group_with_zero.mul sorry group_with_zero.one sorry sorry sorry group_with_zero.zero sorry sorry
    group_with_zero.inv group_with_zero.div sorry sorry sorry

protected instance semiring {α : Type u} [semiring α] : semiring (with_zero α) :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry mul_zero_class.mul sorry
    monoid_with_zero.one sorry sorry sorry sorry sorry sorry

