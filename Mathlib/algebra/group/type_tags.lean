/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.hom
import Mathlib.data.equiv.basic
import Mathlib.PostPort

universes u_1 u v 

namespace Mathlib

/-!
# Type tags that turn additive structures into multiplicative, and vice versa

We define two type tags:

* `additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `additive α`;
* `multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `multiplicative α`.

We also define instances `additive.*` and `multiplicative.*` that actually transfer the structures.
-/

/-- If `α` carries some multiplicative structure, then `additive α` carries the corresponding
additive structure. -/
/-- If `α` carries some additive structure, then `multiplicative α` carries the corresponding
def additive (α : Type u_1) :=
  α

multiplicative structure. -/
def multiplicative (α : Type u_1) :=
  α

namespace additive


/-- Reinterpret `x : α` as an element of `additive α`. -/
def of_mul {α : Type u} : α ≃ additive α :=
  equiv.mk (fun (x : α) => x) (fun (x : additive α) => x) sorry sorry

/-- Reinterpret `x : additive α` as an element of `α`. -/
def to_mul {α : Type u} : additive α ≃ α :=
  equiv.symm of_mul

@[simp] theorem of_mul_symm_eq {α : Type u} : equiv.symm of_mul = to_mul :=
  rfl

@[simp] theorem to_mul_symm_eq {α : Type u} : equiv.symm to_mul = of_mul :=
  rfl

end additive


namespace multiplicative


/-- Reinterpret `x : α` as an element of `multiplicative α`. -/
def of_add {α : Type u} : α ≃ multiplicative α :=
  equiv.mk (fun (x : α) => x) (fun (x : multiplicative α) => x) sorry sorry

/-- Reinterpret `x : multiplicative α` as an element of `α`. -/
def to_add {α : Type u} : multiplicative α ≃ α :=
  equiv.symm of_add

@[simp] theorem of_add_symm_eq {α : Type u} : equiv.symm of_add = to_add :=
  rfl

@[simp] theorem to_add_symm_eq {α : Type u} : equiv.symm to_add = of_add :=
  rfl

end multiplicative


@[simp] theorem to_add_of_add {α : Type u} (x : α) : coe_fn multiplicative.to_add (coe_fn multiplicative.of_add x) = x :=
  rfl

@[simp] theorem of_add_to_add {α : Type u} (x : multiplicative α) : coe_fn multiplicative.of_add (coe_fn multiplicative.to_add x) = x :=
  rfl

@[simp] theorem to_mul_of_mul {α : Type u} (x : α) : coe_fn additive.to_mul (coe_fn additive.of_mul x) = x :=
  rfl

@[simp] theorem of_mul_to_mul {α : Type u} (x : additive α) : coe_fn additive.of_mul (coe_fn additive.to_mul x) = x :=
  rfl

protected instance additive.inhabited {α : Type u} [Inhabited α] : Inhabited (additive α) :=
  { default := coe_fn additive.of_mul Inhabited.default }

protected instance multiplicative.inhabited {α : Type u} [Inhabited α] : Inhabited (multiplicative α) :=
  { default := coe_fn multiplicative.of_add Inhabited.default }

protected instance additive.has_add {α : Type u} [Mul α] : Add (additive α) :=
  { add := fun (x y : additive α) => coe_fn additive.of_mul (coe_fn additive.to_mul x * coe_fn additive.to_mul y) }

protected instance multiplicative.has_mul {α : Type u} [Add α] : Mul (multiplicative α) :=
  { mul :=
      fun (x y : multiplicative α) =>
        coe_fn multiplicative.of_add (coe_fn multiplicative.to_add x + coe_fn multiplicative.to_add y) }

@[simp] theorem of_add_add {α : Type u} [Add α] (x : α) (y : α) : coe_fn multiplicative.of_add (x + y) = coe_fn multiplicative.of_add x * coe_fn multiplicative.of_add y :=
  rfl

@[simp] theorem to_add_mul {α : Type u} [Add α] (x : multiplicative α) (y : multiplicative α) : coe_fn multiplicative.to_add (x * y) = coe_fn multiplicative.to_add x + coe_fn multiplicative.to_add y :=
  rfl

@[simp] theorem of_mul_mul {α : Type u} [Mul α] (x : α) (y : α) : coe_fn additive.of_mul (x * y) = coe_fn additive.of_mul x + coe_fn additive.of_mul y :=
  rfl

@[simp] theorem to_mul_add {α : Type u} [Mul α] (x : additive α) (y : additive α) : coe_fn additive.to_mul (x + y) = coe_fn additive.to_mul x * coe_fn additive.to_mul y :=
  rfl

protected instance additive.add_semigroup {α : Type u} [semigroup α] : add_semigroup (additive α) :=
  add_semigroup.mk Add.add mul_assoc

protected instance multiplicative.semigroup {α : Type u} [add_semigroup α] : semigroup (multiplicative α) :=
  semigroup.mk Mul.mul add_assoc

protected instance additive.add_comm_semigroup {α : Type u} [comm_semigroup α] : add_comm_semigroup (additive α) :=
  add_comm_semigroup.mk add_semigroup.add sorry sorry

protected instance multiplicative.comm_semigroup {α : Type u} [add_comm_semigroup α] : comm_semigroup (multiplicative α) :=
  comm_semigroup.mk semigroup.mul sorry sorry

protected instance additive.add_left_cancel_semigroup {α : Type u} [left_cancel_semigroup α] : add_left_cancel_semigroup (additive α) :=
  add_left_cancel_semigroup.mk add_semigroup.add sorry sorry

protected instance multiplicative.left_cancel_semigroup {α : Type u} [add_left_cancel_semigroup α] : left_cancel_semigroup (multiplicative α) :=
  left_cancel_semigroup.mk semigroup.mul sorry sorry

protected instance additive.add_right_cancel_semigroup {α : Type u} [right_cancel_semigroup α] : add_right_cancel_semigroup (additive α) :=
  add_right_cancel_semigroup.mk add_semigroup.add sorry sorry

protected instance multiplicative.right_cancel_semigroup {α : Type u} [add_right_cancel_semigroup α] : right_cancel_semigroup (multiplicative α) :=
  right_cancel_semigroup.mk semigroup.mul sorry sorry

protected instance additive.has_zero {α : Type u} [HasOne α] : HasZero (additive α) :=
  { zero := coe_fn additive.of_mul 1 }

@[simp] theorem of_mul_one {α : Type u} [HasOne α] : coe_fn additive.of_mul 1 = 0 :=
  rfl

@[simp] theorem to_mul_zero {α : Type u} [HasOne α] : coe_fn additive.to_mul 0 = 1 :=
  rfl

protected instance multiplicative.has_one {α : Type u} [HasZero α] : HasOne (multiplicative α) :=
  { one := coe_fn multiplicative.of_add 0 }

@[simp] theorem of_add_zero {α : Type u} [HasZero α] : coe_fn multiplicative.of_add 0 = 1 :=
  rfl

@[simp] theorem to_add_one {α : Type u} [HasZero α] : coe_fn multiplicative.to_add 1 = 0 :=
  rfl

protected instance additive.add_monoid {α : Type u} [monoid α] : add_monoid (additive α) :=
  add_monoid.mk add_semigroup.add sorry 0 sorry sorry

protected instance multiplicative.monoid {α : Type u} [add_monoid α] : monoid (multiplicative α) :=
  monoid.mk semigroup.mul sorry 1 sorry sorry

protected instance additive.add_comm_monoid {α : Type u} [comm_monoid α] : add_comm_monoid (additive α) :=
  add_comm_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry sorry

protected instance multiplicative.comm_monoid {α : Type u} [add_comm_monoid α] : comm_monoid (multiplicative α) :=
  comm_monoid.mk monoid.mul sorry monoid.one sorry sorry sorry

protected instance additive.has_neg {α : Type u} [has_inv α] : Neg (additive α) :=
  { neg := fun (x : additive α) => coe_fn multiplicative.of_add (coe_fn additive.to_mul x⁻¹) }

@[simp] theorem of_mul_inv {α : Type u} [has_inv α] (x : α) : coe_fn additive.of_mul (x⁻¹) = -coe_fn additive.of_mul x :=
  rfl

@[simp] theorem to_mul_neg {α : Type u} [has_inv α] (x : additive α) : coe_fn additive.to_mul (-x) = (coe_fn additive.to_mul x⁻¹) :=
  rfl

protected instance multiplicative.has_inv {α : Type u} [Neg α] : has_inv (multiplicative α) :=
  has_inv.mk fun (x : multiplicative α) => coe_fn additive.of_mul (-coe_fn multiplicative.to_add x)

@[simp] theorem of_add_neg {α : Type u} [Neg α] (x : α) : coe_fn multiplicative.of_add (-x) = (coe_fn multiplicative.of_add x⁻¹) :=
  rfl

@[simp] theorem to_add_inv {α : Type u} [Neg α] (x : multiplicative α) : coe_fn multiplicative.to_add (x⁻¹) = -coe_fn multiplicative.to_add x :=
  rfl

protected instance additive.has_sub {α : Type u} [Div α] : Sub (additive α) :=
  { sub := fun (x y : additive α) => coe_fn additive.of_mul (coe_fn additive.to_mul x / coe_fn additive.to_mul y) }

protected instance multiplicative.has_div {α : Type u} [Sub α] : Div (multiplicative α) :=
  { div :=
      fun (x y : multiplicative α) =>
        coe_fn multiplicative.of_add (coe_fn multiplicative.to_add x - coe_fn multiplicative.to_add y) }

@[simp] theorem of_add_sub {α : Type u} [Sub α] (x : α) (y : α) : coe_fn multiplicative.of_add (x - y) = coe_fn multiplicative.of_add x / coe_fn multiplicative.of_add y :=
  rfl

@[simp] theorem to_add_div {α : Type u} [Sub α] (x : multiplicative α) (y : multiplicative α) : coe_fn multiplicative.to_add (x / y) = coe_fn multiplicative.to_add x - coe_fn multiplicative.to_add y :=
  rfl

@[simp] theorem of_mul_div {α : Type u} [Div α] (x : α) (y : α) : coe_fn additive.of_mul (x / y) = coe_fn additive.of_mul x - coe_fn additive.of_mul y :=
  rfl

@[simp] theorem to_mul_sub {α : Type u} [Div α] (x : additive α) (y : additive α) : coe_fn additive.to_mul (x - y) = coe_fn additive.to_mul x / coe_fn additive.to_mul y :=
  rfl

protected instance additive.sub_neg_monoid {α : Type u} [div_inv_monoid α] : sub_neg_monoid (additive α) :=
  sub_neg_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry Neg.neg Sub.sub

protected instance multiplicative.div_inv_monoid {α : Type u} [sub_neg_monoid α] : div_inv_monoid (multiplicative α) :=
  div_inv_monoid.mk monoid.mul sorry monoid.one sorry sorry has_inv.inv Div.div

protected instance additive.add_group {α : Type u} [group α] : add_group (additive α) :=
  add_group.mk sub_neg_monoid.add sorry sub_neg_monoid.zero sorry sorry sub_neg_monoid.neg sub_neg_monoid.sub mul_left_inv

protected instance multiplicative.group {α : Type u} [add_group α] : group (multiplicative α) :=
  group.mk div_inv_monoid.mul sorry div_inv_monoid.one sorry sorry div_inv_monoid.inv div_inv_monoid.div add_left_neg

protected instance additive.add_comm_group {α : Type u} [comm_group α] : add_comm_group (additive α) :=
  add_comm_group.mk add_group.add sorry add_group.zero sorry sorry add_group.neg add_group.sub sorry sorry

protected instance multiplicative.comm_group {α : Type u} [add_comm_group α] : comm_group (multiplicative α) :=
  comm_group.mk group.mul sorry group.one sorry sorry group.inv group.div sorry sorry

/-- Reinterpret `α →+ β` as `multiplicative α →* multiplicative β`. -/
def add_monoid_hom.to_multiplicative {α : Type u} {β : Type v} [add_monoid α] [add_monoid β] : (α →+ β) ≃ (multiplicative α →* multiplicative β) :=
  equiv.mk
    (fun (f : α →+ β) => monoid_hom.mk (add_monoid_hom.to_fun f) (add_monoid_hom.map_zero' f) (add_monoid_hom.map_add' f))
    (fun (f : multiplicative α →* multiplicative β) => add_monoid_hom.mk (monoid_hom.to_fun f) sorry sorry) sorry sorry

/-- Reinterpret `α →* β` as `additive α →+ additive β`. -/
def monoid_hom.to_additive {α : Type u} {β : Type v} [monoid α] [monoid β] : (α →* β) ≃ (additive α →+ additive β) :=
  equiv.mk (fun (f : α →* β) => add_monoid_hom.mk (monoid_hom.to_fun f) (monoid_hom.map_one' f) (monoid_hom.map_mul' f))
    (fun (f : additive α →+ additive β) => monoid_hom.mk (add_monoid_hom.to_fun f) sorry sorry) sorry sorry

/-- Reinterpret `additive α →+ β` as `α →* multiplicative β`. -/
def add_monoid_hom.to_multiplicative' {α : Type u} {β : Type v} [monoid α] [add_monoid β] : (additive α →+ β) ≃ (α →* multiplicative β) :=
  equiv.mk (fun (f : additive α →+ β) => monoid_hom.mk (add_monoid_hom.to_fun f) sorry sorry)
    (fun (f : α →* multiplicative β) => add_monoid_hom.mk (monoid_hom.to_fun f) sorry sorry) sorry sorry

/-- Reinterpret `α →* multiplicative β` as `additive α →+ β`. -/
def monoid_hom.to_additive' {α : Type u} {β : Type v} [monoid α] [add_monoid β] : (α →* multiplicative β) ≃ (additive α →+ β) :=
  equiv.symm add_monoid_hom.to_multiplicative'

/-- Reinterpret `α →+ additive β` as `multiplicative α →* β`. -/
def add_monoid_hom.to_multiplicative'' {α : Type u} {β : Type v} [add_monoid α] [monoid β] : (α →+ additive β) ≃ (multiplicative α →* β) :=
  equiv.mk (fun (f : α →+ additive β) => monoid_hom.mk (add_monoid_hom.to_fun f) sorry sorry)
    (fun (f : multiplicative α →* β) => add_monoid_hom.mk (monoid_hom.to_fun f) sorry sorry) sorry sorry

/-- Reinterpret `multiplicative α →* β` as `α →+ additive β`. -/
def monoid_hom.to_additive'' {α : Type u} {β : Type v} [add_monoid α] [monoid β] : (multiplicative α →* β) ≃ (α →+ additive β) :=
  equiv.symm add_monoid_hom.to_multiplicative''

