/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.group_theory.group_action.defs
import Mathlib.algebra.group.units
import Mathlib.algebra.group_with_zero.default
import Mathlib.data.equiv.mul_add
import Mathlib.group_theory.perm.basic
import PostPort

universes u v 

namespace Mathlib

/-!
# Group actions applied to various types of group

This file contains lemmas about `smul` on `units`, `group_with_zero`, and `group`.
-/

@[simp] theorem units.inv_smul_smul {α : Type u} {β : Type v} [monoid α] [mul_action α β] (u : units α) (x : β) : ↑(u⁻¹) • ↑u • x = x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(u⁻¹) • ↑u • x = x)) (smul_smul (↑(u⁻¹)) (↑u) x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((↑(u⁻¹) * ↑u) • x = x)) (units.inv_mul u)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 • x = x)) (one_smul α x))) (Eq.refl x)))

@[simp] theorem units.smul_inv_smul {α : Type u} {β : Type v} [monoid α] [mul_action α β] (u : units α) (x : β) : ↑u • ↑(u⁻¹) • x = x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑u • ↑(u⁻¹) • x = x)) (smul_smul (↑u) (↑(u⁻¹)) x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((↑u * ↑(u⁻¹)) • x = x)) (units.mul_inv u)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 • x = x)) (one_smul α x))) (Eq.refl x)))

/-- If a monoid `α` acts on `β`, then each `u : units α` defines a permutation of `β`. -/
def units.smul_perm_hom {α : Type u} {β : Type v} [monoid α] [mul_action α β] : units α →* equiv.perm β :=
  monoid_hom.mk
    (fun (u : units α) =>
      equiv.mk (fun (x : β) => ↑u • x) (fun (x : β) => ↑(u⁻¹) • x) (units.inv_smul_smul u) (units.smul_inv_smul u))
    sorry sorry

@[simp] theorem units.smul_left_cancel {α : Type u} {β : Type v} [monoid α] [mul_action α β] (u : units α) {x : β} {y : β} : ↑u • x = ↑u • y ↔ x = y :=
  equiv.apply_eq_iff_eq (coe_fn units.smul_perm_hom u)

theorem units.smul_eq_iff_eq_inv_smul {α : Type u} {β : Type v} [monoid α] [mul_action α β] (u : units α) {x : β} {y : β} : ↑u • x = y ↔ x = ↑(u⁻¹) • y :=
  equiv.apply_eq_iff_eq_symm_apply (coe_fn units.smul_perm_hom u)

theorem is_unit.smul_left_cancel {α : Type u} {β : Type v} [monoid α] [mul_action α β] {a : α} (ha : is_unit a) {x : β} {y : β} : a • x = a • y ↔ x = y := sorry

@[simp] theorem inv_smul_smul' {α : Type u} {β : Type v} [group_with_zero α] [mul_action α β] {c : α} (hc : c ≠ 0) (x : β) : c⁻¹ • c • x = x :=
  units.inv_smul_smul (units.mk0 c hc) x

@[simp] theorem smul_inv_smul' {α : Type u} {β : Type v} [group_with_zero α] [mul_action α β] {c : α} (hc : c ≠ 0) (x : β) : c • c⁻¹ • x = x :=
  units.smul_inv_smul (units.mk0 c hc) x

theorem inv_smul_eq_iff' {α : Type u} {β : Type v} [group_with_zero α] [mul_action α β] {a : α} (ha : a ≠ 0) {x : β} {y : β} : a⁻¹ • x = y ↔ x = a • y := sorry

theorem eq_inv_smul_iff' {α : Type u} {β : Type v} [group_with_zero α] [mul_action α β] {a : α} (ha : a ≠ 0) {x : β} {y : β} : x = a⁻¹ • y ↔ a • x = y := sorry

@[simp] theorem inv_smul_smul {α : Type u} {β : Type v} [group α] [mul_action α β] (c : α) (x : β) : c⁻¹ • c • x = x :=
  units.inv_smul_smul (coe_fn to_units c) x

@[simp] theorem smul_inv_smul {α : Type u} {β : Type v} [group α] [mul_action α β] (c : α) (x : β) : c • c⁻¹ • x = x :=
  units.smul_inv_smul (coe_fn to_units c) x

theorem inv_smul_eq_iff {α : Type u} {β : Type v} [group α] [mul_action α β] {a : α} {x : β} {y : β} : a⁻¹ • x = y ↔ x = a • y := sorry

theorem eq_inv_smul_iff {α : Type u} {β : Type v} [group α] [mul_action α β] {a : α} {x : β} {y : β} : x = a⁻¹ • y ↔ a • x = y := sorry

/-- Given an action of a group `α` on a set `β`, each `g : α` defines a permutation of `β`. -/
def mul_action.to_perm (α : Type u) (β : Type v) [group α] [mul_action α β] : α →* equiv.perm β :=
  monoid_hom.comp units.smul_perm_hom (mul_equiv.to_monoid_hom to_units)

protected theorem mul_action.bijective {α : Type u} {β : Type v} [group α] [mul_action α β] (g : α) : function.bijective fun (b : β) => g • b :=
  equiv.bijective (coe_fn (mul_action.to_perm α β) g)

theorem units.smul_eq_zero {α : Type u} {β : Type v} [monoid α] [add_monoid β] [distrib_mul_action α β] (u : units α) {x : β} : ↑u • x = 0 ↔ x = 0 := sorry

theorem units.smul_ne_zero {α : Type u} {β : Type v} [monoid α] [add_monoid β] [distrib_mul_action α β] (u : units α) {x : β} : ↑u • x ≠ 0 ↔ x ≠ 0 :=
  not_congr (units.smul_eq_zero u)

@[simp] theorem is_unit.smul_eq_zero {α : Type u} {β : Type v} [monoid α] [add_monoid β] [distrib_mul_action α β] {u : α} (hu : is_unit u) {x : β} : u • x = 0 ↔ x = 0 :=
  exists.elim hu fun (u_1 : units α) (hu : ↑u_1 = u) => hu ▸ units.smul_eq_zero u_1

