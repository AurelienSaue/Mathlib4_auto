/-
Copyright (c) 2018  Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.hom
import Mathlib.data.equiv.mul_add_aut
import Mathlib.PostPort

universes u u_1 v 

namespace Mathlib

/-!
# Conjugacy of group elements

See also `mul_aut.conj` and `quandle.conj`.
-/

/-- We say that `a` is conjugate to `b` if for some `c` we have `c * a * c⁻¹ = b`. -/
def is_conj {α : Type u} [group α] (a : α) (b : α) :=
  ∃ (c : α), c * a * (c⁻¹) = b

theorem is_conj_refl {α : Type u} [group α] (a : α) : is_conj a a := sorry

theorem is_conj_symm {α : Type u} [group α] {a : α} {b : α} : is_conj a b → is_conj b a := sorry

theorem is_conj_trans {α : Type u} [group α] {a : α} {b : α} {c : α} : is_conj a b → is_conj b c → is_conj a c := sorry

@[simp] theorem is_conj_one_right {α : Type u} [group α] {a : α} : is_conj 1 a ↔ a = 1 := sorry

@[simp] theorem is_conj_one_left {α : Type u} [group α] {a : α} : is_conj a 1 ↔ a = 1 :=
  iff.trans { mp := is_conj_symm, mpr := is_conj_symm } is_conj_one_right

@[simp] theorem conj_inv {α : Type u} [group α] {a : α} {b : α} : b * a * (b⁻¹)⁻¹ = b * (a⁻¹) * (b⁻¹) :=
  Eq.symm (mul_equiv.map_inv (coe_fn mul_aut.conj b) a)

@[simp] theorem conj_mul {α : Type u} [group α] {a : α} {b : α} {c : α} : b * a * (b⁻¹) * (b * c * (b⁻¹)) = b * (a * c) * (b⁻¹) :=
  Eq.symm (mul_equiv.map_mul (coe_fn mul_aut.conj b) a c)

theorem conj_injective {α : Type u} [group α] {x : α} : function.injective fun (g : α) => x * g * (x⁻¹) :=
  mul_equiv.injective (coe_fn mul_aut.conj x)

@[simp] theorem is_conj_iff_eq {α : Type u_1} [comm_group α] {a : α} {b : α} : is_conj a b ↔ a = b := sorry

protected theorem monoid_hom.map_is_conj {α : Type u} {β : Type v} [group α] [group β] (f : α →* β) {a : α} {b : α} : is_conj a b → is_conj (coe_fn f a) (coe_fn f b) := sorry

