/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.split_ifs
import Mathlib.tactic.simpa
import Mathlib.algebra.group.to_additive
import Mathlib.PostPort

universes u v u_1 

namespace Mathlib

/-!
# Instances and theorems on pi types

This file provides basic definitions and notation instances for Pi types.

Instances of more sophisticated classes are defined in `pi.lean` files elsewhere.
-/

namespace pi


/-! `1`, `0`, `+`, `*`, `-`, `⁻¹`, and `/` are defined pointwise. -/

protected instance has_zero {I : Type u} {f : I → Type v} [(i : I) → HasZero (f i)] :
    HasZero ((i : I) → f i) :=
  { zero := fun (_x : I) => 0 }

@[simp] theorem one_apply {I : Type u} {f : I → Type v} (i : I) [(i : I) → HasOne (f i)] :
    HasOne.one i = 1 :=
  rfl

theorem one_def {I : Type u} {f : I → Type v} [(i : I) → HasOne (f i)] : 1 = fun (i : I) => 1 := rfl

protected instance has_mul {I : Type u} {f : I → Type v} [(i : I) → Mul (f i)] :
    Mul ((i : I) → f i) :=
  { mul := fun (f_1 g : (i : I) → f i) (i : I) => f_1 i * g i }

@[simp] theorem mul_apply {I : Type u} {f : I → Type v} (x : (i : I) → f i) (y : (i : I) → f i)
    (i : I) [(i : I) → Mul (f i)] : Mul.mul x y i = x i * y i :=
  rfl

protected instance has_inv {I : Type u} {f : I → Type v} [(i : I) → has_inv (f i)] :
    has_inv ((i : I) → f i) :=
  has_inv.mk fun (f_1 : (i : I) → f i) (i : I) => f_1 i⁻¹

@[simp] theorem neg_apply {I : Type u} {f : I → Type v} (x : (i : I) → f i) (i : I)
    [(i : I) → Neg (f i)] : Neg.neg x i = -x i :=
  rfl

protected instance has_sub {I : Type u} {f : I → Type v} [(i : I) → Sub (f i)] :
    Sub ((i : I) → f i) :=
  { sub := fun (f_1 g : (i : I) → f i) (i : I) => f_1 i - g i }

@[simp] theorem sub_apply {I : Type u} {f : I → Type v} (x : (i : I) → f i) (y : (i : I) → f i)
    (i : I) [(i : I) → Sub (f i)] : Sub.sub x y i = x i - y i :=
  rfl

theorem div_def {I : Type u} {f : I → Type v} (x : (i : I) → f i) (y : (i : I) → f i)
    [(i : I) → Div (f i)] : x / y = fun (i : I) => x i / y i :=
  rfl

/-- The function supported at `i`, with value `x` there. -/
def single {I : Type u} {f : I → Type v} [DecidableEq I] [(i : I) → HasZero (f i)] (i : I)
    (x : f i) : (i : I) → f i :=
  function.update 0 i x

@[simp] theorem single_eq_same {I : Type u} {f : I → Type v} [DecidableEq I]
    [(i : I) → HasZero (f i)] (i : I) (x : f i) : single i x i = x :=
  function.update_same i x 0

@[simp] theorem single_eq_of_ne {I : Type u} {f : I → Type v} [DecidableEq I]
    [(i : I) → HasZero (f i)] {i : I} {i' : I} (h : i' ≠ i) (x : f i) : single i x i' = 0 :=
  function.update_noteq h x 0

theorem single_injective {I : Type u} (f : I → Type v) [DecidableEq I] [(i : I) → HasZero (f i)]
    (i : I) : function.injective (single i) :=
  function.update_injective (fun (a : I) => HasZero.zero a) i

end pi


theorem subsingleton.pi_single_eq {I : Type u} {α : Type u_1} [DecidableEq I] [subsingleton I]
    [HasZero α] (i : I) (x : α) : pi.single i x = fun (_x : I) => x :=
  sorry

end Mathlib