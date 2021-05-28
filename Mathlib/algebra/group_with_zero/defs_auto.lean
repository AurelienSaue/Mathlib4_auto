/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group.defs
import Mathlib.logic.nontrivial
import PostPort

universes u_4 l u_1 u 

namespace Mathlib

/-!
# Typeclasses for groups with an adjoined zero element

This file provides just the typeclass definitions, and the projection lemmas that expose their
members.

## Main definitions

* `group_with_zero`
* `comm_group_with_zero`
-/

-- We have to fix the universe of `G₀` here, since the default argument to

-- `group_with_zero.div'` cannot contain a universe metavariable.

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
class mul_zero_class (M₀ : Type u_4) 
extends Mul M₀, HasZero M₀
where
  zero_mul : ∀ (a : M₀), 0 * a = 0
  mul_zero : ∀ (a : M₀), a * 0 = 0

@[simp] theorem zero_mul {M₀ : Type u_1} [mul_zero_class M₀] (a : M₀) : 0 * a = 0 :=
  mul_zero_class.zero_mul a

@[simp] theorem mul_zero {M₀ : Type u_1} [mul_zero_class M₀] (a : M₀) : a * 0 = 0 :=
  mul_zero_class.mul_zero a

/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `G₀`. -/
class no_zero_divisors (M₀ : Type u_4) [Mul M₀] [HasZero M₀] 
where
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0

/-- A type `M` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
class monoid_with_zero (M₀ : Type u_4) 
extends mul_zero_class M₀, monoid M₀
where

/-- A type `M` is a `cancel_monoid_with_zero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
class cancel_monoid_with_zero (M₀ : Type u_4) 
extends monoid_with_zero M₀
where
  mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c
  mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c

theorem mul_left_cancel' {M₀ : Type u_1} [cancel_monoid_with_zero M₀] {a : M₀} {b : M₀} {c : M₀} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  cancel_monoid_with_zero.mul_left_cancel_of_ne_zero ha h

theorem mul_right_cancel' {M₀ : Type u_1} [cancel_monoid_with_zero M₀] {a : M₀} {b : M₀} {c : M₀} (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
  cancel_monoid_with_zero.mul_right_cancel_of_ne_zero hb h

/-- A type `M` is a commutative “monoid with zero” if it is a commutative monoid with zero
element, and `0` is left and right absorbing. -/
class comm_monoid_with_zero (M₀ : Type u_4) 
extends comm_monoid M₀, monoid_with_zero M₀
where

/-- A type `M` is a `comm_cancel_monoid_with_zero` if it is a commutative monoid with zero element,
 `0` is left and right absorbing,
  and left/right multiplication by a non-zero element is injective. -/
class comm_cancel_monoid_with_zero (M₀ : Type u_4) 
extends comm_monoid_with_zero M₀, cancel_monoid_with_zero M₀
where

/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory.-/
class group_with_zero (G₀ : Type u) 
extends div_inv_monoid G₀, nontrivial G₀, monoid_with_zero G₀
where
  inv_zero : 0⁻¹ = 0
  mul_inv_cancel : ∀ (a : G₀), a ≠ 0 → a * (a⁻¹) = 1

@[simp] theorem inv_zero {G₀ : Type u} [group_with_zero G₀] : 0⁻¹ = 0 :=
  group_with_zero.inv_zero

@[simp] theorem mul_inv_cancel {G₀ : Type u} [group_with_zero G₀] {a : G₀} (h : a ≠ 0) : a * (a⁻¹) = 1 :=
  group_with_zero.mul_inv_cancel a h

/-- A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
class comm_group_with_zero (G₀ : Type u_4) 
extends comm_monoid_with_zero G₀, group_with_zero G₀
where

