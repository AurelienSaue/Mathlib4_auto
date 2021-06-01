/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.invertible
import Mathlib.tactic.linarith.default
import Mathlib.order.filter.at_top_bot
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Quadratic discriminants and roots of a quadratic

This file defines the discriminant of a quadratic and gives the solution to a quadratic equation.

## Main definition

- `discrim a b c`: the discriminant of a quadratic `a * x * x + b * x + c` is `b * b - 4 * a * c`.

## Main statements

- `quadratic_eq_zero_iff`: roots of a quadratic can be written as
  `(-b + s) / (2 * a)` or `(-b - s) / (2 * a)`, where `s` is a square root of the discriminant.
- `quadratic_ne_zero_of_discrim_ne_square`: if the discriminant has no square root,
  then the corresponding quadratic has no root.
- `discrim_le_zero`: if a quadratic is always non-negative, then its discriminant is non-positive.

## Tags

polynomial, quadratic, discriminant, root
-/

/-- Discriminant of a quadratic -/
def discrim {R : Type u_1} [ring R] (a : R) (b : R) (c : R) : R :=
  b ^ bit0 1 - bit0 (bit0 1) * a * c

/--
A quadratic has roots if and only if its discriminant equals some square.
-/
theorem quadratic_eq_zero_iff_discrim_eq_square {R : Type u_1} [integral_domain R] {a : R} {b : R}
    {c : R} (h2 : bit0 1 ≠ 0) (ha : a ≠ 0) (x : R) :
    a * x * x + b * x + c = 0 ↔ discrim a b c = (bit0 1 * a * x + b) ^ bit0 1 :=
  sorry

/-- A quadratic has no root if its discriminant has no square root. -/
theorem quadratic_ne_zero_of_discrim_ne_square {R : Type u_1} [integral_domain R] {a : R} {b : R}
    {c : R} (h2 : bit0 1 ≠ 0) (ha : a ≠ 0) (h : ∀ (s : R), discrim a b c ≠ s * s) (x : R) :
    a * x * x + b * x + c ≠ 0 :=
  sorry

/-- Roots of a quadratic -/
theorem quadratic_eq_zero_iff {K : Type u_1} [field K] [invertible (bit0 1)] {a : K} {b : K} {c : K}
    (ha : a ≠ 0) {s : K} (h : discrim a b c = s * s) (x : K) :
    a * x * x + b * x + c = 0 ↔ x = (-b + s) / (bit0 1 * a) ∨ x = (-b - s) / (bit0 1 * a) :=
  sorry

/-- A quadratic has roots if its discriminant has square roots -/
theorem exists_quadratic_eq_zero {K : Type u_1} [field K] [invertible (bit0 1)] {a : K} {b : K}
    {c : K} (ha : a ≠ 0) (h : ∃ (s : K), discrim a b c = s * s) :
    ∃ (x : K), a * x * x + b * x + c = 0 :=
  sorry

/-- Root of a quadratic when its discriminant equals zero -/
theorem quadratic_eq_zero_iff_of_discrim_eq_zero {K : Type u_1} [field K] [invertible (bit0 1)]
    {a : K} {b : K} {c : K} (ha : a ≠ 0) (h : discrim a b c = 0) (x : K) :
    a * x * x + b * x + c = 0 ↔ x = -b / (bit0 1 * a) :=
  sorry

/-- If a polynomial of degree 2 is always nonnegative, then its discriminant is nonpositive -/
theorem discrim_le_zero {K : Type u_1} [linear_ordered_field K] {a : K} {b : K} {c : K}
    (h : ∀ (x : K), 0 ≤ a * x * x + b * x + c) : discrim a b c ≤ 0 :=
  sorry

/--
If a polynomial of degree 2 is always positive, then its discriminant is negative,
at least when the coefficient of the quadratic term is nonzero.
-/
theorem discrim_lt_zero {K : Type u_1} [linear_ordered_field K] {a : K} {b : K} {c : K} (ha : a ≠ 0)
    (h : ∀ (x : K), 0 < a * x * x + b * x + c) : discrim a b c < 0 :=
  sorry

end Mathlib