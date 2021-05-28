/-
Copyright (c) 2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Kevin Lacker
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.ring
import PostPort

universes u_1 

namespace Mathlib

/-!
# Identities

This file contains some "named" commutative ring identities.
-/

/--
Brahmagupta-Fibonacci identity or Diophantus identity, see
<https://en.wikipedia.org/wiki/Brahmagupta%E2%80%93Fibonacci_identity>.

This sign choice here corresponds to the signs obtained by multiplying two complex numbers.
-/
theorem pow_two_add_pow_two_mul_pow_two_add_pow_two {R : Type u_1} [comm_ring R] {x₁ : R} {x₂ : R} {y₁ : R} {y₂ : R} : (x₁ ^ bit0 1 + x₂ ^ bit0 1) * (y₁ ^ bit0 1 + y₂ ^ bit0 1) = (x₁ * y₁ - x₂ * y₂) ^ bit0 1 + (x₁ * y₂ + x₂ * y₁) ^ bit0 1 := sorry

/--
Brahmagupta's identity, see <https://en.wikipedia.org/wiki/Brahmagupta%27s_identity>
-/
theorem pow_two_add_mul_pow_two_mul_pow_two_add_mul_pow_two {R : Type u_1} [comm_ring R] {x₁ : R} {x₂ : R} {y₁ : R} {y₂ : R} {n : R} : (x₁ ^ bit0 1 + n * x₂ ^ bit0 1) * (y₁ ^ bit0 1 + n * y₂ ^ bit0 1) =
  (x₁ * y₁ - n * x₂ * y₂) ^ bit0 1 + n * (x₁ * y₂ + x₂ * y₁) ^ bit0 1 := sorry

/--
Sophie Germain's identity, see <https://www.cut-the-knot.org/blue/SophieGermainIdentity.shtml>.
-/
theorem pow_four_add_four_mul_pow_four {R : Type u_1} [comm_ring R] {a : R} {b : R} : a ^ bit0 (bit0 1) + bit0 (bit0 1) * b ^ bit0 (bit0 1) =
  ((a - b) ^ bit0 1 + b ^ bit0 1) * ((a + b) ^ bit0 1 + b ^ bit0 1) := sorry

/--
Sophie Germain's identity, see <https://www.cut-the-knot.org/blue/SophieGermainIdentity.shtml>.
-/
theorem pow_four_add_four_mul_pow_four' {R : Type u_1} [comm_ring R] {a : R} {b : R} : a ^ bit0 (bit0 1) + bit0 (bit0 1) * b ^ bit0 (bit0 1) =
  (a ^ bit0 1 - bit0 1 * a * b + bit0 1 * b ^ bit0 1) * (a ^ bit0 1 + bit0 1 * a * b + bit0 1 * b ^ bit0 1) := sorry

/--
Euler's four-square identity, see <https://en.wikipedia.org/wiki/Euler%27s_four-square_identity>.

This sign choice here corresponds to the signs obtained by multiplying two quaternions.
-/
theorem sum_four_sq_mul_sum_four_sq {R : Type u_1} [comm_ring R] {x₁ : R} {x₂ : R} {x₃ : R} {x₄ : R} {y₁ : R} {y₂ : R} {y₃ : R} {y₄ : R} : (x₁ ^ bit0 1 + x₂ ^ bit0 1 + x₃ ^ bit0 1 + x₄ ^ bit0 1) * (y₁ ^ bit0 1 + y₂ ^ bit0 1 + y₃ ^ bit0 1 + y₄ ^ bit0 1) =
  (x₁ * y₁ - x₂ * y₂ - x₃ * y₃ - x₄ * y₄) ^ bit0 1 + (x₁ * y₂ + x₂ * y₁ + x₃ * y₄ - x₄ * y₃) ^ bit0 1 +
      (x₁ * y₃ - x₂ * y₄ + x₃ * y₁ + x₄ * y₂) ^ bit0 1 +
    (x₁ * y₄ + x₂ * y₃ - x₃ * y₂ + x₄ * y₁) ^ bit0 1 := sorry

/--
Degen's eight squares identity, see <https://en.wikipedia.org/wiki/Degen%27s_eight-square_identity>.

This sign choice here corresponds to the signs obtained by multiplying two octonions.
-/
theorem sum_eight_sq_mul_sum_eight_sq {R : Type u_1} [comm_ring R] {x₁ : R} {x₂ : R} {x₃ : R} {x₄ : R} {x₅ : R} {x₆ : R} {x₇ : R} {x₈ : R} {y₁ : R} {y₂ : R} {y₃ : R} {y₄ : R} {y₅ : R} {y₆ : R} {y₇ : R} {y₈ : R} : (x₁ ^ bit0 1 + x₂ ^ bit0 1 + x₃ ^ bit0 1 + x₄ ^ bit0 1 + x₅ ^ bit0 1 + x₆ ^ bit0 1 + x₇ ^ bit0 1 + x₈ ^ bit0 1) *
    (y₁ ^ bit0 1 + y₂ ^ bit0 1 + y₃ ^ bit0 1 + y₄ ^ bit0 1 + y₅ ^ bit0 1 + y₆ ^ bit0 1 + y₇ ^ bit0 1 + y₈ ^ bit0 1) =
  (x₁ * y₁ - x₂ * y₂ - x₃ * y₃ - x₄ * y₄ - x₅ * y₅ - x₆ * y₆ - x₇ * y₇ - x₈ * y₈) ^ bit0 1 +
                (x₁ * y₂ + x₂ * y₁ + x₃ * y₄ - x₄ * y₃ + x₅ * y₆ - x₆ * y₅ - x₇ * y₈ + x₈ * y₇) ^ bit0 1 +
              (x₁ * y₃ - x₂ * y₄ + x₃ * y₁ + x₄ * y₂ + x₅ * y₇ + x₆ * y₈ - x₇ * y₅ - x₈ * y₆) ^ bit0 1 +
            (x₁ * y₄ + x₂ * y₃ - x₃ * y₂ + x₄ * y₁ + x₅ * y₈ - x₆ * y₇ + x₇ * y₆ - x₈ * y₅) ^ bit0 1 +
          (x₁ * y₅ - x₂ * y₆ - x₃ * y₇ - x₄ * y₈ + x₅ * y₁ + x₆ * y₂ + x₇ * y₃ + x₈ * y₄) ^ bit0 1 +
        (x₁ * y₆ + x₂ * y₅ - x₃ * y₈ + x₄ * y₇ - x₅ * y₂ + x₆ * y₁ - x₇ * y₄ + x₈ * y₃) ^ bit0 1 +
      (x₁ * y₇ + x₂ * y₈ + x₃ * y₅ - x₄ * y₆ - x₅ * y₃ + x₆ * y₄ + x₇ * y₁ - x₈ * y₂) ^ bit0 1 +
    (x₁ * y₈ - x₂ * y₇ + x₃ * y₆ + x₄ * y₅ - x₅ * y₄ - x₆ * y₃ + x₇ * y₂ + x₈ * y₁) ^ bit0 1 := sorry

