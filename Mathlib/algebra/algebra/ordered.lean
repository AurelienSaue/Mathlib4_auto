/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.algebra.basic
import Mathlib.algebra.module.ordered
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Ordered algebras

An ordered algebra is an ordered semiring, which is an algebra over an ordered commutative semiring,
for which scalar multiplication is "compatible" with the two orders.

The prototypical example is 2x2 matrices over the reals or complexes (or indeed any C^* algebra)
where the ordering the one determined by the positive cone of positive operators,
i.e. `A ≤ B` iff `B - A = star R * R` for some `R`.
(We don't yet have this example in mathlib.)

## Implementation

Because the axioms for an ordered algebra are exactly the same as those for the underlying
module being ordered, we don't actually introduce a new class, but just use the `ordered_semimodule`
mixin.

## Tags

ordered algebra
-/

theorem algebra_map_monotone {R : Type u_1} {A : Type u_2} [ordered_comm_ring R] [ordered_ring A] [algebra R A] [ordered_semimodule R A] : monotone ⇑(algebra_map R A) := sorry

protected instance linear_ordered_comm_ring.to_ordered_semimodule {R : Type u_1} [linear_ordered_comm_ring R] : ordered_semimodule R R :=
  ordered_semimodule.mk ordered_semiring.mul_lt_mul_of_pos_left
    fun (a b c : R) (w₁ : c • a < c • b) (w₂ : 0 < c) => iff.mp (mul_lt_mul_left w₂) w₁

