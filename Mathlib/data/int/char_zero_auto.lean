/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.int.cast
import Mathlib.algebra.char_zero
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Injectivity of `int.cast` into characteristic zero rings.

-/

namespace int


@[simp] theorem cast_eq_zero {α : Type u_1} [add_group α] [HasOne α] [char_zero α] {n : ℤ} :
    ↑n = 0 ↔ n = 0 :=
  sorry

@[simp] theorem cast_inj {α : Type u_1} [add_group α] [HasOne α] [char_zero α] {m : ℤ} {n : ℤ} :
    ↑m = ↑n ↔ m = n :=
  sorry

theorem cast_injective {α : Type u_1} [add_group α] [HasOne α] [char_zero α] :
    function.injective coe :=
  fun {a₁ a₂ : ℤ} => idRhs (↑a₁ = ↑a₂ → a₁ = a₂) (iff.mp cast_inj)

theorem cast_ne_zero {α : Type u_1} [add_group α] [HasOne α] [char_zero α] {n : ℤ} :
    ↑n ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero

end Mathlib