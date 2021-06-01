/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.sqrt
import Mathlib.PostPort

namespace Mathlib

namespace int


/-- `sqrt n` is the square root of an integer `n`. If `n` is not a
  perfect square, and is positive, it returns the largest `k:ℤ` such
  that `k*k ≤ n`. If it is negative, it returns 0. For example,
  `sqrt 2 = 1` and `sqrt 1 = 1` and `sqrt (-1) = 0` -/
def sqrt (n : ℤ) : ℤ := ↑(nat.sqrt (to_nat n))

theorem sqrt_eq (n : ℤ) : sqrt (n * n) = ↑(nat_abs n) := sorry

theorem exists_mul_self (x : ℤ) : (∃ (n : ℤ), n * n = x) ↔ sqrt x * sqrt x = x := sorry

theorem sqrt_nonneg (n : ℤ) : 0 ≤ sqrt n := coe_nat_nonneg (nat.sqrt (to_nat n))

end Mathlib