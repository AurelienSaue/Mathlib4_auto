/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.rat.order
import Mathlib.data.int.sqrt
import Mathlib.PostPort

namespace Mathlib

/-!
# Square root on rational numbers

This file defines the square root function on rational numbers, `rat.sqrt` and proves several theorems about it.

-/

namespace rat


/-- Square root function on rational numbers, defined by taking the (integer) square root of the
numerator and the square root (on natural numbers) of the denominator. -/
def sqrt (q : ℚ) : ℚ :=
  mk (int.sqrt (num q)) ↑(nat.sqrt (denom q))

theorem sqrt_eq (q : ℚ) : sqrt (q * q) = abs q := sorry

theorem exists_mul_self (x : ℚ) : (∃ (q : ℚ), q * q = x) ↔ sqrt x * sqrt x = x := sorry

theorem sqrt_nonneg (q : ℚ) : 0 ≤ sqrt q := sorry

