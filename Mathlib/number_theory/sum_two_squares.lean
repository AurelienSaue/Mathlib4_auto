/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.zsqrtd.gaussian_int
import Mathlib.PostPort

namespace Mathlib

/-!
# Sums of two squares

Proof of Fermat's theorem on the sum of two squares. Every prime congruent to 1 mod 4 is the sum
of two squares
-/

namespace nat


namespace prime


/-- Fermat's theorem on the sum of two squares. Every prime congruent to 1 mod 4 is the sum
of two squares -/
theorem sum_two_squares (p : ℕ) [hp : fact (prime p)] (hp1 : p % bit0 (bit0 1) = 1) : ∃ (a : ℕ), ∃ (b : ℕ), a ^ bit0 1 + b ^ bit0 1 = p := sorry

