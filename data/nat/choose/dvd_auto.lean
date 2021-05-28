/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.choose.basic
import Mathlib.data.nat.prime
import PostPort

namespace Mathlib

/-!
# Divisibility properties of binomial coefficients
-/

namespace nat


namespace prime


theorem dvd_choose_add {p : ℕ} {a : ℕ} {b : ℕ} (hap : a < p) (hbp : b < p) (h : p ≤ a + b) (hp : prime p) : p ∣ choose (a + b) a := sorry

theorem dvd_choose_self {p : ℕ} {k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : prime p) : p ∣ choose p k := sorry

