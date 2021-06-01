/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# Natural number logarithm

This file defines `log b n`, the logarithm of `n` with base `b`, to be the largest `k` such that
`b ^ k ≤ n`.

-/

namespace nat


/-- `log b n`, is the logarithm of natural number `n` in base `b`. It returns the largest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`. -/
def log (b : ℕ) : ℕ → ℕ := sorry

theorem pow_le_iff_le_log (x : ℕ) (y : ℕ) {b : ℕ} (hb : 1 < b) (hy : 1 ≤ y) :
    b ^ x ≤ y ↔ x ≤ log b y :=
  sorry

theorem log_pow (b : ℕ) (x : ℕ) (hb : 1 < b) : log b (b ^ x) = x := sorry

theorem pow_succ_log_gt_self (b : ℕ) (x : ℕ) (hb : 1 < b) (hy : 1 ≤ x) :
    x < b ^ Nat.succ (log b x) :=
  sorry

theorem pow_log_le_self (b : ℕ) (x : ℕ) (hb : 1 < b) (hx : 1 ≤ x) : b ^ log b x ≤ x :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (b ^ log b x ≤ x)) (propext (pow_le_iff_le_log (log b x) x hb hx))))
    (le_refl (log b x))

end Mathlib