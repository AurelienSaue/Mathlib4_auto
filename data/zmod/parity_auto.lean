/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.parity
import Mathlib.data.zmod.basic
import PostPort

namespace Mathlib

/-!
# Relating parity to natural numbers mod 2

This module provides lemmas relating `zmod 2` to `even` and `odd`.

## Tags

parity, zmod, even, odd
-/

namespace zmod


theorem eq_zero_iff_even {n : ℕ} : ↑n = 0 ↔ even n :=
  iff.trans (char_p.cast_eq_zero_iff (zmod (bit0 1)) (bit0 1) n) (iff.symm even_iff_two_dvd)

theorem eq_one_iff_odd {n : ℕ} : ↑n = 1 ↔ odd n := sorry

theorem ne_zero_iff_odd {n : ℕ} : ↑n ≠ 0 ↔ odd n := sorry

