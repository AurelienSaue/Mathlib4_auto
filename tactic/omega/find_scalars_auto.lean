/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.omega.term
import Mathlib.data.list.min_max
import PostPort

namespace Mathlib

/-
Tactic for performing Fourier–Motzkin elimination to find
a contradictory linear combination of input constraints.
-/

namespace omega


/-- Divide linear combinations into three groups by the coefficient of the
    `m`th variable in their resultant terms: negative, zero, or positive. -/
