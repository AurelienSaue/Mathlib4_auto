/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.omega.int.main
import Mathlib.tactic.omega.nat.main
import PostPort

namespace Mathlib

/-
A tactic for discharging linear integer & natural
number arithmetic goals using the Omega test.
-/

namespace omega


/-- Detects domain of a formula from its expr.
* Returns none, if domain can be either ℤ or ℕ
* Returns some tt, if domain is exclusively ℤ
* Returns some ff, if domain is exclusively ℕ
* Fails, if domain is neither ℤ nor ℕ -/
/-- Use the current goal to determine.
    Return tt if the domain is ℤ, and return ff if it is ℕ -/
/-- Return tt if the domain is ℤ, and return ff if it is ℕ -/
end omega


/-- Attempts to discharge goals in the quantifier-free fragment of
linear integer and natural number arithmetic using the Omega test.
Guesses the correct domain by looking at the goal and hypotheses,
and then reverts all relevant hypotheses and variables.
Use `omega manual` to disable automatic reverts, and `omega int` or
`omega nat` to specify the domain.
-/
/--
`omega` attempts to discharge goals in the quantifier-free fragment of linear integer and natural
