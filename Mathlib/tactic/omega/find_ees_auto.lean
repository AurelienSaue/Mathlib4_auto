/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.omega.eq_elim
import Mathlib.PostPort

universes l 

namespace Mathlib

/-
A tactic for finding a sequence of equality
elimination rules for a given set of constraints.
-/

namespace omega


/-- The state of equality elimination proof search. `eqs` is the list of
    equality constraints, and each `t ∈ eqs` represents the constraint `0 = t`.
    Similarly, `les` is the list of inequality constraints, and each `t ∈ eqs`
    represents the constraint `0 < t`. `ees` is the sequence of equality
    elimination steps that have been used so far to obtain the current set of
    constraints. The list `ees` grows over time until `eqs` becomes empty. -/
structure ee_state where
  eqs : List term
  les : List term
  ees : List ee

/-- Get the current list of equality constraints. -/
/-- Get the current list of inequality constraints. -/
/-- Get the current sequence of equality elimiation steps. -/
/-- Update the list of equality constraints. -/
/-- Update the list of inequality constraints. -/
/-- Update the sequence of equality elimiation steps. -/
/-- Add a new step to the sequence of equality elimination steps. -/
/-- Return the first equality constraint in the current list of
    equality constraints. The returned constraint is 'popped' and
    no longer available in the state. -/
/-- If `t1` succeeds and returns a value, 'commit' to that choice and
    run `t3` with the returned value as argument. Do not backtrack
    to try `t2` even if `t3` fails. If `t1` fails outright, run `t2`. -/
/-- GCD of all elements of the list. -/
def gcd : List ℤ → ℕ := sorry

end Mathlib