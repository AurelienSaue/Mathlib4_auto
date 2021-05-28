/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.omega.find_ees
import Mathlib.tactic.omega.find_scalars
import Mathlib.tactic.omega.lin_comb
import PostPort

namespace Mathlib

/-
A tactic which constructs exprs to discharge
goals of the form `clauses.unsat cs`.
-/

namespace omega


/-- Return expr of proof that given int is negative -/
theorem forall_mem_repeat_zero_eq_zero (m : ℕ) (x : ℤ) (H : x ∈ list.repeat 0 m) : x = 0 :=
  list.eq_of_mem_repeat

