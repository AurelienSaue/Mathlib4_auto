/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.doc_commands
import Mathlib.PostPort

namespace Mathlib

/-!
# `generalize_proofs`

A simple tactic to find and replace all occurrences of proof terms in the
context and goal with new variables.
-/

namespace tactic


/-- Generalize proofs in the goal, naming them with the provided list. -/
namespace interactive


/-- Generalize proofs in the goal, naming them with the provided list.

For example:
```lean
example : list.nth_le [1, 2] 1 dec_trivial = 2 :=
begin
  -- ⊢ [1, 2].nth_le 1 _ = 2
  generalize_proofs h,
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nth_le 1 h = 2
end
```
-/
end interactive


