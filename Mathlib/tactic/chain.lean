/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.ext
import Mathlib.PostPort

universes l 

namespace Mathlib

namespace tactic


/-
This file defines a `chain` tactic, which takes a list of tactics, and exhaustively tries to apply them
to the goals, until no tactic succeeds on any goal.

Along the way, it generates auxiliary declarations, in order to speed up elaboration time
of the resulting (sometimes long!) proofs.

This tactic is used by the `tidy` tactic.
-/

-- α is the return type of our tactics. When `chain` is called by `tidy`, this is string,

-- describing what that tactic did as an interactive tactic.

def tactic_script (α : Type) :=
  _nest_1_1.tactic.tactic_script

