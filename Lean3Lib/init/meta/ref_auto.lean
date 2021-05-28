/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.meta.tactic
import PostPort

namespace Mathlib

namespace tactic


/-- A `ref` performs the role of a mutable variable within a tactic. -/
/-- Create a new reference `r` with initial value `a`, execute `t r`, and then delete `r`. -/
