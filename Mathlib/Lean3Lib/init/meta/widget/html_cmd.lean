/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.widget.basic
import Mathlib.Lean3Lib.init.meta.lean.parser
import Mathlib.Lean3Lib.init.meta.interactive_base
import Mathlib.Lean3Lib.init.data.punit
 

namespace Mathlib

/-- Accepts terms with the type `component tactic_state empty` or `html empty` and
renders them interactively. -/
