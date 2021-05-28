/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
import PrePort
import Lean3Lib.init.meta.widget.basic
import Lean3Lib.init.meta.lean.parser
import Lean3Lib.init.meta.interactive_base
import Lean3Lib.init.data.punit
import PostPort

namespace Mathlib

/-- Accepts terms with the type `component tactic_state empty` or `html empty` and
renders them interactively. -/
