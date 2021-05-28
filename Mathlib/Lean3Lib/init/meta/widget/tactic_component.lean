/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.widget.basic
import Mathlib.PostPort

namespace Mathlib

namespace widget


/-- A component that implicitly depends on tactic_state. For efficiency we always assume that the tactic_state is unchanged between component renderings. -/
