/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.solve_by_elim
import Mathlib.tactic.interactive
import PostPort

namespace Mathlib

namespace tactic


namespace hint


/-- An attribute marking a `tactic unit` or `tactic string` which should be used by the `hint`
tactic. -/
/--
`add_hint_tactic t` runs the tactic `t` whenever `hint` is invoked.
The typical use case is `add_hint_tactic "foo"` for some interactive tactic `foo`.
-/
end hint


/--
Report a list of tactics that can make progress against the current goal,
and for each such tactic, the number of remaining goals afterwards.
-/
namespace interactive


/--
Report a list of tactics that can make progress against the current goal.
-/
/--
`hint` lists possible tactics which will make progress (that is, not fail) against the current goal.
