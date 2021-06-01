/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

namespace tactic


namespace elide


end elide


namespace interactive


/-- The `elide n (at ...)` tactic hides all subterms of the target goal or hypotheses
beyond depth `n` by replacing them with `hidden`, which is a variant
on the identity function. (Tactics should still mostly be able to see
through the abbreviation, but if you want to unhide the term you can use
`unelide`.) -/
/-- The `unelide (at ...)` tactic removes all `hidden` subterms in the target
types (usually added by `elide`). -/
/--
The `elide n (at ...)` tactic hides all subterms of the target goal or hypotheses
end Mathlib