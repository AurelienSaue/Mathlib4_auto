/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.chain
import Mathlib.data.quot
import Mathlib.PostPort

namespace Mathlib

namespace tactic


/-- Auxiliary tactic for `trunc_cases`. -/
/-- Auxiliary tactic for `trunc_cases`. -/
/-- Auxiliary tactic for `trunc_cases`. -/
namespace interactive


/--
`trunc_cases e` performs case analysis on a `trunc` expression `e`,
attempting the following strategies:
1. when the goal is a subsingleton, calling `induction e using trunc.rec_on_subsingleton`,
2. when the goal does not depend on `e`, calling `fapply trunc.lift_on e`,
   and using `intro` and `clear` afterwards to make the goals look like we used `induction`,
3. otherwise, falling through to `trunc.rec_on`, and in the new invariance goal
   calling `cases h_p` on the useless `h_p : true` hypothesis,
   and then attempting to simplify the `eq.rec`.

`trunc_cases e with h` names the new hypothesis `h`.
If `e` is a local hypothesis already,
`trunc_cases` defaults to reusing the same name.

`trunc_cases e with h h_a h_b` will use the names `h_a` and `h_b` for the new hypothesis
in the invariance goal if `trunc_cases` uses `trunc.lift_on` or `trunc.rec_on`.

Finally, if the new hypothesis from inside the `trunc` is a type class,
`trunc_cases` resets the instance cache so that it is immediately available.
-/
end interactive


end tactic


