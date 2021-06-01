/-
Copyright (c) 2019 Rob Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.simp_result
import Mathlib.PostPort

namespace Mathlib

namespace tactic


/--
`delta_instance ids` tries to solve the goal by calling `apply_instance`,
first unfolding the definitions in `ids`.
-/
-- We call `dsimp_result` here because otherwise

-- `delta_target` will insert an `id` in the result.

-- See the note [locally reducible category instances]

-- https://github.com/leanprover-community/mathlib/blob/c9fca15420e2ad443707ace831679fd1762580fe/src/algebra/category/Mon/basic.lean#L27

-- for an example where this used to cause a problem.

end Mathlib