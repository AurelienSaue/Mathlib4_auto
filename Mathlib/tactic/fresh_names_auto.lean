/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.sum
import Mathlib.meta.rb_map
import Mathlib.tactic.dependencies
import Mathlib.PostPort

namespace Mathlib

/-!
# Tactics for giving hypotheses fresh names

When introducing hypotheses, we often want to make sure that their names are
fresh, i.e. not used by any other hypothesis in the context. This file provides
tactics which allow you to give a list of possible names for each hypothesis,
with the tactics picking the first name that is not yet used in the context. If
all names are already used, the tactics use a name derived from the first name
in the list.
-/

namespace tactic


-- This implementation is a bit of a hack, but probably fine in practice since

-- we're unlikely to need more than two or three iterations of the loop.

end Mathlib