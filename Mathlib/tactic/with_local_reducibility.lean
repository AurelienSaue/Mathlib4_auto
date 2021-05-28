/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

universes l 

namespace Mathlib

/-!
# `with_local_reducibility`

Run a tactic in an environment with a temporarily modified reducibility attribute
for a specified declaration.
-/

namespace tactic


/-- Possible reducibility attributes for a declaration:
reducible, semireducible (the default), irreducible. -/
inductive decl_reducibility 
where
| reducible : decl_reducibility
| semireducible : decl_reducibility
| irreducible : decl_reducibility

/-- Satisfy the inhabited linter -/
protected instance decl_reducibility.inhabited : Inhabited decl_reducibility :=
  { default := decl_reducibility.semireducible }

/-- Get the reducibility attribute of a declaration.
Fails if the name does not refer to an existing declaration. -/
/-- Return the attribute (as a `name`) corresponding to a reducibility level. -/
def decl_reducibility.to_attribute : decl_reducibility → name :=
  sorry

