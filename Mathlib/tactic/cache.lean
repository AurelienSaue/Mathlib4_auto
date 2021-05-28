/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.doc_commands
import Mathlib.PostPort

namespace Mathlib

/-!
# Instance cache tactics

For performance reasons, Lean does not automatically update its database
of class instances during a proof. The group of tactics in this file
helps to force such updates.

-/

namespace tactic


/-- Reset the instance cache for the main goal. -/
/-- Unfreeze the local instances while executing `tac` on the main goal. -/
/--
Unfreeze local instances while executing `tac`,
if the passed expression is amongst the frozen instances.
-/
namespace interactive


/--
`unfreezingI { tac }` executes tac while temporarily unfreezing the instance cache.
-/
/-- Reset the instance cache. This allows any new instances
added to the context to be used in typeclass inference. -/
/-- Like `subst`, but can also substitute in instance arguments. -/
/-- Like `cases`, but can also be used with instance arguments. -/
/-- Like `intro`, but uses the introduced variable
in typeclass inference. -/
/-- Like `intros`, but uses the introduced variable(s)
in typeclass inference. -/
/-- Used to add typeclasses to the context so that they can
be used in typeclass inference. The syntax is the same as `have`,
but the proof-omitted version is not supported. For
this one must write `have : t, { <proof> }, resetI, <proof>`. -/
/-- Used to add typeclasses to the context so that they can
be used in typeclass inference. The syntax is the same as `let`. -/
/-- Like `exact`, but uses all variables in the context
for typeclass inference. -/
/--
For performance reasons, Lean does not automatically update its database
