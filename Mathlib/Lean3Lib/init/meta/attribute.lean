/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.tactic
import Mathlib.Lean3Lib.init.meta.rb_map
import Mathlib.Lean3Lib.init.meta.has_reflect
import Mathlib.Lean3Lib.init.meta.lean.parser
import PostPort

namespace Mathlib

/-- Get all of the declaration names that have the given attribute.
Eg. ``get_instances `simp`` returns a list with the names of all of the lemmas in the environment tagged with the `@[simp]` attribute.
 -/
/-- Returns a hash of `get_instances`. You can use this to tell if your attribute instances have changed. -/
