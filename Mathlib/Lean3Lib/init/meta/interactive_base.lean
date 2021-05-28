/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.option.basic
import Mathlib.Lean3Lib.init.meta.lean.parser
import Mathlib.Lean3Lib.init.meta.tactic
import Mathlib.Lean3Lib.init.meta.has_reflect
import Mathlib.PostPort

universes l 

namespace Mathlib

namespace interactive


/-- (parse p) as the parameter type of an interactive tactic will instruct the Lean parser
    to run `p` when parsing the parameter and to pass the parsed value as an argument
    to the tactic. -/
/-- A `loc` is either a 'wildcard', which means "everywhere", or a list of `option name`s. `none` means `target` and `some n` means `n` in the local context.-/
inductive loc 
where
| wildcard : loc
| ns : List (Option name) → loc

