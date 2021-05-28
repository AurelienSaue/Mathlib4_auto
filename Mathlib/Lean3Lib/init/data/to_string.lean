/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.string.basic
import Mathlib.Lean3Lib.init.data.bool.basic
import Mathlib.Lean3Lib.init.data.subtype.basic
import Mathlib.Lean3Lib.init.data.unsigned.basic
import Mathlib.Lean3Lib.init.data.prod
import Mathlib.Lean3Lib.init.data.sum.basic
import Mathlib.Lean3Lib.init.data.nat.div
import Mathlib.Lean3Lib.init.data.repr
import PostPort

universes u l v 

namespace Mathlib

/-- Convert the object into a string for tracing/display purposes. 
Similar to Haskell's `show`.
See also `has_repr`, which is used to output a string which is a valid lean code.
See also `has_to_format` and `has_to_tactic_format`, `format` has additional support for colours and pretty printing multilines.
 -/
