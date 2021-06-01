/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Attribute that can automatically derive typeclass instances.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.attribute
import Mathlib.Lean3Lib.init.meta.interactive_base
import Mathlib.Lean3Lib.init.meta.mk_has_reflect_instance
import Mathlib.Lean3Lib.init.meta.mk_has_sizeof_instance
import Mathlib.Lean3Lib.init.meta.mk_inhabited_instance

namespace Mathlib

/-- A handler that may or may not be able to implement the typeclass `cls` for `decl`.
    It should return `tt` if it was able to derive `cls` and `ff` if it does not know
    how to derive `cls`, in which case lower-priority handlers will be tried next. -/
end Mathlib