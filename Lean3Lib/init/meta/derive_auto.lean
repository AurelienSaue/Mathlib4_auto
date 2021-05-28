/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Attribute that can automatically derive typeclass instances.
-/
import PrePort
import Lean3Lib.init.meta.attribute
import Lean3Lib.init.meta.interactive_base
import Lean3Lib.init.meta.mk_has_reflect_instance
import Lean3Lib.init.meta.mk_has_sizeof_instance
import Lean3Lib.init.meta.mk_inhabited_instance
import PostPort

namespace Mathlib

/-- A handler that may or may not be able to implement the typeclass `cls` for `decl`.
    It should return `tt` if it was able to derive `cls` and `ff` if it does not know
    how to derive `cls`, in which case lower-priority handlers will be tried next. -/
