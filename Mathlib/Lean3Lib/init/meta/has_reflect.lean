/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.expr
import Mathlib.Lean3Lib.init.util
import PostPort

namespace Mathlib

/-- `has_reflect α` lets you produce an `expr` from an instance of α. That is, it is a function from α to expr such that the expr has type α. -/
