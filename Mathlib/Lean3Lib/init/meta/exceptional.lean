/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.monad
import Mathlib.Lean3Lib.init.meta.format
import Mathlib.Lean3Lib.init.util
import Mathlib.PostPort

namespace Mathlib

/-
Remark: we use a function that produces a format object as the exception information.
Motivation: the formatting object may be big, and we may create it on demand.
-/

/-- An exceptional is similar to `Result` in Haskell.-/
