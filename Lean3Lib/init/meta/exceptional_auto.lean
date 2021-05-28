/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.control.monad
import Lean3Lib.init.meta.format
import Lean3Lib.init.util
import PostPort

namespace Mathlib

/-
Remark: we use a function that produces a format object as the exception information.
Motivation: the formatting object may be big, and we may create it on demand.
-/

/-- An exceptional is similar to `Result` in Haskell.-/
