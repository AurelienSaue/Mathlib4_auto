/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for constructing has_sizeof instance.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.rec_util
import Mathlib.Lean3Lib.init.meta.constructor_tactic
import PostPort

namespace Mathlib

namespace tactic


/- Retrieve the name of the type we are building a has_sizeof instance for. -/

