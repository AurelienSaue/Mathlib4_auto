/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for showing that a type has decidable equality.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.tactic
import Mathlib.Lean3Lib.init.data.option.basic
import PostPort

namespace Mathlib

namespace tactic


/-- Return tt iff e's type is of the form `(I_name ...)` -/
