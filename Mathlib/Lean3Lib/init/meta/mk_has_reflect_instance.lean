/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Helper tactic for constructing a has_reflect instance.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.rec_util
 

namespace Mathlib

namespace tactic


/- Retrieve the name of the type we are building a has_reflect instance for. -/

