/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.meta.tactic
import Lean3Lib.init.function
import PostPort

namespace Mathlib

namespace tactic


/- Return target after instantiating metavars and whnf -/

