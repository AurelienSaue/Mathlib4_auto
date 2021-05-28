/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for showing that a type is inhabited.
-/
import PrePort
import Lean3Lib.init.meta.interactive_base
import Lean3Lib.init.meta.contradiction_tactic
import Lean3Lib.init.meta.constructor_tactic
import Lean3Lib.init.meta.injection_tactic
import Lean3Lib.init.meta.relation_tactics
import PostPort

namespace Mathlib

namespace tactic


/- Retrieve the name of the type we are building an inhabitant instance for. -/

