/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for showing that a type has decidable equality.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.contradiction_tactic
import Mathlib.Lean3Lib.init.meta.constructor_tactic
import Mathlib.Lean3Lib.init.meta.injection_tactic
import Mathlib.Lean3Lib.init.meta.relation_tactics
import Mathlib.Lean3Lib.init.meta.rec_util
import Mathlib.Lean3Lib.init.meta.interactive
 

namespace Mathlib

namespace tactic


/- Retrieve the name of the type we are building a decidable equality proof for. -/

