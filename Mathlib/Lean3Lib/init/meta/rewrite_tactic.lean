/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.relation_tactics
import Mathlib.Lean3Lib.init.meta.occurrences
import PostPort

universes l 

namespace Mathlib

namespace tactic


/-- Configuration options for the `rewrite` tactic. -/
structure rewrite_cfg 
extends apply_cfg
where
  symm : Bool
  occs : occurrences

