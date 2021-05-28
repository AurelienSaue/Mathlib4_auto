/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.meta.interactive_base
import Lean3Lib.init.meta.tactic
import Lean3Lib.init.meta.set_get_option_tactics
import PostPort

universes l 

namespace Mathlib

/- If tt, congruence closure will treat implicit instance arguments as constants. -/

structure cc_config 
where
  ignore_instances : Bool
  ac : Bool
  ho_fns : Option (List name)
  em : Bool

