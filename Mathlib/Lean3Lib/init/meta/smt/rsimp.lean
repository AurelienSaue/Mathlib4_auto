/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.smt.smt_tactic
import Mathlib.Lean3Lib.init.meta.fun_info
import Mathlib.Lean3Lib.init.meta.rb_map
 

universes l 

namespace Mathlib

/-- Create a rsimp attribute named `attr_name`, the attribute declaration is named `attr_decl_name`.
    The cached hinst_lemmas structure is built using the lemmas marked with simp attribute `simp_attr_name`,
    but *not* marked with `ex_attr_name`.

    We say `ex_attr_name` is the "exception set". It is useful for excluding lemmas in `simp_attr_name`
    which are not good or redundant for ematching. -/
/- The following lemmas are not needed by rsimp, and they actually hurt performance since they generate a lot of
   instances. -/

namespace rsimp


/-- Return the size of term by considering only explicit arguments. -/
/-- Choose smallest element (with respect to explicit_size) in `e`s equivalence class. -/
structure config 
where
  attr_name : name
  max_rounds : ℕ

