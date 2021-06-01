/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.smt.congruence_closure
import Mathlib.Lean3Lib.init.meta.attribute
import Mathlib.Lean3Lib.init.meta.simp_tactic
import Mathlib.Lean3Lib.init.meta.interactive_base
import Mathlib.Lean3Lib.init.meta.derive

universes l 

namespace Mathlib

/-- Heuristic instantiation lemma -/
/-- `mk_core m e as_simp`, m is used to decide which definitions will be unfolded in patterns.
   If as_simp is tt, then this tactic will try to use the left-hand-side of the conclusion
   as a pattern. -/
/--
Create a new "cached" attribute (attr_name : user_attribute hinst_lemmas).
It also creates "cached" attributes for each attr_names and simp_attr_names if they have not been defined
yet. Moreover, the hinst_lemmas for attr_name will be the union of the lemmas tagged with
    attr_name, attrs_name, and simp_attr_names.
For the ones in simp_attr_names, we use the left-hand-side of the conclusion as the pattern.
-/
structure ematch_config where
  max_instances : ℕ
  max_generation : ℕ

end Mathlib