/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.default
import Mathlib.Lean3Lib.init.meta.simp_tactic
import Mathlib.Lean3Lib.init.meta.smt.congruence_closure
import Mathlib.Lean3Lib.init.meta.smt.ematch
import Mathlib.PostPort

universes l 

namespace Mathlib

/--
  Configuration for the smt tactic preprocessor. The preprocessor
  is applied whenever a new hypothesis is introduced.

  - simp_attr: is the attribute name for the simplification lemmas
    that are used during the preprocessing step.

  - max_steps: it is the maximum number of steps performed by the simplifier.

  - zeta: if tt, then zeta reduction (i.e., unfolding let-expressions)
    is used during preprocessing.
-/
structure smt_pre_config 
where
  simp_attr : name
  max_steps : ℕ
  zeta : Bool

/--
Configuration for the smt_state object.

- em_attr: is the attribute name for the hinst_lemmas
  that are used for ematching -/
structure smt_config 
where
  cc_cfg : cc_config
  em_cfg : ematch_config
  pre_cfg : smt_pre_config
  em_attr : name

