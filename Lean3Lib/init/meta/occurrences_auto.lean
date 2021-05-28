/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.logic
import Lean3Lib.init.data.repr
import Lean3Lib.init.meta.format
import Lean3Lib.init.meta.contradiction_tactic
import Lean3Lib.init.meta.constructor_tactic
import Lean3Lib.init.meta.relation_tactics
import Lean3Lib.init.meta.injection_tactic
import PostPort

universes l 

namespace Mathlib

/--  We can specify the scope of application of some tactics using
   the following type.

   - all : all occurrences of a given term are considered.

   - pos [1, 3] : only the first and third occurrences of a given
     term are consiered.

   - neg [2] : all but the second occurrence of a given term
     are considered. -/
inductive occurrences 
where
| all : occurrences
| pos : List ℕ → occurrences
| neg : List ℕ → occurrences

def occurrences.contains : occurrences → ℕ → Bool :=
  sorry

protected instance occurrences.inhabited : Inhabited occurrences :=
  { default := occurrences.all }

def occurrences_repr : occurrences → string :=
  sorry

protected instance occurrences.has_repr : has_repr occurrences :=
  has_repr.mk occurrences_repr

