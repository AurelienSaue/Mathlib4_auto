/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.ordered_ring
import Mathlib.order.bounded_lattice
import Mathlib.PostPort

universes l u_1 

namespace Mathlib

namespace tactic.interactive


structure mono_cfg 
where
  unify : Bool

inductive mono_selection 
where
| left : mono_selection
| right : mono_selection
| both : mono_selection

def last_two {α : Type u_1} (l : List α) : Option (α × α) :=
  sorry

def mono_key :=
  with_bot name × with_bot name

