/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Traversable instance for dlists.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.Lean3Lib.data.dlist
import Mathlib.control.traversable.equiv
import Mathlib.control.traversable.instances
import Mathlib.PostPort

universes u_1 

namespace Mathlib

namespace dlist


/-- The natural equivalence between lists and difference lists, using
`dlist.of_list` and `dlist.to_list`. -/
def list_equiv_dlist (α : Type u_1) : List α ≃ dlist α := equiv.mk of_list to_list sorry sorry

protected instance traversable : traversable dlist := equiv.traversable list_equiv_dlist

protected instance is_lawful_traversable : is_lawful_traversable dlist :=
  equiv.is_lawful_traversable list_equiv_dlist

protected instance inhabited {α : Type u_1} : Inhabited (dlist α) := { default := empty }

end Mathlib