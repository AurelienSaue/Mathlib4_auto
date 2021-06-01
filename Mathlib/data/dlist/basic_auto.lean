/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.Lean3Lib.data.dlist
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-- Concatenates a list of difference lists to form a single
difference list.  Similar to `list.join`. -/
def dlist.join {α : Type u_1} : List (dlist α) → dlist α := sorry

@[simp] theorem dlist_singleton {α : Type u_1} {a : α} :
    dlist.singleton a = dlist.lazy_of_list fun (_ : Unit) => [a] :=
  rfl

@[simp] theorem dlist_lazy {α : Type u_1} {l : List α} :
    (dlist.lazy_of_list fun (_ : Unit) => l) = dlist.of_list l :=
  rfl

end Mathlib