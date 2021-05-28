/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.list.lemmas
import Mathlib.Lean3Lib.init.wf
import PostPort

universes u_1 

namespace Mathlib

namespace list


-- Note: we can't use the equation compiler here because

-- init.meta.well_founded_tactics uses this file

def qsort.F {α : Type u_1} (lt : α → α → Bool) (x : List α) : ((y : List α) → length y < length x → List α) → List α :=
  sorry

/- This is based on the minimalist Haskell "quicksort".

   Remark: this is *not* really quicksort since it doesn't partition the elements in-place -/

def qsort {α : Type u_1} (lt : α → α → Bool) : List α → List α :=
  well_founded.fix sorry sorry

@[simp] theorem qsort_nil {α : Type u_1} (lt : α → α → Bool) : qsort lt [] = [] := sorry

@[simp] theorem qsort_cons {α : Type u_1} (lt : α → α → Bool) (h : α) (t : List α) : qsort lt (h :: t) =
  (fun (_a : List α × List α) =>
      prod.cases_on _a fun (fst snd : List α) => idRhs (List α) (qsort lt snd ++ h :: qsort lt fst))
    (partition (fun (x : α) => lt h x = tt) t) := sorry

