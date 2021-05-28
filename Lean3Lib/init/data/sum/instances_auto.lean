/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.meta.mk_dec_eq_instance
import PostPort

universes u v 

namespace Mathlib

protected instance sum.decidable_eq {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] : DecidableEq (α ⊕ β) :=
  id
    fun (_v : α ⊕ β) =>
      sum.cases_on _v
        (fun (val : α) (w : α ⊕ β) =>
          sum.cases_on w
            (fun (w : α) =>
              decidable.by_cases (fun (ᾰ : val = w) => Eq._oldrec (is_true sorry) ᾰ) fun (ᾰ : ¬val = w) => isFalse sorry)
            fun (w : β) => isFalse sorry)
        fun (val : β) (w : α ⊕ β) =>
          sum.cases_on w (fun (w : α) => isFalse sorry)
            fun (w : β) =>
              decidable.by_cases (fun (ᾰ : val = w) => Eq._oldrec (is_true sorry) ᾰ) fun (ᾰ : ¬val = w) => isFalse sorry

