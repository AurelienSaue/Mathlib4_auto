/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.mk_dec_eq_instance
import Mathlib.Lean3Lib.init.data.subtype.basic
import PostPort

universes u 

namespace Mathlib

protected instance subtype.decidable_eq {α : Type u} {p : α → Prop} [DecidableEq α] : DecidableEq (Subtype fun (x : α) => p x) :=
  id
    fun (_v : Subtype fun (x : α) => p x) =>
      subtype.cases_on _v
        fun (val : α) (property : p val) (w : Subtype fun (x : α) => p x) =>
          subtype.cases_on w
            fun (w_val : α) (w_property : p w_val) =>
              decidable.by_cases
                (fun (ᾰ : val = w_val) => Eq._oldrec (fun (w_property : p val) => is_true sorry) ᾰ w_property)
                fun (ᾰ : ¬val = w_val) => isFalse sorry

