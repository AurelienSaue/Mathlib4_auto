/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import PrePort
import Lean3Lib.init.default
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Extra facts about `pprod`
-/

@[simp] theorem pprod.mk.eta {α : Sort u_1} {β : Sort u_2} {p : PProd α β} : { fst := pprod.fst p, snd := pprod.snd p } = p :=
  pprod.cases_on p fun (a : α) (b : β) => rfl

