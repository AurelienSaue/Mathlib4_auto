/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.lift
import Mathlib.Lean3Lib.init.data.string.basic
 

universes u v l 

namespace Mathlib

class monad_fail (m : Type u → Type v) 
where
  fail : {a : Type u} → string → m a

def match_failed {α : Type u} {m : Type u → Type v} [monad_fail m] : m α := sorry

protected instance monad_fail_lift (m : Type u → Type v) (n : Type u → Type v) [Monad n] [monad_fail m] [has_monad_lift m n] : monad_fail n :=
  monad_fail.mk fun (α : Type u) (s : string) => monad_lift (monad_fail.fail s)

