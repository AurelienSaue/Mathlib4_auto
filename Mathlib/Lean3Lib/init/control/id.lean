/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The identity monad.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.lift
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

def id_bind {α : Type u} {β : Type u} (x : α) (f : α → id β) : id β :=
  f x

protected instance id.monad : Monad id := sorry

protected instance id.monad_run : monad_run id id :=
  monad_run.mk id

