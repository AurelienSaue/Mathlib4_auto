/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.applicative
import Mathlib.PostPort

universes u v l 

namespace Mathlib

not founddef has_bind.and_then {α : Type u} {β : Type u} {m : Type u → Type v} [Bind m] (x : m α) (y : m β) : m β :=
  do 
    x 
    y

infixl:55 " >>= " => Mathlib.has_bind.bind

infixl:55 " >> " => Mathlib.has_bind.and_then

not founddef return {m : Type u → Type v} [Monad m] {α : Type u} : α → m α :=
  pure

/- Identical to has_bind.and_then, but it is not inlined. -/

def has_bind.seq {α : Type u} {β : Type u} {m : Type u → Type v} [Bind m] (x : m α) (y : m β) : m β :=
  do 
    x 
    y

