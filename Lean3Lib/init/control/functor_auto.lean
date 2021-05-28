/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Sebastian Ullrich, Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.core
import Lean3Lib.init.function
import Lean3Lib.init.meta.name
import PostPort

universes u v l 

namespace Mathlib

not foundinfixr:100 " <$> " => Mathlib.functor.map

infixr:100 " <$ " => Mathlib.functor.map_const

def functor.map_const_rev {f : Type u → Type v} [Functor f] {α : Type u} {β : Type u} : f β → α → f α :=
  fun (a : f β) (b : α) => b <$ a

infixr:100 " $> " => Mathlib.functor.map_const_rev

