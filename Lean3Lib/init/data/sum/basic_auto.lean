/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
import PrePort
import Lean3Lib.init.logic
import PostPort

universes u v 

namespace Mathlib

infixr:30 " ⊕ " => Mathlib.sum

protected instance sum.inhabited_left {α : Type u} {β : Type v} [h : Inhabited α] : Inhabited (α ⊕ β) :=
  { default := sum.inl Inhabited.default }

protected instance sum.inhabited_right {α : Type u} {β : Type v} [h : Inhabited β] : Inhabited (α ⊕ β) :=
  { default := sum.inr Inhabited.default }

