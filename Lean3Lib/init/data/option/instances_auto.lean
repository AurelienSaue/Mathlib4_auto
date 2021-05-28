/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.data.option.basic
import Lean3Lib.init.meta.tactic
import Lean3Lib.init.control.lawful
import PostPort

universes u_1 u 

namespace Mathlib

protected instance option.is_lawful_monad : is_lawful_monad Option :=
  is_lawful_monad.mk (fun (α β : Type u_1) (x : α) (f : α → Option β) => rfl)
    fun (α β γ : Type u_1) (x : Option α) (f : α → Option β) (g : β → Option γ) => Option.rec rfl (fun (x : α) => rfl) x

theorem option.eq_of_eq_some {α : Type u} {x : Option α} {y : Option α} : (∀ (z : α), x = some z ↔ y = some z) → x = y := sorry

theorem option.eq_some_of_is_some {α : Type u} {o : Option α} (h : ↥(option.is_some o)) : o = some (option.get h) := sorry

theorem option.eq_none_of_is_none {α : Type u} {o : Option α} : ↥(option.is_none o) → o = none := sorry

