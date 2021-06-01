/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.logic

universes u v u₁ u₂ v₁ v₂ 

namespace Mathlib

@[simp] theorem prod.mk.eta {α : Type u} {β : Type v} {p : α × β} : (prod.fst p, prod.snd p) = p :=
  prod.cases_on p
    fun (p_fst : α) (p_snd : β) =>
      idRhs
        ((prod.fst (p_fst, p_snd), prod.snd (p_fst, p_snd)) =
          (prod.fst (p_fst, p_snd), prod.snd (p_fst, p_snd)))
        rfl

protected instance prod.inhabited {α : Type u} {β : Type v} [Inhabited α] [Inhabited β] :
    Inhabited (α × β) :=
  { default := (Inhabited.default, Inhabited.default) }

protected instance prod.decidable_eq {α : Type u} {β : Type v} [h₁ : DecidableEq α]
    [h₂ : DecidableEq β] : DecidableEq (α × β) :=
  sorry

protected instance prod.has_lt {α : Type u} {β : Type v} [HasLess α] [HasLess β] :
    HasLess (α × β) :=
  { Less :=
      fun (s t : α × β) =>
        prod.fst s < prod.fst t ∨ prod.fst s = prod.fst t ∧ prod.snd s < prod.snd t }

protected instance prod_has_decidable_lt {α : Type u} {β : Type v} [HasLess α] [HasLess β]
    [DecidableEq α] [DecidableEq β] [DecidableRel Less] [DecidableRel Less] (s : α × β)
    (t : α × β) : Decidable (s < t) :=
  or.decidable

theorem prod.lt_def {α : Type u} {β : Type v} [HasLess α] [HasLess β] (s : α × β) (t : α × β) :
    s < t = (prod.fst s < prod.fst t ∨ prod.fst s = prod.fst t ∧ prod.snd s < prod.snd t) :=
  rfl

def prod.map {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂} (f : α₁ → α₂) (g : β₁ → β₂)
    (x : α₁ × β₁) : α₂ × β₂ :=
  (f (prod.fst x), g (prod.snd x))

end Mathlib