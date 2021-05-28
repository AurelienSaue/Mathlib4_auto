/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.logic
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace subtype


def exists_of_subtype {α : Type u} {p : α → Prop} : (Subtype fun (x : α) => p x) → ∃ (x : α), p x :=
  sorry

theorem tag_irrelevant {α : Type u} {p : α → Prop} {a : α} (h1 : p a) (h2 : p a) : { val := a, property := h1 } = { val := a, property := h2 } :=
  rfl

protected theorem eq {α : Type u} {p : α → Prop} {a1 : Subtype fun (x : α) => p x} {a2 : Subtype fun (x : α) => p x} : val a1 = val a2 → a1 = a2 := sorry

theorem ne_of_val_ne {α : Type u} {p : α → Prop} {a1 : Subtype fun (x : α) => p x} {a2 : Subtype fun (x : α) => p x} : val a1 ≠ val a2 → a1 ≠ a2 :=
  mt (congr_arg fun {a1 : Subtype fun (x : α) => p x} => val a1)

@[simp] theorem eta {α : Type u} {p : α → Prop} (a : Subtype fun (x : α) => p x) (h : p (val a)) : { val := val a, property := h } = a :=
  subtype.eq rfl

end subtype


protected instance subtype.inhabited {α : Type u} {p : α → Prop} {a : α} (h : p a) : Inhabited (Subtype fun (x : α) => p x) :=
  { default := { val := a, property := h } }

