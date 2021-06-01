/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.logic

universes u l 

namespace Mathlib

class setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : equivalence r

protected instance setoid_has_equiv {α : Sort u} [setoid α] : has_equiv α := has_equiv.mk setoid.r

namespace setoid


theorem refl {α : Sort u} [setoid α] (a : α) : a ≈ a := sorry

theorem symm {α : Sort u} [setoid α] {a : α} {b : α} (hab : a ≈ b) : b ≈ a := sorry

theorem trans {α : Sort u} [setoid α] {a : α} {b : α} {c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  sorry

end Mathlib