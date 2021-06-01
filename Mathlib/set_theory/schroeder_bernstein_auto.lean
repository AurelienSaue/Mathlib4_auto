/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

The Schröder-Bernstein theorem, and well ordering of cardinals.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.fixed_points
import Mathlib.order.zorn
import Mathlib.PostPort

universes u v 

namespace Mathlib

namespace function


namespace embedding


theorem schroeder_bernstein {α : Type u} {β : Type v} {f : α → β} {g : β → α} (hf : injective f)
    (hg : injective g) : ∃ (h : α → β), bijective h :=
  sorry

theorem antisymm {α : Type u} {β : Type v} : (α ↪ β) → (β ↪ α) → Nonempty (α ≃ β) := sorry

theorem min_injective {ι : Type u} {β : ι → Type v} (I : Nonempty ι) :
    ∃ (i : ι), Nonempty ((j : ι) → β i ↪ β j) :=
  sorry

theorem total {α : Type u} {β : Type v} : Nonempty (α ↪ β) ∨ Nonempty (β ↪ α) := sorry

end Mathlib