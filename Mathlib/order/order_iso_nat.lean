/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.basic
import Mathlib.order.rel_iso
import Mathlib.logic.function.iterate
import Mathlib.PostPort

universes u_1 

namespace Mathlib

namespace rel_embedding


/-- If `f` is a strictly `r`-increasing sequence, then this returns `f` as an order embedding. -/
def nat_lt {α : Type u_1} {r : α → α → Prop} [is_strict_order α r] (f : ℕ → α) (H : ∀ (n : ℕ), r (f n) (f (n + 1))) : Less ↪r r :=
  of_monotone f sorry

/-- If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order embedding. -/
def nat_gt {α : Type u_1} {r : α → α → Prop} [is_strict_order α r] (f : ℕ → α) (H : ∀ (n : ℕ), r (f (n + 1)) (f n)) : gt ↪r r :=
  rel_embedding.swap (nat_lt f H)

theorem well_founded_iff_no_descending_seq {α : Type u_1} {r : α → α → Prop} [is_strict_order α r] : well_founded r ↔ ¬Nonempty (gt ↪r r) := sorry

