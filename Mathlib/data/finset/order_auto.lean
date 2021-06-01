/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finset.basic
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Finsets of ordered types
-/

theorem directed.finset_le {α : Type u} {r : α → α → Prop} [is_trans α r] {ι : Type u_1}
    [hι : Nonempty ι] {f : ι → α} (D : directed r f) (s : finset ι) :
    ∃ (z : ι), ∀ (i : ι), i ∈ s → r (f i) (f z) :=
  sorry

theorem finset.exists_le {α : Type u} [Nonempty α] [directed_order α] (s : finset α) :
    ∃ (M : α), ∀ (i : α), i ∈ s → i ≤ M :=
  directed.finset_le directed_order.directed s

end Mathlib