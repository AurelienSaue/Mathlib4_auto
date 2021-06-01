/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.uniform_space.cauchy
import Mathlib.topology.uniform_space.separation
import Mathlib.topology.dense_embedding
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Theory of complete separated uniform spaces.

This file is for elementary lemmas that depend on both Cauchy filters and separation.
-/

/-In a separated space, a complete set is closed -/

theorem is_complete.is_closed {α : Type u_1} [uniform_space α] [separated_space α] {s : set α}
    (h : is_complete s) : is_closed s :=
  sorry

namespace dense_inducing


theorem continuous_extend_of_cauchy {α : Type u_1} [topological_space α] {β : Type u_2}
    [topological_space β] {γ : Type u_3} [uniform_space γ] [complete_space γ] [separated_space γ]
    {e : α → β} {f : α → γ} (de : dense_inducing e)
    (h : ∀ (b : β), cauchy (filter.map f (filter.comap e (nhds b)))) : continuous (extend de f) :=
  continuous_extend de fun (b : β) => complete_space.complete (h b)

end Mathlib