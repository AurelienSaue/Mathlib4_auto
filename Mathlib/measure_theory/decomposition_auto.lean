/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Hahn decomposition theorem

TODO:
* introduce finite measures (into ℝ≥0)
* show general for signed measures (into ℝ)
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.measure_space
import Mathlib.PostPort

universes u_1 

namespace Mathlib

namespace measure_theory


-- suddenly this is necessary?!

theorem hahn_decomposition {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    (hμ : coe_fn μ set.univ < ⊤) (hν : coe_fn ν set.univ < ⊤) :
    ∃ (s : set α),
        is_measurable s ∧
          (∀ (t : set α), is_measurable t → t ⊆ s → coe_fn ν t ≤ coe_fn μ t) ∧
            ∀ (t : set α), is_measurable t → t ⊆ (sᶜ) → coe_fn μ t ≤ coe_fn ν t :=
  sorry

end Mathlib