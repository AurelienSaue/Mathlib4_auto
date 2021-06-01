/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.specific_limits
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Hofer's lemma

This is an elementary lemma about complete metric spaces. It is motivated by an
application to the bubbling-off analysis for holomorphic curves in symplectic topology.
We are *very* far away from having these applications, but the proof here is a nice
example of a proof needing to construct a sequence by induction in the middle of the proof.

## References:

* H. Hofer and C. Viterbo, *The Weinstein conjecture in the presence of holomorphic spheres*
-/

theorem hofer {X : Type u_1} [metric_space X] [complete_space X] (x : X) (ε : ℝ) (ε_pos : 0 < ε)
    {ϕ : X → ℝ} (cont : continuous ϕ) (nonneg : ∀ (y : X), 0 ≤ ϕ y) :
    ∃ (ε' : ℝ),
        ∃ (H : ε' > 0),
          ∃ (x' : X),
            ε' ≤ ε ∧
              dist x' x ≤ bit0 1 * ε ∧
                ε * ϕ x ≤ ε' * ϕ x' ∧ ∀ (y : X), dist x' y ≤ ε' → ϕ y ≤ bit0 1 * ϕ x' :=
  sorry

end Mathlib