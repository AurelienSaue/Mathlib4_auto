/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.metric_space.hausdorff_distance
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Riesz's lemma

Riesz's lemma, stated for a normed space over a normed field: for any
closed proper subspace F of E, there is a nonzero x such that ∥x - F∥
is at least r * ∥x∥ for any r < 1.
-/

/-- Riesz's lemma, which usually states that it is possible to find a
vector with norm 1 whose distance to a closed proper subspace is
arbitrarily close to 1. The statement here is in terms of multiples of
norms, since in general the existence of an element of norm exactly 1
is not guaranteed. -/
theorem riesz_lemma {𝕜 : Type u_1} [normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : subspace 𝕜 E} (hFc : is_closed ↑F) (hF : ∃ (x : E), ¬x ∈ F) {r : ℝ} (hr : r < 1) : ∃ (x₀ : E), ¬x₀ ∈ F ∧ ∀ (y : E), y ∈ F → r * norm x₀ ≤ norm (x₀ - y) := sorry

