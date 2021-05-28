/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.uniform_space.completion
import Mathlib.topology.metric_space.isometry
import PostPort

universes u 

namespace Mathlib

/-!
# The completion of a metric space

Completion of uniform spaces are already defined in `topology.uniform_space.completion`. We show
here that the uniform space completion of a metric space inherits a metric space structure,
by extending the distance to the completion and checking that it is indeed a distance, and that
it defines the same uniformity as the already defined uniform structure on the completion
-/

namespace metric


/-- The distance on the completion is obtained by extending the distance on the original space,
by uniform continuity. -/
protected instance uniform_space.completion.has_dist {α : Type u} [metric_space α] : has_dist (uniform_space.completion α) :=
  has_dist.mk (uniform_space.completion.extension₂ dist)

/-- The new distance is uniformly continuous. -/
protected theorem completion.uniform_continuous_dist {α : Type u} [metric_space α] : uniform_continuous fun (p : uniform_space.completion α × uniform_space.completion α) => dist (prod.fst p) (prod.snd p) :=
  uniform_space.completion.uniform_continuous_extension₂ dist

/-- The new distance is an extension of the original distance. -/
protected theorem completion.dist_eq {α : Type u} [metric_space α] (x : α) (y : α) : dist ↑x ↑y = dist x y :=
  uniform_space.completion.extension₂_coe_coe uniform_continuous_dist x y

/- Let us check that the new distance satisfies the axioms of a distance, by starting from the
properties on α and extending them to `completion α` by continuity. -/

protected theorem completion.dist_self {α : Type u} [metric_space α] (x : uniform_space.completion α) : dist x x = 0 := sorry

protected theorem completion.dist_comm {α : Type u} [metric_space α] (x : uniform_space.completion α) (y : uniform_space.completion α) : dist x y = dist y x := sorry

protected theorem completion.dist_triangle {α : Type u} [metric_space α] (x : uniform_space.completion α) (y : uniform_space.completion α) (z : uniform_space.completion α) : dist x z ≤ dist x y + dist y z := sorry

/-- Elements of the uniformity (defined generally for completions) can be characterized in terms
of the distance. -/
protected theorem completion.mem_uniformity_dist {α : Type u} [metric_space α] (s : set (uniform_space.completion α × uniform_space.completion α)) : s ∈ uniformity (uniform_space.completion α) ↔
  ∃ (ε : ℝ), ∃ (H : ε > 0), ∀ {a b : uniform_space.completion α}, dist a b < ε → (a, b) ∈ s := sorry

/-- If two points are at distance 0, then they coincide. -/
protected theorem completion.eq_of_dist_eq_zero {α : Type u} [metric_space α] (x : uniform_space.completion α) (y : uniform_space.completion α) (h : dist x y = 0) : x = y := sorry

/-- Reformulate `completion.mem_uniformity_dist` in terms that are suitable for the definition
of the metric space structure. -/
protected theorem completion.uniformity_dist' {α : Type u} [metric_space α] : uniformity (uniform_space.completion α) =
  infi
    fun (ε : Subtype fun (ε : ℝ) => 0 < ε) =>
      filter.principal
        (set_of
          fun (p : uniform_space.completion α × uniform_space.completion α) =>
            dist (prod.fst p) (prod.snd p) < subtype.val ε) := sorry

protected theorem completion.uniformity_dist {α : Type u} [metric_space α] : uniformity (uniform_space.completion α) =
  infi
    fun (ε : ℝ) =>
      infi
        fun (H : ε > 0) =>
          filter.principal
            (set_of
              fun (p : uniform_space.completion α × uniform_space.completion α) => dist (prod.fst p) (prod.snd p) < ε) := sorry

/-- Metric space structure on the completion of a metric space. -/
protected instance completion.metric_space {α : Type u} [metric_space α] : metric_space (uniform_space.completion α) :=
  metric_space.mk completion.dist_self completion.eq_of_dist_eq_zero completion.dist_comm completion.dist_triangle
    (fun (x y : uniform_space.completion α) => ennreal.of_real (uniform_space.completion.extension₂ dist x y))
    (uniform_space.completion.uniform_space α)

/-- The embedding of a metric space in its completion is an isometry. -/
theorem completion.coe_isometry {α : Type u} [metric_space α] : isometry coe :=
  iff.mpr isometry_emetric_iff_metric completion.dist_eq

