/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.metric_space.hausdorff_distance
import Mathlib.analysis.specific_limits
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Closed subsets

This file defines the metric and emetric space structure on the types of closed subsets and nonempty compact
subsets of a metric or emetric space.

The Hausdorff distance induces an emetric space structure on the type of closed subsets
of an emetric space, called `closeds`. Its completeness, resp. compactness, resp.
second-countability, follow from the corresponding properties of the original space.

In a metric space, the type of nonempty compact subsets (called `nonempty_compacts`) also
inherits a metric space structure from the Hausdorff distance, as the Hausdorff edistance is
always finite in this context.
-/

namespace emetric


/-- In emetric spaces, the Hausdorff edistance defines an emetric space structure
on the type of closed subsets -/
protected instance closeds.emetric_space {α : Type u} [emetric_space α] : emetric_space (topological_space.closeds α) :=
  emetric_space.mk sorry sorry sorry sorry
    (uniform_space_of_edist (fun (s t : topological_space.closeds α) => Hausdorff_edist (subtype.val s) (subtype.val t))
      sorry sorry sorry)

/-- The edistance to a closed set depends continuously on the point and the set -/
theorem continuous_inf_edist_Hausdorff_edist {α : Type u} [emetric_space α] : continuous fun (p : α × topological_space.closeds α) => inf_edist (prod.fst p) (subtype.val (prod.snd p)) := sorry

/-- Subsets of a given closed subset form a closed set -/
theorem is_closed_subsets_of_is_closed {α : Type u} [emetric_space α] {s : set α} (hs : is_closed s) : is_closed (set_of fun (t : topological_space.closeds α) => subtype.val t ⊆ s) := sorry

/-- By definition, the edistance on `closeds α` is given by the Hausdorff edistance -/
theorem closeds.edist_eq {α : Type u} [emetric_space α] {s : topological_space.closeds α} {t : topological_space.closeds α} : edist s t = Hausdorff_edist (subtype.val s) (subtype.val t) :=
  rfl

/-- In a complete space, the type of closed subsets is complete for the
Hausdorff edistance. -/
protected instance closeds.complete_space {α : Type u} [emetric_space α] [complete_space α] : complete_space (topological_space.closeds α) := sorry

/-- In a compact space, the type of closed subsets is compact. -/
protected instance closeds.compact_space {α : Type u} [emetric_space α] [compact_space α] : compact_space (topological_space.closeds α) := sorry

/-- In an emetric space, the type of non-empty compact subsets is an emetric space,
where the edistance is the Hausdorff edistance -/
protected instance nonempty_compacts.emetric_space {α : Type u} [emetric_space α] : emetric_space (topological_space.nonempty_compacts α) :=
  emetric_space.mk sorry sorry sorry sorry
    (uniform_space_of_edist
      (fun (s t : topological_space.nonempty_compacts α) => Hausdorff_edist (subtype.val s) (subtype.val t)) sorry sorry
      sorry)

/-- `nonempty_compacts.to_closeds` is a uniform embedding (as it is an isometry) -/
theorem nonempty_compacts.to_closeds.uniform_embedding {α : Type u} [emetric_space α] : uniform_embedding topological_space.nonempty_compacts.to_closeds :=
  isometry.uniform_embedding fun (x y : topological_space.nonempty_compacts α) => rfl

/-- The range of `nonempty_compacts.to_closeds` is closed in a complete space -/
theorem nonempty_compacts.is_closed_in_closeds {α : Type u} [emetric_space α] [complete_space α] : is_closed (set.range topological_space.nonempty_compacts.to_closeds) := sorry

/-- In a complete space, the type of nonempty compact subsets is complete. This follows
from the same statement for closed subsets -/
protected instance nonempty_compacts.complete_space {α : Type u} [emetric_space α] [complete_space α] : complete_space (topological_space.nonempty_compacts α) :=
  iff.mpr (complete_space_iff_is_complete_range nonempty_compacts.to_closeds.uniform_embedding)
    (is_closed.is_complete nonempty_compacts.is_closed_in_closeds)

/-- In a compact space, the type of nonempty compact subsets is compact. This follows from
the same statement for closed subsets -/
protected instance nonempty_compacts.compact_space {α : Type u} [emetric_space α] [compact_space α] : compact_space (topological_space.nonempty_compacts α) :=
  compact_space.mk
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (is_compact set.univ))
          (propext
            (embedding.compact_iff_compact_image
              (uniform_embedding.embedding nonempty_compacts.to_closeds.uniform_embedding)))))
      (eq.mpr
        (id
          (Eq._oldrec (Eq.refl (is_compact (topological_space.nonempty_compacts.to_closeds '' set.univ))) set.image_univ))
        (is_closed.compact nonempty_compacts.is_closed_in_closeds)))

/-- In a second countable space, the type of nonempty compact subsets is second countable -/
protected instance nonempty_compacts.second_countable_topology {α : Type u} [emetric_space α] [topological_space.second_countable_topology α] : topological_space.second_countable_topology (topological_space.nonempty_compacts α) :=
  second_countable_of_separable (topological_space.nonempty_compacts α)

namespace metric


/-- `nonempty_compacts α` inherits a metric space structure, as the Hausdorff
edistance between two such sets is finite. -/
protected instance Mathlib.metric.nonempty_compacts.metric_space {α : Type u} [metric_space α] : metric_space (topological_space.nonempty_compacts α) :=
  emetric_space.to_metric_space sorry

/-- The distance on `nonempty_compacts α` is the Hausdorff distance, by construction -/
theorem Mathlib.metric.nonempty_compacts.dist_eq {α : Type u} [metric_space α] {x : topological_space.nonempty_compacts α} {y : topological_space.nonempty_compacts α} : dist x y = metric.Hausdorff_dist (subtype.val x) (subtype.val y) :=
  rfl

theorem Mathlib.metric.lipschitz_inf_dist_set {α : Type u} [metric_space α] (x : α) : lipschitz_with 1 fun (s : topological_space.nonempty_compacts α) => metric.inf_dist x (subtype.val s) := sorry

theorem Mathlib.metric.lipschitz_inf_dist {α : Type u} [metric_space α] : lipschitz_with (bit0 1)
  fun (p : α × topological_space.nonempty_compacts α) => metric.inf_dist (prod.fst p) (subtype.val (prod.snd p)) :=
  lipschitz_with.uncurry (fun (s : topological_space.nonempty_compacts α) => metric.lipschitz_inf_dist_pt (subtype.val s))
    metric.lipschitz_inf_dist_set

theorem Mathlib.metric.uniform_continuous_inf_dist_Hausdorff_dist {α : Type u} [metric_space α] : uniform_continuous
  fun (p : α × topological_space.nonempty_compacts α) => metric.inf_dist (prod.fst p) (subtype.val (prod.snd p)) :=
  lipschitz_with.uniform_continuous metric.lipschitz_inf_dist

