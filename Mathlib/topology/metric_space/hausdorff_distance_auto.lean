/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.metric_space.isometry
import Mathlib.topology.instances.ennreal
import PostPort

universes u v 

namespace Mathlib

/-!
# Hausdorff distance

The Hausdorff distance on subsets of a metric (or emetric) space.

Given two subsets `s` and `t` of a metric space, their Hausdorff distance is the smallest `d`
such that any point `s` is within `d` of a point in `t`, and conversely. This quantity
is often infinite (think of `s` bounded and `t` unbounded), and therefore better
expressed in the setting of emetric spaces.

## Main definitions

This files introduces:
* `inf_edist x s`, the infimum edistance of a point `x` to a set `s` in an emetric space
* `Hausdorff_edist s t`, the Hausdorff edistance of two sets in an emetric space
* Versions of these notions on metric spaces, called respectively `inf_dist` and
`Hausdorff_dist`.
-/

namespace emetric


/-! ### Distance of a point to a set as a function into `ennreal`. -/

/-- The minimal edistance of a point to a set -/
def inf_edist {α : Type u} [emetric_space α] (x : α) (s : set α) : ennreal :=
  Inf (edist x '' s)

@[simp] theorem inf_edist_empty {α : Type u} [emetric_space α] {x : α} : inf_edist x ∅ = ⊤ := sorry

/-- The edist to a union is the minimum of the edists -/
@[simp] theorem inf_edist_union {α : Type u} [emetric_space α] {x : α} {s : set α} {t : set α} : inf_edist x (s ∪ t) = inf_edist x s ⊓ inf_edist x t := sorry

/-- The edist to a singleton is the edistance to the single point of this singleton -/
@[simp] theorem inf_edist_singleton {α : Type u} [emetric_space α] {x : α} {y : α} : inf_edist x (singleton y) = edist x y := sorry

/-- The edist to a set is bounded above by the edist to any of its points -/
theorem inf_edist_le_edist_of_mem {α : Type u} [emetric_space α] {x : α} {y : α} {s : set α} (h : y ∈ s) : inf_edist x s ≤ edist x y :=
  Inf_le (iff.mpr (set.mem_image (edist x) s (edist x y)) (Exists.intro y { left := h, right := Eq.refl (edist x y) }))

/-- If a point `x` belongs to `s`, then its edist to `s` vanishes -/
theorem inf_edist_zero_of_mem {α : Type u} [emetric_space α] {x : α} {s : set α} (h : x ∈ s) : inf_edist x s = 0 :=
  iff.mp nonpos_iff_eq_zero (edist_self x ▸ inf_edist_le_edist_of_mem h)

/-- The edist is monotonous with respect to inclusion -/
theorem inf_edist_le_inf_edist_of_subset {α : Type u} [emetric_space α] {x : α} {s : set α} {t : set α} (h : s ⊆ t) : inf_edist x t ≤ inf_edist x s :=
  Inf_le_Inf (set.image_subset (edist x) h)

/-- If the edist to a set is `< r`, there exists a point in the set at edistance `< r` -/
theorem exists_edist_lt_of_inf_edist_lt {α : Type u} [emetric_space α] {x : α} {s : set α} {r : ennreal} (h : inf_edist x s < r) : ∃ (y : α), ∃ (H : y ∈ s), edist x y < r := sorry

/-- The edist of `x` to `s` is bounded by the sum of the edist of `y` to `s` and
the edist from `x` to `y` -/
theorem inf_edist_le_inf_edist_add_edist {α : Type u} [emetric_space α] {x : α} {y : α} {s : set α} : inf_edist x s ≤ inf_edist y s + edist x y := sorry

/-- The edist to a set depends continuously on the point -/
theorem continuous_inf_edist {α : Type u} [emetric_space α] {s : set α} : continuous fun (x : α) => inf_edist x s := sorry

/-- The edist to a set and to its closure coincide -/
theorem inf_edist_closure {α : Type u} [emetric_space α] {x : α} {s : set α} : inf_edist x (closure s) = inf_edist x s := sorry

/-- A point belongs to the closure of `s` iff its infimum edistance to this set vanishes -/
theorem mem_closure_iff_inf_edist_zero {α : Type u} [emetric_space α] {x : α} {s : set α} : x ∈ closure s ↔ inf_edist x s = 0 := sorry

/-- Given a closed set `s`, a point belongs to `s` iff its infimum edistance to this set vanishes -/
theorem mem_iff_ind_edist_zero_of_closed {α : Type u} [emetric_space α] {x : α} {s : set α} (h : is_closed s) : x ∈ s ↔ inf_edist x s = 0 := sorry

/-- The infimum edistance is invariant under isometries -/
theorem inf_edist_image {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {x : α} {t : set α} {Φ : α → β} (hΦ : isometry Φ) : inf_edist (Φ x) (Φ '' t) = inf_edist x t := sorry

/-! ### The Hausdorff distance as a function into `ennreal`. -/

/-- The Hausdorff edistance between two sets is the smallest `r` such that each set
is contained in the `r`-neighborhood of the other one -/
def Hausdorff_edist {α : Type u} [emetric_space α] (s : set α) (t : set α) : ennreal :=
  Sup ((fun (x : α) => inf_edist x t) '' s) ⊔ Sup ((fun (x : α) => inf_edist x s) '' t)

theorem Hausdorff_edist_def {α : Type u} [emetric_space α] (s : set α) (t : set α) : Hausdorff_edist s t = Sup ((fun (x : α) => inf_edist x t) '' s) ⊔ Sup ((fun (x : α) => inf_edist x s) '' t) :=
  rfl

/-- The Hausdorff edistance of a set to itself vanishes -/
@[simp] theorem Hausdorff_edist_self {α : Type u} [emetric_space α] {s : set α} : Hausdorff_edist s s = 0 := sorry

/-- The Haudorff edistances of `s` to `t` and of `t` to `s` coincide -/
theorem Hausdorff_edist_comm {α : Type u} [emetric_space α] {s : set α} {t : set α} : Hausdorff_edist s t = Hausdorff_edist t s := sorry

/-- Bounding the Hausdorff edistance by bounding the edistance of any point
in each set to the other set -/
theorem Hausdorff_edist_le_of_inf_edist {α : Type u} [emetric_space α] {s : set α} {t : set α} {r : ennreal} (H1 : ∀ (x : α), x ∈ s → inf_edist x t ≤ r) (H2 : ∀ (x : α), x ∈ t → inf_edist x s ≤ r) : Hausdorff_edist s t ≤ r := sorry

/-- Bounding the Hausdorff edistance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
theorem Hausdorff_edist_le_of_mem_edist {α : Type u} [emetric_space α] {s : set α} {t : set α} {r : ennreal} (H1 : ∀ (x : α) (H : x ∈ s), ∃ (y : α), ∃ (H : y ∈ t), edist x y ≤ r) (H2 : ∀ (x : α) (H : x ∈ t), ∃ (y : α), ∃ (H : y ∈ s), edist x y ≤ r) : Hausdorff_edist s t ≤ r := sorry

/-- The distance to a set is controlled by the Hausdorff distance -/
theorem inf_edist_le_Hausdorff_edist_of_mem {α : Type u} [emetric_space α] {x : α} {s : set α} {t : set α} (h : x ∈ s) : inf_edist x t ≤ Hausdorff_edist s t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (inf_edist x t ≤ Hausdorff_edist s t)) (Hausdorff_edist_def s t)))
    (le_trans (le_Sup (set.mem_image_of_mem (fun (x : α) => inf_edist x t) h)) le_sup_left)

/-- If the Hausdorff distance is `<r`, then any point in one of the sets has
a corresponding point at distance `<r` in the other set -/
theorem exists_edist_lt_of_Hausdorff_edist_lt {α : Type u} [emetric_space α] {x : α} {s : set α} {t : set α} {r : ennreal} (h : x ∈ s) (H : Hausdorff_edist s t < r) : ∃ (y : α), ∃ (H : y ∈ t), edist x y < r :=
  exists_edist_lt_of_inf_edist_lt
    (lt_of_le_of_lt (le_trans (le_Sup (set.mem_image_of_mem (fun (x : α) => inf_edist x t) h)) le_sup_left)
      (eq.mp (Eq._oldrec (Eq.refl (Hausdorff_edist s t < r)) (Hausdorff_edist_def s t)) H))

/-- The distance from `x` to `s` or `t` is controlled in terms of the Hausdorff distance
between `s` and `t` -/
theorem inf_edist_le_inf_edist_add_Hausdorff_edist {α : Type u} [emetric_space α] {x : α} {s : set α} {t : set α} : inf_edist x t ≤ inf_edist x s + Hausdorff_edist s t := sorry

/-- The Hausdorff edistance is invariant under eisometries -/
theorem Hausdorff_edist_image {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {s : set α} {t : set α} {Φ : α → β} (h : isometry Φ) : Hausdorff_edist (Φ '' s) (Φ '' t) = Hausdorff_edist s t := sorry

/-- The Hausdorff distance is controlled by the diameter of the union -/
theorem Hausdorff_edist_le_ediam {α : Type u} [emetric_space α] {s : set α} {t : set α} (hs : set.nonempty s) (ht : set.nonempty t) : Hausdorff_edist s t ≤ diam (s ∪ t) := sorry

/-- The Hausdorff distance satisfies the triangular inequality -/
theorem Hausdorff_edist_triangle {α : Type u} [emetric_space α] {s : set α} {t : set α} {u : set α} : Hausdorff_edist s u ≤ Hausdorff_edist s t + Hausdorff_edist t u := sorry

/-- The Hausdorff edistance between a set and its closure vanishes -/
@[simp] theorem Hausdorff_edist_self_closure {α : Type u} [emetric_space α] {s : set α} : Hausdorff_edist s (closure s) = 0 := sorry

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp] theorem Hausdorff_edist_closure₁ {α : Type u} [emetric_space α] {s : set α} {t : set α} : Hausdorff_edist (closure s) t = Hausdorff_edist s t := sorry

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp] theorem Hausdorff_edist_closure₂ {α : Type u} [emetric_space α] {s : set α} {t : set α} : Hausdorff_edist s (closure t) = Hausdorff_edist s t := sorry

/-- The Hausdorff edistance between sets or their closures is the same -/
@[simp] theorem Hausdorff_edist_closure {α : Type u} [emetric_space α] {s : set α} {t : set α} : Hausdorff_edist (closure s) (closure t) = Hausdorff_edist s t := sorry

/-- Two sets are at zero Hausdorff edistance if and only if they have the same closure -/
theorem Hausdorff_edist_zero_iff_closure_eq_closure {α : Type u} [emetric_space α] {s : set α} {t : set α} : Hausdorff_edist s t = 0 ↔ closure s = closure t := sorry

/-- Two closed sets are at zero Hausdorff edistance if and only if they coincide -/
theorem Hausdorff_edist_zero_iff_eq_of_closed {α : Type u} [emetric_space α] {s : set α} {t : set α} (hs : is_closed s) (ht : is_closed t) : Hausdorff_edist s t = 0 ↔ s = t := sorry

/-- The Haudorff edistance to the empty set is infinite -/
theorem Hausdorff_edist_empty {α : Type u} [emetric_space α] {s : set α} (ne : set.nonempty s) : Hausdorff_edist s ∅ = ⊤ := sorry

/-- If a set is at finite Hausdorff edistance of a nonempty set, it is nonempty -/
theorem nonempty_of_Hausdorff_edist_ne_top {α : Type u} [emetric_space α] {s : set α} {t : set α} (hs : set.nonempty s) (fin : Hausdorff_edist s t ≠ ⊤) : set.nonempty t :=
  or.elim (set.eq_empty_or_nonempty t) (fun (ht : t = ∅) => false.elim (fin (Eq.symm ht ▸ Hausdorff_edist_empty hs))) id

theorem empty_or_nonempty_of_Hausdorff_edist_ne_top {α : Type u} [emetric_space α] {s : set α} {t : set α} (fin : Hausdorff_edist s t ≠ ⊤) : s = ∅ ∧ t = ∅ ∨ set.nonempty s ∧ set.nonempty t := sorry

/-! Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
`Inf` and `Sup` on `ℝ` (which is only conditionally complete), we use the notions in `ennreal`
formulated in terms of the edistance, and coerce them to `ℝ`.
Then their properties follow readily from the corresponding properties in `ennreal`,
modulo some tedious rewriting of inequalities from one to the other. -/

namespace metric


/-! ### Distance of a point to a set as a function into `ℝ`. -/

/-- The minimal distance of a point to a set -/
def Mathlib.metric.inf_dist {α : Type u} [metric_space α] (x : α) (s : set α) : ℝ :=
  ennreal.to_real (inf_edist x s)

/-- the minimal distance is always nonnegative -/
theorem Mathlib.metric.inf_dist_nonneg {α : Type u} [metric_space α] {s : set α} {x : α} : 0 ≤ metric.inf_dist x s := sorry

/-- the minimal distance to the empty set is 0 (if you want to have the more reasonable
value ∞ instead, use `inf_edist`, which takes values in ennreal) -/
@[simp] theorem Mathlib.metric.inf_dist_empty {α : Type u} [metric_space α] {x : α} : metric.inf_dist x ∅ = 0 := sorry

/-- In a metric space, the minimal edistance to a nonempty set is finite -/
theorem Mathlib.metric.inf_edist_ne_top {α : Type u} [metric_space α] {s : set α} {x : α} (h : set.nonempty s) : inf_edist x s ≠ ⊤ := sorry

/-- The minimal distance of a point to a set containing it vanishes -/
theorem Mathlib.metric.inf_dist_zero_of_mem {α : Type u} [metric_space α] {s : set α} {x : α} (h : x ∈ s) : metric.inf_dist x s = 0 := sorry

/-- The minimal distance to a singleton is the distance to the unique point in this singleton -/
@[simp] theorem Mathlib.metric.inf_dist_singleton {α : Type u} [metric_space α] {x : α} {y : α} : metric.inf_dist x (singleton y) = dist x y := sorry

/-- The minimal distance to a set is bounded by the distance to any point in this set -/
theorem Mathlib.metric.inf_dist_le_dist_of_mem {α : Type u} [metric_space α] {s : set α} {x : α} {y : α} (h : y ∈ s) : metric.inf_dist x s ≤ dist x y := sorry

/-- The minimal distance is monotonous with respect to inclusion -/
theorem Mathlib.metric.inf_dist_le_inf_dist_of_subset {α : Type u} [metric_space α] {s : set α} {t : set α} {x : α} (h : s ⊆ t) (hs : set.nonempty s) : metric.inf_dist x t ≤ metric.inf_dist x s := sorry

/-- If the minimal distance to a set is `<r`, there exists a point in this set at distance `<r` -/
theorem Mathlib.metric.exists_dist_lt_of_inf_dist_lt {α : Type u} [metric_space α] {s : set α} {x : α} {r : ℝ} (h : metric.inf_dist x s < r) (hs : set.nonempty s) : ∃ (y : α), ∃ (H : y ∈ s), dist x y < r := sorry

/-- The minimal distance from `x` to `s` is bounded by the distance from `y` to `s`, modulo
the distance between `x` and `y` -/
theorem Mathlib.metric.inf_dist_le_inf_dist_add_dist {α : Type u} [metric_space α] {s : set α} {x : α} {y : α} : metric.inf_dist x s ≤ metric.inf_dist y s + dist x y := sorry

/-- The minimal distance to a set is Lipschitz in point with constant 1 -/
theorem Mathlib.metric.lipschitz_inf_dist_pt {α : Type u} [metric_space α] (s : set α) : lipschitz_with 1 fun (x : α) => metric.inf_dist x s :=
  lipschitz_with.of_le_add fun (x y : α) => metric.inf_dist_le_inf_dist_add_dist

/-- The minimal distance to a set is uniformly continuous in point -/
theorem Mathlib.metric.uniform_continuous_inf_dist_pt {α : Type u} [metric_space α] (s : set α) : uniform_continuous fun (x : α) => metric.inf_dist x s :=
  lipschitz_with.uniform_continuous (metric.lipschitz_inf_dist_pt s)

/-- The minimal distance to a set is continuous in point -/
theorem Mathlib.metric.continuous_inf_dist_pt {α : Type u} [metric_space α] (s : set α) : continuous fun (x : α) => metric.inf_dist x s :=
  uniform_continuous.continuous (metric.uniform_continuous_inf_dist_pt s)

/-- The minimal distance to a set and its closure coincide -/
theorem Mathlib.metric.inf_dist_eq_closure {α : Type u} [metric_space α] {s : set α} {x : α} : metric.inf_dist x (closure s) = metric.inf_dist x s := sorry

/-- A point belongs to the closure of `s` iff its infimum distance to this set vanishes -/
theorem Mathlib.metric.mem_closure_iff_inf_dist_zero {α : Type u} [metric_space α] {s : set α} {x : α} (h : set.nonempty s) : x ∈ closure s ↔ metric.inf_dist x s = 0 := sorry

/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
theorem Mathlib.metric.mem_iff_inf_dist_zero_of_closed {α : Type u} [metric_space α] {s : set α} {x : α} (h : is_closed s) (hs : set.nonempty s) : x ∈ s ↔ metric.inf_dist x s = 0 :=
  eq.mp (Eq._oldrec (Eq.refl (x ∈ closure s ↔ metric.inf_dist x s = 0)) (is_closed.closure_eq h))
    (metric.mem_closure_iff_inf_dist_zero hs)

/-- The infimum distance is invariant under isometries -/
theorem Mathlib.metric.inf_dist_image {α : Type u} {β : Type v} [metric_space α] [metric_space β] {t : set α} {x : α} {Φ : α → β} (hΦ : isometry Φ) : metric.inf_dist (Φ x) (Φ '' t) = metric.inf_dist x t := sorry

/-! ### Distance of a point to a set as a function into `ℝ≥0`. -/

/-- The minimal distance of a point to a set as a `ℝ≥0` -/
def Mathlib.metric.inf_nndist {α : Type u} [metric_space α] (x : α) (s : set α) : nnreal :=
  ennreal.to_nnreal (inf_edist x s)

@[simp] theorem Mathlib.metric.coe_inf_nndist {α : Type u} [metric_space α] {s : set α} {x : α} : ↑(metric.inf_nndist x s) = metric.inf_dist x s :=
  rfl

/-- The minimal distance to a set (as `ℝ≥0`) is Lipschitz in point with constant 1 -/
theorem Mathlib.metric.lipschitz_inf_nndist_pt {α : Type u} [metric_space α] (s : set α) : lipschitz_with 1 fun (x : α) => metric.inf_nndist x s :=
  lipschitz_with.of_le_add fun (x y : α) => metric.inf_dist_le_inf_dist_add_dist

/-- The minimal distance to a set (as `ℝ≥0`) is uniformly continuous in point -/
theorem Mathlib.metric.uniform_continuous_inf_nndist_pt {α : Type u} [metric_space α] (s : set α) : uniform_continuous fun (x : α) => metric.inf_nndist x s :=
  lipschitz_with.uniform_continuous (metric.lipschitz_inf_nndist_pt s)

/-- The minimal distance to a set (as `ℝ≥0`) is continuous in point -/
theorem Mathlib.metric.continuous_inf_nndist_pt {α : Type u} [metric_space α] (s : set α) : continuous fun (x : α) => metric.inf_nndist x s :=
  uniform_continuous.continuous (metric.uniform_continuous_inf_nndist_pt s)

/-! ### The Hausdorff distance as a function into `ℝ`. -/

/-- The Hausdorff distance between two sets is the smallest nonnegative `r` such that each set is
included in the `r`-neighborhood of the other. If there is no such `r`, it is defined to
be `0`, arbitrarily -/
def Mathlib.metric.Hausdorff_dist {α : Type u} [metric_space α] (s : set α) (t : set α) : ℝ :=
  ennreal.to_real (Hausdorff_edist s t)

/-- The Hausdorff distance is nonnegative -/
theorem Mathlib.metric.Hausdorff_dist_nonneg {α : Type u} [metric_space α] {s : set α} {t : set α} : 0 ≤ metric.Hausdorff_dist s t := sorry

/-- If two sets are nonempty and bounded in a metric space, they are at finite Hausdorff
edistance. -/
theorem Mathlib.metric.Hausdorff_edist_ne_top_of_nonempty_of_bounded {α : Type u} [metric_space α] {s : set α} {t : set α} (hs : set.nonempty s) (ht : set.nonempty t) (bs : metric.bounded s) (bt : metric.bounded t) : Hausdorff_edist s t ≠ ⊤ := sorry

/-- The Hausdorff distance between a set and itself is zero -/
@[simp] theorem Mathlib.metric.Hausdorff_dist_self_zero {α : Type u} [metric_space α] {s : set α} : metric.Hausdorff_dist s s = 0 := sorry

/-- The Hausdorff distance from `s` to `t` and from `t` to `s` coincide -/
theorem Mathlib.metric.Hausdorff_dist_comm {α : Type u} [metric_space α] {s : set α} {t : set α} : metric.Hausdorff_dist s t = metric.Hausdorff_dist t s := sorry

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value ∞ instead, use `Hausdorff_edist`, which takes values in ennreal) -/
@[simp] theorem Mathlib.metric.Hausdorff_dist_empty {α : Type u} [metric_space α] {s : set α} : metric.Hausdorff_dist s ∅ = 0 := sorry

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value ∞ instead, use `Hausdorff_edist`, which takes values in ennreal) -/
@[simp] theorem Mathlib.metric.Hausdorff_dist_empty' {α : Type u} [metric_space α] {s : set α} : metric.Hausdorff_dist ∅ s = 0 := sorry

/-- Bounding the Hausdorff distance by bounding the distance of any point
in each set to the other set -/
theorem Mathlib.metric.Hausdorff_dist_le_of_inf_dist {α : Type u} [metric_space α] {s : set α} {t : set α} {r : ℝ} (hr : 0 ≤ r) (H1 : ∀ (x : α), x ∈ s → metric.inf_dist x t ≤ r) (H2 : ∀ (x : α), x ∈ t → metric.inf_dist x s ≤ r) : metric.Hausdorff_dist s t ≤ r := sorry

/-- Bounding the Hausdorff distance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
theorem Mathlib.metric.Hausdorff_dist_le_of_mem_dist {α : Type u} [metric_space α] {s : set α} {t : set α} {r : ℝ} (hr : 0 ≤ r) (H1 : ∀ (x : α) (H : x ∈ s), ∃ (y : α), ∃ (H : y ∈ t), dist x y ≤ r) (H2 : ∀ (x : α) (H : x ∈ t), ∃ (y : α), ∃ (H : y ∈ s), dist x y ≤ r) : metric.Hausdorff_dist s t ≤ r := sorry

/-- The Hausdorff distance is controlled by the diameter of the union -/
theorem Mathlib.metric.Hausdorff_dist_le_diam {α : Type u} [metric_space α] {s : set α} {t : set α} (hs : set.nonempty s) (bs : metric.bounded s) (ht : set.nonempty t) (bt : metric.bounded t) : metric.Hausdorff_dist s t ≤ metric.diam (s ∪ t) := sorry

/-- The distance to a set is controlled by the Hausdorff distance -/
theorem Mathlib.metric.inf_dist_le_Hausdorff_dist_of_mem {α : Type u} [metric_space α] {s : set α} {t : set α} {x : α} (hx : x ∈ s) (fin : Hausdorff_edist s t ≠ ⊤) : metric.inf_dist x t ≤ metric.Hausdorff_dist s t := sorry

/-- If the Hausdorff distance is `<r`, then any point in one of the sets is at distance
`<r` of a point in the other set -/
theorem Mathlib.metric.exists_dist_lt_of_Hausdorff_dist_lt {α : Type u} [metric_space α] {s : set α} {t : set α} {x : α} {r : ℝ} (h : x ∈ s) (H : metric.Hausdorff_dist s t < r) (fin : Hausdorff_edist s t ≠ ⊤) : ∃ (y : α), ∃ (H : y ∈ t), dist x y < r := sorry

/-- If the Hausdorff distance is `<r`, then any point in one of the sets is at distance
`<r` of a point in the other set -/
theorem Mathlib.metric.exists_dist_lt_of_Hausdorff_dist_lt' {α : Type u} [metric_space α] {s : set α} {t : set α} {y : α} {r : ℝ} (h : y ∈ t) (H : metric.Hausdorff_dist s t < r) (fin : Hausdorff_edist s t ≠ ⊤) : ∃ (x : α), ∃ (H : x ∈ s), dist x y < r := sorry

/-- The infimum distance to `s` and `t` are the same, up to the Hausdorff distance
between `s` and `t` -/
theorem Mathlib.metric.inf_dist_le_inf_dist_add_Hausdorff_dist {α : Type u} [metric_space α] {s : set α} {t : set α} {x : α} (fin : Hausdorff_edist s t ≠ ⊤) : metric.inf_dist x t ≤ metric.inf_dist x s + metric.Hausdorff_dist s t := sorry

/-- The Hausdorff distance is invariant under isometries -/
theorem Mathlib.metric.Hausdorff_dist_image {α : Type u} {β : Type v} [metric_space α] [metric_space β] {s : set α} {t : set α} {Φ : α → β} (h : isometry Φ) : metric.Hausdorff_dist (Φ '' s) (Φ '' t) = metric.Hausdorff_dist s t := sorry

/-- The Hausdorff distance satisfies the triangular inequality -/
theorem Mathlib.metric.Hausdorff_dist_triangle {α : Type u} [metric_space α] {s : set α} {t : set α} {u : set α} (fin : Hausdorff_edist s t ≠ ⊤) : metric.Hausdorff_dist s u ≤ metric.Hausdorff_dist s t + metric.Hausdorff_dist t u := sorry

/-- The Hausdorff distance satisfies the triangular inequality -/
theorem Mathlib.metric.Hausdorff_dist_triangle' {α : Type u} [metric_space α] {s : set α} {t : set α} {u : set α} (fin : Hausdorff_edist t u ≠ ⊤) : metric.Hausdorff_dist s u ≤ metric.Hausdorff_dist s t + metric.Hausdorff_dist t u := sorry

/-- The Hausdorff distance between a set and its closure vanish -/
@[simp] theorem Mathlib.metric.Hausdorff_dist_self_closure {α : Type u} [metric_space α] {s : set α} : metric.Hausdorff_dist s (closure s) = 0 := sorry

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp] theorem Mathlib.metric.Hausdorff_dist_closure₁ {α : Type u} [metric_space α] {s : set α} {t : set α} : metric.Hausdorff_dist (closure s) t = metric.Hausdorff_dist s t := sorry

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp] theorem Mathlib.metric.Hausdorff_dist_closure₂ {α : Type u} [metric_space α] {s : set α} {t : set α} : metric.Hausdorff_dist s (closure t) = metric.Hausdorff_dist s t := sorry

/-- The Hausdorff distance between two sets and their closures coincide -/
@[simp] theorem Mathlib.metric.Hausdorff_dist_closure {α : Type u} [metric_space α] {s : set α} {t : set α} : metric.Hausdorff_dist (closure s) (closure t) = metric.Hausdorff_dist s t := sorry

/-- Two sets are at zero Hausdorff distance if and only if they have the same closures -/
theorem Mathlib.metric.Hausdorff_dist_zero_iff_closure_eq_closure {α : Type u} [metric_space α] {s : set α} {t : set α} (fin : Hausdorff_edist s t ≠ ⊤) : metric.Hausdorff_dist s t = 0 ↔ closure s = closure t := sorry

/-- Two closed sets are at zero Hausdorff distance if and only if they coincide -/
theorem Mathlib.metric.Hausdorff_dist_zero_iff_eq_of_closed {α : Type u} [metric_space α] {s : set α} {t : set α} (hs : is_closed s) (ht : is_closed t) (fin : Hausdorff_edist s t ≠ ⊤) : metric.Hausdorff_dist s t = 0 ↔ s = t := sorry

