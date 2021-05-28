/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.convex.basic
import Mathlib.analysis.normed_space.finite_dimension
import Mathlib.topology.path_connected
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Topological and metric properties of convex sets

We prove the following facts:

* `convex.interior` : interior of a convex set is convex;
* `convex.closure` : closure of a convex set is convex;
* `set.finite.compact_convex_hull` : convex hull of a finite set is compact;
* `set.finite.is_closed_convex_hull` : convex hull of a finite set is closed;
* `convex_on_dist` : distance to a fixed point is convex on any convex set;
* `convex_hull_ediam`, `convex_hull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `bounded_convex_hull` : convex hull of a set is bounded if and only if the original set
  is bounded.
* `bounded_std_simplex`, `is_closed_std_simplex`, `compact_std_simplex`: topological properties
  of the standard simplex;
-/

theorem real.convex_iff_is_preconnected {s : set ℝ} : convex s ↔ is_preconnected s :=
  iff.trans real.convex_iff_ord_connected (iff.symm is_preconnected_iff_ord_connected)

theorem is_preconnected.convex {s : set ℝ} : is_preconnected s → convex s :=
  iff.mpr real.convex_iff_is_preconnected

/-! ### Standard simplex -/

/-- Every vector in `std_simplex ι` has `max`-norm at most `1`. -/
theorem std_simplex_subset_closed_ball {ι : Type u_1} [fintype ι] : std_simplex ι ⊆ metric.closed_ball 0 1 := sorry

/-- `std_simplex ι` is bounded. -/
theorem bounded_std_simplex (ι : Type u_1) [fintype ι] : metric.bounded (std_simplex ι) :=
  iff.mpr (metric.bounded_iff_subset_ball 0) (Exists.intro 1 std_simplex_subset_closed_ball)

/-- `std_simplex ι` is closed. -/
theorem is_closed_std_simplex (ι : Type u_1) [fintype ι] : is_closed (std_simplex ι) := sorry

/-- `std_simplex ι` is compact. -/
theorem compact_std_simplex (ι : Type u_1) [fintype ι] : is_compact (std_simplex ι) :=
  iff.mpr metric.compact_iff_closed_bounded { left := is_closed_std_simplex ι, right := bounded_std_simplex ι }

/-! ### Topological vector space -/

/-- In a topological vector space, the interior of a convex set is convex. -/
theorem convex.interior {E : Type u_2} [add_comm_group E] [vector_space ℝ E] [topological_space E] [topological_add_group E] [topological_vector_space ℝ E] {s : set E} (hs : convex s) : convex (interior s) := sorry

/-- In a topological vector space, the closure of a convex set is convex. -/
theorem convex.closure {E : Type u_2} [add_comm_group E] [vector_space ℝ E] [topological_space E] [topological_add_group E] [topological_vector_space ℝ E] {s : set E} (hs : convex s) : convex (closure s) := sorry

/-- Convex hull of a finite set is compact. -/
theorem set.finite.compact_convex_hull {E : Type u_2} [add_comm_group E] [vector_space ℝ E] [topological_space E] [topological_add_group E] [topological_vector_space ℝ E] {s : set E} (hs : set.finite s) : is_compact (convex_hull s) := sorry

/-- Convex hull of a finite set is closed. -/
theorem set.finite.is_closed_convex_hull {E : Type u_2} [add_comm_group E] [vector_space ℝ E] [topological_space E] [topological_add_group E] [topological_vector_space ℝ E] [t2_space E] {s : set E} (hs : set.finite s) : is_closed (convex_hull s) :=
  is_compact.is_closed (set.finite.compact_convex_hull hs)

/-! ### Normed vector space -/

theorem convex_on_dist {E : Type u_2} [normed_group E] [normed_space ℝ E] (z : E) (s : set E) (hs : convex s) : convex_on s fun (z' : E) => dist z' z := sorry

theorem convex_ball {E : Type u_2} [normed_group E] [normed_space ℝ E] (a : E) (r : ℝ) : convex (metric.ball a r) := sorry

theorem convex_closed_ball {E : Type u_2} [normed_group E] [normed_space ℝ E] (a : E) (r : ℝ) : convex (metric.closed_ball a r) := sorry

/-- Given a point `x` in the convex hull of `s` and a point `y`, there exists a point
of `s` at distance at least `dist x y` from `y`. -/
theorem convex_hull_exists_dist_ge {E : Type u_2} [normed_group E] [normed_space ℝ E] {s : set E} {x : E} (hx : x ∈ convex_hull s) (y : E) : ∃ (x' : E), ∃ (H : x' ∈ s), dist x y ≤ dist x' y :=
  convex_on.exists_ge_of_mem_convex_hull (convex_on_dist y (convex_hull s) (convex_convex_hull s)) hx

/-- Given a point `x` in the convex hull of `s` and a point `y` in the convex hull of `t`,
there exist points `x' ∈ s` and `y' ∈ t` at distance at least `dist x y`. -/
theorem convex_hull_exists_dist_ge2 {E : Type u_2} [normed_group E] [normed_space ℝ E] {s : set E} {t : set E} {x : E} {y : E} (hx : x ∈ convex_hull s) (hy : y ∈ convex_hull t) : ∃ (x' : E), ∃ (H : x' ∈ s), ∃ (y' : E), ∃ (H : y' ∈ t), dist x y ≤ dist x' y' := sorry

/-- Emetric diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp] theorem convex_hull_ediam {E : Type u_2} [normed_group E] [normed_space ℝ E] (s : set E) : emetric.diam (convex_hull s) = emetric.diam s := sorry

/-- Diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp] theorem convex_hull_diam {E : Type u_2} [normed_group E] [normed_space ℝ E] (s : set E) : metric.diam (convex_hull s) = metric.diam s := sorry

/-- Convex hull of `s` is bounded if and only if `s` is bounded. -/
@[simp] theorem bounded_convex_hull {E : Type u_2} [normed_group E] [normed_space ℝ E] {s : set E} : metric.bounded (convex_hull s) ↔ metric.bounded s := sorry

theorem convex.is_path_connected {E : Type u_2} [normed_group E] [normed_space ℝ E] {s : set E} (hconv : convex s) (hne : set.nonempty s) : is_path_connected s := sorry

protected instance normed_space.path_connected {E : Type u_2} [normed_group E] [normed_space ℝ E] : path_connected_space E :=
  iff.mpr path_connected_space_iff_univ (convex.is_path_connected convex_univ (Exists.intro 0 trivial))

protected instance normed_space.loc_path_connected {E : Type u_2} [normed_group E] [normed_space ℝ E] : loc_path_connected_space E :=
  loc_path_connected_of_bases (fun (x : E) => metric.nhds_basis_ball)
    fun (x : E) (r : ℝ) (r_pos : 0 < r) =>
      convex.is_path_connected (convex_ball x r)
        (eq.mpr
          (id
            (propext
              ((fun {α : Type u_2} [_inst_1 : metric_space α] {x : α} {ε : ℝ} (h : 0 < ε) =>
                  iff_true_intro (metric.nonempty_ball h))
                (iff.mpr (iff_true_intro r_pos) True.intro))))
          trivial)

