/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.convex.basic
import Mathlib.linear_algebra.finite_dimensional
import PostPort

universes u 

namespace Mathlib

/-!
# Carathéodory's convexity theorem

This file is devoted to proving Carathéodory's convexity theorem:
The convex hull of a set `s` in ℝᵈ is the union of the convex hulls of the (d+1)-tuples in `s`.

## Main results:

* `convex_hull_eq_union`: Carathéodory's convexity theorem

## Implementation details

This theorem was formalized as part of the Sphere Eversion project.

## Tags
convex hull, caratheodory

-/

namespace caratheodory


/--
If `x` is in the convex hull of some finset `t` with strictly more than `findim + 1` elements,
then it is in the union of the convex hulls of the finsets `t.erase y` for `y ∈ t`.
-/
theorem mem_convex_hull_erase {E : Type u} [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E] [DecidableEq E] {t : finset E} (h : finite_dimensional.findim ℝ E + 1 < finset.card t) {x : E} (m : x ∈ convex_hull ↑t) : ∃ (y : ↥↑t), x ∈ convex_hull ↑(finset.erase t ↑y) := sorry

/--
The convex hull of a finset `t` with `findim ℝ E + 1 < t.card` is equal to
the union of the convex hulls of the finsets `t.erase x` for `x ∈ t`.
-/
theorem step {E : Type u} [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E] [DecidableEq E] (t : finset E) (h : finite_dimensional.findim ℝ E + 1 < finset.card t) : convex_hull ↑t = set.Union fun (x : ↥↑t) => convex_hull ↑(finset.erase t ↑x) := sorry

/--
The convex hull of a finset `t` with `findim ℝ E + 1 < t.card` is contained in
the union of the convex hulls of the finsets `t' ⊆ t` with `t'.card ≤ findim ℝ E + 1`.
-/
theorem shrink' {E : Type u} [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E] (t : finset E) (k : ℕ) (h : finset.card t = finite_dimensional.findim ℝ E + 1 + k) : convex_hull ↑t ⊆
  set.Union
    fun (t' : finset E) =>
      set.Union
        fun (w : t' ⊆ t) => set.Union fun (b : finset.card t' ≤ finite_dimensional.findim ℝ E + 1) => convex_hull ↑t' := sorry

/--
The convex hull of any finset `t` is contained in
the union of the convex hulls of the finsets `t' ⊆ t` with `t'.card ≤ findim ℝ E + 1`.
-/
theorem shrink {E : Type u} [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E] (t : finset E) : convex_hull ↑t ⊆
  set.Union
    fun (t' : finset E) =>
      set.Union
        fun (w : t' ⊆ t) => set.Union fun (b : finset.card t' ≤ finite_dimensional.findim ℝ E + 1) => convex_hull ↑t' := sorry

end caratheodory


/--
One inclusion of Carathéodory's convexity theorem.

The convex hull of a set `s` in ℝᵈ is contained in
the union of the convex hulls of the (d+1)-tuples in `s`.
-/
theorem convex_hull_subset_union {E : Type u} [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E] (s : set E) : convex_hull s ⊆
  set.Union
    fun (t : finset E) =>
      set.Union
        fun (w : ↑t ⊆ s) => set.Union fun (b : finset.card t ≤ finite_dimensional.findim ℝ E + 1) => convex_hull ↑t := sorry

/--
Carathéodory's convexity theorem.

The convex hull of a set `s` in ℝᵈ is the union of the convex hulls of the (d+1)-tuples in `s`.
-/
theorem convex_hull_eq_union {E : Type u} [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E] (s : set E) : convex_hull s =
  set.Union
    fun (t : finset E) =>
      set.Union
        fun (w : ↑t ⊆ s) => set.Union fun (b : finset.card t ≤ finite_dimensional.findim ℝ E + 1) => convex_hull ↑t := sorry

/--
A more explicit formulation of Carathéodory's convexity theorem,
writing an element of a convex hull as the center of mass
of an explicit `finset` with cardinality at most `dim + 1`.
-/
theorem eq_center_mass_card_le_dim_succ_of_mem_convex_hull {E : Type u} [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E] {s : set E} {x : E} (h : x ∈ convex_hull s) : ∃ (t : finset E),
  ∃ (w : ↑t ⊆ s),
    ∃ (b : finset.card t ≤ finite_dimensional.findim ℝ E + 1),
      ∃ (f : E → ℝ), (∀ (y : E), y ∈ t → 0 ≤ f y) ∧ finset.sum t f = 1 ∧ finset.center_mass t f id = x := sorry

/--
A variation on Carathéodory's convexity theorem,
writing an element of a convex hull as a center of mass
of an explicit `finset` with cardinality at most `dim + 1`,
where all coefficients in the center of mass formula
are strictly positive.

(This is proved using `eq_center_mass_card_le_dim_succ_of_mem_convex_hull`,
and discarding any elements of the set with coefficient zero.)
-/
theorem eq_pos_center_mass_card_le_dim_succ_of_mem_convex_hull {E : Type u} [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E] {s : set E} {x : E} (h : x ∈ convex_hull s) : ∃ (t : finset E),
  ∃ (w : ↑t ⊆ s),
    ∃ (b : finset.card t ≤ finite_dimensional.findim ℝ E + 1),
      ∃ (f : E → ℝ), (∀ (y : E), y ∈ t → 0 < f y) ∧ finset.sum t f = 1 ∧ finset.center_mass t f id = x := sorry

