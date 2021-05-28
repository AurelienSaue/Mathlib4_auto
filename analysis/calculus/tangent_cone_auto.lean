/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.convex.basic
import Mathlib.analysis.normed_space.bounded_linear_maps
import Mathlib.analysis.specific_limits
import PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Tangent cone

In this file, we define two predicates `unique_diff_within_at 𝕜 s x` and `unique_diff_on 𝕜 s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangent_cone_at`,
and express `unique_diff_within_at` and `unique_diff_on` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `unique_diff_within_at` and `unique_diff_on` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `fderiv.lean`. Hence, derivatives are not defined yet. The
property of uniqueness of the derivative is therefore proved in `fderiv.lean`, but based on the
properties of the tangent cone we prove here.
-/

/-- The set of all tangent directions to the set `s` at the point `x`. -/
def tangent_cone_at (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] (s : set E) (x : E) : set E :=
  set_of
    fun (y : E) =>
      ∃ (c : ℕ → 𝕜),
        ∃ (d : ℕ → E),
          filter.eventually (fun (n : ℕ) => x + d n ∈ s) filter.at_top ∧
            filter.tendsto (fun (n : ℕ) => norm (c n)) filter.at_top filter.at_top ∧
              filter.tendsto (fun (n : ℕ) => c n • d n) filter.at_top (nhds y)

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `unique_diff_within_at.eq` in `fderiv.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional).
 -/
def unique_diff_within_at (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] (s : set E) (x : E)  :=
  dense ↑(submodule.span 𝕜 (tangent_cone_at 𝕜 s x)) ∧ x ∈ closure s

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space.  The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `unique_diff_on.eq` in
`fderiv.lean`. -/
def unique_diff_on (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] (s : set E)  :=
  ∀ (x : E), x ∈ s → unique_diff_within_at 𝕜 s x

/- This section is devoted to the properties of the tangent cone. -/

theorem tangent_cone_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} : tangent_cone_at 𝕜 set.univ x = set.univ := sorry

theorem tangent_cone_mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {t : set E} (h : s ⊆ t) : tangent_cone_at 𝕜 s x ⊆ tangent_cone_at 𝕜 t x := sorry

/-- Auxiliary lemma ensuring that, under the assumptions defining the tangent cone,
the sequence `d` tends to 0 at infinity. -/
theorem tangent_cone_at.lim_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {y : E} {α : Type u_3} (l : filter α) {c : α → 𝕜} {d : α → E} (hc : filter.tendsto (fun (n : α) => norm (c n)) l filter.at_top) (hd : filter.tendsto (fun (n : α) => c n • d n) l (nhds y)) : filter.tendsto d l (nhds 0) := sorry

theorem tangent_cone_mono_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {t : set E} (h : nhds_within x s ≤ nhds_within x t) : tangent_cone_at 𝕜 s x ⊆ tangent_cone_at 𝕜 t x := sorry

/-- Tangent cone of `s` at `x` depends only on `𝓝[s] x`. -/
theorem tangent_cone_congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {t : set E} (h : nhds_within x s = nhds_within x t) : tangent_cone_at 𝕜 s x = tangent_cone_at 𝕜 t x :=
  set.subset.antisymm (tangent_cone_mono_nhds (le_of_eq h)) (tangent_cone_mono_nhds (le_of_eq (Eq.symm h)))

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
theorem tangent_cone_inter_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {t : set E} (ht : t ∈ nhds x) : tangent_cone_at 𝕜 (s ∩ t) x = tangent_cone_at 𝕜 s x :=
  tangent_cone_congr (Eq.symm (nhds_within_restrict' s ht))

/-- The tangent cone of a product contains the tangent cone of its left factor. -/
theorem subset_tangent_cone_prod_left {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {s : set E} {t : set F} {y : F} (ht : y ∈ closure t) : ⇑(linear_map.inl 𝕜 E F) '' tangent_cone_at 𝕜 s x ⊆ tangent_cone_at 𝕜 (set.prod s t) (x, y) := sorry

/-- The tangent cone of a product contains the tangent cone of its right factor. -/
theorem subset_tangent_cone_prod_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {s : set E} {t : set F} {y : F} (hs : x ∈ closure s) : ⇑(linear_map.inr 𝕜 E F) '' tangent_cone_at 𝕜 t y ⊆ tangent_cone_at 𝕜 (set.prod s t) (x, y) := sorry

/-- If a subset of a real vector space contains a segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
theorem mem_tangent_cone_of_segment_subset {G : Type u_4} [normed_group G] [normed_space ℝ G] {s : set G} {x : G} {y : G} (h : segment x y ⊆ s) : y - x ∈ tangent_cone_at ℝ s x := sorry

/-!
### Properties of `unique_diff_within_at` and `unique_diff_on`

This section is devoted to properties of the predicates `unique_diff_within_at` and `unique_diff_on`. -/

theorem unique_diff_on.unique_diff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {s : set E} {x : E} (hs : unique_diff_on 𝕜 s) (h : x ∈ s) : unique_diff_within_at 𝕜 s x :=
  hs x h

theorem unique_diff_within_at_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} : unique_diff_within_at 𝕜 set.univ x := sorry

theorem unique_diff_on_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] : unique_diff_on 𝕜 set.univ :=
  fun (x : E) (hx : x ∈ set.univ) => unique_diff_within_at_univ

theorem unique_diff_on_empty {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] : unique_diff_on 𝕜 ∅ :=
  fun (x : E) (hx : x ∈ ∅) => false.elim hx

theorem unique_diff_within_at.mono_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {t : set E} (h : unique_diff_within_at 𝕜 s x) (st : nhds_within x s ≤ nhds_within x t) : unique_diff_within_at 𝕜 t x := sorry

theorem unique_diff_within_at.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {t : set E} (h : unique_diff_within_at 𝕜 s x) (st : s ⊆ t) : unique_diff_within_at 𝕜 t x :=
  unique_diff_within_at.mono_nhds h (nhds_within_mono x st)

theorem unique_diff_within_at_congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {t : set E} (st : nhds_within x s = nhds_within x t) : unique_diff_within_at 𝕜 s x ↔ unique_diff_within_at 𝕜 t x :=
  { mp := fun (h : unique_diff_within_at 𝕜 s x) => unique_diff_within_at.mono_nhds h (le_of_eq st),
    mpr := fun (h : unique_diff_within_at 𝕜 t x) => unique_diff_within_at.mono_nhds h (le_of_eq (Eq.symm st)) }

theorem unique_diff_within_at_inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {t : set E} (ht : t ∈ nhds x) : unique_diff_within_at 𝕜 (s ∩ t) x ↔ unique_diff_within_at 𝕜 s x :=
  unique_diff_within_at_congr (Eq.symm (nhds_within_restrict' s ht))

theorem unique_diff_within_at.inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {t : set E} (hs : unique_diff_within_at 𝕜 s x) (ht : t ∈ nhds x) : unique_diff_within_at 𝕜 (s ∩ t) x :=
  iff.mpr (unique_diff_within_at_inter ht) hs

theorem unique_diff_within_at_inter' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {t : set E} (ht : t ∈ nhds_within x s) : unique_diff_within_at 𝕜 (s ∩ t) x ↔ unique_diff_within_at 𝕜 s x :=
  unique_diff_within_at_congr (Eq.symm (nhds_within_restrict'' s ht))

theorem unique_diff_within_at.inter' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {t : set E} (hs : unique_diff_within_at 𝕜 s x) (ht : t ∈ nhds_within x s) : unique_diff_within_at 𝕜 (s ∩ t) x :=
  iff.mpr (unique_diff_within_at_inter' ht) hs

theorem unique_diff_within_at_of_mem_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} (h : s ∈ nhds x) : unique_diff_within_at 𝕜 s x := sorry

theorem is_open.unique_diff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} (hs : is_open s) (xs : x ∈ s) : unique_diff_within_at 𝕜 s x :=
  unique_diff_within_at_of_mem_nhds (mem_nhds_sets hs xs)

theorem unique_diff_on.inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {s : set E} {t : set E} (hs : unique_diff_on 𝕜 s) (ht : is_open t) : unique_diff_on 𝕜 (s ∩ t) :=
  fun (x : E) (hx : x ∈ s ∩ t) => unique_diff_within_at.inter (hs x (and.left hx)) (mem_nhds_sets ht (and.right hx))

theorem is_open.unique_diff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {s : set E} (hs : is_open s) : unique_diff_on 𝕜 s :=
  fun (x : E) (hx : x ∈ s) => is_open.unique_diff_within_at hs hx

/-- The product of two sets of unique differentiability at points `x` and `y` has unique
differentiability at `(x, y)`. -/
theorem unique_diff_within_at.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {s : set E} {t : set F} {y : F} (hs : unique_diff_within_at 𝕜 s x) (ht : unique_diff_within_at 𝕜 t y) : unique_diff_within_at 𝕜 (set.prod s t) (x, y) := sorry

/-- The product of two sets of unique differentiability is a set of unique differentiability. -/
theorem unique_diff_on.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {t : set F} (hs : unique_diff_on 𝕜 s) (ht : unique_diff_on 𝕜 t) : unique_diff_on 𝕜 (set.prod s t) := sorry

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
theorem unique_diff_on_convex {G : Type u_4} [normed_group G] [normed_space ℝ G] {s : set G} (conv : convex s) (hs : set.nonempty (interior s)) : unique_diff_on ℝ s := sorry

theorem unique_diff_on_Ici (a : ℝ) : unique_diff_on ℝ (set.Ici a) := sorry

theorem unique_diff_on_Iic (a : ℝ) : unique_diff_on ℝ (set.Iic a) := sorry

theorem unique_diff_on_Ioi (a : ℝ) : unique_diff_on ℝ (set.Ioi a) :=
  is_open.unique_diff_on is_open_Ioi

theorem unique_diff_on_Iio (a : ℝ) : unique_diff_on ℝ (set.Iio a) :=
  is_open.unique_diff_on is_open_Iio

theorem unique_diff_on_Icc {a : ℝ} {b : ℝ} (hab : a < b) : unique_diff_on ℝ (set.Icc a b) := sorry

theorem unique_diff_on_Ico (a : ℝ) (b : ℝ) : unique_diff_on ℝ (set.Ico a b) := sorry

theorem unique_diff_on_Ioc (a : ℝ) (b : ℝ) : unique_diff_on ℝ (set.Ioc a b) := sorry

theorem unique_diff_on_Ioo (a : ℝ) (b : ℝ) : unique_diff_on ℝ (set.Ioo a b) :=
  is_open.unique_diff_on is_open_Ioo

/-- The real interval `[0, 1]` is a set of unique differentiability. -/
theorem unique_diff_on_Icc_zero_one : unique_diff_on ℝ (set.Icc 0 1) :=
  unique_diff_on_Icc zero_lt_one

