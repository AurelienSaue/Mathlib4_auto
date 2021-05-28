/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finset.sort
import Mathlib.data.matrix.notation
import Mathlib.linear_algebra.affine_space.combination
import Mathlib.linear_algebra.basis
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 l 

namespace Mathlib

/-!
# Affine independence

This file defines affinely independent families of points.

## Main definitions

* `affine_independent` defines affinely independent families of points
  as those where no nontrivial weighted subtraction is 0.  This is
  proved equivalent to two other formulations: linear independence of
  the results of subtracting a base point in the family from the other
  points in the family, or any equal affine combinations having the
  same weights.  A bundled type `simplex` is provided for finite
  affinely independent families of points, with an abbreviation
  `triangle` for the case of three points.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

/-- An indexed family is said to be affinely independent if no
nontrivial weighted subtractions (where the sum of weights is 0) are
0. -/
def affine_independent (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P)  :=
  ∀ (s : finset ι) (w : ι → k),
    (finset.sum s fun (i : ι) => w i) = 0 → coe_fn (finset.weighted_vsub s p) w = 0 → ∀ (i : ι), i ∈ s → w i = 0

/-- The definition of `affine_independent`. -/
theorem affine_independent_def (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P) : affine_independent k p ↔
  ∀ (s : finset ι) (w : ι → k),
    (finset.sum s fun (i : ι) => w i) = 0 → coe_fn (finset.weighted_vsub s p) w = 0 → ∀ (i : ι), i ∈ s → w i = 0 :=
  iff.rfl

/-- A family with at most one point is affinely independent. -/
theorem affine_independent_of_subsingleton (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [subsingleton ι] (p : ι → P) : affine_independent k p :=
  fun (s : finset ι) (w : ι → k) (h : (finset.sum s fun (i : ι) => w i) = 0)
    (hs : coe_fn (finset.weighted_vsub s p) w = 0) (i : ι) (hi : i ∈ s) => fintype.eq_of_subsingleton_of_sum_eq h i hi

/-- A family indexed by a `fintype` is affinely independent if and
only if no nontrivial weighted subtractions over `finset.univ` (where
the sum of the weights is 0) are 0. -/
theorem affine_independent_iff_of_fintype (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] (p : ι → P) : affine_independent k p ↔
  ∀ (w : ι → k),
    (finset.sum finset.univ fun (i : ι) => w i) = 0 →
      coe_fn (finset.weighted_vsub finset.univ p) w = 0 → ∀ (i : ι), w i = 0 := sorry

/-- A family is affinely independent if and only if the differences
from a base point in that family are linearly independent. -/
theorem affine_independent_iff_linear_independent_vsub (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P) (i1 : ι) : affine_independent k p ↔ linear_independent k fun (i : Subtype fun (x : ι) => x ≠ i1) => p ↑i -ᵥ p i1 := sorry

/-- A set is affinely independent if and only if the differences from
a base point in that set are linearly independent. -/
theorem affine_independent_set_iff_linear_independent_vsub (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} {p₁ : P} (hp₁ : p₁ ∈ s) : (affine_independent k fun (p : ↥s) => ↑p) ↔
  linear_independent k fun (v : ↥((fun (p : P) => p -ᵥ p₁) '' (s \ singleton p₁))) => ↑v := sorry

/-- A set of nonzero vectors is linearly independent if and only if,
given a point `p₁`, the vectors added to `p₁` and `p₁` itself are
affinely independent. -/
theorem linear_independent_set_iff_affine_independent_vadd_union_singleton (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set V} (hs : ∀ (v : V), v ∈ s → v ≠ 0) (p₁ : P) : (linear_independent k fun (v : ↥s) => ↑v) ↔
  affine_independent k fun (p : ↥(singleton p₁ ∪ (fun (v : V) => v +ᵥ p₁) '' s)) => ↑p := sorry

/-- A family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point
have equal `set.indicator`. -/
theorem affine_independent_iff_indicator_eq_of_affine_combination_eq (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P) : affine_independent k p ↔
  ∀ (s1 s2 : finset ι) (w1 w2 : ι → k),
    (finset.sum s1 fun (i : ι) => w1 i) = 1 →
      (finset.sum s2 fun (i : ι) => w2 i) = 1 →
        coe_fn (finset.affine_combination s1 p) w1 = coe_fn (finset.affine_combination s2 p) w2 →
          set.indicator (↑s1) w1 = set.indicator (↑s2) w2 := sorry

/-- An affinely independent family is injective, if the underlying
ring is nontrivial. -/
theorem injective_of_affine_independent {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [nontrivial k] {p : ι → P} (ha : affine_independent k p) : function.injective p := sorry

/-- If a family is affinely independent, so is any subfamily given by
composition of an embedding into index type with the original
family. -/
theorem affine_independent_embedding_of_affine_independent {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {ι2 : Type u_5} (f : ι2 ↪ ι) {p : ι → P} (ha : affine_independent k p) : affine_independent k (p ∘ ⇑f) := sorry

/-- If a family is affinely independent, so is any subfamily indexed
by a subtype of the index type. -/
theorem affine_independent_subtype_of_affine_independent {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {p : ι → P} (ha : affine_independent k p) (s : set ι) : affine_independent k fun (i : ↥s) => p ↑i :=
  affine_independent_embedding_of_affine_independent (function.embedding.subtype fun (x : ι) => x ∈ s) ha

/-- If an indexed family of points is affinely independent, so is the
corresponding set of points. -/
theorem affine_independent_set_of_affine_independent {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {p : ι → P} (ha : affine_independent k p) : affine_independent k fun (x : ↥(set.range p)) => ↑x := sorry

/-- If a set of points is affinely independent, so is any subset. -/
theorem affine_independent_of_subset_affine_independent {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} {t : set P} (ha : affine_independent k fun (x : ↥t) => ↑x) (hs : s ⊆ t) : affine_independent k fun (x : ↥s) => ↑x :=
  affine_independent_embedding_of_affine_independent (set.embedding_of_subset s t hs) ha

/-- If the range of an injective indexed family of points is affinely
independent, so is that family. -/
theorem affine_independent_of_affine_independent_set_of_injective {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {p : ι → P} (ha : affine_independent k fun (x : ↥(set.range p)) => ↑x) (hi : function.injective p) : affine_independent k p := sorry

/-- If a family is affinely independent, and the spans of points
indexed by two subsets of the index type have a point in common, those
subsets of the index type have an element in common, if the underlying
ring is nontrivial. -/
theorem exists_mem_inter_of_exists_mem_inter_affine_span_of_affine_independent {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [nontrivial k] {p : ι → P} (ha : affine_independent k p) {s1 : set ι} {s2 : set ι} {p0 : P} (hp0s1 : p0 ∈ affine_span k (p '' s1)) (hp0s2 : p0 ∈ affine_span k (p '' s2)) : ∃ (i : ι), i ∈ s1 ∩ s2 := sorry

/-- If a family is affinely independent, the spans of points indexed
by disjoint subsets of the index type are disjoint, if the underlying
ring is nontrivial. -/
theorem affine_span_disjoint_of_disjoint_of_affine_independent {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [nontrivial k] {p : ι → P} (ha : affine_independent k p) {s1 : set ι} {s2 : set ι} (hd : s1 ∩ s2 = ∅) : ↑(affine_span k (p '' s1)) ∩ ↑(affine_span k (p '' s2)) = ∅ := sorry

/-- If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial. -/
@[simp] theorem mem_affine_span_iff_mem_of_affine_independent {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [nontrivial k] {p : ι → P} (ha : affine_independent k p) (i : ι) (s : set ι) : p i ∈ affine_span k (p '' s) ↔ i ∈ s := sorry

/-- If a family is affinely independent, a point in the family is not
in the affine span of the other points, if the underlying ring is
nontrivial. -/
theorem not_mem_affine_span_diff_of_affine_independent {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [nontrivial k] {p : ι → P} (ha : affine_independent k p) (i : ι) (s : set ι) : ¬p i ∈ affine_span k (p '' (s \ singleton i)) := sorry

/-- An affinely independent set of points can be extended to such a
set that spans the whole space. -/
theorem exists_subset_affine_independent_affine_span_eq_top {k : Type u_1} {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} (h : affine_independent k fun (p : ↥s) => ↑p) : ∃ (t : set P), s ⊆ t ∧ (affine_independent k fun (p : ↥t) => ↑p) ∧ affine_span k t = ⊤ := sorry

/-- Two different points are affinely independent. -/
theorem affine_independent_of_ne (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {p₁ : P} {p₂ : P} (h : p₁ ≠ p₂) : affine_independent k (matrix.vec_cons p₁ (matrix.vec_cons p₂ matrix.vec_empty)) := sorry

namespace affine


/-- A `simplex k P n` is a collection of `n + 1` affinely
independent points. -/
structure simplex (k : Type u_1) {V : Type u_2} (P : Type u_3) [ring k] [add_comm_group V] [module k V] [add_torsor V P] (n : ℕ) 
where
  points : fin (n + 1) → P
  independent : affine_independent k points

/-- A `triangle k P` is a collection of three affinely independent points. -/
def triangle (k : Type u_1) {V : Type u_2} (P : Type u_3) [ring k] [add_comm_group V] [module k V] [add_torsor V P]  :=
  simplex k P (bit0 1)

namespace simplex


/-- Construct a 0-simplex from a point. -/
def mk_of_point (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (p : P) : simplex k P 0 :=
  mk (fun (_x : fin (0 + 1)) => p) sorry

/-- The point in a simplex constructed with `mk_of_point`. -/
@[simp] theorem mk_of_point_points (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (p : P) (i : fin 1) : points (mk_of_point k p) i = p :=
  rfl

protected instance inhabited (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] [Inhabited P] : Inhabited (simplex k P 0) :=
  { default := mk_of_point k Inhabited.default }

protected instance nonempty (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] : Nonempty (simplex k P 0) :=
  Nonempty.intro (mk_of_point k (nonempty.some add_torsor.nonempty))

/-- Two simplices are equal if they have the same points. -/
theorem ext {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {n : ℕ} {s1 : simplex k P n} {s2 : simplex k P n} (h : ∀ (i : fin (n + 1)), points s1 i = points s2 i) : s1 = s2 := sorry

/-- Two simplices are equal if and only if they have the same points. -/
theorem ext_iff {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {n : ℕ} (s1 : simplex k P n) (s2 : simplex k P n) : s1 = s2 ↔ ∀ (i : fin (n + 1)), points s1 i = points s2 i :=
  { mp := fun (h : s1 = s2) (_x : fin (n + 1)) => h ▸ rfl, mpr := ext }

/-- A face of a simplex is a simplex with the given subset of
points. -/
def face {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))} {m : ℕ} (h : finset.card fs = m + 1) : simplex k P m :=
  mk (points s ∘ ⇑(finset.order_emb_of_fin fs h)) sorry

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
theorem face_points {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))} {m : ℕ} (h : finset.card fs = m + 1) (i : fin (m + 1)) : points (face s h) i = points s (coe_fn (finset.order_emb_of_fin fs h) i) :=
  rfl

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
theorem face_points' {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))} {m : ℕ} (h : finset.card fs = m + 1) : points (face s h) = points s ∘ ⇑(finset.order_emb_of_fin fs h) :=
  rfl

/-- A single-point face equals the 0-simplex constructed with
`mk_of_point`. -/
@[simp] theorem face_eq_mk_of_point {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {n : ℕ} (s : simplex k P n) (i : fin (n + 1)) : face s (finset.card_singleton i) = mk_of_point k (points s i) := sorry

/-- The set of points of a face. -/
@[simp] theorem range_face_points {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))} {m : ℕ} (h : finset.card fs = m + 1) : set.range (points (face s h)) = points s '' ↑fs := sorry

end simplex


end affine


namespace affine


namespace simplex


/-- The centroid of a face of a simplex as the centroid of a subset of
the points. -/
@[simp] theorem face_centroid_eq_centroid {k : Type u_1} {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))} {m : ℕ} (h : finset.card fs = m + 1) : finset.centroid k finset.univ (points (face s h)) = finset.centroid k fs (points s) := sorry

/-- Over a characteristic-zero division ring, the centroids given by
two subsets of the points of a simplex are equal if and only if those
faces are given by the same subset of points. -/
@[simp] theorem centroid_eq_iff {k : Type u_1} {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] [char_zero k] {n : ℕ} (s : simplex k P n) {fs₁ : finset (fin (n + 1))} {fs₂ : finset (fin (n + 1))} {m₁ : ℕ} {m₂ : ℕ} (h₁ : finset.card fs₁ = m₁ + 1) (h₂ : finset.card fs₂ = m₂ + 1) : finset.centroid k fs₁ (points s) = finset.centroid k fs₂ (points s) ↔ fs₁ = fs₂ := sorry

/-- Over a characteristic-zero division ring, the centroids of two
faces of a simplex are equal if and only if those faces are given by
the same subset of points. -/
theorem face_centroid_eq_iff {k : Type u_1} {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] [char_zero k] {n : ℕ} (s : simplex k P n) {fs₁ : finset (fin (n + 1))} {fs₂ : finset (fin (n + 1))} {m₁ : ℕ} {m₂ : ℕ} (h₁ : finset.card fs₁ = m₁ + 1) (h₂ : finset.card fs₂ = m₂ + 1) : finset.centroid k finset.univ (points (face s h₁)) = finset.centroid k finset.univ (points (face s h₂)) ↔ fs₁ = fs₂ := sorry

/-- Two simplices with the same points have the same centroid. -/
theorem centroid_eq_of_range_eq {k : Type u_1} {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {n : ℕ} {s₁ : simplex k P n} {s₂ : simplex k P n} (h : set.range (points s₁) = set.range (points s₂)) : finset.centroid k finset.univ (points s₁) = finset.centroid k finset.univ (points s₂) := sorry

