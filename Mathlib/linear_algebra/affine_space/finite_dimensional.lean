/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.affine_space.independent
import Mathlib.linear_algebra.finite_dimensional
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Finite-dimensional subspaces of affine spaces.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

## Main definitions

* `collinear` defines collinear sets of points as those that span a
  subspace of dimension at most 1.

-/

/-- The `vector_span` of a finite set is finite-dimensional. -/
theorem finite_dimensional_vector_span_of_finite (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} (h : set.finite s) : finite_dimensional k ↥(vector_span k s) :=
  finite_dimensional.span_of_finite k (set.finite.vsub h h)

/-- The `vector_span` of a family indexed by a `fintype` is
finite-dimensional. -/
protected instance finite_dimensional_vector_span_of_fintype (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] (p : ι → P) : finite_dimensional k ↥(vector_span k (set.range p)) :=
  finite_dimensional_vector_span_of_finite k (set.finite_range p)

/-- The `vector_span` of a subset of a family indexed by a `fintype`
is finite-dimensional. -/
protected instance finite_dimensional_vector_span_image_of_fintype (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] (p : ι → P) (s : set ι) : finite_dimensional k ↥(vector_span k (p '' s)) :=
  finite_dimensional_vector_span_of_finite k (set.finite.image p (set.finite.of_fintype s))

/-- The direction of the affine span of a finite set is
finite-dimensional. -/
theorem finite_dimensional_direction_affine_span_of_finite (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} (h : set.finite s) : finite_dimensional k ↥(affine_subspace.direction (affine_span k s)) :=
  Eq.symm (direction_affine_span k s) ▸ finite_dimensional_vector_span_of_finite k h

/-- The direction of the affine span of a family indexed by a
`fintype` is finite-dimensional. -/
protected instance finite_dimensional_direction_affine_span_of_fintype (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] (p : ι → P) : finite_dimensional k ↥(affine_subspace.direction (affine_span k (set.range p))) :=
  finite_dimensional_direction_affine_span_of_finite k (set.finite_range p)

/-- The direction of the affine span of a subset of a family indexed
by a `fintype` is finite-dimensional. -/
protected instance finite_dimensional_direction_affine_span_image_of_fintype (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] (p : ι → P) (s : set ι) : finite_dimensional k ↥(affine_subspace.direction (affine_span k (p '' s))) :=
  finite_dimensional_direction_affine_span_of_finite k (set.finite.image p (set.finite.of_fintype s))

/-- The `vector_span` of a finite subset of an affinely independent
family has dimension one less than its cardinality. -/
theorem findim_vector_span_image_finset_of_affine_independent {k : Type u_1} {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {p : ι → P} (hi : affine_independent k p) {s : finset ι} {n : ℕ} (hc : finset.card s = n + 1) : finite_dimensional.findim k ↥(vector_span k (p '' ↑s)) = n := sorry

/-- The `vector_span` of a finite affinely independent family has
dimension one less than its cardinality. -/
theorem findim_vector_span_of_affine_independent {k : Type u_1} {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] {p : ι → P} (hi : affine_independent k p) {n : ℕ} (hc : fintype.card ι = n + 1) : finite_dimensional.findim k ↥(vector_span k (set.range p)) = n := sorry

/-- If the `vector_span` of a finite subset of an affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
theorem vector_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one {k : Type u_1} {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {p : ι → P} (hi : affine_independent k p) {s : finset ι} {sm : submodule k V} [finite_dimensional k ↥sm] (hle : vector_span k (p '' ↑s) ≤ sm) (hc : finset.card s = finite_dimensional.findim k ↥sm + 1) : vector_span k (p '' ↑s) = sm :=
  finite_dimensional.eq_of_le_of_findim_eq hle (findim_vector_span_image_finset_of_affine_independent hi hc)

/-- If the `vector_span` of a finite affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
theorem vector_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one {k : Type u_1} {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] {p : ι → P} (hi : affine_independent k p) {sm : submodule k V} [finite_dimensional k ↥sm] (hle : vector_span k (set.range p) ≤ sm) (hc : fintype.card ι = finite_dimensional.findim k ↥sm + 1) : vector_span k (set.range p) = sm :=
  finite_dimensional.eq_of_le_of_findim_eq hle (findim_vector_span_of_affine_independent hi hc)

/-- If the `affine_span` of a finite subset of an affinely independent
family lies in an affine subspace whose direction has dimension one
less than its cardinality, it equals that subspace. -/
theorem affine_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one {k : Type u_1} {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {p : ι → P} (hi : affine_independent k p) {s : finset ι} {sp : affine_subspace k P} [finite_dimensional k ↥(affine_subspace.direction sp)] (hle : affine_span k (p '' ↑s) ≤ sp) (hc : finset.card s = finite_dimensional.findim k ↥(affine_subspace.direction sp) + 1) : affine_span k (p '' ↑s) = sp := sorry

/-- If the `affine_span` of a finite affinely independent family lies
in an affine subspace whose direction has dimension one less than its
cardinality, it equals that subspace. -/
theorem affine_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one {k : Type u_1} {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] {p : ι → P} (hi : affine_independent k p) {sp : affine_subspace k P} [finite_dimensional k ↥(affine_subspace.direction sp)] (hle : affine_span k (set.range p) ≤ sp) (hc : fintype.card ι = finite_dimensional.findim k ↥(affine_subspace.direction sp) + 1) : affine_span k (set.range p) = sp := sorry

/-- The `vector_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
theorem vector_span_eq_top_of_affine_independent_of_card_eq_findim_add_one {k : Type u_1} {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [finite_dimensional k V] [fintype ι] {p : ι → P} (hi : affine_independent k p) (hc : fintype.card ι = finite_dimensional.findim k V + 1) : vector_span k (set.range p) = ⊤ :=
  finite_dimensional.eq_top_of_findim_eq (findim_vector_span_of_affine_independent hi hc)

/-- The `affine_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
theorem affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one {k : Type u_1} {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [finite_dimensional k V] [fintype ι] {p : ι → P} (hi : affine_independent k p) (hc : fintype.card ι = finite_dimensional.findim k V + 1) : affine_span k (set.range p) = ⊤ := sorry

/-- The `vector_span` of `n + 1` points in an indexed family has
dimension at most `n`. -/
theorem findim_vector_span_image_finset_le (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P) (s : finset ι) {n : ℕ} (hc : finset.card s = n + 1) : finite_dimensional.findim k ↥(vector_span k (p '' ↑s)) ≤ n := sorry

/-- The `vector_span` of an indexed family of `n + 1` points has
dimension at most `n`. -/
theorem findim_vector_span_range_le (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] (p : ι → P) {n : ℕ} (hc : fintype.card ι = n + 1) : finite_dimensional.findim k ↥(vector_span k (set.range p)) ≤ n := sorry

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension `n`. -/
theorem affine_independent_iff_findim_vector_span_eq (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] (p : ι → P) {n : ℕ} (hc : fintype.card ι = n + 1) : affine_independent k p ↔ finite_dimensional.findim k ↥(vector_span k (set.range p)) = n := sorry

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension at least `n`. -/
theorem affine_independent_iff_le_findim_vector_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] (p : ι → P) {n : ℕ} (hc : fintype.card ι = n + 1) : affine_independent k p ↔ n ≤ finite_dimensional.findim k ↥(vector_span k (set.range p)) := sorry

/-- `n + 2` points are affinely independent if and only if their
`vector_span` does not have dimension at most `n`. -/
theorem affine_independent_iff_not_findim_vector_span_le (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] (p : ι → P) {n : ℕ} (hc : fintype.card ι = n + bit0 1) : affine_independent k p ↔ ¬finite_dimensional.findim k ↥(vector_span k (set.range p)) ≤ n := sorry

/-- `n + 2` points have a `vector_span` with dimension at most `n` if
and only if they are not affinely independent. -/
theorem findim_vector_span_le_iff_not_affine_independent (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [fintype ι] (p : ι → P) {n : ℕ} (hc : fintype.card ι = n + bit0 1) : finite_dimensional.findim k ↥(vector_span k (set.range p)) ≤ n ↔ ¬affine_independent k p :=
  iff.symm (iff.mp not_iff_comm (iff.symm (affine_independent_iff_not_findim_vector_span_le k p hc)))

/-- A set of points is collinear if their `vector_span` has dimension
at most `1`. -/
def collinear (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P)  :=
  vector_space.dim k ↥(vector_span k s) ≤ 1

/-- The definition of `collinear`. -/
theorem collinear_iff_dim_le_one (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : collinear k s ↔ vector_space.dim k ↥(vector_span k s) ≤ 1 :=
  iff.rfl

/-- A set of points, whose `vector_span` is finite-dimensional, is
collinear if and only if their `vector_span` has dimension at most
`1`. -/
theorem collinear_iff_findim_le_one (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) [finite_dimensional k ↥(vector_span k s)] : collinear k s ↔ finite_dimensional.findim k ↥(vector_span k s) ≤ 1 := sorry

/-- The empty set is collinear. -/
theorem collinear_empty (k : Type u_1) {V : Type u_2} (P : Type u_3) [field k] [add_comm_group V] [module k V] [add_torsor V P] : collinear k ∅ := sorry

/-- A single point is collinear. -/
theorem collinear_singleton (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] (p : P) : collinear k (singleton p) := sorry

/-- Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`. -/
theorem collinear_iff_of_mem (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} {p₀ : P} (h : p₀ ∈ s) : collinear k s ↔ ∃ (v : V), ∀ (p : P), p ∈ s → ∃ (r : k), p = r • v +ᵥ p₀ := sorry

/-- A set of points is collinear if and only if they can all be
expressed as multiples of the same vector, added to the same base
point. -/
theorem collinear_iff_exists_forall_eq_smul_vadd (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : collinear k s ↔ ∃ (p₀ : P), ∃ (v : V), ∀ (p : P), p ∈ s → ∃ (r : k), p = r • v +ᵥ p₀ := sorry

/-- Two points are collinear. -/
theorem collinear_insert_singleton (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] (p₁ : P) (p₂ : P) : collinear k (insert p₁ (singleton p₂)) := sorry

/-- Three points are affinely independent if and only if they are not
collinear. -/
theorem affine_independent_iff_not_collinear (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] (p : fin (bit1 1) → P) : affine_independent k p ↔ ¬collinear k (set.range p) := sorry

/-- Three points are collinear if and only if they are not affinely
independent. -/
theorem collinear_iff_not_affine_independent (k : Type u_1) {V : Type u_2} {P : Type u_3} [field k] [add_comm_group V] [module k V] [add_torsor V P] (p : fin (bit1 1) → P) : collinear k (set.range p) ↔ ¬affine_independent k p := sorry

