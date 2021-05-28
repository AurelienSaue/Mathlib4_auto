/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.invertible
import Mathlib.data.indicator_function
import Mathlib.linear_algebra.affine_space.affine_map
import Mathlib.linear_algebra.affine_space.affine_subspace
import Mathlib.linear_algebra.finsupp
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# Affine combinations of points

This file defines affine combinations of points.

## Main definitions

* `weighted_vsub_of_point` is a general weighted combination of
  subtractions with an explicit base point, yielding a vector.

* `weighted_vsub` uses an arbitrary choice of base point and is intended
  to be used when the sum of weights is 0, in which case the result is
  independent of the choice of base point.

* `affine_combination` adds the weighted combination to the arbitrary
  base point, yielding a point rather than a vector, and is intended
  to be used when the sum of weights is 1, in which case the result is
  independent of the choice of base point.

These definitions are for sums over a `finset`; versions for a
`fintype` may be obtained using `finset.univ`, while versions for a
`finsupp` may be obtained using `finsupp.support`.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

namespace finset


/-- A weighted sum of the results of subtracting a base point from the
given points, as a linear map on the weights.  The main cases of
interest are where the sum of the weights is 0, in which case the sum
is independent of the choice of base point, and where the sum of the
weights is 1, in which case the sum added to the base point is
independent of the choice of base point. -/
def weighted_vsub_of_point {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (p : ι → P) (b : P) : linear_map k (ι → k) V :=
  finset.sum s fun (i : ι) => linear_map.smul_right (linear_map.proj i) (p i -ᵥ b)

@[simp] theorem weighted_vsub_of_point_apply {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w : ι → k) (p : ι → P) (b : P) : coe_fn (weighted_vsub_of_point s p b) w = finset.sum s fun (i : ι) => w i • (p i -ᵥ b) := sorry

/-- The weighted sum is independent of the base point when the sum of
the weights is 0. -/
theorem weighted_vsub_of_point_eq_of_sum_eq_zero {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w : ι → k) (p : ι → P) (h : (finset.sum s fun (i : ι) => w i) = 0) (b₁ : P) (b₂ : P) : coe_fn (weighted_vsub_of_point s p b₁) w = coe_fn (weighted_vsub_of_point s p b₂) w := sorry

/-- The weighted sum, added to the base point, is independent of the
base point when the sum of the weights is 1. -/
theorem weighted_vsub_of_point_vadd_eq_of_sum_eq_one {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w : ι → k) (p : ι → P) (h : (finset.sum s fun (i : ι) => w i) = 1) (b₁ : P) (b₂ : P) : coe_fn (weighted_vsub_of_point s p b₁) w +ᵥ b₁ = coe_fn (weighted_vsub_of_point s p b₂) w +ᵥ b₂ := sorry

/-- The weighted sum is unaffected by removing the base point, if
present, from the set of points. -/
@[simp] theorem weighted_vsub_of_point_erase {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w : ι → k) (p : ι → P) (i : ι) : coe_fn (weighted_vsub_of_point (erase s i) p (p i)) w = coe_fn (weighted_vsub_of_point s p (p i)) w := sorry

/-- The weighted sum is unaffected by adding the base point, whether
or not present, to the set of points. -/
@[simp] theorem weighted_vsub_of_point_insert {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w : ι → k) (p : ι → P) (i : ι) : coe_fn (weighted_vsub_of_point (insert i s) p (p i)) w = coe_fn (weighted_vsub_of_point s p (p i)) w := sorry

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem weighted_vsub_of_point_indicator_subset {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (w : ι → k) (p : ι → P) (b : P) {s₁ : finset ι} {s₂ : finset ι} (h : s₁ ⊆ s₂) : coe_fn (weighted_vsub_of_point s₁ p b) w = coe_fn (weighted_vsub_of_point s₂ p b) (set.indicator (↑s₁) w) := sorry

/-- A weighted sum, over the image of an embedding, equals a weighted
sum with the same points and weights over the original
`finset`. -/
theorem weighted_vsub_of_point_map {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} {ι₂ : Type u_5} (s₂ : finset ι₂) (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) (b : P) : coe_fn (weighted_vsub_of_point (map e s₂) p b) w = coe_fn (weighted_vsub_of_point s₂ (p ∘ ⇑e) b) (w ∘ ⇑e) := sorry

/-- A weighted sum of the results of subtracting a default base point
from the given points, as a linear map on the weights.  This is
intended to be used when the sum of the weights is 0; that condition
is specified as a hypothesis on those lemmas that require it. -/
def weighted_vsub {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (p : ι → P) : linear_map k (ι → k) V :=
  weighted_vsub_of_point s p (Classical.choice sorry)

/-- Applying `weighted_vsub` with given weights.  This is for the case
where a result involving a default base point is OK (for example, when
that base point will cancel out later); a more typical use case for
`weighted_vsub` would involve selecting a preferred base point with
`weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero` and then
using `weighted_vsub_of_point_apply`. -/
theorem weighted_vsub_apply {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w : ι → k) (p : ι → P) : coe_fn (weighted_vsub s p) w = finset.sum s fun (i : ι) => w i • (p i -ᵥ Classical.choice add_torsor.nonempty) := sorry

/-- `weighted_vsub` gives the sum of the results of subtracting any
base point, when the sum of the weights is 0. -/
theorem weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w : ι → k) (p : ι → P) (h : (finset.sum s fun (i : ι) => w i) = 0) (b : P) : coe_fn (weighted_vsub s p) w = coe_fn (weighted_vsub_of_point s p b) w :=
  weighted_vsub_of_point_eq_of_sum_eq_zero s w p h (Classical.choice weighted_vsub._proof_1) b

/-- The `weighted_vsub` for an empty set is 0. -/
@[simp] theorem weighted_vsub_empty {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (w : ι → k) (p : ι → P) : coe_fn (weighted_vsub ∅ p) w = 0 := sorry

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem weighted_vsub_indicator_subset {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (w : ι → k) (p : ι → P) {s₁ : finset ι} {s₂ : finset ι} (h : s₁ ⊆ s₂) : coe_fn (weighted_vsub s₁ p) w = coe_fn (weighted_vsub s₂ p) (set.indicator (↑s₁) w) :=
  weighted_vsub_of_point_indicator_subset w p (Classical.choice weighted_vsub._proof_1) h

/-- A weighted subtraction, over the image of an embedding, equals a
weighted subtraction with the same points and weights over the
original `finset`. -/
theorem weighted_vsub_map {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} {ι₂ : Type u_5} (s₂ : finset ι₂) (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) : coe_fn (weighted_vsub (map e s₂) p) w = coe_fn (weighted_vsub s₂ (p ∘ ⇑e)) (w ∘ ⇑e) :=
  weighted_vsub_of_point_map s₂ e w p (Classical.choice weighted_vsub._proof_1)

/-- A weighted sum of the results of subtracting a default base point
from the given points, added to that base point, as an affine map on
the weights.  This is intended to be used when the sum of the weights
is 1, in which case it is an affine combination (barycenter) of the
points with the given weights; that condition is specified as a
hypothesis on those lemmas that require it. -/
def affine_combination {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (p : ι → P) : affine_map k (ι → k) P :=
  affine_map.mk
    (fun (w : ι → k) => coe_fn (weighted_vsub_of_point s p (Classical.choice sorry)) w +ᵥ Classical.choice sorry)
    (weighted_vsub s p) sorry

/-- The linear map corresponding to `affine_combination` is
`weighted_vsub`. -/
@[simp] theorem affine_combination_linear {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (p : ι → P) : affine_map.linear (affine_combination s p) = weighted_vsub s p :=
  rfl

/-- Applying `affine_combination` with given weights.  This is for the
case where a result involving a default base point is OK (for example,
when that base point will cancel out later); a more typical use case
for `affine_combination` would involve selecting a preferred base
point with
`affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one` and
then using `weighted_vsub_of_point_apply`. -/
theorem affine_combination_apply {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w : ι → k) (p : ι → P) : coe_fn (affine_combination s p) w =
  coe_fn (weighted_vsub_of_point s p (Classical.choice add_torsor.nonempty)) w +ᵥ Classical.choice add_torsor.nonempty :=
  rfl

/-- `affine_combination` gives the sum with any base point, when the
sum of the weights is 1. -/
theorem affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w : ι → k) (p : ι → P) (h : (finset.sum s fun (i : ι) => w i) = 1) (b : P) : coe_fn (affine_combination s p) w = coe_fn (weighted_vsub_of_point s p b) w +ᵥ b :=
  weighted_vsub_of_point_vadd_eq_of_sum_eq_one s w p h (Classical.choice affine_combination._proof_1) b

/-- Adding a `weighted_vsub` to an `affine_combination`. -/
theorem weighted_vsub_vadd_affine_combination {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w₁ : ι → k) (w₂ : ι → k) (p : ι → P) : coe_fn (weighted_vsub s p) w₁ +ᵥ coe_fn (affine_combination s p) w₂ = coe_fn (affine_combination s p) (w₁ + w₂) := sorry

/-- Subtracting two `affine_combination`s. -/
theorem affine_combination_vsub {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w₁ : ι → k) (w₂ : ι → k) (p : ι → P) : coe_fn (affine_combination s p) w₁ -ᵥ coe_fn (affine_combination s p) w₂ = coe_fn (weighted_vsub s p) (w₁ - w₂) := sorry

/-- An `affine_combination` equals a point if that point is in the set
and has weight 1 and the other points in the set have weight 0. -/
@[simp] theorem affine_combination_of_eq_one_of_eq_zero {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : finset ι) (w : ι → k) (p : ι → P) {i : ι} (his : i ∈ s) (hwi : w i = 1) (hw0 : ∀ (i2 : ι), i2 ∈ s → i2 ≠ i → w i2 = 0) : coe_fn (affine_combination s p) w = p i := sorry

/-- An affine combination is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem affine_combination_indicator_subset {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (w : ι → k) (p : ι → P) {s₁ : finset ι} {s₂ : finset ι} (h : s₁ ⊆ s₂) : coe_fn (affine_combination s₁ p) w = coe_fn (affine_combination s₂ p) (set.indicator (↑s₁) w) := sorry

/-- An affine combination, over the image of an embedding, equals an
affine combination with the same points and weights over the original
`finset`. -/
theorem affine_combination_map {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} {ι₂ : Type u_5} (s₂ : finset ι₂) (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) : coe_fn (affine_combination (map e s₂) p) w = coe_fn (affine_combination s₂ (p ∘ ⇑e)) (w ∘ ⇑e) := sorry

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as
`weighted_vsub_of_point` using a `finset` lying within that subset and
with a given sum of weights if and only if it can be expressed as
`weighted_vsub_of_point` with that sum of weights for the
corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
theorem eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} {v : V} {x : k} {s : set ι} {p : ι → P} {b : P} : (∃ (fs : finset ι),
    ∃ (hfs : ↑fs ⊆ s),
      ∃ (w : ι → k), ∃ (hw : (finset.sum fs fun (i : ι) => w i) = x), v = coe_fn (weighted_vsub_of_point fs p b) w) ↔
  ∃ (fs : finset ↥s),
    ∃ (w : ↥s → k),
      ∃ (hw : (finset.sum fs fun (i : ↥s) => w i) = x),
        v = coe_fn (weighted_vsub_of_point fs (fun (i : ↥s) => p ↑i) b) w := sorry

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as `weighted_vsub` using
a `finset` lying within that subset and with sum of weights 0 if and
only if it can be expressed as `weighted_vsub` with sum of weights 0
for the corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
theorem eq_weighted_vsub_subset_iff_eq_weighted_vsub_subtype (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} {v : V} {s : set ι} {p : ι → P} : (∃ (fs : finset ι),
    ∃ (hfs : ↑fs ⊆ s),
      ∃ (w : ι → k), ∃ (hw : (finset.sum fs fun (i : ι) => w i) = 0), v = coe_fn (weighted_vsub fs p) w) ↔
  ∃ (fs : finset ↥s),
    ∃ (w : ↥s → k),
      ∃ (hw : (finset.sum fs fun (i : ↥s) => w i) = 0), v = coe_fn (weighted_vsub fs fun (i : ↥s) => p ↑i) w :=
  eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A point can be expressed as an
`affine_combination` using a `finset` lying within that subset and
with sum of weights 1 if and only if it can be expressed an
`affine_combination` with sum of weights 1 for the corresponding
indexed family whose index type is the subtype corresponding to that
subset. -/
theorem eq_affine_combination_subset_iff_eq_affine_combination_subtype (k : Type u_1) (V : Type u_2) {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} {p0 : P} {s : set ι} {p : ι → P} : (∃ (fs : finset ι),
    ∃ (hfs : ↑fs ⊆ s),
      ∃ (w : ι → k), ∃ (hw : (finset.sum fs fun (i : ι) => w i) = 1), p0 = coe_fn (affine_combination fs p) w) ↔
  ∃ (fs : finset ↥s),
    ∃ (w : ↥s → k),
      ∃ (hw : (finset.sum fs fun (i : ↥s) => w i) = 1), p0 = coe_fn (affine_combination fs fun (i : ↥s) => p ↑i) w := sorry

end finset


namespace finset


/-- The weights for the centroid of some points. -/
def centroid_weights (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) : ι → k :=
  function.const ι (↑(card s)⁻¹)

/-- `centroid_weights` at any point. -/
@[simp] theorem centroid_weights_apply (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) (i : ι) : centroid_weights k s i = (↑(card s)⁻¹) :=
  rfl

/-- `centroid_weights` equals a constant function. -/
theorem centroid_weights_eq_const (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) : centroid_weights k s = function.const ι (↑(card s)⁻¹) :=
  rfl

/-- The weights in the centroid sum to 1, if the number of points,
converted to `k`, is not zero. -/
theorem sum_centroid_weights_eq_one_of_cast_card_ne_zero {k : Type u_1} [division_ring k] {ι : Type u_4} (s : finset ι) (h : ↑(card s) ≠ 0) : (finset.sum s fun (i : ι) => centroid_weights k s i) = 1 := sorry

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is not zero. -/
theorem sum_centroid_weights_eq_one_of_card_ne_zero (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) [char_zero k] (h : card s ≠ 0) : (finset.sum s fun (i : ι) => centroid_weights k s i) = 1 := sorry

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the set is nonempty. -/
theorem sum_centroid_weights_eq_one_of_nonempty (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) [char_zero k] (h : finset.nonempty s) : (finset.sum s fun (i : ι) => centroid_weights k s i) = 1 :=
  sum_centroid_weights_eq_one_of_card_ne_zero k s (ne_of_gt (iff.mpr card_pos h))

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is `n + 1`. -/
theorem sum_centroid_weights_eq_one_of_card_eq_add_one (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) [char_zero k] {n : ℕ} (h : card s = n + 1) : (finset.sum s fun (i : ι) => centroid_weights k s i) = 1 :=
  sum_centroid_weights_eq_one_of_card_ne_zero k s (Eq.symm h ▸ nat.succ_ne_zero n)

/-- The centroid of some points.  Although defined for any `s`, this
is intended to be used in the case where the number of points,
converted to `k`, is not zero. -/
def centroid (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (s : finset ι) (p : ι → P) : P :=
  coe_fn (affine_combination s p) (centroid_weights k s)

/-- The definition of the centroid. -/
theorem centroid_def (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (s : finset ι) (p : ι → P) : centroid k s p = coe_fn (affine_combination s p) (centroid_weights k s) :=
  rfl

/-- The centroid of a single point. -/
@[simp] theorem centroid_singleton (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P) (i : ι) : centroid k (singleton i) p = p i := sorry

/-- The centroid of two points, expressed directly as adding a vector
to a point. -/
theorem centroid_insert_singleton (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [invertible (bit0 1)] (p : ι → P) (i₁ : ι) (i₂ : ι) : centroid k (insert i₁ (singleton i₂)) p = bit0 1⁻¹ • (p i₂ -ᵥ p i₁) +ᵥ p i₁ := sorry

/-- The centroid of two points indexed by `fin 2`, expressed directly
as adding a vector to the first point. -/
theorem centroid_insert_singleton_fin (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] [invertible (bit0 1)] (p : fin (bit0 1) → P) : centroid k univ p = bit0 1⁻¹ • (p 1 -ᵥ p 0) +ᵥ p 0 := sorry

/-- A centroid, over the image of an embedding, equals a centroid with
the same points and weights over the original `finset`. -/
theorem centroid_map (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {ι₂ : Type u_5} (s₂ : finset ι₂) (e : ι₂ ↪ ι) (p : ι → P) : centroid k (map e s₂) p = centroid k s₂ (p ∘ ⇑e) := sorry

/-- `centroid_weights` gives the weights for the centroid as a
constant function, which is suitable when summing over the points
whose centroid is being taken.  This function gives the weights in a
form suitable for summing over a larger set of points, as an indicator
function that is zero outside the set whose centroid is being taken.
In the case of a `fintype`, the sum may be over `univ`. -/
def centroid_weights_indicator (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) : ι → k :=
  set.indicator (↑s) (centroid_weights k s)

/-- The definition of `centroid_weights_indicator`. -/
theorem centroid_weights_indicator_def (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) : centroid_weights_indicator k s = set.indicator (↑s) (centroid_weights k s) :=
  rfl

/-- The sum of the weights for the centroid indexed by a `fintype`. -/
theorem sum_centroid_weights_indicator (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) [fintype ι] : (finset.sum univ fun (i : ι) => centroid_weights_indicator k s i) = finset.sum s fun (i : ι) => centroid_weights k s i :=
  Eq.symm (set.sum_indicator_subset (fun (i : ι) => centroid_weights k s i) (subset_univ s))

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the number of points is not
zero. -/
theorem sum_centroid_weights_indicator_eq_one_of_card_ne_zero (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) [char_zero k] [fintype ι] (h : card s ≠ 0) : (finset.sum univ fun (i : ι) => centroid_weights_indicator k s i) = 1 := sorry

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the set is nonempty. -/
theorem sum_centroid_weights_indicator_eq_one_of_nonempty (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) [char_zero k] [fintype ι] (h : finset.nonempty s) : (finset.sum univ fun (i : ι) => centroid_weights_indicator k s i) = 1 := sorry

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the number of points is `n + 1`. -/
theorem sum_centroid_weights_indicator_eq_one_of_card_eq_add_one (k : Type u_1) [division_ring k] {ι : Type u_4} (s : finset ι) [char_zero k] [fintype ι] {n : ℕ} (h : card s = n + 1) : (finset.sum univ fun (i : ι) => centroid_weights_indicator k s i) = 1 := sorry

/-- The centroid as an affine combination over a `fintype`. -/
theorem centroid_eq_affine_combination_fintype (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (s : finset ι) [fintype ι] (p : ι → P) : centroid k s p = coe_fn (affine_combination univ p) (centroid_weights_indicator k s) :=
  affine_combination_indicator_subset (centroid_weights k s) p (subset_univ s)

/-- An indexed family of points that is injective on the given
`finset` has the same centroid as the image of that `finset`.  This is
stated in terms of a set equal to the image to provide control of
definitional equality for the index type used for the centroid of the
image. -/
theorem centroid_eq_centroid_image_of_inj_on (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (s : finset ι) {p : ι → P} (hi : ∀ (i j : ι), i ∈ s → j ∈ s → p i = p j → i = j) {ps : set P} [fintype ↥ps] (hps : ps = p '' ↑s) : centroid k s p = centroid k univ fun (x : ↥ps) => ↑x := sorry

/-- Two indexed families of points that are injective on the given
`finset`s and with the same points in the image of those `finset`s
have the same centroid. -/
theorem centroid_eq_of_inj_on_of_image_eq (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (s : finset ι) {ι₂ : Type u_5} (s₂ : finset ι₂) {p : ι → P} (hi : ∀ (i j : ι), i ∈ s → j ∈ s → p i = p j → i = j) {p₂ : ι₂ → P} (hi₂ : ∀ (i j : ι₂), i ∈ s₂ → j ∈ s₂ → p₂ i = p₂ j → i = j) (he : p '' ↑s = p₂ '' ↑s₂) : centroid k s p = centroid k s₂ p₂ := sorry

end finset


/-- A `weighted_vsub` with sum of weights 0 is in the `vector_span` of
an indexed family. -/
theorem weighted_vsub_mem_vector_span {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {s : finset ι} {w : ι → k} (h : (finset.sum s fun (i : ι) => w i) = 0) (p : ι → P) : coe_fn (finset.weighted_vsub s p) w ∈ vector_span k (set.range p) := sorry

/-- An `affine_combination` with sum of weights 1 is in the
`affine_span` of an indexed family, if the underlying ring is
nontrivial. -/
theorem affine_combination_mem_affine_span {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [nontrivial k] {s : finset ι} {w : ι → k} (h : (finset.sum s fun (i : ι) => w i) = 1) (p : ι → P) : coe_fn (finset.affine_combination s p) w ∈ affine_span k (set.range p) := sorry

/-- A vector is in the `vector_span` of an indexed family if and only
if it is a `weighted_vsub` with sum of weights 0. -/
theorem mem_vector_span_iff_eq_weighted_vsub (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {v : V} {p : ι → P} : v ∈ vector_span k (set.range p) ↔
  ∃ (s : finset ι),
    ∃ (w : ι → k), ∃ (h : (finset.sum s fun (i : ι) => w i) = 0), v = coe_fn (finset.weighted_vsub s p) w := sorry

/-- A point in the `affine_span` of an indexed family is an
`affine_combination` with sum of weights 1. -/
theorem eq_affine_combination_of_mem_affine_span {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {p1 : P} {p : ι → P} (h : p1 ∈ affine_span k (set.range p)) : ∃ (s : finset ι),
  ∃ (w : ι → k), ∃ (hw : (finset.sum s fun (i : ι) => w i) = 1), p1 = coe_fn (finset.affine_combination s p) w := sorry

/-- A point is in the `affine_span` of an indexed family if and only
if it is an `affine_combination` with sum of weights 1, provided the
underlying ring is nontrivial. -/
theorem mem_affine_span_iff_eq_affine_combination (k : Type u_1) (V : Type u_2) {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [nontrivial k] {p1 : P} {p : ι → P} : p1 ∈ affine_span k (set.range p) ↔
  ∃ (s : finset ι),
    ∃ (w : ι → k), ∃ (hw : (finset.sum s fun (i : ι) => w i) = 1), p1 = coe_fn (finset.affine_combination s p) w := sorry

/-- The centroid lies in the affine span if the number of points,
converted to `k`, is not zero. -/
theorem centroid_mem_affine_span_of_cast_card_ne_zero {k : Type u_1} {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} {s : finset ι} (p : ι → P) (h : ↑(finset.card s) ≠ 0) : finset.centroid k s p ∈ affine_span k (set.range p) :=
  affine_combination_mem_affine_span (finset.sum_centroid_weights_eq_one_of_cast_card_ne_zero s h) p

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is not zero. -/
theorem centroid_mem_affine_span_of_card_ne_zero (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [char_zero k] {s : finset ι} (p : ι → P) (h : finset.card s ≠ 0) : finset.centroid k s p ∈ affine_span k (set.range p) :=
  affine_combination_mem_affine_span (finset.sum_centroid_weights_eq_one_of_card_ne_zero k s h) p

/-- In the characteristic zero case, the centroid lies in the affine
span if the set is nonempty. -/
theorem centroid_mem_affine_span_of_nonempty (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [char_zero k] {s : finset ι} (p : ι → P) (h : finset.nonempty s) : finset.centroid k s p ∈ affine_span k (set.range p) :=
  affine_combination_mem_affine_span (finset.sum_centroid_weights_eq_one_of_nonempty k s h) p

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is `n + 1`. -/
theorem centroid_mem_affine_span_of_card_eq_add_one (k : Type u_1) {V : Type u_2} {P : Type u_3} [division_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} [char_zero k] {s : finset ι} (p : ι → P) {n : ℕ} (h : finset.card s = n + 1) : finset.centroid k s p ∈ affine_span k (set.range p) :=
  affine_combination_mem_affine_span (finset.sum_centroid_weights_eq_one_of_card_eq_add_one k s h) p

namespace affine_map


-- TODO: define `affine_map.proj`, `affine_map.fst`, `affine_map.snd`

/-- A weighted sum, as an affine map on the points involved. -/
def weighted_vsub_of_point {k : Type u_1} {V : Type u_2} (P : Type u_3) [comm_ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (s : finset ι) (w : ι → k) : affine_map k ((ι → P) × P) V :=
  mk (fun (p : (ι → P) × P) => coe_fn (finset.weighted_vsub_of_point s (prod.fst p) (prod.snd p)) w)
    (finset.sum s
      fun (i : ι) =>
        w i • (linear_map.comp (linear_map.proj i) (linear_map.fst k (ι → V) V) - linear_map.snd k (ι → V) V))
    sorry

