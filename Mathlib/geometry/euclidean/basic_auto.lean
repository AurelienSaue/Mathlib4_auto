/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.inner_product
import Mathlib.algebra.quadratic_discriminant
import Mathlib.analysis.normed_space.add_torsor
import Mathlib.data.matrix.notation
import Mathlib.linear_algebra.affine_space.finite_dimensional
import Mathlib.tactic.fin_cases
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Euclidean spaces

This file makes some definitions and proves very basic geometrical
results about real inner product spaces and Euclidean affine spaces.
Results about real inner product spaces that involve the norm and
inner product but not angles generally go in
`analysis.normed_space.inner_product`.  Results with longer
proofs or more geometrical content generally go in separate files.

## Main definitions

* `inner_product_geometry.angle` is the undirected angle between two
  vectors.

* `euclidean_geometry.angle`, with notation `∠`, is the undirected
  angle determined by three points.

* `euclidean_geometry.orthogonal_projection` is the orthogonal
  projection of a point onto an affine subspace.

* `euclidean_geometry.reflection` is the reflection of a point in an
  affine subspace.

## Implementation notes

To declare `P` as the type of points in a Euclidean affine space with
`V` as the type of vectors, use `[inner_product_space ℝ V] [metric_space P]
[normed_add_torsor V P]`.  This works better with `out_param` to make
`V` implicit in most cases than having a separate type alias for
Euclidean affine spaces.

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/

namespace inner_product_geometry


/-!
### Geometrical results on real inner product spaces

This section develops some geometrical definitions and results on real
inner product spaces, where those definitions and results can most
conveniently be developed in terms of vectors and then used to deduce
corresponding results for Euclidean affine spaces.
-/

/-- The undirected angle between two vectors. If either vector is 0,
this is π/2. -/
def angle {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V) : ℝ :=
  real.arccos (inner x y / (norm x * norm y))

/-- The cosine of the angle between two vectors. -/
theorem cos_angle {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V) :
    real.cos (angle x y) = inner x y / (norm x * norm y) :=
  real.cos_arccos (and.left (iff.mp abs_le (abs_real_inner_div_norm_mul_norm_le_one x y)))
    (and.right (iff.mp abs_le (abs_real_inner_div_norm_mul_norm_le_one x y)))

/-- The angle between two vectors does not depend on their order. -/
theorem angle_comm {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V) :
    angle x y = angle y x :=
  sorry

/-- The angle between the negation of two vectors. -/
@[simp] theorem angle_neg_neg {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V) :
    angle (-x) (-y) = angle x y :=
  sorry

/-- The angle between two vectors is nonnegative. -/
theorem angle_nonneg {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V) : 0 ≤ angle x y :=
  real.arccos_nonneg (inner x y / (norm x * norm y))

/-- The angle between two vectors is at most π. -/
theorem angle_le_pi {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V) :
    angle x y ≤ real.pi :=
  real.arccos_le_pi (inner x y / (norm x * norm y))

/-- The angle between a vector and the negation of another vector. -/
theorem angle_neg_right {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V) :
    angle x (-y) = real.pi - angle x y :=
  sorry

/-- The angle between the negation of a vector and another vector. -/
theorem angle_neg_left {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V) :
    angle (-x) y = real.pi - angle x y :=
  sorry

/-- The angle between the zero vector and a vector. -/
@[simp] theorem angle_zero_left {V : Type u_1} [inner_product_space ℝ V] (x : V) :
    angle 0 x = real.pi / bit0 1 :=
  sorry

/-- The angle between a vector and the zero vector. -/
@[simp] theorem angle_zero_right {V : Type u_1} [inner_product_space ℝ V] (x : V) :
    angle x 0 = real.pi / bit0 1 :=
  sorry

/-- The angle between a nonzero vector and itself. -/
@[simp] theorem angle_self {V : Type u_1} [inner_product_space ℝ V] {x : V} (hx : x ≠ 0) :
    angle x x = 0 :=
  sorry

/-- The angle between a nonzero vector and its negation. -/
@[simp] theorem angle_self_neg_of_nonzero {V : Type u_1} [inner_product_space ℝ V] {x : V}
    (hx : x ≠ 0) : angle x (-x) = real.pi :=
  eq.mpr (id (Eq._oldrec (Eq.refl (angle x (-x) = real.pi)) (angle_neg_right x x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (real.pi - angle x x = real.pi)) (angle_self hx)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (real.pi - 0 = real.pi)) (sub_zero real.pi)))
        (Eq.refl real.pi)))

/-- The angle between the negation of a nonzero vector and that
vector. -/
@[simp] theorem angle_neg_self_of_nonzero {V : Type u_1} [inner_product_space ℝ V] {x : V}
    (hx : x ≠ 0) : angle (-x) x = real.pi :=
  eq.mpr (id (Eq._oldrec (Eq.refl (angle (-x) x = real.pi)) (angle_comm (-x) x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (angle x (-x) = real.pi)) (angle_self_neg_of_nonzero hx)))
      (Eq.refl real.pi))

/-- The angle between a vector and a positive multiple of a vector. -/
@[simp] theorem angle_smul_right_of_pos {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V)
    {r : ℝ} (hr : 0 < r) : angle x (r • y) = angle x y :=
  sorry

/-- The angle between a positive multiple of a vector and a vector. -/
@[simp] theorem angle_smul_left_of_pos {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V)
    {r : ℝ} (hr : 0 < r) : angle (r • x) y = angle x y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (angle (r • x) y = angle x y)) (angle_comm (r • x) y)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (angle y (r • x) = angle x y)) (angle_smul_right_of_pos y x hr)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (angle y x = angle x y)) (angle_comm y x)))
        (Eq.refl (angle x y))))

/-- The angle between a vector and a negative multiple of a vector. -/
@[simp] theorem angle_smul_right_of_neg {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V)
    {r : ℝ} (hr : r < 0) : angle x (r • y) = angle x (-y) :=
  sorry

/-- The angle between a negative multiple of a vector and a vector. -/
@[simp] theorem angle_smul_left_of_neg {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V)
    {r : ℝ} (hr : r < 0) : angle (r • x) y = angle (-x) y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (angle (r • x) y = angle (-x) y)) (angle_comm (r • x) y)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (angle y (r • x) = angle (-x) y)) (angle_smul_right_of_neg y x hr)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (angle y (-x) = angle (-x) y)) (angle_comm y (-x))))
        (Eq.refl (angle (-x) y))))

/-- The cosine of the angle between two vectors, multiplied by the
product of their norms. -/
theorem cos_angle_mul_norm_mul_norm {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V) :
    real.cos (angle x y) * (norm x * norm y) = inner x y :=
  sorry

/-- The sine of the angle between two vectors, multiplied by the
product of their norms. -/
theorem sin_angle_mul_norm_mul_norm {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V) :
    real.sin (angle x y) * (norm x * norm y) =
        real.sqrt (inner x x * inner y y - inner x y * inner x y) :=
  sorry

/-- The angle between two vectors is zero if and only if they are
nonzero and one is a positive multiple of the other. -/
theorem angle_eq_zero_iff {V : Type u_1} [inner_product_space ℝ V] {x : V} {y : V} :
    angle x y = 0 ↔ x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x :=
  sorry

/-- The angle between two vectors is π if and only if they are nonzero
and one is a negative multiple of the other. -/
theorem angle_eq_pi_iff {V : Type u_1} [inner_product_space ℝ V] {x : V} {y : V} :
    angle x y = real.pi ↔ x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x :=
  sorry

/-- If the angle between two vectors is π, the angles between those
vectors and a third vector add to π. -/
theorem angle_add_angle_eq_pi_of_angle_eq_pi {V : Type u_1} [inner_product_space ℝ V] {x : V}
    {y : V} (z : V) (h : angle x y = real.pi) : angle x z + angle y z = real.pi :=
  sorry

/-- Two vectors have inner product 0 if and only if the angle between
them is π/2. -/
theorem inner_eq_zero_iff_angle_eq_pi_div_two {V : Type u_1} [inner_product_space ℝ V] (x : V)
    (y : V) : inner x y = 0 ↔ angle x y = real.pi / bit0 1 :=
  sorry

end inner_product_geometry


namespace euclidean_geometry


/-!
### Geometrical results on Euclidean affine spaces

This section develops some geometrical definitions and results on
Euclidean affine spaces.
-/

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. If either of those points equals `p2`, this is π/2. Use
`open_locale euclidean_geometry` to access the `∠ p1 p2 p3`
notation. -/
def angle {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] (p1 : P) (p2 : P) (p3 : P) : ℝ :=
  inner_product_geometry.angle (p1 -ᵥ p2) (p3 -ᵥ p2)

/-- The angle at a point does not depend on the order of the other two
points. -/
theorem angle_comm {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] (p1 : P) (p2 : P) (p3 : P) : angle p1 p2 p3 = angle p3 p2 p1 :=
  inner_product_geometry.angle_comm (p1 -ᵥ p2) (p3 -ᵥ p2)

/-- The angle at a point is nonnegative. -/
theorem angle_nonneg {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] (p1 : P) (p2 : P) (p3 : P) : 0 ≤ angle p1 p2 p3 :=
  inner_product_geometry.angle_nonneg (p1 -ᵥ p2) (p3 -ᵥ p2)

/-- The angle at a point is at most π. -/
theorem angle_le_pi {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] (p1 : P) (p2 : P) (p3 : P) : angle p1 p2 p3 ≤ real.pi :=
  inner_product_geometry.angle_le_pi (p1 -ᵥ p2) (p3 -ᵥ p2)

/-- The angle ∠AAB at a point. -/
theorem angle_eq_left {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] (p1 : P) (p2 : P) : angle p1 p1 p2 = real.pi / bit0 1 :=
  sorry

/-- The angle ∠ABB at a point. -/
theorem angle_eq_right {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] (p1 : P) (p2 : P) : angle p1 p2 p2 = real.pi / bit0 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (angle p1 p2 p2 = real.pi / bit0 1)) (angle_comm p1 p2 p2)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (angle p2 p2 p1 = real.pi / bit0 1)) (angle_eq_left p2 p1)))
      (Eq.refl (real.pi / bit0 1)))

/-- The angle ∠ABA at a point. -/
theorem angle_eq_of_ne {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] {p1 : P} {p2 : P} (h : p1 ≠ p2) : angle p1 p2 p1 = 0 :=
  inner_product_geometry.angle_self fun (he : p1 -ᵥ p2 = 0) => h (iff.mp vsub_eq_zero_iff_eq he)

/-- If the angle ∠ABC at a point is π, the angle ∠BAC is 0. -/
theorem angle_eq_zero_of_angle_eq_pi_left {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {p1 : P} {p2 : P} {p3 : P}
    (h : angle p1 p2 p3 = real.pi) : angle p2 p1 p3 = 0 :=
  sorry

/-- If the angle ∠ABC at a point is π, the angle ∠BCA is 0. -/
theorem angle_eq_zero_of_angle_eq_pi_right {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {p1 : P} {p2 : P} {p3 : P}
    (h : angle p1 p2 p3 = real.pi) : angle p2 p3 p1 = 0 :=
  angle_eq_zero_of_angle_eq_pi_left
    (eq.mp (Eq._oldrec (Eq.refl (angle p1 p2 p3 = real.pi)) (angle_comm p1 p2 p3)) h)

/-- If ∠BCD = π, then ∠ABC = ∠ABD. -/
theorem angle_eq_angle_of_angle_eq_pi {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] (p1 : P) {p2 : P} {p3 : P} {p4 : P}
    (h : angle p2 p3 p4 = real.pi) : angle p1 p2 p3 = angle p1 p2 p4 :=
  sorry

/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
theorem angle_add_angle_eq_pi_of_angle_eq_pi {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] (p1 : P) {p2 : P} {p3 : P} {p4 : P}
    (h : angle p2 p3 p4 = real.pi) : angle p1 p3 p2 + angle p1 p3 p4 = real.pi :=
  sorry

/-- The inner product of two vectors given with `weighted_vsub`, in
terms of the pairwise distances. -/
theorem inner_weighted_vsub {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] {ι₁ : Type u_3} {s₁ : finset ι₁} {w₁ : ι₁ → ℝ} (p₁ : ι₁ → P)
    (h₁ : (finset.sum s₁ fun (i : ι₁) => w₁ i) = 0) {ι₂ : Type u_4} {s₂ : finset ι₂} {w₂ : ι₂ → ℝ}
    (p₂ : ι₂ → P) (h₂ : (finset.sum s₂ fun (i : ι₂) => w₂ i) = 0) :
    inner (coe_fn (finset.weighted_vsub s₁ p₁) w₁) (coe_fn (finset.weighted_vsub s₂ p₂) w₂) =
        (-finset.sum s₁
              fun (i₁ : ι₁) =>
                finset.sum s₂
                  fun (i₂ : ι₂) => w₁ i₁ * w₂ i₂ * (dist (p₁ i₁) (p₂ i₂) * dist (p₁ i₁) (p₂ i₂))) /
          bit0 1 :=
  sorry

/-- The distance between two points given with `affine_combination`,
in terms of the pairwise distances between the points in that
combination. -/
theorem dist_affine_combination {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {ι : Type u_3} {s : finset ι} {w₁ : ι → ℝ} {w₂ : ι → ℝ}
    (p : ι → P) (h₁ : (finset.sum s fun (i : ι) => w₁ i) = 1)
    (h₂ : (finset.sum s fun (i : ι) => w₂ i) = 1) :
    dist (coe_fn (finset.affine_combination s p) w₁) (coe_fn (finset.affine_combination s p) w₂) *
          dist (coe_fn (finset.affine_combination s p) w₁)
            (coe_fn (finset.affine_combination s p) w₂) =
        (-finset.sum s
              fun (i₁ : ι) =>
                finset.sum s
                  fun (i₂ : ι) =>
                    Sub.sub w₁ w₂ i₁ * Sub.sub w₁ w₂ i₂ *
                      (dist (p i₁) (p i₂) * dist (p i₁) (p i₂))) /
          bit0 1 :=
  sorry

/-- Suppose that `c₁` is equidistant from `p₁` and `p₂`, and the same
applies to `c₂`.  Then the vector between `c₁` and `c₂` is orthogonal
to that between `p₁` and `p₂`.  (In two dimensions, this says that the
diagonals of a kite are orthogonal.) -/
theorem inner_vsub_vsub_of_dist_eq_of_dist_eq {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {c₁ : P} {c₂ : P} {p₁ : P}
    {p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁) (hc₂ : dist p₁ c₂ = dist p₂ c₂) :
    inner (c₂ -ᵥ c₁) (p₂ -ᵥ p₁) = 0 :=
  sorry

/-- The squared distance between points on a line (expressed as a
multiple of a fixed vector added to a point) and another point,
expressed as a quadratic. -/
theorem dist_smul_vadd_square {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] (r : ℝ) (v : V) (p₁ : P) (p₂ : P) :
    dist (r • v +ᵥ p₁) p₂ * dist (r • v +ᵥ p₁) p₂ =
        inner v v * r * r + bit0 1 * inner v (p₁ -ᵥ p₂) * r + inner (p₁ -ᵥ p₂) (p₁ -ᵥ p₂) :=
  sorry

/-- The condition for two points on a line to be equidistant from
another point. -/
theorem dist_smul_vadd_eq_dist {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {v : V} (p₁ : P) (p₂ : P) (hv : v ≠ 0) (r : ℝ) :
    dist (r • v +ᵥ p₁) p₂ = dist p₁ p₂ ↔ r = 0 ∨ r = -bit0 1 * inner v (p₁ -ᵥ p₂) / inner v v :=
  sorry

/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in a two-dimensional subspace containing those points
(two circles intersect in at most two points). -/
theorem eq_of_dist_eq_of_dist_eq_of_mem_of_findim_eq_two {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    [finite_dimensional ℝ ↥(affine_subspace.direction s)]
    (hd : finite_dimensional.findim ℝ ↥(affine_subspace.direction s) = bit0 1) {c₁ : P} {c₂ : P}
    {p₁ : P} {p₂ : P} {p : P} (hc₁s : c₁ ∈ s) (hc₂s : c₂ ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s)
    (hps : p ∈ s) {r₁ : ℝ} {r₂ : ℝ} (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁)
    (hp₂c₁ : dist p₂ c₁ = r₁) (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂)
    (hp₂c₂ : dist p₂ c₂ = r₂) (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ :=
  sorry

/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in two-dimensional space (two circles intersect in at
most two points). -/
theorem eq_of_dist_eq_of_dist_eq_of_findim_eq_two {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] [finite_dimensional ℝ V]
    (hd : finite_dimensional.findim ℝ V = bit0 1) {c₁ : P} {c₂ : P} {p₁ : P} {p₂ : P} {p : P}
    {r₁ : ℝ} {r₂ : ℝ} (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁)
    (hp₂c₁ : dist p₂ c₁ = r₁) (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂)
    (hp₂c₂ : dist p₂ c₂ = r₂) (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ :=
  sorry

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete, as an unbundled function.  This
definition is only intended for use in setting up the bundled version
`orthogonal_projection` and should not be used once that is
defined. -/
def orthogonal_projection_fn {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] (s : affine_subspace ℝ P) [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] (p : P) : P :=
  classical.some sorry

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection_fn` of that
point onto the subspace.  This lemma is only intended for use in
setting up the bundled version and should not be used once that is
defined. -/
theorem inter_eq_singleton_orthogonal_projection_fn {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] (p : P) :
    ↑s ∩ ↑(affine_subspace.mk' p (affine_subspace.direction sᗮ)) =
        singleton (orthogonal_projection_fn s p) :=
  sorry

/-- The `orthogonal_projection_fn` lies in the given subspace.  This
lemma is only intended for use in setting up the bundled version and
should not be used once that is defined. -/
theorem orthogonal_projection_fn_mem {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P} [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] (p : P) : orthogonal_projection_fn s p ∈ s :=
  sorry

/-- The `orthogonal_projection_fn` lies in the orthogonal
subspace.  This lemma is only intended for use in setting up the
bundled version and should not be used once that is defined. -/
theorem orthogonal_projection_fn_mem_orthogonal {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] (p : P) :
    orthogonal_projection_fn s p ∈ affine_subspace.mk' p (affine_subspace.direction sᗮ) :=
  sorry

/-- Subtracting `p` from its `orthogonal_projection_fn` produces a
result in the orthogonal direction.  This lemma is only intended for
use in setting up the bundled version and should not be used once that
is defined. -/
theorem orthogonal_projection_fn_vsub_mem_direction_orthogonal {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] (p : P) :
    orthogonal_projection_fn s p -ᵥ p ∈ (affine_subspace.direction sᗮ) :=
  affine_subspace.direction_mk' p (affine_subspace.direction sᗮ) ▸
    affine_subspace.vsub_mem_direction (orthogonal_projection_fn_mem_orthogonal p)
      (affine_subspace.self_mem_mk' p (affine_subspace.direction sᗮ))

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete. The corresponding linear map
(mapping a vector to the difference between the projections of two
points whose difference is that vector) is the `orthogonal_projection`
for real inner product spaces, onto the direction of the affine
subspace being projected onto. -/
def orthogonal_projection {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] (s : affine_subspace ℝ P) [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] : affine_map ℝ P ↥s :=
  affine_map.mk
    (fun (p : P) =>
      { val := orthogonal_projection_fn s p, property := orthogonal_projection_fn_mem p })
    ↑(orthogonal_projection (affine_subspace.direction s)) sorry

@[simp] theorem orthogonal_projection_fn_eq {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P} [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] (p : P) :
    orthogonal_projection_fn s p = ↑(coe_fn (orthogonal_projection s) p) :=
  rfl

/-- The linear map corresponding to `orthogonal_projection`. -/
@[simp] theorem orthogonal_projection_linear {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P} [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] :
    affine_map.linear (orthogonal_projection s) =
        ↑(orthogonal_projection (affine_subspace.direction s)) :=
  rfl

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection` of that point
onto the subspace. -/
theorem inter_eq_singleton_orthogonal_projection {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] (p : P) :
    ↑s ∩ ↑(affine_subspace.mk' p (affine_subspace.direction sᗮ)) =
        singleton ↑(coe_fn (orthogonal_projection s) p) :=
  sorry

/-- The `orthogonal_projection` lies in the given subspace. -/
theorem orthogonal_projection_mem {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P} [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] (p : P) :
    ↑(coe_fn (orthogonal_projection s) p) ∈ s :=
  subtype.property (coe_fn (orthogonal_projection s) p)

/-- The `orthogonal_projection` lies in the orthogonal subspace. -/
theorem orthogonal_projection_mem_orthogonal {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] (s : affine_subspace ℝ P) [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] (p : P) :
    ↑(coe_fn (orthogonal_projection s) p) ∈ affine_subspace.mk' p (affine_subspace.direction sᗮ) :=
  orthogonal_projection_fn_mem_orthogonal p

/-- Subtracting a point in the given subspace from the
`orthogonal_projection` produces a result in the direction of the
given subspace. -/
theorem orthogonal_projection_vsub_mem_direction {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
    ↑(coe_fn (orthogonal_projection s) p2 -ᵥ { val := p1, property := hp1 }) ∈
        affine_subspace.direction s :=
  subtype.property (coe_fn (orthogonal_projection s) p2 -ᵥ { val := p1, property := hp1 })

/-- Subtracting the `orthogonal_projection` from a point in the given
subspace produces a result in the direction of the given subspace. -/
theorem vsub_orthogonal_projection_mem_direction {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
    ↑({ val := p1, property := hp1 } -ᵥ coe_fn (orthogonal_projection s) p2) ∈
        affine_subspace.direction s :=
  subtype.property ({ val := p1, property := hp1 } -ᵥ coe_fn (orthogonal_projection s) p2)

/-- A point equals its orthogonal projection if and only if it lies in
the subspace. -/
theorem orthogonal_projection_eq_self_iff {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P} [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] {p : P} :
    ↑(coe_fn (orthogonal_projection s) p) = p ↔ p ∈ s :=
  sorry

/-- Orthogonal projection is idempotent. -/
@[simp] theorem orthogonal_projection_orthogonal_projection {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (s : affine_subspace ℝ P)
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] (p : P) :
    coe_fn (orthogonal_projection s) ↑(coe_fn (orthogonal_projection s) p) =
        coe_fn (orthogonal_projection s) p :=
  sorry

theorem eq_orthogonal_projection_of_eq_subspace {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    {s' : affine_subspace ℝ P} [Nonempty ↥s] [Nonempty ↥s']
    [complete_space ↥(affine_subspace.direction s)] [complete_space ↥(affine_subspace.direction s')]
    (h : s = s') (p : P) :
    ↑(coe_fn (orthogonal_projection s) p) = ↑(coe_fn (orthogonal_projection s') p) :=
  sorry

/-- The distance to a point's orthogonal projection is 0 iff it lies in the subspace. -/
theorem dist_orthogonal_projection_eq_zero_iff {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] {p : P} :
    dist p ↑(coe_fn (orthogonal_projection s) p) = 0 ↔ p ∈ s :=
  sorry

/-- The distance between a point and its orthogonal projection is
nonzero if it does not lie in the subspace. -/
theorem dist_orthogonal_projection_ne_zero_of_not_mem {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] {p : P} (hp : ¬p ∈ s) :
    dist p ↑(coe_fn (orthogonal_projection s) p) ≠ 0 :=
  mt (iff.mp dist_orthogonal_projection_eq_zero_iff) hp

/-- Subtracting `p` from its `orthogonal_projection` produces a result
in the orthogonal direction. -/
theorem orthogonal_projection_vsub_mem_direction_orthogonal {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (s : affine_subspace ℝ P)
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] (p : P) :
    ↑(coe_fn (orthogonal_projection s) p) -ᵥ p ∈ (affine_subspace.direction sᗮ) :=
  orthogonal_projection_fn_vsub_mem_direction_orthogonal p

/-- Subtracting the `orthogonal_projection` from `p` produces a result
in the orthogonal direction. -/
theorem vsub_orthogonal_projection_mem_direction_orthogonal {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (s : affine_subspace ℝ P)
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] (p : P) :
    p -ᵥ ↑(coe_fn (orthogonal_projection s) p) ∈ (affine_subspace.direction sᗮ) :=
  affine_subspace.direction_mk' p (affine_subspace.direction sᗮ) ▸
    affine_subspace.vsub_mem_direction
      (affine_subspace.self_mem_mk' p (affine_subspace.direction sᗮ))
      (orthogonal_projection_mem_orthogonal s p)

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector was
in the orthogonal direction. -/
theorem orthogonal_projection_vadd_eq_self {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P} [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] {p : P} (hp : p ∈ s) {v : V}
    (hv : v ∈ (affine_subspace.direction sᗮ)) :
    coe_fn (orthogonal_projection s) (v +ᵥ p) = { val := p, property := hp } :=
  sorry

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
theorem orthogonal_projection_vadd_smul_vsub_orthogonal_projection {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] {p1 : P} (p2 : P) (r : ℝ)
    (hp : p1 ∈ s) :
    coe_fn (orthogonal_projection s) (r • (p2 -ᵥ ↑(coe_fn (orthogonal_projection s) p2)) +ᵥ p1) =
        { val := p1, property := hp } :=
  orthogonal_projection_vadd_eq_self hp
    (submodule.smul_mem (affine_subspace.direction sᗮ) r
      (vsub_orthogonal_projection_mem_direction_orthogonal s p2))

/-- The square of the distance from a point in `s` to `p2` equals the
sum of the squares of the distances of the two points to the
`orthogonal_projection`. -/
theorem dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
    {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
    {s : affine_subspace ℝ P} [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] {p1 : P}
    (p2 : P) (hp1 : p1 ∈ s) :
    dist p1 p2 * dist p1 p2 =
        dist p1 ↑(coe_fn (orthogonal_projection s) p2) *
            dist p1 ↑(coe_fn (orthogonal_projection s) p2) +
          dist p2 ↑(coe_fn (orthogonal_projection s) p2) *
            dist p2 ↑(coe_fn (orthogonal_projection s) p2) :=
  sorry

/-- The square of the distance between two points constructed by
adding multiples of the same orthogonal vector to points in the same
subspace. -/
theorem dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    {p1 : P} {p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (r1 : ℝ) (r2 : ℝ) {v : V}
    (hv : v ∈ (affine_subspace.direction sᗮ)) :
    dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) =
        dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (norm v * norm v) :=
  sorry

/-- Reflection in an affine subspace, which is expected to be nonempty
and complete.  The word "reflection" is sometimes understood to mean
specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The
definition here, of reflection in an affine subspace, is a more
general sense of the word that includes both those common cases.  If
the subspace is empty or not complete, `orthogonal_projection` is
defined as the identity map, which results in `reflection` being the
identity map in that case as well. -/
def reflection {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] (s : affine_subspace ℝ P) [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] : P ≃ᵢ P :=
  isometric.mk
    (equiv.mk
      (fun (p : P) =>
        ↑(coe_fn (orthogonal_projection s) p) -ᵥ p +ᵥ ↑(coe_fn (orthogonal_projection s) p))
      (fun (p : P) =>
        ↑(coe_fn (orthogonal_projection s) p) -ᵥ p +ᵥ ↑(coe_fn (orthogonal_projection s) p))
      sorry sorry)
    sorry

/-- The result of reflecting. -/
theorem reflection_apply {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] (s : affine_subspace ℝ P) [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] (p : P) :
    coe_fn (reflection s) p =
        ↑(coe_fn (orthogonal_projection s) p) -ᵥ p +ᵥ ↑(coe_fn (orthogonal_projection s) p) :=
  rfl

theorem eq_reflection_of_eq_subspace {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P} {s' : affine_subspace ℝ P}
    [Nonempty ↥s] [Nonempty ↥s'] [complete_space ↥(affine_subspace.direction s)]
    [complete_space ↥(affine_subspace.direction s')] (h : s = s') (p : P) :
    coe_fn (reflection s) p = coe_fn (reflection s') p :=
  sorry

/-- Reflection is its own inverse. -/
@[simp] theorem reflection_symm {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] (s : affine_subspace ℝ P) [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] :
    isometric.symm (reflection s) = reflection s :=
  rfl

/-- Reflecting twice in the same subspace. -/
@[simp] theorem reflection_reflection {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] (s : affine_subspace ℝ P) [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] (p : P) :
    coe_fn (reflection s) (coe_fn (reflection s) p) = p :=
  equiv.left_inv (isometric.to_equiv (reflection s)) p

/-- Reflection is involutive. -/
theorem reflection_involutive {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] (s : affine_subspace ℝ P) [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] : function.involutive ⇑(reflection s) :=
  reflection_reflection s

/-- A point is its own reflection if and only if it is in the
subspace. -/
theorem reflection_eq_self_iff {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P} [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] (p : P) : coe_fn (reflection s) p = p ↔ p ∈ s :=
  sorry

/-- Reflecting a point in two subspaces produces the same result if
and only if the point has the same orthogonal projection in each of
those subspaces. -/
theorem reflection_eq_iff_orthogonal_projection_eq {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (s₁ : affine_subspace ℝ P)
    (s₂ : affine_subspace ℝ P) [Nonempty ↥s₁] [Nonempty ↥s₂]
    [complete_space ↥(affine_subspace.direction s₁)]
    [complete_space ↥(affine_subspace.direction s₂)] (p : P) :
    coe_fn (reflection s₁) p = coe_fn (reflection s₂) p ↔
        ↑(coe_fn (orthogonal_projection s₁) p) = ↑(coe_fn (orthogonal_projection s₂) p) :=
  sorry

/-- The distance between `p₁` and the reflection of `p₂` equals that
between the reflection of `p₁` and `p₂`. -/
theorem dist_reflection {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] (s : affine_subspace ℝ P) [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] (p₁ : P) (p₂ : P) :
    dist p₁ (coe_fn (reflection s) p₂) = dist (coe_fn (reflection s) p₁) p₂ :=
  sorry

/-- A point in the subspace is equidistant from another point and its
reflection. -/
theorem dist_reflection_eq_of_mem {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] (s : affine_subspace ℝ P) [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ : P) :
    dist p₁ (coe_fn (reflection s) p₂) = dist p₁ p₂ :=
  sorry

/-- The reflection of a point in a subspace is contained in any larger
subspace containing both the point and the subspace reflected in. -/
theorem reflection_mem_of_le_of_mem {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {s₁ : affine_subspace ℝ P} {s₂ : affine_subspace ℝ P}
    [Nonempty ↥s₁] [complete_space ↥(affine_subspace.direction s₁)] (hle : s₁ ≤ s₂) {p : P}
    (hp : p ∈ s₂) : coe_fn (reflection s₁) p ∈ s₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (reflection s₁) p ∈ s₂)) (reflection_apply s₁ p)))
    (affine_subspace.vadd_mem_of_mem_direction
      (affine_subspace.vsub_mem_direction (hle (orthogonal_projection_mem p)) hp)
      (hle (orthogonal_projection_mem p)))

/-- Reflecting an orthogonal vector plus a point in the subspace
produces the negation of that vector plus the point. -/
theorem reflection_orthogonal_vadd {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P} [Nonempty ↥s]
    [complete_space ↥(affine_subspace.direction s)] {p : P} (hp : p ∈ s) {v : V}
    (hv : v ∈ (affine_subspace.direction sᗮ)) : coe_fn (reflection s) (v +ᵥ p) = -v +ᵥ p :=
  sorry

/-- Reflecting a vector plus a point in the subspace produces the
negation of that vector plus the point if the vector is a multiple of
the result of subtracting a point's orthogonal projection from that
point. -/
theorem reflection_vadd_smul_vsub_orthogonal_projection {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : affine_subspace ℝ P}
    [Nonempty ↥s] [complete_space ↥(affine_subspace.direction s)] {p₁ : P} (p₂ : P) (r : ℝ)
    (hp₁ : p₁ ∈ s) :
    coe_fn (reflection s) (r • (p₂ -ᵥ ↑(coe_fn (orthogonal_projection s) p₂)) +ᵥ p₁) =
        -(r • (p₂ -ᵥ ↑(coe_fn (orthogonal_projection s) p₂))) +ᵥ p₁ :=
  reflection_orthogonal_vadd hp₁
    (submodule.smul_mem (affine_subspace.direction sᗮ) r
      (vsub_orthogonal_projection_mem_direction_orthogonal s p₂))

/-- A set of points is cospherical if they are equidistant from some
point.  In two dimensions, this is the same thing as being
concyclic. -/
def cospherical {P : Type u_2} [metric_space P] (ps : set P) :=
  ∃ (center : P), ∃ (radius : ℝ), ∀ (p : P), p ∈ ps → dist p center = radius

/-- The definition of `cospherical`. -/
theorem cospherical_def {P : Type u_2} [metric_space P] (ps : set P) :
    cospherical ps ↔ ∃ (center : P), ∃ (radius : ℝ), ∀ (p : P), p ∈ ps → dist p center = radius :=
  iff.rfl

/-- A subset of a cospherical set is cospherical. -/
theorem cospherical_subset {P : Type u_2} [metric_space P] {ps₁ : set P} {ps₂ : set P}
    (hs : ps₁ ⊆ ps₂) (hc : cospherical ps₂) : cospherical ps₁ :=
  sorry

/-- The empty set is cospherical. -/
theorem cospherical_empty {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P] : cospherical ∅ :=
  sorry

/-- A single point is cospherical. -/
theorem cospherical_singleton {P : Type u_2} [metric_space P] (p : P) : cospherical (singleton p) :=
  sorry

/-- Two points are cospherical. -/
theorem cospherical_insert_singleton {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] (p₁ : P) (p₂ : P) :
    cospherical (insert p₁ (singleton p₂)) :=
  sorry

/-- Any three points in a cospherical set are affinely independent. -/
theorem cospherical.affine_independent {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {s : set P} (hs : cospherical s) {p : fin (bit1 1) → P}
    (hps : set.range p ⊆ s) (hpi : function.injective p) : affine_independent ℝ p :=
  sorry

end Mathlib