/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.geometry.euclidean.circumcenter
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Monge point and orthocenter

This file defines the orthocenter of a triangle, via its n-dimensional
generalization, the Monge point of a simplex.

## Main definitions

* `monge_point` is the Monge point of a simplex, defined in terms of
  its position on the Euler line and then shown to be the point of
  concurrence of the Monge planes.

* `monge_plane` is a Monge plane of an (n+2)-simplex, which is the
  (n+1)-dimensional affine subspace of the subspace spanned by the
  simplex that passes through the centroid of an n-dimensional face
  and is orthogonal to the opposite edge (in 2 dimensions, this is the
  same as an altitude).

* `altitude` is the line that passes through a vertex of a simplex and
  is orthogonal to the opposite face.

* `orthocenter` is defined, for the case of a triangle, to be the same
  as its Monge point, then shown to be the point of concurrence of the
  altitudes.

* `orthocentric_system` is a predicate on sets of points that says
  whether they are four points, one of which is the orthocenter of the
  other three (in which case various other properties hold, including
  that each is the orthocenter of the other three).

## References

* https://en.wikipedia.org/wiki/Altitude_(triangle)
* https://en.wikipedia.org/wiki/Monge_point
* https://en.wikipedia.org/wiki/Orthocentric_system
* Małgorzata Buba-Brzozowa, [The Monge Point and the 3(n+1) Point
  Sphere of an
  n-Simplex](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf)

-/

namespace affine


namespace simplex


/-- The Monge point of a simplex (in 2 or more dimensions) is a
generalization of the orthocenter of a triangle.  It is defined to be
the intersection of the Monge planes, where a Monge plane is the
(n-1)-dimensional affine subspace of the subspace spanned by the
simplex that passes through the centroid of an (n-2)-dimensional face
and is orthogonal to the opposite edge (in 2 dimensions, this is the
same as an altitude).  The circumcenter O, centroid G and Monge point
M are collinear in that order on the Euler line, with OG : GM = (n-1)
: 2.  Here, we use that ratio to define the Monge point (so resulting
in a point that equals the centroid in 0 or 1 dimensions), and then
show in subsequent lemmas that the point so defined lies in the Monge
planes and is their unique point of intersection. -/
def monge_point {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P n) : P :=
  (↑(n + 1) / ↑(n - 1)) • (finset.centroid ℝ finset.univ (points s) -ᵥ circumcenter s) +ᵥ circumcenter s

/-- The position of the Monge point in relation to the circumcenter
and centroid. -/
theorem monge_point_eq_smul_vsub_vadd_circumcenter {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P n) : monge_point s = (↑(n + 1) / ↑(n - 1)) • (finset.centroid ℝ finset.univ (points s) -ᵥ circumcenter s) +ᵥ circumcenter s :=
  rfl

/-- The Monge point lies in the affine span. -/
theorem monge_point_mem_affine_span {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P n) : monge_point s ∈ affine_span ℝ (set.range (points s)) :=
  affine_subspace.smul_vsub_vadd_mem (affine_span ℝ (set.range (points s))) (↑(n + 1) / ↑(n - 1))
    (centroid_mem_affine_span_of_card_eq_add_one ℝ (points s) (finset.card_fin (n + 1))) (circumcenter_mem_affine_span s)
    (circumcenter_mem_affine_span s)

/-- Two simplices with the same points have the same Monge point. -/
theorem monge_point_eq_of_range_eq {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} {s₁ : simplex ℝ P n} {s₂ : simplex ℝ P n} (h : set.range (points s₁) = set.range (points s₂)) : monge_point s₁ = monge_point s₂ := sorry

/-- The weights for the Monge point of an (n+2)-simplex, in terms of
`points_with_circumcenter`. -/
def monge_point_weights_with_circumcenter (n : ℕ) : points_with_circumcenter_index (n + bit0 1) → ℝ :=
  sorry

/-- `monge_point_weights_with_circumcenter` sums to 1. -/
@[simp] theorem sum_monge_point_weights_with_circumcenter (n : ℕ) : (finset.sum finset.univ
    fun (i : points_with_circumcenter_index (n + bit0 1)) => monge_point_weights_with_circumcenter n i) =
  1 := sorry

/-- The Monge point of an (n+2)-simplex, in terms of
`points_with_circumcenter`. -/
theorem monge_point_eq_affine_combination_of_points_with_circumcenter {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + bit0 1)) : monge_point s =
  coe_fn (finset.affine_combination finset.univ (points_with_circumcenter s)) (monge_point_weights_with_circumcenter n) := sorry

/-- The weights for the Monge point of an (n+2)-simplex, minus the
centroid of an n-dimensional face, in terms of
`points_with_circumcenter`.  This definition is only valid when `i₁ ≠ i₂`. -/
def monge_point_vsub_face_centroid_weights_with_circumcenter {n : ℕ} (i₁ : fin (n + bit1 1)) (i₂ : fin (n + bit1 1)) : points_with_circumcenter_index (n + bit0 1) → ℝ :=
  sorry

/-- `monge_point_vsub_face_centroid_weights_with_circumcenter` is the
result of subtracting `centroid_weights_with_circumcenter` from
`monge_point_weights_with_circumcenter`. -/
theorem monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub {n : ℕ} {i₁ : fin (n + bit1 1)} {i₂ : fin (n + bit1 1)} (h : i₁ ≠ i₂) : monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂ =
  monge_point_weights_with_circumcenter n - centroid_weights_with_circumcenter (insert i₁ (singleton i₂)ᶜ) := sorry

/-- `monge_point_vsub_face_centroid_weights_with_circumcenter` sums to 0. -/
@[simp] theorem sum_monge_point_vsub_face_centroid_weights_with_circumcenter {n : ℕ} {i₁ : fin (n + bit1 1)} {i₂ : fin (n + bit1 1)} (h : i₁ ≠ i₂) : (finset.sum finset.univ
    fun (i : points_with_circumcenter_index (n + bit0 1)) =>
      monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂ i) =
  0 := sorry

/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, in terms of `points_with_circumcenter`. -/
theorem monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + bit0 1)) {i₁ : fin (n + bit1 1)} {i₂ : fin (n + bit1 1)} (h : i₁ ≠ i₂) : monge_point s -ᵥ finset.centroid ℝ (insert i₁ (singleton i₂)ᶜ) (points s) =
  coe_fn (finset.weighted_vsub finset.univ (points_with_circumcenter s))
    (monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂) := sorry

/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, is orthogonal to the difference of the two
vertices not in that face. -/
theorem inner_monge_point_vsub_face_centroid_vsub {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + bit0 1)) {i₁ : fin (n + bit1 1)} {i₂ : fin (n + bit1 1)} (h : i₁ ≠ i₂) : inner (monge_point s -ᵥ finset.centroid ℝ (insert i₁ (singleton i₂)ᶜ) (points s)) (points s i₁ -ᵥ points s i₂) = 0 := sorry

/-- A Monge plane of an (n+2)-simplex is the (n+1)-dimensional affine
subspace of the subspace spanned by the simplex that passes through
the centroid of an n-dimensional face and is orthogonal to the
opposite edge (in 2 dimensions, this is the same as an altitude).
This definition is only intended to be used when `i₁ ≠ i₂`. -/
def monge_plane {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + bit0 1)) (i₁ : fin (n + bit1 1)) (i₂ : fin (n + bit1 1)) : affine_subspace ℝ P :=
  affine_subspace.mk' (finset.centroid ℝ (insert i₁ (singleton i₂)ᶜ) (points s))
      (submodule.span ℝ (singleton (points s i₁ -ᵥ points s i₂))ᗮ) ⊓
    affine_span ℝ (set.range (points s))

/-- The definition of a Monge plane. -/
theorem monge_plane_def {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + bit0 1)) (i₁ : fin (n + bit1 1)) (i₂ : fin (n + bit1 1)) : monge_plane s i₁ i₂ =
  affine_subspace.mk' (finset.centroid ℝ (insert i₁ (singleton i₂)ᶜ) (points s))
      (submodule.span ℝ (singleton (points s i₁ -ᵥ points s i₂))ᗮ) ⊓
    affine_span ℝ (set.range (points s)) :=
  rfl

/-- The Monge plane associated with vertices `i₁` and `i₂` equals that
associated with `i₂` and `i₁`. -/
theorem monge_plane_comm {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + bit0 1)) (i₁ : fin (n + bit1 1)) (i₂ : fin (n + bit1 1)) : monge_plane s i₁ i₂ = monge_plane s i₂ i₁ := sorry

/-- The Monge point lies in the Monge planes. -/
theorem monge_point_mem_monge_plane {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + bit0 1)) {i₁ : fin (n + bit1 1)} {i₂ : fin (n + bit1 1)} (h : i₁ ≠ i₂) : monge_point s ∈ monge_plane s i₁ i₂ := sorry

-- This doesn't actually need the `i₁ ≠ i₂` hypothesis, but it's

-- convenient for the proof and `monge_plane` isn't intended to be

-- useful without that hypothesis.

/-- The direction of a Monge plane. -/
theorem direction_monge_plane {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + bit0 1)) {i₁ : fin (n + bit1 1)} {i₂ : fin (n + bit1 1)} (h : i₁ ≠ i₂) : affine_subspace.direction (monge_plane s i₁ i₂) =
  submodule.span ℝ (singleton (points s i₁ -ᵥ points s i₂))ᗮ ⊓ vector_span ℝ (set.range (points s)) := sorry

/-- The Monge point is the only point in all the Monge planes from any
one vertex. -/
theorem eq_monge_point_of_forall_mem_monge_plane {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} {s : simplex ℝ P (n + bit0 1)} {i₁ : fin (n + bit1 1)} {p : P} (h : ∀ (i₂ : fin (n + bit1 1)), i₁ ≠ i₂ → p ∈ monge_plane s i₁ i₂) : p = monge_point s := sorry

/-- An altitude of a simplex is the line that passes through a vertex
and is orthogonal to the opposite face. -/
def altitude {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + bit0 1)) : affine_subspace ℝ P :=
  affine_subspace.mk' (points s i)
      (affine_subspace.direction (affine_span ℝ (points s '' ↑(finset.erase finset.univ i)))ᗮ) ⊓
    affine_span ℝ (set.range (points s))

/-- The definition of an altitude. -/
theorem altitude_def {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + bit0 1)) : altitude s i =
  affine_subspace.mk' (points s i)
      (affine_subspace.direction (affine_span ℝ (points s '' ↑(finset.erase finset.univ i)))ᗮ) ⊓
    affine_span ℝ (set.range (points s)) :=
  rfl

/-- A vertex lies in the corresponding altitude. -/
theorem mem_altitude {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + bit0 1)) : points s i ∈ altitude s i := sorry

/-- The direction of an altitude. -/
theorem direction_altitude {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + bit0 1)) : affine_subspace.direction (altitude s i) =
  vector_span ℝ (points s '' ↑(finset.erase finset.univ i))ᗮ ⊓ vector_span ℝ (set.range (points s)) := sorry

/-- The vector span of the opposite face lies in the direction
orthogonal to an altitude. -/
theorem vector_span_le_altitude_direction_orthogonal {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + bit0 1)) : vector_span ℝ (points s '' ↑(finset.erase finset.univ i)) ≤ (affine_subspace.direction (altitude s i)ᗮ) := sorry

/-- An altitude is finite-dimensional. -/
protected instance finite_dimensional_direction_altitude {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + bit0 1)) : finite_dimensional ℝ ↥(affine_subspace.direction (altitude s i)) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (finite_dimensional ℝ ↥(affine_subspace.direction (altitude s i)))) (direction_altitude s i)))
    (submodule.finite_dimensional_inf_right (vector_span ℝ (points s '' ↑(finset.erase finset.univ i))ᗮ)
      (vector_span ℝ (set.range (points s))))

/-- An altitude is one-dimensional (i.e., a line). -/
@[simp] theorem findim_direction_altitude {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + bit0 1)) : finite_dimensional.findim ℝ ↥(affine_subspace.direction (altitude s i)) = 1 := sorry

/-- A line through a vertex is the altitude through that vertex if and
only if it is orthogonal to the opposite face. -/
theorem affine_span_insert_singleton_eq_altitude_iff {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + bit0 1)) (p : P) : affine_span ℝ (insert p (singleton (points s i))) = altitude s i ↔
  p ≠ points s i ∧
    p ∈ affine_span ℝ (set.range (points s)) ∧
      p -ᵥ points s i ∈ (affine_subspace.direction (affine_span ℝ (points s '' ↑(finset.erase finset.univ i)))ᗮ) := sorry

end simplex


namespace triangle


/-- The orthocenter of a triangle is the intersection of its
altitudes.  It is defined here as the 2-dimensional case of the
Monge point. -/
def orthocenter {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (t : triangle ℝ P) : P :=
  simplex.monge_point t

/-- The orthocenter equals the Monge point. -/
theorem orthocenter_eq_monge_point {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (t : triangle ℝ P) : orthocenter t = simplex.monge_point t :=
  rfl

/-- The position of the orthocenter in relation to the circumcenter
and centroid. -/
theorem orthocenter_eq_smul_vsub_vadd_circumcenter {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (t : triangle ℝ P) : orthocenter t =
  bit1 1 • (finset.centroid ℝ finset.univ (simplex.points t) -ᵥ simplex.circumcenter t) +ᵥ simplex.circumcenter t := sorry

/-- The orthocenter lies in the affine span. -/
theorem orthocenter_mem_affine_span {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (t : triangle ℝ P) : orthocenter t ∈ affine_span ℝ (set.range (simplex.points t)) :=
  simplex.monge_point_mem_affine_span t

/-- Two triangles with the same points have the same orthocenter. -/
theorem orthocenter_eq_of_range_eq {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {t₁ : triangle ℝ P} {t₂ : triangle ℝ P} (h : set.range (simplex.points t₁) = set.range (simplex.points t₂)) : orthocenter t₁ = orthocenter t₂ :=
  simplex.monge_point_eq_of_range_eq h

/-- In the case of a triangle, altitudes are the same thing as Monge
planes. -/
theorem altitude_eq_monge_plane {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (t : triangle ℝ P) {i₁ : fin (bit1 1)} {i₂ : fin (bit1 1)} {i₃ : fin (bit1 1)} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) : simplex.altitude t i₁ = simplex.monge_plane t i₂ i₃ := sorry

/-- The orthocenter lies in the altitudes. -/
theorem orthocenter_mem_altitude {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (t : triangle ℝ P) {i₁ : fin (bit1 1)} : orthocenter t ∈ simplex.altitude t i₁ := sorry

/-- The orthocenter is the only point lying in any two of the
altitudes. -/
theorem eq_orthocenter_of_forall_mem_altitude {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {t : triangle ℝ P} {i₁ : fin (bit1 1)} {i₂ : fin (bit1 1)} {p : P} (h₁₂ : i₁ ≠ i₂) (h₁ : p ∈ simplex.altitude t i₁) (h₂ : p ∈ simplex.altitude t i₂) : p = orthocenter t := sorry

/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius. -/
theorem dist_orthocenter_reflection_circumcenter {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (t : triangle ℝ P) {i₁ : fin (bit1 1)} {i₂ : fin (bit1 1)} (h : i₁ ≠ i₂) : dist (orthocenter t)
    (coe_fn (euclidean_geometry.reflection (affine_span ℝ (simplex.points t '' insert i₁ (singleton i₂))))
      (simplex.circumcenter t)) =
  simplex.circumradius t := sorry

/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius, variant using a
`finset`. -/
theorem dist_orthocenter_reflection_circumcenter_finset {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (t : triangle ℝ P) {i₁ : fin (bit1 1)} {i₂ : fin (bit1 1)} (h : i₁ ≠ i₂) : dist (orthocenter t)
    (coe_fn (euclidean_geometry.reflection (affine_span ℝ (simplex.points t '' ↑(insert i₁ (singleton i₂)))))
      (simplex.circumcenter t)) =
  simplex.circumradius t := sorry

/-- The affine span of the orthocenter and a vertex is contained in
the altitude. -/
theorem affine_span_orthocenter_point_le_altitude {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (t : triangle ℝ P) (i : fin (bit1 1)) : affine_span ℝ (insert (orthocenter t) (singleton (simplex.points t i))) ≤ simplex.altitude t i := sorry

/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then an altitude of `t₂` from
a vertex that was not replaced is the corresponding side of `t₁`. -/
theorem altitude_replace_orthocenter_eq_affine_span {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {t₁ : triangle ℝ P} {t₂ : triangle ℝ P} {i₁ : fin (bit1 1)} {i₂ : fin (bit1 1)} {i₃ : fin (bit1 1)} {j₁ : fin (bit1 1)} {j₂ : fin (bit1 1)} {j₃ : fin (bit1 1)} (hi₁₂ : i₁ ≠ i₂) (hi₁₃ : i₁ ≠ i₃) (hi₂₃ : i₂ ≠ i₃) (hj₁₂ : j₁ ≠ j₂) (hj₁₃ : j₁ ≠ j₃) (hj₂₃ : j₂ ≠ j₃) (h₁ : simplex.points t₂ j₁ = orthocenter t₁) (h₂ : simplex.points t₂ j₂ = simplex.points t₁ i₂) (h₃ : simplex.points t₂ j₃ = simplex.points t₁ i₃) : simplex.altitude t₂ j₂ = affine_span ℝ (insert (simplex.points t₁ i₁) (singleton (simplex.points t₁ i₂))) := sorry

/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then the orthocenter of `t₂`
is the vertex of `t₁` that was replaced. -/
theorem orthocenter_replace_orthocenter_eq_point {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {t₁ : triangle ℝ P} {t₂ : triangle ℝ P} {i₁ : fin (bit1 1)} {i₂ : fin (bit1 1)} {i₃ : fin (bit1 1)} {j₁ : fin (bit1 1)} {j₂ : fin (bit1 1)} {j₃ : fin (bit1 1)} (hi₁₂ : i₁ ≠ i₂) (hi₁₃ : i₁ ≠ i₃) (hi₂₃ : i₂ ≠ i₃) (hj₁₂ : j₁ ≠ j₂) (hj₁₃ : j₁ ≠ j₃) (hj₂₃ : j₂ ≠ j₃) (h₁ : simplex.points t₂ j₁ = orthocenter t₁) (h₂ : simplex.points t₂ j₂ = simplex.points t₁ i₂) (h₃ : simplex.points t₂ j₃ = simplex.points t₁ i₃) : orthocenter t₂ = simplex.points t₁ i₁ := sorry

end triangle


end affine


namespace euclidean_geometry


/-- Four points form an orthocentric system if they consist of the
vertices of a triangle and its orthocenter. -/
def orthocentric_system {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (s : set P) :=
  ∃ (t : affine.triangle ℝ P),
    ¬affine.triangle.orthocenter t ∈ set.range (affine.simplex.points t) ∧
      s = insert (affine.triangle.orthocenter t) (set.range (affine.simplex.points t))

/-- This is an auxiliary lemma giving information about the relation
of two triangles in an orthocentric system; it abstracts some
reasoning, with no geometric content, that is common to some other
lemmas.  Suppose the orthocentric system is generated by triangle `t`,
and we are given three points `p` in the orthocentric system.  Then
either we can find indices `i₁`, `i₂` and `i₃` for `p` such that `p
i₁` is the orthocenter of `t` and `p i₂` and `p i₃` are points `j₂`
and `j₃` of `t`, or `p` has the same points as `t`. -/
theorem exists_of_range_subset_orthocentric_system {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {t : affine.triangle ℝ P} (ho : ¬affine.triangle.orthocenter t ∈ set.range (affine.simplex.points t)) {p : fin (bit1 1) → P} (hps : set.range p ⊆ insert (affine.triangle.orthocenter t) (set.range (affine.simplex.points t))) (hpi : function.injective p) : (∃ (i₁ : fin (bit1 1)),
    ∃ (i₂ : fin (bit1 1)),
      ∃ (i₃ : fin (bit1 1)),
        ∃ (j₂ : fin (bit1 1)),
          ∃ (j₃ : fin (bit1 1)),
            i₁ ≠ i₂ ∧
              i₁ ≠ i₃ ∧
                i₂ ≠ i₃ ∧
                  (∀ (i : fin (bit1 1)), i = i₁ ∨ i = i₂ ∨ i = i₃) ∧
                    p i₁ = affine.triangle.orthocenter t ∧
                      j₂ ≠ j₃ ∧ affine.simplex.points t j₂ = p i₂ ∧ affine.simplex.points t j₃ = p i₃) ∨
  set.range p = set.range (affine.simplex.points t) := sorry

/-- For any three points in an orthocentric system generated by
triangle `t`, there is a point in the subspace spanned by the triangle
from which the distance of all those three points equals the circumradius. -/
theorem exists_dist_eq_circumradius_of_subset_insert_orthocenter {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {t : affine.triangle ℝ P} (ho : ¬affine.triangle.orthocenter t ∈ set.range (affine.simplex.points t)) {p : fin (bit1 1) → P} (hps : set.range p ⊆ insert (affine.triangle.orthocenter t) (set.range (affine.simplex.points t))) (hpi : function.injective p) : ∃ (c : P),
  ∃ (H : c ∈ affine_span ℝ (set.range (affine.simplex.points t))),
    ∀ (p₁ : P), p₁ ∈ set.range p → dist p₁ c = affine.simplex.circumradius t := sorry

/-- Any three points in an orthocentric system are affinely independent. -/
theorem orthocentric_system.affine_independent {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : set P} (ho : orthocentric_system s) {p : fin (bit1 1) → P} (hps : set.range p ⊆ s) (hpi : function.injective p) : affine_independent ℝ p := sorry

/-- Any three points in an orthocentric system span the same subspace
as the whole orthocentric system. -/
theorem affine_span_of_orthocentric_system {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : set P} (ho : orthocentric_system s) {p : fin (bit1 1) → P} (hps : set.range p ⊆ s) (hpi : function.injective p) : affine_span ℝ (set.range p) = affine_span ℝ s := sorry

/-- All triangles in an orthocentric system have the same circumradius. -/
theorem orthocentric_system.exists_circumradius_eq {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : set P} (ho : orthocentric_system s) : ∃ (r : ℝ), ∀ (t : affine.triangle ℝ P), set.range (affine.simplex.points t) ⊆ s → affine.simplex.circumradius t = r := sorry

/-- Given any triangle in an orthocentric system, the fourth point is
its orthocenter. -/
theorem orthocentric_system.eq_insert_orthocenter {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {s : set P} (ho : orthocentric_system s) {t : affine.triangle ℝ P} (ht : set.range (affine.simplex.points t) ⊆ s) : s = insert (affine.triangle.orthocenter t) (set.range (affine.simplex.points t)) := sorry

