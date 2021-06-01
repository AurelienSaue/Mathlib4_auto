/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.geometry.euclidean.basic
import Mathlib.tactic.interval_cases
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Triangles

This file proves basic geometrical results about distances and angles
in (possibly degenerate) triangles in real inner product spaces and
Euclidean affine spaces.  More specialized results, and results
developed for simplices in general rather than just for triangles, are
in separate files.  Definitions and results that make sense in more
general affine spaces rather than just in the Euclidean case go under
`linear_algebra.affine_space`.

## Implementation notes

Results in this file are generally given in a form with only those
non-degeneracy conditions needed for the particular result, rather
than requiring affine independence of the points of a triangle
unnecessarily.

## References

* https://en.wikipedia.org/wiki/Pythagorean_theorem
* https://en.wikipedia.org/wiki/Law_of_cosines
* https://en.wikipedia.org/wiki/Pons_asinorum
* https://en.wikipedia.org/wiki/Sum_of_angles_of_a_triangle

-/

namespace inner_product_geometry


/-!
### Geometrical results on triangles in real inner product spaces

This section develops some results on (possibly degenerate) triangles
in real inner product spaces, where those definitions and results can
most conveniently be developed in terms of vectors and then used to
deduce corresponding results for Euclidean affine spaces.
-/

/-- Pythagorean theorem, if-and-only-if vector angle form. -/
theorem norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two {V : Type u_1}
    [inner_product_space ℝ V] (x : V) (y : V) :
    norm (x + y) * norm (x + y) = norm x * norm x + norm y * norm y ↔
        angle x y = real.pi / bit0 1 :=
  sorry

/-- Pythagorean theorem, vector angle form. -/
theorem norm_add_square_eq_norm_square_add_norm_square' {V : Type u_1} [inner_product_space ℝ V]
    (x : V) (y : V) (h : angle x y = real.pi / bit0 1) :
    norm (x + y) * norm (x + y) = norm x * norm x + norm y * norm y :=
  iff.mpr (norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two x y) h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector angle form. -/
theorem norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two {V : Type u_1}
    [inner_product_space ℝ V] (x : V) (y : V) :
    norm (x - y) * norm (x - y) = norm x * norm x + norm y * norm y ↔
        angle x y = real.pi / bit0 1 :=
  sorry

/-- Pythagorean theorem, subtracting vectors, vector angle form. -/
theorem norm_sub_square_eq_norm_square_add_norm_square' {V : Type u_1} [inner_product_space ℝ V]
    (x : V) (y : V) (h : angle x y = real.pi / bit0 1) :
    norm (x - y) * norm (x - y) = norm x * norm x + norm y * norm y :=
  iff.mpr (norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two x y) h

/-- Law of cosines (cosine rule), vector angle form. -/
theorem norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
    {V : Type u_1} [inner_product_space ℝ V] (x : V) (y : V) :
    norm (x - y) * norm (x - y) =
        norm x * norm x + norm y * norm y - bit0 1 * norm x * norm y * real.cos (angle x y) :=
  sorry

/-- Pons asinorum, vector angle form. -/
theorem angle_sub_eq_angle_sub_rev_of_norm_eq {V : Type u_1} [inner_product_space ℝ V] {x : V}
    {y : V} (h : norm x = norm y) : angle x (x - y) = angle y (y - x) :=
  sorry

/-- Converse of pons asinorum, vector angle form. -/
theorem norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {V : Type u_1}
    [inner_product_space ℝ V] {x : V} {y : V} (h : angle x (x - y) = angle y (y - x))
    (hpi : angle x y ≠ real.pi) : norm x = norm y :=
  sorry

/-- The cosine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle {V : Type u_1} [inner_product_space ℝ V]
    {x : V} {y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    real.cos (angle x (x - y) + angle y (y - x)) = -real.cos (angle x y) :=
  sorry

/-- The sine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem sin_angle_sub_add_angle_sub_rev_eq_sin_angle {V : Type u_1} [inner_product_space ℝ V]
    {x : V} {y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    real.sin (angle x (x - y) + angle y (y - x)) = real.sin (angle x y) :=
  sorry

/-- The cosine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem cos_angle_add_angle_sub_add_angle_sub_eq_neg_one {V : Type u_1} [inner_product_space ℝ V]
    {x : V} {y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    real.cos (angle x y + angle x (x - y) + angle y (y - x)) = -1 :=
  sorry

/-- The sine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem sin_angle_add_angle_sub_add_angle_sub_eq_zero {V : Type u_1} [inner_product_space ℝ V]
    {x : V} {y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    real.sin (angle x y + angle x (x - y) + angle y (y - x)) = 0 :=
  sorry

/-- The sum of the angles of a possibly degenerate triangle (where the
two given sides are nonzero), vector angle form. -/
theorem angle_add_angle_sub_add_angle_sub_eq_pi {V : Type u_1} [inner_product_space ℝ V] {x : V}
    {y : V} (hx : x ≠ 0) (hy : y ≠ 0) : angle x y + angle x (x - y) + angle y (y - x) = real.pi :=
  sorry

end inner_product_geometry


namespace euclidean_geometry


/-!
### Geometrical results on triangles in Euclidean affine spaces

This section develops some geometrical definitions and results on
(possible degenerate) triangles in Euclidean affine spaces.
-/

/-- Pythagorean theorem, if-and-only-if angle-at-point form. -/
theorem dist_square_eq_dist_square_add_dist_square_iff_angle_eq_pi_div_two {V : Type u_1}
    {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] (p1 : P)
    (p2 : P) (p3 : P) :
    dist p1 p3 * dist p1 p3 = dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 ↔
        angle p1 p2 p3 = real.pi / bit0 1 :=
  sorry

/-- Law of cosines (cosine rule), angle-at-point form. -/
theorem dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle
    {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
    (p1 : P) (p2 : P) (p3 : P) :
    dist p1 p3 * dist p1 p3 =
        dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 -
          bit0 1 * dist p1 p2 * dist p3 p2 * real.cos (angle p1 p2 p3) :=
  sorry

/-- Pons asinorum, angle-at-point form. -/
theorem angle_eq_angle_of_dist_eq {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {p1 : P} {p2 : P} {p3 : P}
    (h : dist p1 p2 = dist p1 p3) : angle p1 p2 p3 = angle p1 p3 p2 :=
  sorry

/-- Converse of pons asinorum, angle-at-point form. -/
theorem dist_eq_of_angle_eq_angle_of_angle_ne_pi {V : Type u_1} {P : Type u_2}
    [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P] {p1 : P} {p2 : P} {p3 : P}
    (h : angle p1 p2 p3 = angle p1 p3 p2) (hpi : angle p2 p1 p3 ≠ real.pi) :
    dist p1 p2 = dist p1 p3 :=
  sorry

/-- The sum of the angles of a possibly degenerate triangle (where the
given vertex is distinct from the others), angle-at-point. -/
theorem angle_add_angle_add_angle_eq_pi {V : Type u_1} {P : Type u_2} [inner_product_space ℝ V]
    [metric_space P] [normed_add_torsor V P] {p1 : P} {p2 : P} {p3 : P} (h2 : p2 ≠ p1)
    (h3 : p3 ≠ p1) : angle p1 p2 p3 + angle p2 p3 p1 + angle p3 p1 p2 = real.pi :=
  sorry

end Mathlib