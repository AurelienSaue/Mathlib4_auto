/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.geometry.manifold.algebra.smooth_functions
import Mathlib.linear_algebra.finite_dimensional
import Mathlib.analysis.normed_space.inner_product
import Mathlib.PostPort

namespace Mathlib

/-!
# Constructing examples of manifolds over ℝ

We introduce the necessary bits to be able to define manifolds modelled over `ℝ^n`, boundaryless
or with boundary or with corners. As a concrete example, we construct explicitly the manifold with
boundary structure on the real interval `[x, y]`.

More specifically, we introduce
* `model_with_corners ℝ (euclidean_space ℝ (fin n)) (euclidean_half_space n)` for the model space used
  to define `n`-dimensional real manifolds with boundary
* `model_with_corners ℝ (euclidean_space ℝ (fin n)) (euclidean_quadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

## Notations

In the locale `manifold`, we introduce the notations
* `𝓡 n` for the identity model with corners on `euclidean_space ℝ (fin n)`
* `𝓡∂ n` for `model_with_corners ℝ (euclidean_space ℝ (fin n)) (euclidean_half_space n)`.

For instance, if a manifold `M` is boundaryless, smooth and modelled on `euclidean_space ℝ (fin m)`,
and `N` is smooth with boundary modelled on `euclidean_half_space n`, and `f : M → N` is a smooth
map, then the derivative of `f` can be written simply as `mfderiv (𝓡 m) (𝓡∂ n) f` (as to why the
model with corners can not be implicit, see the discussion in `smooth_manifold_with_corners.lean`).

## Implementation notes

The manifold structure on the interval `[x, y] = Icc x y` requires the assumption `x < y` as a
typeclass. We provide it as `[fact (x < y)]`.
-/

/--
The half-space in `ℝ^n`, used to model manifolds with boundary. We only define it when
`1 ≤ n`, as the definition only makes sense in this case.
-/
def euclidean_half_space (n : ℕ) [HasZero (fin n)] :=
  Subtype fun (x : euclidean_space ℝ (fin n)) => 0 ≤ x 0

/--
The quadrant in `ℝ^n`, used to model manifolds with corners, made of all vectors with nonnegative
coordinates.
-/
def euclidean_quadrant (n : ℕ) :=
  Subtype fun (x : euclidean_space ℝ (fin n)) => ∀ (i : fin n), 0 ≤ x i

/- Register class instances for euclidean half-space and quadrant, that can not be noticed
without the following reducibility attribute (which is only set in this section). -/

protected instance euclidean_half_space.topological_space {n : ℕ} [HasZero (fin n)] : topological_space (euclidean_half_space n) :=
  subtype.topological_space

protected instance euclidean_quadrant.topological_space {n : ℕ} : topological_space (euclidean_quadrant n) :=
  subtype.topological_space

protected instance euclidean_half_space.inhabited {n : ℕ} [HasZero (fin n)] : Inhabited (euclidean_half_space n) :=
  { default := { val := 0, property := sorry } }

protected instance euclidean_quadrant.inhabited {n : ℕ} : Inhabited (euclidean_quadrant n) :=
  { default := { val := 0, property := sorry } }

theorem range_half_space (n : ℕ) [HasZero (fin n)] : (set.range fun (x : euclidean_half_space n) => subtype.val x) = set_of fun (x : euclidean_space ℝ (fin n)) => 0 ≤ x 0 := sorry

theorem range_quadrant (n : ℕ) : (set.range fun (x : euclidean_quadrant n) => subtype.val x) =
  set_of fun (x : euclidean_space ℝ (fin n)) => ∀ (i : fin n), 0 ≤ x i := sorry

/--
Definition of the model with corners `(euclidean_space ℝ (fin n), euclidean_half_space n)`, used as a
model for manifolds with boundary. In the locale `manifold`, use the shortcut `𝓡∂ n`.
-/
def model_with_corners_euclidean_half_space (n : ℕ) [HasZero (fin n)] : model_with_corners ℝ (euclidean_space ℝ (fin n)) (euclidean_half_space n) :=
  model_with_corners.mk
    (local_equiv.mk (fun (x : euclidean_half_space n) => subtype.val x)
      (fun (x : euclidean_space ℝ (fin n)) =>
        { val := fun (i : fin n) => dite (i = 0) (fun (h : i = 0) => max (x i) 0) fun (h : ¬i = 0) => x i,
          property := sorry })
      set.univ (set.range fun (x : euclidean_half_space n) => subtype.val x) sorry sorry sorry sorry)
    sorry sorry

/--
Definition of the model with corners `(euclidean_space ℝ (fin n), euclidean_quadrant n)`, used as a
model for manifolds with corners -/
def model_with_corners_euclidean_quadrant (n : ℕ) : model_with_corners ℝ (euclidean_space ℝ (fin n)) (euclidean_quadrant n) :=
  model_with_corners.mk
    (local_equiv.mk (fun (x : euclidean_quadrant n) => subtype.val x)
      (fun (x : euclidean_space ℝ (fin n)) => { val := fun (i : fin n) => max (x i) 0, property := sorry }) set.univ
      (set.range fun (x : euclidean_quadrant n) => subtype.val x) sorry sorry sorry sorry)
    sorry sorry

/--
The left chart for the topological space `[x, y]`, defined on `[x,y)` and sending `x` to `0` in
`euclidean_half_space 1`.
-/
def Icc_left_chart (x : ℝ) (y : ℝ) [fact (x < y)] : local_homeomorph (↥(set.Icc x y)) (euclidean_half_space 1) :=
  local_homeomorph.mk
    (local_equiv.mk (fun (z : ↥(set.Icc x y)) => { val := fun (i : fin 1) => subtype.val z - x, property := sorry })
      (fun (z : euclidean_half_space 1) => { val := min (subtype.val z 0 + x) y, property := sorry })
      (set_of fun (z : ↥(set.Icc x y)) => subtype.val z < y)
      (set_of fun (z : euclidean_half_space 1) => subtype.val z 0 < y - x) sorry sorry sorry sorry)
    sorry sorry sorry sorry

/--
The right chart for the topological space `[x, y]`, defined on `(x,y]` and sending `y` to `0` in
`euclidean_half_space 1`.
-/
def Icc_right_chart (x : ℝ) (y : ℝ) [fact (x < y)] : local_homeomorph (↥(set.Icc x y)) (euclidean_half_space 1) :=
  local_homeomorph.mk
    (local_equiv.mk (fun (z : ↥(set.Icc x y)) => { val := fun (i : fin 1) => y - subtype.val z, property := sorry })
      (fun (z : euclidean_half_space 1) => { val := max (y - subtype.val z 0) x, property := sorry })
      (set_of fun (z : ↥(set.Icc x y)) => x < subtype.val z)
      (set_of fun (z : euclidean_half_space 1) => subtype.val z 0 < y - x) sorry sorry sorry sorry)
    sorry sorry sorry sorry

/--
Charted space structure on `[x, y]`, using only two charts taking values in `euclidean_half_space 1`.
-/
protected instance Icc_manifold (x : ℝ) (y : ℝ) [fact (x < y)] : charted_space (euclidean_half_space 1) ↥(set.Icc x y) :=
  charted_space.mk (insert (Icc_left_chart x y) (singleton (Icc_right_chart x y)))
    (fun (z : ↥(set.Icc x y)) => ite (subtype.val z < y) (Icc_left_chart x y) (Icc_right_chart x y)) sorry sorry

/--
The manifold structure on `[x, y]` is smooth.
-/
protected instance Icc_smooth_manifold (x : ℝ) (y : ℝ) [fact (x < y)] : smooth_manifold_with_corners (model_with_corners_euclidean_half_space 1) ↥(set.Icc x y) := sorry

/-! Register the manifold structure on `Icc 0 1`, and also its zero and one. -/

theorem fact_zero_lt_one : fact (0 < 1) :=
  zero_lt_one

protected instance set.Icc.charted_space : charted_space (euclidean_half_space 1) ↥(set.Icc 0 1) :=
  Mathlib.Icc_manifold 0 1

protected instance set.Icc.smooth_manifold_with_corners : smooth_manifold_with_corners (model_with_corners_euclidean_half_space 1) ↥(set.Icc 0 1) :=
  Mathlib.Icc_smooth_manifold 0 1

