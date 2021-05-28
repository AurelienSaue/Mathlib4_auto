/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.local_extr
import Mathlib.analysis.calculus.deriv
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Local extrema of smooth functions

## Main definitions

In a real normed space `E` we define `pos_tangent_cone_at (s : set E) (x : E)`.
This would be the same as `tangent_cone_at ℝ≥0 s x` if we had a theory of normed semifields.
This set is used in the proof of Fermat's Theorem (see below), and can be used to formalize
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) and/or
[Karush–Kuhn–Tucker conditions](https://en.wikipedia.org/wiki/Karush–Kuhn–Tucker_conditions).

## Main statements

For each theorem name listed below, we also prove similar theorems for `min`, `extr` (if applicable)`,
and `(f)deriv` instead of `has_fderiv`.

* `is_local_max_on.has_fderiv_within_at_nonpos` : `f' y ≤ 0` whenever `a` is a local maximum
  of `f` on `s`, `f` has derivative `f'` at `a` within `s`, and `y` belongs to the positive tangent
  cone of `s` at `a`.

* `is_local_max_on.has_fderiv_within_at_eq_zero` : In the settings of the previous theorem, if both
  `y` and `-y` belong to the positive tangent cone, then `f' y = 0`.

* `is_local_max.has_fderiv_at_eq_zero` :
  [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points)),
  the derivative of a differentiable function at a local extremum point equals zero.

* `exists_has_deriv_at_eq_zero` :
  [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem): given a function `f` continuous
  on `[a, b]` and differentiable on `(a, b)`, there exists `c ∈ (a, b)` such that `f' c = 0`.

## Implementation notes

For each mathematical fact we prove several versions of its formalization:

* for maxima and minima;
* using `has_fderiv*`/`has_deriv*` or `fderiv*`/`deriv*`.

For the `fderiv*`/`deriv*` versions we omit the differentiability condition whenever it is possible
due to the fact that `fderiv` and `deriv` are defined to be zero for non-differentiable functions.

## References

* [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points));
* [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem);
* [Tangent cone](https://en.wikipedia.org/wiki/Tangent_cone);

## Tags

local extremum, Fermat's Theorem, Rolle's Theorem
-/

/-- "Positive" tangent cone to `s` at `x`; the only difference from `tangent_cone_at`
is that we require `c n → ∞` instead of `∥c n∥ → ∞`. One can think about `pos_tangent_cone_at`
as `tangent_cone_at nnreal` but we have no theory of normed semifields yet. -/
def pos_tangent_cone_at {E : Type u} [normed_group E] [normed_space ℝ E] (s : set E) (x : E) : set E :=
  set_of
    fun (y : E) =>
      ∃ (c : ℕ → ℝ),
        ∃ (d : ℕ → E),
          filter.eventually (fun (n : ℕ) => x + d n ∈ s) filter.at_top ∧
            filter.tendsto c filter.at_top filter.at_top ∧
              filter.tendsto (fun (n : ℕ) => c n • d n) filter.at_top (nhds y)

theorem pos_tangent_cone_at_mono {E : Type u} [normed_group E] [normed_space ℝ E] {a : E} : monotone fun (s : set E) => pos_tangent_cone_at s a := sorry

theorem mem_pos_tangent_cone_at_of_segment_subset {E : Type u} [normed_group E] [normed_space ℝ E] {s : set E} {x : E} {y : E} (h : segment x y ⊆ s) : y - x ∈ pos_tangent_cone_at s x := sorry

theorem pos_tangent_cone_at_univ {E : Type u} [normed_group E] [normed_space ℝ E] {a : E} : pos_tangent_cone_at set.univ a = set.univ := sorry

/-- If `f` has a local max on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem is_local_max_on.has_fderiv_within_at_nonpos {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} {f' : continuous_linear_map ℝ E ℝ} {s : set E} (h : is_local_max_on f s a) (hf : has_fderiv_within_at f f' s a) {y : E} (hy : y ∈ pos_tangent_cone_at s a) : coe_fn f' y ≤ 0 := sorry

/-- If `f` has a local max on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `f' y ≤ 0`. -/
theorem is_local_max_on.fderiv_within_nonpos {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} {s : set E} (h : is_local_max_on f s a) {y : E} (hy : y ∈ pos_tangent_cone_at s a) : coe_fn (fderiv_within ℝ f s a) y ≤ 0 := sorry

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem is_local_max_on.has_fderiv_within_at_eq_zero {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} {f' : continuous_linear_map ℝ E ℝ} {s : set E} (h : is_local_max_on f s a) (hf : has_fderiv_within_at f f' s a) {y : E} (hy : y ∈ pos_tangent_cone_at s a) (hy' : -y ∈ pos_tangent_cone_at s a) : coe_fn f' y = 0 := sorry

/-- If `f` has a local max on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
theorem is_local_max_on.fderiv_within_eq_zero {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} {s : set E} (h : is_local_max_on f s a) {y : E} (hy : y ∈ pos_tangent_cone_at s a) (hy' : -y ∈ pos_tangent_cone_at s a) : coe_fn (fderiv_within ℝ f s a) y = 0 := sorry

/-- If `f` has a local min on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `0 ≤ f' y`. -/
theorem is_local_min_on.has_fderiv_within_at_nonneg {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} {f' : continuous_linear_map ℝ E ℝ} {s : set E} (h : is_local_min_on f s a) (hf : has_fderiv_within_at f f' s a) {y : E} (hy : y ∈ pos_tangent_cone_at s a) : 0 ≤ coe_fn f' y := sorry

/-- If `f` has a local min on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `0 ≤ f' y`. -/
theorem is_local_min_on.fderiv_within_nonneg {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} {s : set E} (h : is_local_min_on f s a) {y : E} (hy : y ∈ pos_tangent_cone_at s a) : 0 ≤ coe_fn (fderiv_within ℝ f s a) y := sorry

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem is_local_min_on.has_fderiv_within_at_eq_zero {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} {f' : continuous_linear_map ℝ E ℝ} {s : set E} (h : is_local_min_on f s a) (hf : has_fderiv_within_at f f' s a) {y : E} (hy : y ∈ pos_tangent_cone_at s a) (hy' : -y ∈ pos_tangent_cone_at s a) : coe_fn f' y = 0 := sorry

/-- If `f` has a local min on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
theorem is_local_min_on.fderiv_within_eq_zero {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} {s : set E} (h : is_local_min_on f s a) {y : E} (hy : y ∈ pos_tangent_cone_at s a) (hy' : -y ∈ pos_tangent_cone_at s a) : coe_fn (fderiv_within ℝ f s a) y = 0 := sorry

/-- Fermat's Theorem: the derivative of a function at a local minimum equals zero. -/
theorem is_local_min.has_fderiv_at_eq_zero {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} {f' : continuous_linear_map ℝ E ℝ} (h : is_local_min f a) (hf : has_fderiv_at f f' a) : f' = 0 := sorry

/-- Fermat's Theorem: the derivative of a function at a local minimum equals zero. -/
theorem is_local_min.fderiv_eq_zero {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} (h : is_local_min f a) : fderiv ℝ f a = 0 :=
  dite (differentiable_at ℝ f a)
    (fun (hf : differentiable_at ℝ f a) => is_local_min.has_fderiv_at_eq_zero h (differentiable_at.has_fderiv_at hf))
    fun (hf : ¬differentiable_at ℝ f a) => fderiv_zero_of_not_differentiable_at hf

/-- Fermat's Theorem: the derivative of a function at a local maximum equals zero. -/
theorem is_local_max.has_fderiv_at_eq_zero {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} {f' : continuous_linear_map ℝ E ℝ} (h : is_local_max f a) (hf : has_fderiv_at f f' a) : f' = 0 :=
  iff.mp neg_eq_zero (is_local_min.has_fderiv_at_eq_zero (is_local_max.neg h) (has_fderiv_at.neg hf))

/-- Fermat's Theorem: the derivative of a function at a local maximum equals zero. -/
theorem is_local_max.fderiv_eq_zero {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} (h : is_local_max f a) : fderiv ℝ f a = 0 :=
  dite (differentiable_at ℝ f a)
    (fun (hf : differentiable_at ℝ f a) => is_local_max.has_fderiv_at_eq_zero h (differentiable_at.has_fderiv_at hf))
    fun (hf : ¬differentiable_at ℝ f a) => fderiv_zero_of_not_differentiable_at hf

/-- Fermat's Theorem: the derivative of a function at a local extremum equals zero. -/
theorem is_local_extr.has_fderiv_at_eq_zero {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} {f' : continuous_linear_map ℝ E ℝ} (h : is_local_extr f a) : has_fderiv_at f f' a → f' = 0 :=
  is_local_extr.elim h is_local_min.has_fderiv_at_eq_zero is_local_max.has_fderiv_at_eq_zero

/-- Fermat's Theorem: the derivative of a function at a local extremum equals zero. -/
theorem is_local_extr.fderiv_eq_zero {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E} (h : is_local_extr f a) : fderiv ℝ f a = 0 :=
  is_local_extr.elim h is_local_min.fderiv_eq_zero is_local_max.fderiv_eq_zero

/-- Fermat's Theorem: the derivative of a function at a local minimum equals zero. -/
theorem is_local_min.has_deriv_at_eq_zero {f : ℝ → ℝ} {f' : ℝ} {a : ℝ} (h : is_local_min f a) (hf : has_deriv_at f f' a) : f' = 0 := sorry

/-- Fermat's Theorem: the derivative of a function at a local minimum equals zero. -/
theorem is_local_min.deriv_eq_zero {f : ℝ → ℝ} {a : ℝ} (h : is_local_min f a) : deriv f a = 0 :=
  dite (differentiable_at ℝ f a)
    (fun (hf : differentiable_at ℝ f a) => is_local_min.has_deriv_at_eq_zero h (differentiable_at.has_deriv_at hf))
    fun (hf : ¬differentiable_at ℝ f a) => deriv_zero_of_not_differentiable_at hf

/-- Fermat's Theorem: the derivative of a function at a local maximum equals zero. -/
theorem is_local_max.has_deriv_at_eq_zero {f : ℝ → ℝ} {f' : ℝ} {a : ℝ} (h : is_local_max f a) (hf : has_deriv_at f f' a) : f' = 0 :=
  iff.mp neg_eq_zero (is_local_min.has_deriv_at_eq_zero (is_local_max.neg h) (has_deriv_at.neg hf))

/-- Fermat's Theorem: the derivative of a function at a local maximum equals zero. -/
theorem is_local_max.deriv_eq_zero {f : ℝ → ℝ} {a : ℝ} (h : is_local_max f a) : deriv f a = 0 :=
  dite (differentiable_at ℝ f a)
    (fun (hf : differentiable_at ℝ f a) => is_local_max.has_deriv_at_eq_zero h (differentiable_at.has_deriv_at hf))
    fun (hf : ¬differentiable_at ℝ f a) => deriv_zero_of_not_differentiable_at hf

/-- Fermat's Theorem: the derivative of a function at a local extremum equals zero. -/
theorem is_local_extr.has_deriv_at_eq_zero {f : ℝ → ℝ} {f' : ℝ} {a : ℝ} (h : is_local_extr f a) : has_deriv_at f f' a → f' = 0 :=
  is_local_extr.elim h is_local_min.has_deriv_at_eq_zero is_local_max.has_deriv_at_eq_zero

/-- Fermat's Theorem: the derivative of a function at a local extremum equals zero. -/
theorem is_local_extr.deriv_eq_zero {f : ℝ → ℝ} {a : ℝ} (h : is_local_extr f a) : deriv f a = 0 :=
  is_local_extr.elim h is_local_min.deriv_eq_zero is_local_max.deriv_eq_zero

/-- A continuous function on a closed interval with `f a = f b` takes either its maximum
or its minimum value at a point in the interior of the interval. -/
theorem exists_Ioo_extr_on_Icc (f : ℝ → ℝ) {a : ℝ} {b : ℝ} (hab : a < b) (hfc : continuous_on f (set.Icc a b)) (hfI : f a = f b) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), is_extr_on f (set.Icc a b) c := sorry

/-- A continuous function on a closed interval with `f a = f b` has a local extremum at some
point of the corresponding open interval. -/
theorem exists_local_extr_Ioo (f : ℝ → ℝ) {a : ℝ} {b : ℝ} (hab : a < b) (hfc : continuous_on f (set.Icc a b)) (hfI : f a = f b) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), is_local_extr f c := sorry

/-- Rolle's Theorem `has_deriv_at` version -/
theorem exists_has_deriv_at_eq_zero (f : ℝ → ℝ) (f' : ℝ → ℝ) {a : ℝ} {b : ℝ} (hab : a < b) (hfc : continuous_on f (set.Icc a b)) (hfI : f a = f b) (hff' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at f (f' x) x) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), f' c = 0 := sorry

/-- Rolle's Theorem `deriv` version -/
theorem exists_deriv_eq_zero (f : ℝ → ℝ) {a : ℝ} {b : ℝ} (hab : a < b) (hfc : continuous_on f (set.Icc a b)) (hfI : f a = f b) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), deriv f c = 0 := sorry

theorem exists_has_deriv_at_eq_zero' {f : ℝ → ℝ} {f' : ℝ → ℝ} {a : ℝ} {b : ℝ} (hab : a < b) {l : ℝ} (hfa : filter.tendsto f (nhds_within a (set.Ioi a)) (nhds l)) (hfb : filter.tendsto f (nhds_within b (set.Iio b)) (nhds l)) (hff' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at f (f' x) x) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), f' c = 0 := sorry

theorem exists_deriv_eq_zero' {f : ℝ → ℝ} {a : ℝ} {b : ℝ} (hab : a < b) {l : ℝ} (hfa : filter.tendsto f (nhds_within a (set.Ioi a)) (nhds l)) (hfb : filter.tendsto f (nhds_within b (set.Iio b)) (nhds l)) : ∃ (c : ℝ), ∃ (H : c ∈ set.Ioo a b), deriv f c = 0 := sorry

