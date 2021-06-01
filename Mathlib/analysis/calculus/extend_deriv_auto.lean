/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.calculus.mean_value
import Mathlib.tactic.monotonicity.default
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Extending differentiability to the boundary

We investigate how differentiable functions inside a set extend to differentiable functions
on the boundary. For this, it suffices that the function and its derivative admit limits there.
A general version of this statement is given in `has_fderiv_at_boundary_of_tendsto_fderiv`.

One-dimensional versions, in which one wants to obtain differentiability at the left endpoint or
the right endpoint of an interval, are given in
`has_deriv_at_interval_left_endpoint_of_tendsto_deriv` and
`has_deriv_at_interval_right_endpoint_of_tendsto_deriv`. These versions are formulated in terms
of the one-dimensional derivative `deriv ℝ f`.
-/

/-- If a function `f` is differentiable in a convex open set and continuous on its closure, and its
derivative converges to a limit `f'` at a point on the boundary, then `f` is differentiable there
with derivative `f'`. -/
theorem has_fderiv_at_boundary_of_tendsto_fderiv {E : Type u_1} [normed_group E] [normed_space ℝ E]
    {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F} {s : set E} {x : E}
    {f' : continuous_linear_map ℝ E F} (f_diff : differentiable_on ℝ f s) (s_conv : convex s)
    (s_open : is_open s) (f_cont : ∀ (y : E), y ∈ closure s → continuous_within_at f s y)
    (h : filter.tendsto (fun (y : E) => fderiv ℝ f y) (nhds_within x s) (nhds f')) :
    has_fderiv_within_at f f' (closure s) x :=
  sorry

/-- If a function is differentiable on the right of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the right at `a`. -/
theorem has_deriv_at_interval_left_endpoint_of_tendsto_deriv {E : Type u_1} [normed_group E]
    [normed_space ℝ E] {s : set ℝ} {e : E} {a : ℝ} {f : ℝ → E} (f_diff : differentiable_on ℝ f s)
    (f_lim : continuous_within_at f s a) (hs : s ∈ nhds_within a (set.Ioi a))
    (f_lim' : filter.tendsto (fun (x : ℝ) => deriv f x) (nhds_within a (set.Ioi a)) (nhds e)) :
    has_deriv_within_at f e (set.Ici a) a :=
  sorry

/-- If a function is differentiable on the left of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the left at `a`. -/
theorem has_deriv_at_interval_right_endpoint_of_tendsto_deriv {E : Type u_1} [normed_group E]
    [normed_space ℝ E] {s : set ℝ} {e : E} {a : ℝ} {f : ℝ → E} (f_diff : differentiable_on ℝ f s)
    (f_lim : continuous_within_at f s a) (hs : s ∈ nhds_within a (set.Iio a))
    (f_lim' : filter.tendsto (fun (x : ℝ) => deriv f x) (nhds_within a (set.Iio a)) (nhds e)) :
    has_deriv_within_at f e (set.Iic a) a :=
  sorry

/-- If a real function `f` has a derivative `g` everywhere but at a point, and `f` and `g` are
continuous at this point, then `g` is also the derivative of `f` at this point. -/
theorem has_deriv_at_of_has_deriv_at_of_ne {E : Type u_1} [normed_group E] [normed_space ℝ E]
    {f : ℝ → E} {g : ℝ → E} {x : ℝ} (f_diff : ∀ (y : ℝ), y ≠ x → has_deriv_at f (g y) y)
    (hf : continuous_at f x) (hg : continuous_at g x) : has_deriv_at f (g x) x :=
  sorry

end Mathlib