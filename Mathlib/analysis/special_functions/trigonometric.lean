/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.special_functions.exp_log
import Mathlib.data.set.intervals.infinite
import Mathlib.algebra.quadratic_discriminant
import Mathlib.ring_theory.polynomial.chebyshev.defs
import Mathlib.analysis.calculus.times_cont_diff
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Trigonometric functions

## Main definitions

This file contains the following definitions:
* π, arcsin, arccos, arctan
* argument of a complex number
* logarithm on complex numbers

## Main statements

Many basic inequalities on trigonometric functions are established.

The continuity and differentiability of the usual trigonometric functions are proved, and their
derivatives are computed.

* `polynomial.chebyshev₁_complex_cos`: the `n`-th Chebyshev polynomial evaluates on `complex.cos θ`
  to the value `n * complex.cos θ`.

## Tags

log, sin, cos, tan, arcsin, arccos, arctan, angle, argument
-/

namespace complex


/-- The complex sine function is everywhere differentiable, with the derivative `cos x`. -/
theorem has_deriv_at_sin (x : ℂ) : has_deriv_at sin (cos x) x := sorry

theorem times_cont_diff_sin {n : with_top ℕ} : times_cont_diff ℂ n sin := sorry

theorem differentiable_sin : differentiable ℂ sin :=
  fun (x : ℂ) => has_deriv_at.differentiable_at (has_deriv_at_sin x)

theorem differentiable_at_sin {x : ℂ} : differentiable_at ℂ sin x :=
  differentiable_sin x

@[simp] theorem deriv_sin : deriv sin = cos :=
  funext fun (x : ℂ) => has_deriv_at.deriv (has_deriv_at_sin x)

theorem continuous_sin : continuous sin :=
  differentiable.continuous differentiable_sin

theorem continuous_on_sin {s : set ℂ} : continuous_on sin s :=
  continuous.continuous_on continuous_sin

theorem measurable_sin : measurable sin :=
  continuous.measurable continuous_sin

/-- The complex cosine function is everywhere differentiable, with the derivative `-sin x`. -/
theorem has_deriv_at_cos (x : ℂ) : has_deriv_at cos (-sin x) x := sorry

theorem times_cont_diff_cos {n : with_top ℕ} : times_cont_diff ℂ n cos :=
  times_cont_diff.div_const
    (times_cont_diff.add (times_cont_diff.cexp (times_cont_diff.mul times_cont_diff_id times_cont_diff_const))
      (times_cont_diff.cexp (times_cont_diff.mul times_cont_diff_neg times_cont_diff_const)))

theorem differentiable_cos : differentiable ℂ cos :=
  fun (x : ℂ) => has_deriv_at.differentiable_at (has_deriv_at_cos x)

theorem differentiable_at_cos {x : ℂ} : differentiable_at ℂ cos x :=
  differentiable_cos x

theorem deriv_cos {x : ℂ} : deriv cos x = -sin x :=
  has_deriv_at.deriv (has_deriv_at_cos x)

@[simp] theorem deriv_cos' : deriv cos = fun (x : ℂ) => -sin x :=
  funext fun (x : ℂ) => deriv_cos

theorem continuous_cos : continuous cos :=
  differentiable.continuous differentiable_cos

theorem continuous_on_cos {s : set ℂ} : continuous_on cos s :=
  continuous.continuous_on continuous_cos

theorem measurable_cos : measurable cos :=
  continuous.measurable continuous_cos

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative
`cosh x`. -/
theorem has_deriv_at_sinh (x : ℂ) : has_deriv_at sinh (cosh x) x := sorry

theorem times_cont_diff_sinh {n : with_top ℕ} : times_cont_diff ℂ n sinh :=
  times_cont_diff.div_const (times_cont_diff.sub times_cont_diff_exp (times_cont_diff.cexp times_cont_diff_neg))

theorem differentiable_sinh : differentiable ℂ sinh :=
  fun (x : ℂ) => has_deriv_at.differentiable_at (has_deriv_at_sinh x)

theorem differentiable_at_sinh {x : ℂ} : differentiable_at ℂ sinh x :=
  differentiable_sinh x

@[simp] theorem deriv_sinh : deriv sinh = cosh :=
  funext fun (x : ℂ) => has_deriv_at.deriv (has_deriv_at_sinh x)

theorem continuous_sinh : continuous sinh :=
  differentiable.continuous differentiable_sinh

theorem measurable_sinh : measurable sinh :=
  continuous.measurable continuous_sinh

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative
`sinh x`. -/
theorem has_deriv_at_cosh (x : ℂ) : has_deriv_at cosh (sinh x) x := sorry

theorem times_cont_diff_cosh {n : with_top ℕ} : times_cont_diff ℂ n cosh :=
  times_cont_diff.div_const (times_cont_diff.add times_cont_diff_exp (times_cont_diff.cexp times_cont_diff_neg))

theorem differentiable_cosh : differentiable ℂ cosh :=
  fun (x : ℂ) => has_deriv_at.differentiable_at (has_deriv_at_cosh x)

theorem differentiable_at_cosh {x : ℂ} : differentiable_at ℂ cos x :=
  differentiable_cos x

@[simp] theorem deriv_cosh : deriv cosh = sinh :=
  funext fun (x : ℂ) => has_deriv_at.deriv (has_deriv_at_cosh x)

theorem continuous_cosh : continuous cosh :=
  differentiable.continuous differentiable_cosh

theorem measurable_cosh : measurable cosh :=
  continuous.measurable continuous_cosh

end complex


/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : ℂ → ℂ` -/

/-! #### `complex.cos` -/

theorem measurable.ccos {α : Type u_1} [measurable_space α] {f : α → ℂ} (hf : measurable f) : measurable fun (x : α) => complex.cos (f x) :=
  measurable.comp complex.measurable_cos hf

theorem has_deriv_at.ccos {f : ℂ → ℂ} {f' : ℂ} {x : ℂ} (hf : has_deriv_at f f' x) : has_deriv_at (fun (x : ℂ) => complex.cos (f x)) (-complex.sin (f x) * f') x :=
  has_deriv_at.comp x (complex.has_deriv_at_cos (f x)) hf

theorem has_deriv_within_at.ccos {f : ℂ → ℂ} {f' : ℂ} {x : ℂ} {s : set ℂ} (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (x : ℂ) => complex.cos (f x)) (-complex.sin (f x) * f') s x :=
  has_deriv_at.comp_has_deriv_within_at x (complex.has_deriv_at_cos (f x)) hf

theorem deriv_within_ccos {f : ℂ → ℂ} {x : ℂ} {s : set ℂ} (hf : differentiable_within_at ℂ f s x) (hxs : unique_diff_within_at ℂ s x) : deriv_within (fun (x : ℂ) => complex.cos (f x)) s x = -complex.sin (f x) * deriv_within f s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.ccos (differentiable_within_at.has_deriv_within_at hf)) hxs

@[simp] theorem deriv_ccos {f : ℂ → ℂ} {x : ℂ} (hc : differentiable_at ℂ f x) : deriv (fun (x : ℂ) => complex.cos (f x)) x = -complex.sin (f x) * deriv f x :=
  has_deriv_at.deriv (has_deriv_at.ccos (differentiable_at.has_deriv_at hc))

/-! #### `complex.sin` -/

theorem measurable.csin {α : Type u_1} [measurable_space α] {f : α → ℂ} (hf : measurable f) : measurable fun (x : α) => complex.sin (f x) :=
  measurable.comp complex.measurable_sin hf

theorem has_deriv_at.csin {f : ℂ → ℂ} {f' : ℂ} {x : ℂ} (hf : has_deriv_at f f' x) : has_deriv_at (fun (x : ℂ) => complex.sin (f x)) (complex.cos (f x) * f') x :=
  has_deriv_at.comp x (complex.has_deriv_at_sin (f x)) hf

theorem has_deriv_within_at.csin {f : ℂ → ℂ} {f' : ℂ} {x : ℂ} {s : set ℂ} (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (x : ℂ) => complex.sin (f x)) (complex.cos (f x) * f') s x :=
  has_deriv_at.comp_has_deriv_within_at x (complex.has_deriv_at_sin (f x)) hf

theorem deriv_within_csin {f : ℂ → ℂ} {x : ℂ} {s : set ℂ} (hf : differentiable_within_at ℂ f s x) (hxs : unique_diff_within_at ℂ s x) : deriv_within (fun (x : ℂ) => complex.sin (f x)) s x = complex.cos (f x) * deriv_within f s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.csin (differentiable_within_at.has_deriv_within_at hf)) hxs

@[simp] theorem deriv_csin {f : ℂ → ℂ} {x : ℂ} (hc : differentiable_at ℂ f x) : deriv (fun (x : ℂ) => complex.sin (f x)) x = complex.cos (f x) * deriv f x :=
  has_deriv_at.deriv (has_deriv_at.csin (differentiable_at.has_deriv_at hc))

/-! #### `complex.cosh` -/

theorem measurable.ccosh {α : Type u_1} [measurable_space α] {f : α → ℂ} (hf : measurable f) : measurable fun (x : α) => complex.cosh (f x) :=
  measurable.comp complex.measurable_cosh hf

theorem has_deriv_at.ccosh {f : ℂ → ℂ} {f' : ℂ} {x : ℂ} (hf : has_deriv_at f f' x) : has_deriv_at (fun (x : ℂ) => complex.cosh (f x)) (complex.sinh (f x) * f') x :=
  has_deriv_at.comp x (complex.has_deriv_at_cosh (f x)) hf

theorem has_deriv_within_at.ccosh {f : ℂ → ℂ} {f' : ℂ} {x : ℂ} {s : set ℂ} (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (x : ℂ) => complex.cosh (f x)) (complex.sinh (f x) * f') s x :=
  has_deriv_at.comp_has_deriv_within_at x (complex.has_deriv_at_cosh (f x)) hf

theorem deriv_within_ccosh {f : ℂ → ℂ} {x : ℂ} {s : set ℂ} (hf : differentiable_within_at ℂ f s x) (hxs : unique_diff_within_at ℂ s x) : deriv_within (fun (x : ℂ) => complex.cosh (f x)) s x = complex.sinh (f x) * deriv_within f s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.ccosh (differentiable_within_at.has_deriv_within_at hf)) hxs

@[simp] theorem deriv_ccosh {f : ℂ → ℂ} {x : ℂ} (hc : differentiable_at ℂ f x) : deriv (fun (x : ℂ) => complex.cosh (f x)) x = complex.sinh (f x) * deriv f x :=
  has_deriv_at.deriv (has_deriv_at.ccosh (differentiable_at.has_deriv_at hc))

/-! #### `complex.sinh` -/

theorem measurable.csinh {α : Type u_1} [measurable_space α] {f : α → ℂ} (hf : measurable f) : measurable fun (x : α) => complex.sinh (f x) :=
  measurable.comp complex.measurable_sinh hf

theorem has_deriv_at.csinh {f : ℂ → ℂ} {f' : ℂ} {x : ℂ} (hf : has_deriv_at f f' x) : has_deriv_at (fun (x : ℂ) => complex.sinh (f x)) (complex.cosh (f x) * f') x :=
  has_deriv_at.comp x (complex.has_deriv_at_sinh (f x)) hf

theorem has_deriv_within_at.csinh {f : ℂ → ℂ} {f' : ℂ} {x : ℂ} {s : set ℂ} (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (x : ℂ) => complex.sinh (f x)) (complex.cosh (f x) * f') s x :=
  has_deriv_at.comp_has_deriv_within_at x (complex.has_deriv_at_sinh (f x)) hf

theorem deriv_within_csinh {f : ℂ → ℂ} {x : ℂ} {s : set ℂ} (hf : differentiable_within_at ℂ f s x) (hxs : unique_diff_within_at ℂ s x) : deriv_within (fun (x : ℂ) => complex.sinh (f x)) s x = complex.cosh (f x) * deriv_within f s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.csinh (differentiable_within_at.has_deriv_within_at hf)) hxs

@[simp] theorem deriv_csinh {f : ℂ → ℂ} {x : ℂ} (hc : differentiable_at ℂ f x) : deriv (fun (x : ℂ) => complex.sinh (f x)) x = complex.cosh (f x) * deriv f x :=
  has_deriv_at.deriv (has_deriv_at.csinh (differentiable_at.has_deriv_at hc))

/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : E → ℂ` -/

/-! #### `complex.cos` -/

theorem has_fderiv_at.ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : continuous_linear_map ℂ E ℂ} {x : E} (hf : has_fderiv_at f f' x) : has_fderiv_at (fun (x : E) => complex.cos (f x)) (-complex.sin (f x) • f') x :=
  has_deriv_at.comp_has_fderiv_at x (complex.has_deriv_at_cos (f x)) hf

theorem has_fderiv_within_at.ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : continuous_linear_map ℂ E ℂ} {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) : has_fderiv_within_at (fun (x : E) => complex.cos (f x)) (-complex.sin (f x) • f') s x :=
  has_deriv_at.comp_has_fderiv_within_at x (complex.has_deriv_at_cos (f x)) hf

theorem differentiable_within_at.ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} (hf : differentiable_within_at ℂ f s x) : differentiable_within_at ℂ (fun (x : E) => complex.cos (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.ccos (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} (hc : differentiable_at ℂ f x) : differentiable_at ℂ (fun (x : E) => complex.cos (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.ccos (differentiable_at.has_fderiv_at hc))

theorem differentiable_on.ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {s : set E} (hc : differentiable_on ℂ f s) : differentiable_on ℂ (fun (x : E) => complex.cos (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.ccos (hc x h)

@[simp] theorem differentiable.ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} (hc : differentiable ℂ f) : differentiable ℂ fun (x : E) => complex.cos (f x) :=
  fun (x : E) => differentiable_at.ccos (hc x)

theorem fderiv_within_ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} (hf : differentiable_within_at ℂ f s x) (hxs : unique_diff_within_at ℂ s x) : fderiv_within ℂ (fun (x : E) => complex.cos (f x)) s x = -complex.sin (f x) • fderiv_within ℂ f s x :=
  has_fderiv_within_at.fderiv_within (has_fderiv_within_at.ccos (differentiable_within_at.has_fderiv_within_at hf)) hxs

@[simp] theorem fderiv_ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} (hc : differentiable_at ℂ f x) : fderiv ℂ (fun (x : E) => complex.cos (f x)) x = -complex.sin (f x) • fderiv ℂ f x :=
  has_fderiv_at.fderiv (has_fderiv_at.ccos (differentiable_at.has_fderiv_at hc))

theorem times_cont_diff.ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {n : with_top ℕ} (h : times_cont_diff ℂ n f) : times_cont_diff ℂ n fun (x : E) => complex.cos (f x) :=
  times_cont_diff.comp complex.times_cont_diff_cos h

theorem times_cont_diff_at.ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {n : with_top ℕ} (hf : times_cont_diff_at ℂ n f x) : times_cont_diff_at ℂ n (fun (x : E) => complex.cos (f x)) x :=
  times_cont_diff_at.comp x (times_cont_diff.times_cont_diff_at complex.times_cont_diff_cos) hf

theorem times_cont_diff_on.ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_on ℂ n f s) : times_cont_diff_on ℂ n (fun (x : E) => complex.cos (f x)) s :=
  times_cont_diff.comp_times_cont_diff_on complex.times_cont_diff_cos hf

theorem times_cont_diff_within_at.ccos {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_within_at ℂ n f s x) : times_cont_diff_within_at ℂ n (fun (x : E) => complex.cos (f x)) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x (times_cont_diff.times_cont_diff_at complex.times_cont_diff_cos) hf

/-! #### `complex.sin` -/

theorem has_fderiv_at.csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : continuous_linear_map ℂ E ℂ} {x : E} (hf : has_fderiv_at f f' x) : has_fderiv_at (fun (x : E) => complex.sin (f x)) (complex.cos (f x) • f') x :=
  has_deriv_at.comp_has_fderiv_at x (complex.has_deriv_at_sin (f x)) hf

theorem has_fderiv_within_at.csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : continuous_linear_map ℂ E ℂ} {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) : has_fderiv_within_at (fun (x : E) => complex.sin (f x)) (complex.cos (f x) • f') s x :=
  has_deriv_at.comp_has_fderiv_within_at x (complex.has_deriv_at_sin (f x)) hf

theorem differentiable_within_at.csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} (hf : differentiable_within_at ℂ f s x) : differentiable_within_at ℂ (fun (x : E) => complex.sin (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.csin (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} (hc : differentiable_at ℂ f x) : differentiable_at ℂ (fun (x : E) => complex.sin (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.csin (differentiable_at.has_fderiv_at hc))

theorem differentiable_on.csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {s : set E} (hc : differentiable_on ℂ f s) : differentiable_on ℂ (fun (x : E) => complex.sin (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.csin (hc x h)

@[simp] theorem differentiable.csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} (hc : differentiable ℂ f) : differentiable ℂ fun (x : E) => complex.sin (f x) :=
  fun (x : E) => differentiable_at.csin (hc x)

theorem fderiv_within_csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} (hf : differentiable_within_at ℂ f s x) (hxs : unique_diff_within_at ℂ s x) : fderiv_within ℂ (fun (x : E) => complex.sin (f x)) s x = complex.cos (f x) • fderiv_within ℂ f s x :=
  has_fderiv_within_at.fderiv_within (has_fderiv_within_at.csin (differentiable_within_at.has_fderiv_within_at hf)) hxs

@[simp] theorem fderiv_csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} (hc : differentiable_at ℂ f x) : fderiv ℂ (fun (x : E) => complex.sin (f x)) x = complex.cos (f x) • fderiv ℂ f x :=
  has_fderiv_at.fderiv (has_fderiv_at.csin (differentiable_at.has_fderiv_at hc))

theorem times_cont_diff.csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {n : with_top ℕ} (h : times_cont_diff ℂ n f) : times_cont_diff ℂ n fun (x : E) => complex.sin (f x) :=
  times_cont_diff.comp complex.times_cont_diff_sin h

theorem times_cont_diff_at.csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {n : with_top ℕ} (hf : times_cont_diff_at ℂ n f x) : times_cont_diff_at ℂ n (fun (x : E) => complex.sin (f x)) x :=
  times_cont_diff_at.comp x (times_cont_diff.times_cont_diff_at complex.times_cont_diff_sin) hf

theorem times_cont_diff_on.csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_on ℂ n f s) : times_cont_diff_on ℂ n (fun (x : E) => complex.sin (f x)) s :=
  times_cont_diff.comp_times_cont_diff_on complex.times_cont_diff_sin hf

theorem times_cont_diff_within_at.csin {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_within_at ℂ n f s x) : times_cont_diff_within_at ℂ n (fun (x : E) => complex.sin (f x)) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x (times_cont_diff.times_cont_diff_at complex.times_cont_diff_sin) hf

/-! #### `complex.cosh` -/

theorem has_fderiv_at.ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : continuous_linear_map ℂ E ℂ} {x : E} (hf : has_fderiv_at f f' x) : has_fderiv_at (fun (x : E) => complex.cosh (f x)) (complex.sinh (f x) • f') x :=
  has_deriv_at.comp_has_fderiv_at x (complex.has_deriv_at_cosh (f x)) hf

theorem has_fderiv_within_at.ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : continuous_linear_map ℂ E ℂ} {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) : has_fderiv_within_at (fun (x : E) => complex.cosh (f x)) (complex.sinh (f x) • f') s x :=
  has_deriv_at.comp_has_fderiv_within_at x (complex.has_deriv_at_cosh (f x)) hf

theorem differentiable_within_at.ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} (hf : differentiable_within_at ℂ f s x) : differentiable_within_at ℂ (fun (x : E) => complex.cosh (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.ccosh (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} (hc : differentiable_at ℂ f x) : differentiable_at ℂ (fun (x : E) => complex.cosh (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.ccosh (differentiable_at.has_fderiv_at hc))

theorem differentiable_on.ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {s : set E} (hc : differentiable_on ℂ f s) : differentiable_on ℂ (fun (x : E) => complex.cosh (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.ccosh (hc x h)

@[simp] theorem differentiable.ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} (hc : differentiable ℂ f) : differentiable ℂ fun (x : E) => complex.cosh (f x) :=
  fun (x : E) => differentiable_at.ccosh (hc x)

theorem fderiv_within_ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} (hf : differentiable_within_at ℂ f s x) (hxs : unique_diff_within_at ℂ s x) : fderiv_within ℂ (fun (x : E) => complex.cosh (f x)) s x = complex.sinh (f x) • fderiv_within ℂ f s x :=
  has_fderiv_within_at.fderiv_within (has_fderiv_within_at.ccosh (differentiable_within_at.has_fderiv_within_at hf)) hxs

@[simp] theorem fderiv_ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} (hc : differentiable_at ℂ f x) : fderiv ℂ (fun (x : E) => complex.cosh (f x)) x = complex.sinh (f x) • fderiv ℂ f x :=
  has_fderiv_at.fderiv (has_fderiv_at.ccosh (differentiable_at.has_fderiv_at hc))

theorem times_cont_diff.ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {n : with_top ℕ} (h : times_cont_diff ℂ n f) : times_cont_diff ℂ n fun (x : E) => complex.cosh (f x) :=
  times_cont_diff.comp complex.times_cont_diff_cosh h

theorem times_cont_diff_at.ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {n : with_top ℕ} (hf : times_cont_diff_at ℂ n f x) : times_cont_diff_at ℂ n (fun (x : E) => complex.cosh (f x)) x :=
  times_cont_diff_at.comp x (times_cont_diff.times_cont_diff_at complex.times_cont_diff_cosh) hf

theorem times_cont_diff_on.ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_on ℂ n f s) : times_cont_diff_on ℂ n (fun (x : E) => complex.cosh (f x)) s :=
  times_cont_diff.comp_times_cont_diff_on complex.times_cont_diff_cosh hf

theorem times_cont_diff_within_at.ccosh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_within_at ℂ n f s x) : times_cont_diff_within_at ℂ n (fun (x : E) => complex.cosh (f x)) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x (times_cont_diff.times_cont_diff_at complex.times_cont_diff_cosh) hf

/-! #### `complex.sinh` -/

theorem has_fderiv_at.csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : continuous_linear_map ℂ E ℂ} {x : E} (hf : has_fderiv_at f f' x) : has_fderiv_at (fun (x : E) => complex.sinh (f x)) (complex.cosh (f x) • f') x :=
  has_deriv_at.comp_has_fderiv_at x (complex.has_deriv_at_sinh (f x)) hf

theorem has_fderiv_within_at.csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : continuous_linear_map ℂ E ℂ} {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) : has_fderiv_within_at (fun (x : E) => complex.sinh (f x)) (complex.cosh (f x) • f') s x :=
  has_deriv_at.comp_has_fderiv_within_at x (complex.has_deriv_at_sinh (f x)) hf

theorem differentiable_within_at.csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} (hf : differentiable_within_at ℂ f s x) : differentiable_within_at ℂ (fun (x : E) => complex.sinh (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.csinh (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} (hc : differentiable_at ℂ f x) : differentiable_at ℂ (fun (x : E) => complex.sinh (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.csinh (differentiable_at.has_fderiv_at hc))

theorem differentiable_on.csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {s : set E} (hc : differentiable_on ℂ f s) : differentiable_on ℂ (fun (x : E) => complex.sinh (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.csinh (hc x h)

@[simp] theorem differentiable.csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} (hc : differentiable ℂ f) : differentiable ℂ fun (x : E) => complex.sinh (f x) :=
  fun (x : E) => differentiable_at.csinh (hc x)

theorem fderiv_within_csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} (hf : differentiable_within_at ℂ f s x) (hxs : unique_diff_within_at ℂ s x) : fderiv_within ℂ (fun (x : E) => complex.sinh (f x)) s x = complex.cosh (f x) • fderiv_within ℂ f s x :=
  has_fderiv_within_at.fderiv_within (has_fderiv_within_at.csinh (differentiable_within_at.has_fderiv_within_at hf)) hxs

@[simp] theorem fderiv_csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} (hc : differentiable_at ℂ f x) : fderiv ℂ (fun (x : E) => complex.sinh (f x)) x = complex.cosh (f x) • fderiv ℂ f x :=
  has_fderiv_at.fderiv (has_fderiv_at.csinh (differentiable_at.has_fderiv_at hc))

theorem times_cont_diff.csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {n : with_top ℕ} (h : times_cont_diff ℂ n f) : times_cont_diff ℂ n fun (x : E) => complex.sinh (f x) :=
  times_cont_diff.comp complex.times_cont_diff_sinh h

theorem times_cont_diff_at.csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {n : with_top ℕ} (hf : times_cont_diff_at ℂ n f x) : times_cont_diff_at ℂ n (fun (x : E) => complex.sinh (f x)) x :=
  times_cont_diff_at.comp x (times_cont_diff.times_cont_diff_at complex.times_cont_diff_sinh) hf

theorem times_cont_diff_on.csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_on ℂ n f s) : times_cont_diff_on ℂ n (fun (x : E) => complex.sinh (f x)) s :=
  times_cont_diff.comp_times_cont_diff_on complex.times_cont_diff_sinh hf

theorem times_cont_diff_within_at.csinh {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {x : E} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_within_at ℂ n f s x) : times_cont_diff_within_at ℂ n (fun (x : E) => complex.sinh (f x)) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x (times_cont_diff.times_cont_diff_at complex.times_cont_diff_sinh) hf

namespace real


theorem has_deriv_at_sin (x : ℝ) : has_deriv_at sin (cos x) x :=
  has_deriv_at.real_of_complex (complex.has_deriv_at_sin ↑x)

theorem times_cont_diff_sin {n : with_top ℕ} : times_cont_diff ℝ n sin :=
  times_cont_diff.real_of_complex complex.times_cont_diff_sin

theorem differentiable_sin : differentiable ℝ sin :=
  fun (x : ℝ) => has_deriv_at.differentiable_at (has_deriv_at_sin x)

theorem differentiable_at_sin {x : ℝ} : differentiable_at ℝ sin x :=
  differentiable_sin x

@[simp] theorem deriv_sin : deriv sin = cos :=
  funext fun (x : ℝ) => has_deriv_at.deriv (has_deriv_at_sin x)

theorem continuous_sin : continuous sin :=
  differentiable.continuous differentiable_sin

theorem measurable_sin : measurable sin :=
  continuous.measurable continuous_sin

theorem has_deriv_at_cos (x : ℝ) : has_deriv_at cos (-sin x) x :=
  has_deriv_at.real_of_complex (complex.has_deriv_at_cos ↑x)

theorem times_cont_diff_cos {n : with_top ℕ} : times_cont_diff ℝ n cos :=
  times_cont_diff.real_of_complex complex.times_cont_diff_cos

theorem differentiable_cos : differentiable ℝ cos :=
  fun (x : ℝ) => has_deriv_at.differentiable_at (has_deriv_at_cos x)

theorem differentiable_at_cos {x : ℝ} : differentiable_at ℝ cos x :=
  differentiable_cos x

theorem deriv_cos {x : ℝ} : deriv cos x = -sin x :=
  has_deriv_at.deriv (has_deriv_at_cos x)

@[simp] theorem deriv_cos' : deriv cos = fun (x : ℝ) => -sin x :=
  funext fun (_x : ℝ) => deriv_cos

theorem continuous_cos : continuous cos :=
  differentiable.continuous differentiable_cos

theorem continuous_on_cos {s : set ℝ} : continuous_on cos s :=
  continuous.continuous_on continuous_cos

theorem measurable_cos : measurable cos :=
  continuous.measurable continuous_cos

theorem has_deriv_at_sinh (x : ℝ) : has_deriv_at sinh (cosh x) x :=
  has_deriv_at.real_of_complex (complex.has_deriv_at_sinh ↑x)

theorem times_cont_diff_sinh {n : with_top ℕ} : times_cont_diff ℝ n sinh :=
  times_cont_diff.real_of_complex complex.times_cont_diff_sinh

theorem differentiable_sinh : differentiable ℝ sinh :=
  fun (x : ℝ) => has_deriv_at.differentiable_at (has_deriv_at_sinh x)

theorem differentiable_at_sinh {x : ℝ} : differentiable_at ℝ sinh x :=
  differentiable_sinh x

@[simp] theorem deriv_sinh : deriv sinh = cosh :=
  funext fun (x : ℝ) => has_deriv_at.deriv (has_deriv_at_sinh x)

theorem continuous_sinh : continuous sinh :=
  differentiable.continuous differentiable_sinh

theorem measurable_sinh : measurable sinh :=
  continuous.measurable continuous_sinh

theorem has_deriv_at_cosh (x : ℝ) : has_deriv_at cosh (sinh x) x :=
  has_deriv_at.real_of_complex (complex.has_deriv_at_cosh ↑x)

theorem times_cont_diff_cosh {n : with_top ℕ} : times_cont_diff ℝ n cosh :=
  times_cont_diff.real_of_complex complex.times_cont_diff_cosh

theorem differentiable_cosh : differentiable ℝ cosh :=
  fun (x : ℝ) => has_deriv_at.differentiable_at (has_deriv_at_cosh x)

theorem differentiable_at_cosh {x : ℝ} : differentiable_at ℝ cosh x :=
  differentiable_cosh x

@[simp] theorem deriv_cosh : deriv cosh = sinh :=
  funext fun (x : ℝ) => has_deriv_at.deriv (has_deriv_at_cosh x)

theorem continuous_cosh : continuous cosh :=
  differentiable.continuous differentiable_cosh

theorem measurable_cosh : measurable cosh :=
  continuous.measurable continuous_cosh

/-- `sinh` is strictly monotone. -/
theorem sinh_strict_mono : strict_mono sinh :=
  strict_mono_of_deriv_pos differentiable_sinh
    (eq.mpr (id (Eq._oldrec (Eq.refl (∀ (x : ℝ), 0 < deriv sinh x)) deriv_sinh)) cosh_pos)

end real


/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : ℝ → ℝ` -/

/-! #### `real.cos` -/

theorem measurable.cos {α : Type u_1} [measurable_space α] {f : α → ℝ} (hf : measurable f) : measurable fun (x : α) => real.cos (f x) :=
  measurable.comp real.measurable_cos hf

theorem has_deriv_at.cos {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hf : has_deriv_at f f' x) : has_deriv_at (fun (x : ℝ) => real.cos (f x)) (-real.sin (f x) * f') x :=
  has_deriv_at.comp x (real.has_deriv_at_cos (f x)) hf

theorem has_deriv_within_at.cos {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} {s : set ℝ} (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (x : ℝ) => real.cos (f x)) (-real.sin (f x) * f') s x :=
  has_deriv_at.comp_has_deriv_within_at x (real.has_deriv_at_cos (f x)) hf

theorem deriv_within_cos {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} (hf : differentiable_within_at ℝ f s x) (hxs : unique_diff_within_at ℝ s x) : deriv_within (fun (x : ℝ) => real.cos (f x)) s x = -real.sin (f x) * deriv_within f s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.cos (differentiable_within_at.has_deriv_within_at hf)) hxs

@[simp] theorem deriv_cos {f : ℝ → ℝ} {x : ℝ} (hc : differentiable_at ℝ f x) : deriv (fun (x : ℝ) => real.cos (f x)) x = -real.sin (f x) * deriv f x :=
  has_deriv_at.deriv (has_deriv_at.cos (differentiable_at.has_deriv_at hc))

/-! #### `real.sin` -/

theorem measurable.sin {α : Type u_1} [measurable_space α] {f : α → ℝ} (hf : measurable f) : measurable fun (x : α) => real.sin (f x) :=
  measurable.comp real.measurable_sin hf

theorem has_deriv_at.sin {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hf : has_deriv_at f f' x) : has_deriv_at (fun (x : ℝ) => real.sin (f x)) (real.cos (f x) * f') x :=
  has_deriv_at.comp x (real.has_deriv_at_sin (f x)) hf

theorem has_deriv_within_at.sin {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} {s : set ℝ} (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (x : ℝ) => real.sin (f x)) (real.cos (f x) * f') s x :=
  has_deriv_at.comp_has_deriv_within_at x (real.has_deriv_at_sin (f x)) hf

theorem deriv_within_sin {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} (hf : differentiable_within_at ℝ f s x) (hxs : unique_diff_within_at ℝ s x) : deriv_within (fun (x : ℝ) => real.sin (f x)) s x = real.cos (f x) * deriv_within f s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.sin (differentiable_within_at.has_deriv_within_at hf)) hxs

@[simp] theorem deriv_sin {f : ℝ → ℝ} {x : ℝ} (hc : differentiable_at ℝ f x) : deriv (fun (x : ℝ) => real.sin (f x)) x = real.cos (f x) * deriv f x :=
  has_deriv_at.deriv (has_deriv_at.sin (differentiable_at.has_deriv_at hc))

/-! #### `real.cosh` -/

theorem measurable.cosh {α : Type u_1} [measurable_space α] {f : α → ℝ} (hf : measurable f) : measurable fun (x : α) => real.cosh (f x) :=
  measurable.comp real.measurable_cosh hf

theorem has_deriv_at.cosh {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hf : has_deriv_at f f' x) : has_deriv_at (fun (x : ℝ) => real.cosh (f x)) (real.sinh (f x) * f') x :=
  has_deriv_at.comp x (real.has_deriv_at_cosh (f x)) hf

theorem has_deriv_within_at.cosh {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} {s : set ℝ} (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (x : ℝ) => real.cosh (f x)) (real.sinh (f x) * f') s x :=
  has_deriv_at.comp_has_deriv_within_at x (real.has_deriv_at_cosh (f x)) hf

theorem deriv_within_cosh {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} (hf : differentiable_within_at ℝ f s x) (hxs : unique_diff_within_at ℝ s x) : deriv_within (fun (x : ℝ) => real.cosh (f x)) s x = real.sinh (f x) * deriv_within f s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.cosh (differentiable_within_at.has_deriv_within_at hf)) hxs

@[simp] theorem deriv_cosh {f : ℝ → ℝ} {x : ℝ} (hc : differentiable_at ℝ f x) : deriv (fun (x : ℝ) => real.cosh (f x)) x = real.sinh (f x) * deriv f x :=
  has_deriv_at.deriv (has_deriv_at.cosh (differentiable_at.has_deriv_at hc))

/-! #### `real.sinh` -/

theorem measurable.sinh {α : Type u_1} [measurable_space α] {f : α → ℝ} (hf : measurable f) : measurable fun (x : α) => real.sinh (f x) :=
  measurable.comp real.measurable_sinh hf

theorem has_deriv_at.sinh {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hf : has_deriv_at f f' x) : has_deriv_at (fun (x : ℝ) => real.sinh (f x)) (real.cosh (f x) * f') x :=
  has_deriv_at.comp x (real.has_deriv_at_sinh (f x)) hf

theorem has_deriv_within_at.sinh {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} {s : set ℝ} (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (x : ℝ) => real.sinh (f x)) (real.cosh (f x) * f') s x :=
  has_deriv_at.comp_has_deriv_within_at x (real.has_deriv_at_sinh (f x)) hf

theorem deriv_within_sinh {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} (hf : differentiable_within_at ℝ f s x) (hxs : unique_diff_within_at ℝ s x) : deriv_within (fun (x : ℝ) => real.sinh (f x)) s x = real.cosh (f x) * deriv_within f s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.sinh (differentiable_within_at.has_deriv_within_at hf)) hxs

@[simp] theorem deriv_sinh {f : ℝ → ℝ} {x : ℝ} (hc : differentiable_at ℝ f x) : deriv (fun (x : ℝ) => real.sinh (f x)) x = real.cosh (f x) * deriv f x :=
  has_deriv_at.deriv (has_deriv_at.sinh (differentiable_at.has_deriv_at hc))

/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : E → ℝ` -/

/-! #### `real.cos` -/

theorem has_fderiv_at.cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : continuous_linear_map ℝ E ℝ} {x : E} (hf : has_fderiv_at f f' x) : has_fderiv_at (fun (x : E) => real.cos (f x)) (-real.sin (f x) • f') x :=
  has_deriv_at.comp_has_fderiv_at x (real.has_deriv_at_cos (f x)) hf

theorem has_fderiv_within_at.cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : continuous_linear_map ℝ E ℝ} {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) : has_fderiv_within_at (fun (x : E) => real.cos (f x)) (-real.sin (f x) • f') s x :=
  has_deriv_at.comp_has_fderiv_within_at x (real.has_deriv_at_cos (f x)) hf

theorem differentiable_within_at.cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) : differentiable_within_at ℝ (fun (x : E) => real.cos (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.cos (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} (hc : differentiable_at ℝ f x) : differentiable_at ℝ (fun (x : E) => real.cos (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.cos (differentiable_at.has_fderiv_at hc))

theorem differentiable_on.cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} (hc : differentiable_on ℝ f s) : differentiable_on ℝ (fun (x : E) => real.cos (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.cos (hc x h)

@[simp] theorem differentiable.cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} (hc : differentiable ℝ f) : differentiable ℝ fun (x : E) => real.cos (f x) :=
  fun (x : E) => differentiable_at.cos (hc x)

theorem fderiv_within_cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) (hxs : unique_diff_within_at ℝ s x) : fderiv_within ℝ (fun (x : E) => real.cos (f x)) s x = -real.sin (f x) • fderiv_within ℝ f s x :=
  has_fderiv_within_at.fderiv_within (has_fderiv_within_at.cos (differentiable_within_at.has_fderiv_within_at hf)) hxs

@[simp] theorem fderiv_cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} (hc : differentiable_at ℝ f x) : fderiv ℝ (fun (x : E) => real.cos (f x)) x = -real.sin (f x) • fderiv ℝ f x :=
  has_fderiv_at.fderiv (has_fderiv_at.cos (differentiable_at.has_fderiv_at hc))

theorem times_cont_diff.cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {n : with_top ℕ} (h : times_cont_diff ℝ n f) : times_cont_diff ℝ n fun (x : E) => real.cos (f x) :=
  times_cont_diff.comp real.times_cont_diff_cos h

theorem times_cont_diff_at.cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {n : with_top ℕ} (hf : times_cont_diff_at ℝ n f x) : times_cont_diff_at ℝ n (fun (x : E) => real.cos (f x)) x :=
  times_cont_diff_at.comp x (times_cont_diff.times_cont_diff_at real.times_cont_diff_cos) hf

theorem times_cont_diff_on.cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_on ℝ n f s) : times_cont_diff_on ℝ n (fun (x : E) => real.cos (f x)) s :=
  times_cont_diff.comp_times_cont_diff_on real.times_cont_diff_cos hf

theorem times_cont_diff_within_at.cos {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_within_at ℝ n f s x) : times_cont_diff_within_at ℝ n (fun (x : E) => real.cos (f x)) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x (times_cont_diff.times_cont_diff_at real.times_cont_diff_cos) hf

/-! #### `real.sin` -/

theorem has_fderiv_at.sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : continuous_linear_map ℝ E ℝ} {x : E} (hf : has_fderiv_at f f' x) : has_fderiv_at (fun (x : E) => real.sin (f x)) (real.cos (f x) • f') x :=
  has_deriv_at.comp_has_fderiv_at x (real.has_deriv_at_sin (f x)) hf

theorem has_fderiv_within_at.sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : continuous_linear_map ℝ E ℝ} {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) : has_fderiv_within_at (fun (x : E) => real.sin (f x)) (real.cos (f x) • f') s x :=
  has_deriv_at.comp_has_fderiv_within_at x (real.has_deriv_at_sin (f x)) hf

theorem differentiable_within_at.sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) : differentiable_within_at ℝ (fun (x : E) => real.sin (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.sin (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} (hc : differentiable_at ℝ f x) : differentiable_at ℝ (fun (x : E) => real.sin (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.sin (differentiable_at.has_fderiv_at hc))

theorem differentiable_on.sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} (hc : differentiable_on ℝ f s) : differentiable_on ℝ (fun (x : E) => real.sin (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.sin (hc x h)

@[simp] theorem differentiable.sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} (hc : differentiable ℝ f) : differentiable ℝ fun (x : E) => real.sin (f x) :=
  fun (x : E) => differentiable_at.sin (hc x)

theorem fderiv_within_sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) (hxs : unique_diff_within_at ℝ s x) : fderiv_within ℝ (fun (x : E) => real.sin (f x)) s x = real.cos (f x) • fderiv_within ℝ f s x :=
  has_fderiv_within_at.fderiv_within (has_fderiv_within_at.sin (differentiable_within_at.has_fderiv_within_at hf)) hxs

@[simp] theorem fderiv_sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} (hc : differentiable_at ℝ f x) : fderiv ℝ (fun (x : E) => real.sin (f x)) x = real.cos (f x) • fderiv ℝ f x :=
  has_fderiv_at.fderiv (has_fderiv_at.sin (differentiable_at.has_fderiv_at hc))

theorem times_cont_diff.sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {n : with_top ℕ} (h : times_cont_diff ℝ n f) : times_cont_diff ℝ n fun (x : E) => real.sin (f x) :=
  times_cont_diff.comp real.times_cont_diff_sin h

theorem times_cont_diff_at.sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {n : with_top ℕ} (hf : times_cont_diff_at ℝ n f x) : times_cont_diff_at ℝ n (fun (x : E) => real.sin (f x)) x :=
  times_cont_diff_at.comp x (times_cont_diff.times_cont_diff_at real.times_cont_diff_sin) hf

theorem times_cont_diff_on.sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_on ℝ n f s) : times_cont_diff_on ℝ n (fun (x : E) => real.sin (f x)) s :=
  times_cont_diff.comp_times_cont_diff_on real.times_cont_diff_sin hf

theorem times_cont_diff_within_at.sin {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_within_at ℝ n f s x) : times_cont_diff_within_at ℝ n (fun (x : E) => real.sin (f x)) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x (times_cont_diff.times_cont_diff_at real.times_cont_diff_sin) hf

/-! #### `real.cosh` -/

theorem has_fderiv_at.cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : continuous_linear_map ℝ E ℝ} {x : E} (hf : has_fderiv_at f f' x) : has_fderiv_at (fun (x : E) => real.cosh (f x)) (real.sinh (f x) • f') x :=
  has_deriv_at.comp_has_fderiv_at x (real.has_deriv_at_cosh (f x)) hf

theorem has_fderiv_within_at.cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : continuous_linear_map ℝ E ℝ} {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) : has_fderiv_within_at (fun (x : E) => real.cosh (f x)) (real.sinh (f x) • f') s x :=
  has_deriv_at.comp_has_fderiv_within_at x (real.has_deriv_at_cosh (f x)) hf

theorem differentiable_within_at.cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) : differentiable_within_at ℝ (fun (x : E) => real.cosh (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.cosh (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} (hc : differentiable_at ℝ f x) : differentiable_at ℝ (fun (x : E) => real.cosh (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.cosh (differentiable_at.has_fderiv_at hc))

theorem differentiable_on.cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} (hc : differentiable_on ℝ f s) : differentiable_on ℝ (fun (x : E) => real.cosh (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.cosh (hc x h)

@[simp] theorem differentiable.cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} (hc : differentiable ℝ f) : differentiable ℝ fun (x : E) => real.cosh (f x) :=
  fun (x : E) => differentiable_at.cosh (hc x)

theorem fderiv_within_cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) (hxs : unique_diff_within_at ℝ s x) : fderiv_within ℝ (fun (x : E) => real.cosh (f x)) s x = real.sinh (f x) • fderiv_within ℝ f s x :=
  has_fderiv_within_at.fderiv_within (has_fderiv_within_at.cosh (differentiable_within_at.has_fderiv_within_at hf)) hxs

@[simp] theorem fderiv_cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} (hc : differentiable_at ℝ f x) : fderiv ℝ (fun (x : E) => real.cosh (f x)) x = real.sinh (f x) • fderiv ℝ f x :=
  has_fderiv_at.fderiv (has_fderiv_at.cosh (differentiable_at.has_fderiv_at hc))

theorem times_cont_diff.cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {n : with_top ℕ} (h : times_cont_diff ℝ n f) : times_cont_diff ℝ n fun (x : E) => real.cosh (f x) :=
  times_cont_diff.comp real.times_cont_diff_cosh h

theorem times_cont_diff_at.cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {n : with_top ℕ} (hf : times_cont_diff_at ℝ n f x) : times_cont_diff_at ℝ n (fun (x : E) => real.cosh (f x)) x :=
  times_cont_diff_at.comp x (times_cont_diff.times_cont_diff_at real.times_cont_diff_cosh) hf

theorem times_cont_diff_on.cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_on ℝ n f s) : times_cont_diff_on ℝ n (fun (x : E) => real.cosh (f x)) s :=
  times_cont_diff.comp_times_cont_diff_on real.times_cont_diff_cosh hf

theorem times_cont_diff_within_at.cosh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_within_at ℝ n f s x) : times_cont_diff_within_at ℝ n (fun (x : E) => real.cosh (f x)) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x (times_cont_diff.times_cont_diff_at real.times_cont_diff_cosh) hf

/-! #### `real.sinh` -/

theorem has_fderiv_at.sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : continuous_linear_map ℝ E ℝ} {x : E} (hf : has_fderiv_at f f' x) : has_fderiv_at (fun (x : E) => real.sinh (f x)) (real.cosh (f x) • f') x :=
  has_deriv_at.comp_has_fderiv_at x (real.has_deriv_at_sinh (f x)) hf

theorem has_fderiv_within_at.sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : continuous_linear_map ℝ E ℝ} {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) : has_fderiv_within_at (fun (x : E) => real.sinh (f x)) (real.cosh (f x) • f') s x :=
  has_deriv_at.comp_has_fderiv_within_at x (real.has_deriv_at_sinh (f x)) hf

theorem differentiable_within_at.sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) : differentiable_within_at ℝ (fun (x : E) => real.sinh (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.sinh (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} (hc : differentiable_at ℝ f x) : differentiable_at ℝ (fun (x : E) => real.sinh (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.sinh (differentiable_at.has_fderiv_at hc))

theorem differentiable_on.sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} (hc : differentiable_on ℝ f s) : differentiable_on ℝ (fun (x : E) => real.sinh (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.sinh (hc x h)

@[simp] theorem differentiable.sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} (hc : differentiable ℝ f) : differentiable ℝ fun (x : E) => real.sinh (f x) :=
  fun (x : E) => differentiable_at.sinh (hc x)

theorem fderiv_within_sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) (hxs : unique_diff_within_at ℝ s x) : fderiv_within ℝ (fun (x : E) => real.sinh (f x)) s x = real.cosh (f x) • fderiv_within ℝ f s x :=
  has_fderiv_within_at.fderiv_within (has_fderiv_within_at.sinh (differentiable_within_at.has_fderiv_within_at hf)) hxs

@[simp] theorem fderiv_sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} (hc : differentiable_at ℝ f x) : fderiv ℝ (fun (x : E) => real.sinh (f x)) x = real.cosh (f x) • fderiv ℝ f x :=
  has_fderiv_at.fderiv (has_fderiv_at.sinh (differentiable_at.has_fderiv_at hc))

theorem times_cont_diff.sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {n : with_top ℕ} (h : times_cont_diff ℝ n f) : times_cont_diff ℝ n fun (x : E) => real.sinh (f x) :=
  times_cont_diff.comp real.times_cont_diff_sinh h

theorem times_cont_diff_at.sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {n : with_top ℕ} (hf : times_cont_diff_at ℝ n f x) : times_cont_diff_at ℝ n (fun (x : E) => real.sinh (f x)) x :=
  times_cont_diff_at.comp x (times_cont_diff.times_cont_diff_at real.times_cont_diff_sinh) hf

theorem times_cont_diff_on.sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_on ℝ n f s) : times_cont_diff_on ℝ n (fun (x : E) => real.sinh (f x)) s :=
  times_cont_diff.comp_times_cont_diff_on real.times_cont_diff_sinh hf

theorem times_cont_diff_within_at.sinh {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_within_at ℝ n f s x) : times_cont_diff_within_at ℝ n (fun (x : E) => real.sinh (f x)) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x (times_cont_diff.times_cont_diff_at real.times_cont_diff_sinh) hf

namespace real


theorem exists_cos_eq_zero : 0 ∈ cos '' set.Icc 1 (bit0 1) :=
  intermediate_value_Icc' (eq.mpr (id (eq_true_intro (norm_num.le_one_bit0 1 (le_refl 1)))) trivial) continuous_on_cos
    { left := le_of_lt cos_two_neg, right := le_of_lt cos_one_pos }

/-- The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from
which one can derive all its properties. For explicit bounds on π, see `data.real.pi`. -/
def pi : ℝ :=
  bit0 1 * classical.some exists_cos_eq_zero

@[simp] theorem cos_pi_div_two : cos (pi / bit0 1) = 0 := sorry

theorem one_le_pi_div_two : 1 ≤ pi / bit0 1 := sorry

theorem pi_div_two_le_two : pi / bit0 1 ≤ bit0 1 := sorry

theorem two_le_pi : bit0 1 ≤ pi :=
  iff.mp
    (div_le_div_right ((fun (this : 0 < bit0 1) => this) (eq.mpr (id (eq_true_intro (bit0_pos zero_lt_one'))) trivial)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (bit0 1 / bit0 1 ≤ pi / bit0 1)) (div_self two_ne_zero'))) one_le_pi_div_two)

theorem pi_le_four : pi ≤ bit0 (bit0 1) := sorry

theorem pi_pos : 0 < pi :=
  lt_of_lt_of_le (eq.mpr (id (eq_true_intro (bit0_pos zero_lt_one'))) trivial) two_le_pi

theorem pi_ne_zero : pi ≠ 0 :=
  ne_of_gt pi_pos

theorem pi_div_two_pos : 0 < pi / bit0 1 :=
  half_pos pi_pos

theorem two_pi_pos : 0 < bit0 1 * pi := sorry

@[simp] theorem sin_pi : sin pi = 0 := sorry

@[simp] theorem cos_pi : cos pi = -1 := sorry

@[simp] theorem sin_two_pi : sin (bit0 1 * pi) = 0 := sorry

@[simp] theorem cos_two_pi : cos (bit0 1 * pi) = 1 := sorry

theorem sin_add_pi (x : ℝ) : sin (x + pi) = -sin x := sorry

theorem sin_add_two_pi (x : ℝ) : sin (x + bit0 1 * pi) = sin x := sorry

theorem cos_add_two_pi (x : ℝ) : cos (x + bit0 1 * pi) = cos x := sorry

theorem sin_pi_sub (x : ℝ) : sin (pi - x) = sin x := sorry

theorem cos_add_pi (x : ℝ) : cos (x + pi) = -cos x := sorry

theorem cos_pi_sub (x : ℝ) : cos (pi - x) = -cos x := sorry

theorem sin_pos_of_pos_of_lt_pi {x : ℝ} (h0x : 0 < x) (hxp : x < pi) : 0 < sin x := sorry

theorem sin_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ set.Ioo 0 pi) : 0 < sin x :=
  sin_pos_of_pos_of_lt_pi (and.left hx) (and.right hx)

theorem sin_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ set.Icc 0 pi) : 0 ≤ sin x :=
  closure_lt_subset_le continuous_const continuous_sin
    (closure_mono (fun (y : ℝ) => sin_pos_of_mem_Ioo)
      (eq.mp (Eq._oldrec (Eq.refl (x ∈ set.Icc 0 pi)) (Eq.symm (closure_Ioo pi_pos))) hx))

theorem sin_nonneg_of_nonneg_of_le_pi {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ pi) : 0 ≤ sin x :=
  sin_nonneg_of_mem_Icc { left := h0x, right := hxp }

theorem sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx0 : x < 0) (hpx : -pi < x) : sin x < 0 :=
  iff.mp neg_pos (sin_neg x ▸ sin_pos_of_pos_of_lt_pi (iff.mpr neg_pos hx0) (iff.mp neg_lt hpx))

theorem sin_nonpos_of_nonnpos_of_neg_pi_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -pi ≤ x) : sin x ≤ 0 :=
  iff.mp neg_nonneg (sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (iff.mpr neg_nonneg hx0) (iff.mp neg_le hpx))

@[simp] theorem sin_pi_div_two : sin (pi / bit0 1) = 1 := sorry

theorem sin_add_pi_div_two (x : ℝ) : sin (x + pi / bit0 1) = cos x := sorry

theorem sin_sub_pi_div_two (x : ℝ) : sin (x - pi / bit0 1) = -cos x := sorry

theorem sin_pi_div_two_sub (x : ℝ) : sin (pi / bit0 1 - x) = cos x := sorry

theorem cos_add_pi_div_two (x : ℝ) : cos (x + pi / bit0 1) = -sin x := sorry

theorem cos_sub_pi_div_two (x : ℝ) : cos (x - pi / bit0 1) = sin x := sorry

theorem cos_pi_div_two_sub (x : ℝ) : cos (pi / bit0 1 - x) = sin x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (cos (pi / bit0 1 - x) = sin x)) (Eq.symm (cos_neg (pi / bit0 1 - x)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (cos (-(pi / bit0 1 - x)) = sin x)) (neg_sub (pi / bit0 1) x)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (cos (x - pi / bit0 1) = sin x)) (cos_sub_pi_div_two x))) (Eq.refl (sin x))))

theorem cos_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) : 0 < cos x := sorry

theorem cos_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1)) : 0 ≤ cos x := sorry

theorem cos_neg_of_pi_div_two_lt_of_lt {x : ℝ} (hx₁ : pi / bit0 1 < x) (hx₂ : x < pi + pi / bit0 1) : cos x < 0 := sorry

theorem cos_nonpos_of_pi_div_two_le_of_le {x : ℝ} (hx₁ : pi / bit0 1 ≤ x) (hx₂ : x ≤ pi + pi / bit0 1) : cos x ≤ 0 := sorry

theorem sin_nat_mul_pi (n : ℕ) : sin (↑n * pi) = 0 := sorry

theorem sin_int_mul_pi (n : ℤ) : sin (↑n * pi) = 0 := sorry

theorem cos_nat_mul_two_pi (n : ℕ) : cos (↑n * (bit0 1 * pi)) = 1 := sorry

theorem cos_int_mul_two_pi (n : ℤ) : cos (↑n * (bit0 1 * pi)) = 1 := sorry

theorem cos_int_mul_two_pi_add_pi (n : ℤ) : cos (↑n * (bit0 1 * pi) + pi) = -1 := sorry

theorem sin_eq_zero_iff_of_lt_of_lt {x : ℝ} (hx₁ : -pi < x) (hx₂ : x < pi) : sin x = 0 ↔ x = 0 := sorry

theorem sin_eq_zero_iff {x : ℝ} : sin x = 0 ↔ ∃ (n : ℤ), ↑n * pi = x := sorry

theorem sin_ne_zero_iff {x : ℝ} : sin x ≠ 0 ↔ ∀ (n : ℤ), ↑n * pi ≠ x := sorry

theorem sin_eq_zero_iff_cos_eq {x : ℝ} : sin x = 0 ↔ cos x = 1 ∨ cos x = -1 := sorry

theorem cos_eq_one_iff (x : ℝ) : cos x = 1 ↔ ∃ (n : ℤ), ↑n * (bit0 1 * pi) = x := sorry

theorem cos_eq_one_iff_of_lt_of_lt {x : ℝ} (hx₁ : -(bit0 1 * pi) < x) (hx₂ : x < bit0 1 * pi) : cos x = 1 ↔ x = 0 := sorry

theorem cos_lt_cos_of_nonneg_of_le_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ pi / bit0 1) (hxy : x < y) : cos y < cos x := sorry

theorem cos_lt_cos_of_nonneg_of_le_pi {x : ℝ} {y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ pi) (hxy : x < y) : cos y < cos x := sorry

theorem strict_mono_decr_on_cos : strict_mono_decr_on cos (set.Icc 0 pi) :=
  fun (x : ℝ) (hx : x ∈ set.Icc 0 pi) (y : ℝ) (hy : y ∈ set.Icc 0 pi) (hxy : x < y) =>
    cos_lt_cos_of_nonneg_of_le_pi (and.left hx) (and.right hy) hxy

theorem cos_le_cos_of_nonneg_of_le_pi {x : ℝ} {y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ pi) (hxy : x ≤ y) : cos y ≤ cos x := sorry

theorem sin_lt_sin_of_lt_of_le_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : -(pi / bit0 1) ≤ x) (hy₂ : y ≤ pi / bit0 1) (hxy : x < y) : sin x < sin y := sorry

theorem strict_mono_incr_on_sin : strict_mono_incr_on sin (set.Icc (-(pi / bit0 1)) (pi / bit0 1)) :=
  fun (x : ℝ) (hx : x ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1)) (y : ℝ) (hy : y ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1))
    (hxy : x < y) => sin_lt_sin_of_lt_of_le_pi_div_two (and.left hx) (and.right hy) hxy

theorem sin_le_sin_of_le_of_le_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : -(pi / bit0 1) ≤ x) (hy₂ : y ≤ pi / bit0 1) (hxy : x ≤ y) : sin x ≤ sin y := sorry

theorem inj_on_sin : set.inj_on sin (set.Icc (-(pi / bit0 1)) (pi / bit0 1)) :=
  strict_mono_incr_on.inj_on strict_mono_incr_on_sin

theorem inj_on_cos : set.inj_on cos (set.Icc 0 pi) :=
  strict_mono_decr_on.inj_on strict_mono_decr_on_cos

theorem surj_on_sin : set.surj_on sin (set.Icc (-(pi / bit0 1)) (pi / bit0 1)) (set.Icc (-1) 1) := sorry

theorem surj_on_cos : set.surj_on cos (set.Icc 0 pi) (set.Icc (-1) 1) := sorry

theorem sin_mem_Icc (x : ℝ) : sin x ∈ set.Icc (-1) 1 :=
  { left := neg_one_le_sin x, right := sin_le_one x }

theorem cos_mem_Icc (x : ℝ) : cos x ∈ set.Icc (-1) 1 :=
  { left := neg_one_le_cos x, right := cos_le_one x }

theorem maps_to_sin (s : set ℝ) : set.maps_to sin s (set.Icc (-1) 1) :=
  fun (x : ℝ) (_x : x ∈ s) => sin_mem_Icc x

theorem maps_to_cos (s : set ℝ) : set.maps_to cos s (set.Icc (-1) 1) :=
  fun (x : ℝ) (_x : x ∈ s) => cos_mem_Icc x

theorem bij_on_sin : set.bij_on sin (set.Icc (-(pi / bit0 1)) (pi / bit0 1)) (set.Icc (-1) 1) :=
  { left := maps_to_sin (set.Icc (-(pi / bit0 1)) (pi / bit0 1)), right := { left := inj_on_sin, right := surj_on_sin } }

theorem bij_on_cos : set.bij_on cos (set.Icc 0 pi) (set.Icc (-1) 1) :=
  { left := maps_to_cos (set.Icc 0 pi), right := { left := inj_on_cos, right := surj_on_cos } }

@[simp] theorem range_cos : set.range cos = set.Icc (-1) 1 :=
  set.subset.antisymm (iff.mpr set.range_subset_iff cos_mem_Icc) (set.surj_on.subset_range surj_on_cos)

@[simp] theorem range_sin : set.range sin = set.Icc (-1) 1 :=
  set.subset.antisymm (iff.mpr set.range_subset_iff sin_mem_Icc) (set.surj_on.subset_range surj_on_sin)

theorem range_cos_infinite : set.infinite (set.range cos) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (set.infinite (set.range cos))) range_cos))
    (set.Icc.infinite (eq.mpr (id (eq_true_intro (norm_num.lt_neg_pos 1 1 zero_lt_one' zero_lt_one'))) trivial))

theorem range_sin_infinite : set.infinite (set.range sin) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (set.infinite (set.range sin))) range_sin))
    (set.Icc.infinite (eq.mpr (id (eq_true_intro (norm_num.lt_neg_pos 1 1 zero_lt_one' zero_lt_one'))) trivial))

theorem sin_lt {x : ℝ} (h : 0 < x) : sin x < x := sorry

/- note 1: this inequality is not tight, the tighter inequality is sin x > x - x ^ 3 / 6.
   note 2: this is also true for x > 1, but it's nontrivial for x just above 1. -/

theorem sin_gt_sub_cube {x : ℝ} (h : 0 < x) (h' : x ≤ 1) : x - x ^ bit1 1 / bit0 (bit0 1) < sin x := sorry

/-- the series `sqrt_two_add_series x n` is `sqrt(2 + sqrt(2 + ... ))` with `n` square roots,
  starting with `x`. We define it here because `cos (pi / 2 ^ (n+1)) = sqrt_two_add_series 0 n / 2`
-/
@[simp] def sqrt_two_add_series (x : ℝ) : ℕ → ℝ :=
  sorry

theorem sqrt_two_add_series_zero (x : ℝ) : sqrt_two_add_series x 0 = x := sorry

theorem sqrt_two_add_series_one : sqrt_two_add_series 0 1 = sqrt (bit0 1) := sorry

theorem sqrt_two_add_series_two : sqrt_two_add_series 0 (bit0 1) = sqrt (bit0 1 + sqrt (bit0 1)) := sorry

theorem sqrt_two_add_series_zero_nonneg (n : ℕ) : 0 ≤ sqrt_two_add_series 0 n := sorry

theorem sqrt_two_add_series_nonneg {x : ℝ} (h : 0 ≤ x) (n : ℕ) : 0 ≤ sqrt_two_add_series x n := sorry

theorem sqrt_two_add_series_lt_two (n : ℕ) : sqrt_two_add_series 0 n < bit0 1 := sorry

theorem sqrt_two_add_series_succ (x : ℝ) (n : ℕ) : sqrt_two_add_series x (n + 1) = sqrt_two_add_series (sqrt (bit0 1 + x)) n := sorry

theorem sqrt_two_add_series_monotone_left {x : ℝ} {y : ℝ} (h : x ≤ y) (n : ℕ) : sqrt_two_add_series x n ≤ sqrt_two_add_series y n := sorry

@[simp] theorem cos_pi_over_two_pow (n : ℕ) : cos (pi / bit0 1 ^ (n + 1)) = sqrt_two_add_series 0 n / bit0 1 := sorry

theorem sin_square_pi_over_two_pow (n : ℕ) : sin (pi / bit0 1 ^ (n + 1)) ^ bit0 1 = 1 - (sqrt_two_add_series 0 n / bit0 1) ^ bit0 1 := sorry

theorem sin_square_pi_over_two_pow_succ (n : ℕ) : sin (pi / bit0 1 ^ (n + bit0 1)) ^ bit0 1 = 1 / bit0 1 - sqrt_two_add_series 0 n / bit0 (bit0 1) := sorry

@[simp] theorem sin_pi_over_two_pow_succ (n : ℕ) : sin (pi / bit0 1 ^ (n + bit0 1)) = sqrt (bit0 1 - sqrt_two_add_series 0 n) / bit0 1 := sorry

@[simp] theorem cos_pi_div_four : cos (pi / bit0 (bit0 1)) = sqrt (bit0 1) / bit0 1 := sorry

@[simp] theorem sin_pi_div_four : sin (pi / bit0 (bit0 1)) = sqrt (bit0 1) / bit0 1 := sorry

@[simp] theorem cos_pi_div_eight : cos (pi / bit0 (bit0 (bit0 1))) = sqrt (bit0 1 + sqrt (bit0 1)) / bit0 1 := sorry

@[simp] theorem sin_pi_div_eight : sin (pi / bit0 (bit0 (bit0 1))) = sqrt (bit0 1 - sqrt (bit0 1)) / bit0 1 := sorry

@[simp] theorem cos_pi_div_sixteen : cos (pi / bit0 (bit0 (bit0 (bit0 1)))) = sqrt (bit0 1 + sqrt (bit0 1 + sqrt (bit0 1))) / bit0 1 := sorry

@[simp] theorem sin_pi_div_sixteen : sin (pi / bit0 (bit0 (bit0 (bit0 1)))) = sqrt (bit0 1 - sqrt (bit0 1 + sqrt (bit0 1))) / bit0 1 := sorry

@[simp] theorem cos_pi_div_thirty_two : cos (pi / bit0 (bit0 (bit0 (bit0 (bit0 1))))) = sqrt (bit0 1 + sqrt (bit0 1 + sqrt (bit0 1 + sqrt (bit0 1)))) / bit0 1 := sorry

@[simp] theorem sin_pi_div_thirty_two : sin (pi / bit0 (bit0 (bit0 (bit0 (bit0 1))))) = sqrt (bit0 1 - sqrt (bit0 1 + sqrt (bit0 1 + sqrt (bit0 1)))) / bit0 1 := sorry

-- This section is also a convenient location for other explicit values of `sin` and `cos`.

/-- The cosine of `π / 3` is `1 / 2`. -/
@[simp] theorem cos_pi_div_three : cos (pi / bit1 1) = 1 / bit0 1 := sorry

/-- The square of the cosine of `π / 6` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
theorem square_cos_pi_div_six : cos (pi / bit0 (bit1 1)) ^ bit0 1 = bit1 1 / bit0 (bit0 1) := sorry

/-- The cosine of `π / 6` is `√3 / 2`. -/
@[simp] theorem cos_pi_div_six : cos (pi / bit0 (bit1 1)) = sqrt (bit1 1) / bit0 1 := sorry

/-- The sine of `π / 6` is `1 / 2`. -/
@[simp] theorem sin_pi_div_six : sin (pi / bit0 (bit1 1)) = 1 / bit0 1 := sorry

/-- The square of the sine of `π / 3` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
theorem square_sin_pi_div_three : sin (pi / bit1 1) ^ bit0 1 = bit1 1 / bit0 (bit0 1) := sorry

/-- The sine of `π / 3` is `√3 / 2`. -/
@[simp] theorem sin_pi_div_three : sin (pi / bit1 1) = sqrt (bit1 1) / bit0 1 := sorry

/-- The type of angles -/
def angle  :=
  quotient_add_group.quotient (add_subgroup.gmultiples (bit0 1 * pi))

namespace angle


protected instance angle.add_comm_group : add_comm_group angle :=
  quotient_add_group.add_comm_group (add_subgroup.gmultiples (bit0 1 * pi))

protected instance inhabited : Inhabited angle :=
  { default := 0 }

protected instance angle.has_coe : has_coe ℝ angle :=
  has_coe.mk quotient.mk'

@[simp] theorem coe_zero : ↑0 = 0 :=
  rfl

@[simp] theorem coe_add (x : ℝ) (y : ℝ) : ↑(x + y) = ↑x + ↑y :=
  rfl

@[simp] theorem coe_neg (x : ℝ) : ↑(-x) = -↑x :=
  rfl

@[simp] theorem coe_sub (x : ℝ) (y : ℝ) : ↑(x - y) = ↑x - ↑y := sorry

@[simp] theorem coe_nat_mul_eq_nsmul (x : ℝ) (n : ℕ) : ↑(↑n * x) = n •ℕ ↑x := sorry

@[simp] theorem coe_int_mul_eq_gsmul (x : ℝ) (n : ℤ) : ↑(↑n * x) = n •ℤ ↑x := sorry

@[simp] theorem coe_two_pi : ↑(bit0 1 * pi) = 0 := sorry

theorem angle_eq_iff_two_pi_dvd_sub {ψ : ℝ} {θ : ℝ} : ↑θ = ↑ψ ↔ ∃ (k : ℤ), θ - ψ = bit0 1 * pi * ↑k := sorry

theorem cos_eq_iff_eq_or_eq_neg {θ : ℝ} {ψ : ℝ} : cos θ = cos ψ ↔ ↑θ = ↑ψ ∨ ↑θ = -↑ψ := sorry

theorem sin_eq_iff_eq_or_add_eq_pi {θ : ℝ} {ψ : ℝ} : sin θ = sin ψ ↔ ↑θ = ↑ψ ∨ ↑θ + ↑ψ = ↑pi := sorry

theorem cos_sin_inj {θ : ℝ} {ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : ↑θ = ↑ψ := sorry

end angle


/-- `real.sin` as an `order_iso` between `[-(π / 2), π / 2]` and `[-1, 1]`. -/
def sin_order_iso : ↥(set.Icc (-(pi / bit0 1)) (pi / bit0 1)) ≃o ↥(set.Icc (-1) 1) :=
  order_iso.trans (strict_mono_incr_on.order_iso sin (set.Icc (-(pi / bit0 1)) (pi / bit0 1)) strict_mono_incr_on_sin)
    (order_iso.set_congr (sin '' set.Icc (-(pi / bit0 1)) (pi / bit0 1)) (set.Icc (-1) 1) sorry)

@[simp] theorem coe_sin_order_iso_apply (x : ↥(set.Icc (-(pi / bit0 1)) (pi / bit0 1))) : ↑(coe_fn sin_order_iso x) = sin ↑x :=
  rfl

theorem sin_order_iso_apply (x : ↥(set.Icc (-(pi / bit0 1)) (pi / bit0 1))) : coe_fn sin_order_iso x = { val := sin ↑x, property := sin_mem_Icc ↑x } :=
  rfl

/-- Inverse of the `sin` function, returns values in the range `-π / 2 ≤ arcsin x ≤ π / 2`.
It defaults to `-π / 2` on `(-∞, -1)` and to `π / 2` to `(1, ∞)`. -/
def arcsin : ℝ → ℝ :=
  coe ∘ set.Icc_extend sorry ⇑(order_iso.symm sin_order_iso)

theorem arcsin_mem_Icc (x : ℝ) : arcsin x ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1) :=
  subtype.coe_prop (set.Icc_extend arcsin._proof_1 (⇑(order_iso.symm sin_order_iso)) x)

@[simp] theorem range_arcsin : set.range arcsin = set.Icc (-(pi / bit0 1)) (pi / bit0 1) := sorry

theorem arcsin_le_pi_div_two (x : ℝ) : arcsin x ≤ pi / bit0 1 :=
  and.right (arcsin_mem_Icc x)

theorem neg_pi_div_two_le_arcsin (x : ℝ) : -(pi / bit0 1) ≤ arcsin x :=
  and.left (arcsin_mem_Icc x)

theorem arcsin_proj_Icc (x : ℝ) : arcsin ↑(set.proj_Icc (-1) 1 (neg_le_self zero_le_one) x) = arcsin x := sorry

theorem sin_arcsin' {x : ℝ} (hx : x ∈ set.Icc (-1) 1) : sin (arcsin x) = x := sorry

theorem sin_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arcsin x) = x :=
  sin_arcsin' { left := hx₁, right := hx₂ }

theorem arcsin_sin' {x : ℝ} (hx : x ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1)) : arcsin (sin x) = x :=
  inj_on_sin (arcsin_mem_Icc (sin x)) hx
    (eq.mpr (id (Eq._oldrec (Eq.refl (sin (arcsin (sin x)) = sin x)) (sin_arcsin (neg_one_le_sin x) (sin_le_one x))))
      (Eq.refl (sin x)))

theorem arcsin_sin {x : ℝ} (hx₁ : -(pi / bit0 1) ≤ x) (hx₂ : x ≤ pi / bit0 1) : arcsin (sin x) = x :=
  arcsin_sin' { left := hx₁, right := hx₂ }

theorem strict_mono_incr_on_arcsin : strict_mono_incr_on arcsin (set.Icc (-1) 1) :=
  strict_mono.comp_strict_mono_incr_on (subtype.strict_mono_coe fun (x : ℝ) => x ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1))
    (strict_mono.strict_mono_incr_on_Icc_extend arcsin._proof_1 (order_iso.strict_mono (order_iso.symm sin_order_iso)))

theorem monotone_arcsin : monotone arcsin :=
  monotone.comp (subtype.mono_coe fun (x : ℝ) => x ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1))
    (monotone.Icc_extend arcsin._proof_1 (order_iso.monotone (order_iso.symm sin_order_iso)))

theorem inj_on_arcsin : set.inj_on arcsin (set.Icc (-1) 1) :=
  strict_mono_incr_on.inj_on strict_mono_incr_on_arcsin

theorem arcsin_inj {x : ℝ} {y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) : arcsin x = arcsin y ↔ x = y :=
  set.inj_on.eq_iff inj_on_arcsin { left := hx₁, right := hx₂ } { left := hy₁, right := hy₂ }

theorem continuous_arcsin : continuous arcsin :=
  continuous.comp continuous_subtype_coe (continuous.Icc_extend (order_iso.continuous (order_iso.symm sin_order_iso)))

theorem continuous_at_arcsin {x : ℝ} : continuous_at arcsin x :=
  continuous.continuous_at continuous_arcsin

theorem arcsin_eq_of_sin_eq {x : ℝ} {y : ℝ} (h₁ : sin x = y) (h₂ : x ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1)) : arcsin y = x :=
  Eq._oldrec (inj_on_sin (arcsin_mem_Icc (sin x)) h₂ (sin_arcsin' (sin_mem_Icc x))) h₁

@[simp] theorem arcsin_zero : arcsin 0 = 0 :=
  arcsin_eq_of_sin_eq sin_zero
    { left := iff.mpr neg_nonpos (has_lt.lt.le pi_div_two_pos), right := has_lt.lt.le pi_div_two_pos }

@[simp] theorem arcsin_one : arcsin 1 = pi / bit0 1 :=
  arcsin_eq_of_sin_eq sin_pi_div_two (iff.mpr set.right_mem_Icc (neg_le_self (has_lt.lt.le pi_div_two_pos)))

theorem arcsin_of_one_le {x : ℝ} (hx : 1 ≤ x) : arcsin x = pi / bit0 1 := sorry

theorem arcsin_neg_one : arcsin (-1) = -(pi / bit0 1) := sorry

theorem arcsin_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : arcsin x = -(pi / bit0 1) := sorry

@[simp] theorem arcsin_neg (x : ℝ) : arcsin (-x) = -arcsin x := sorry

theorem arcsin_le_iff_le_sin {x : ℝ} {y : ℝ} (hx : x ∈ set.Icc (-1) 1) (hy : y ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1)) : arcsin x ≤ y ↔ x ≤ sin y := sorry

theorem arcsin_le_iff_le_sin' {x : ℝ} {y : ℝ} (hy : y ∈ set.Ico (-(pi / bit0 1)) (pi / bit0 1)) : arcsin x ≤ y ↔ x ≤ sin y := sorry

theorem le_arcsin_iff_sin_le {x : ℝ} {y : ℝ} (hx : x ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1)) (hy : y ∈ set.Icc (-1) 1) : x ≤ arcsin y ↔ sin x ≤ y := sorry

theorem le_arcsin_iff_sin_le' {x : ℝ} {y : ℝ} (hx : x ∈ set.Ioc (-(pi / bit0 1)) (pi / bit0 1)) : x ≤ arcsin y ↔ sin x ≤ y := sorry

theorem arcsin_lt_iff_lt_sin {x : ℝ} {y : ℝ} (hx : x ∈ set.Icc (-1) 1) (hy : y ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1)) : arcsin x < y ↔ x < sin y :=
  iff.trans (iff.symm not_le) (iff.trans (not_congr (le_arcsin_iff_sin_le hy hx)) not_le)

theorem arcsin_lt_iff_lt_sin' {x : ℝ} {y : ℝ} (hy : y ∈ set.Ioc (-(pi / bit0 1)) (pi / bit0 1)) : arcsin x < y ↔ x < sin y :=
  iff.trans (iff.symm not_le) (iff.trans (not_congr (le_arcsin_iff_sin_le' hy)) not_le)

theorem lt_arcsin_iff_sin_lt {x : ℝ} {y : ℝ} (hx : x ∈ set.Icc (-(pi / bit0 1)) (pi / bit0 1)) (hy : y ∈ set.Icc (-1) 1) : x < arcsin y ↔ sin x < y :=
  iff.trans (iff.symm not_le) (iff.trans (not_congr (arcsin_le_iff_le_sin hy hx)) not_le)

theorem lt_arcsin_iff_sin_lt' {x : ℝ} {y : ℝ} (hx : x ∈ set.Ico (-(pi / bit0 1)) (pi / bit0 1)) : x < arcsin y ↔ sin x < y :=
  iff.trans (iff.symm not_le) (iff.trans (not_congr (arcsin_le_iff_le_sin' hx)) not_le)

theorem arcsin_eq_iff_eq_sin {x : ℝ} {y : ℝ} (hy : y ∈ set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) : arcsin x = y ↔ x = sin y := sorry

@[simp] theorem arcsin_nonneg {x : ℝ} : 0 ≤ arcsin x ↔ 0 ≤ x :=
  iff.trans (le_arcsin_iff_sin_le' { left := iff.mpr neg_lt_zero pi_div_two_pos, right := has_lt.lt.le pi_div_two_pos })
    (eq.mpr (id (Eq._oldrec (Eq.refl (sin 0 ≤ x ↔ 0 ≤ x)) sin_zero)) (iff.refl (0 ≤ x)))

@[simp] theorem arcsin_nonpos {x : ℝ} : arcsin x ≤ 0 ↔ x ≤ 0 :=
  iff.trans (iff.symm neg_nonneg) (arcsin_neg x ▸ iff.trans arcsin_nonneg neg_nonneg)

@[simp] theorem arcsin_eq_zero_iff {x : ℝ} : arcsin x = 0 ↔ x = 0 := sorry

@[simp] theorem zero_eq_arcsin_iff {x : ℝ} : 0 = arcsin x ↔ x = 0 :=
  iff.trans eq_comm arcsin_eq_zero_iff

@[simp] theorem arcsin_pos {x : ℝ} : 0 < arcsin x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arcsin_nonpos

@[simp] theorem arcsin_lt_zero {x : ℝ} : arcsin x < 0 ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arcsin_nonneg

@[simp] theorem arcsin_lt_pi_div_two {x : ℝ} : arcsin x < pi / bit0 1 ↔ x < 1 :=
  iff.trans (arcsin_lt_iff_lt_sin' (iff.mpr set.right_mem_Ioc (neg_lt_self pi_div_two_pos)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x < sin (pi / bit0 1) ↔ x < 1)) sin_pi_div_two)) (iff.refl (x < 1)))

@[simp] theorem neg_pi_div_two_lt_arcsin {x : ℝ} : -(pi / bit0 1) < arcsin x ↔ -1 < x :=
  iff.trans (lt_arcsin_iff_sin_lt' (iff.mpr set.left_mem_Ico (neg_lt_self pi_div_two_pos)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sin (-(pi / bit0 1)) < x ↔ -1 < x)) (sin_neg (pi / bit0 1))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (-sin (pi / bit0 1) < x ↔ -1 < x)) sin_pi_div_two)) (iff.refl (-1 < x))))

@[simp] theorem arcsin_eq_pi_div_two {x : ℝ} : arcsin x = pi / bit0 1 ↔ 1 ≤ x := sorry

@[simp] theorem pi_div_two_eq_arcsin {x : ℝ} : pi / bit0 1 = arcsin x ↔ 1 ≤ x :=
  iff.trans eq_comm arcsin_eq_pi_div_two

@[simp] theorem pi_div_two_le_arcsin {x : ℝ} : pi / bit0 1 ≤ arcsin x ↔ 1 ≤ x :=
  iff.trans (has_le.le.le_iff_eq (arcsin_le_pi_div_two x)) pi_div_two_eq_arcsin

@[simp] theorem arcsin_eq_neg_pi_div_two {x : ℝ} : arcsin x = -(pi / bit0 1) ↔ x ≤ -1 := sorry

@[simp] theorem neg_pi_div_two_eq_arcsin {x : ℝ} : -(pi / bit0 1) = arcsin x ↔ x ≤ -1 :=
  iff.trans eq_comm arcsin_eq_neg_pi_div_two

@[simp] theorem arcsin_le_neg_pi_div_two {x : ℝ} : arcsin x ≤ -(pi / bit0 1) ↔ x ≤ -1 :=
  iff.trans (has_le.le.le_iff_eq (neg_pi_div_two_le_arcsin x)) arcsin_eq_neg_pi_div_two

theorem maps_to_sin_Ioo : set.maps_to sin (set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) (set.Ioo (-1) 1) := sorry

/-- `real.sin` as a `local_homeomorph` between `(-π / 2, π / 2)` and `(-1, 1)`. -/
@[simp] def sin_local_homeomorph : local_homeomorph ℝ ℝ :=
  local_homeomorph.mk
    (local_equiv.mk sin arcsin (set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) (set.Ioo (-1) 1) maps_to_sin_Ioo sorry sorry
      sorry)
    sorry sorry sorry sorry

theorem cos_arcsin_nonneg (x : ℝ) : 0 ≤ cos (arcsin x) :=
  cos_nonneg_of_mem_Icc { left := neg_pi_div_two_le_arcsin x, right := arcsin_le_pi_div_two x }

theorem cos_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arcsin x) = sqrt (1 - x ^ bit0 1) := sorry

theorem deriv_arcsin_aux {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) : has_deriv_at arcsin (1 / sqrt (1 - x ^ bit0 1)) x ∧ times_cont_diff_at ℝ ⊤ arcsin x := sorry

theorem has_deriv_at_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) : has_deriv_at arcsin (1 / sqrt (1 - x ^ bit0 1)) x :=
  and.left (deriv_arcsin_aux h₁ h₂)

theorem times_cont_diff_at_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : with_top ℕ} : times_cont_diff_at ℝ n arcsin x :=
  times_cont_diff_at.of_le (and.right (deriv_arcsin_aux h₁ h₂)) le_top

theorem has_deriv_within_at_arcsin_Ici {x : ℝ} (h : x ≠ -1) : has_deriv_within_at arcsin (1 / sqrt (1 - x ^ bit0 1)) (set.Ici x) x := sorry

theorem has_deriv_within_at_arcsin_Iic {x : ℝ} (h : x ≠ 1) : has_deriv_within_at arcsin (1 / sqrt (1 - x ^ bit0 1)) (set.Iic x) x := sorry

theorem differentiable_within_at_arcsin_Ici {x : ℝ} : differentiable_within_at ℝ arcsin (set.Ici x) x ↔ x ≠ -1 := sorry

theorem differentiable_within_at_arcsin_Iic {x : ℝ} : differentiable_within_at ℝ arcsin (set.Iic x) x ↔ x ≠ 1 := sorry

theorem differentiable_at_arcsin {x : ℝ} : differentiable_at ℝ arcsin x ↔ x ≠ -1 ∧ x ≠ 1 := sorry

@[simp] theorem deriv_arcsin : deriv arcsin = fun (x : ℝ) => 1 / sqrt (1 - x ^ bit0 1) := sorry

theorem differentiable_on_arcsin : differentiable_on ℝ arcsin (insert (-1) (singleton 1)ᶜ) := sorry

theorem times_cont_diff_on_arcsin {n : with_top ℕ} : times_cont_diff_on ℝ n arcsin (insert (-1) (singleton 1)ᶜ) :=
  fun (x : ℝ) (hx : x ∈ (insert (-1) (singleton 1)ᶜ)) =>
    times_cont_diff_at.times_cont_diff_within_at (times_cont_diff_at_arcsin (mt Or.inl hx) (mt Or.inr hx))

theorem times_cont_diff_at_arcsin_iff {x : ℝ} {n : with_top ℕ} : times_cont_diff_at ℝ n arcsin x ↔ n = 0 ∨ x ≠ -1 ∧ x ≠ 1 := sorry

theorem measurable_arcsin : measurable arcsin :=
  continuous.measurable continuous_arcsin

/-- Inverse of the `cos` function, returns values in the range `0 ≤ arccos x` and `arccos x ≤ π`.
  If the argument is not between `-1` and `1` it defaults to `π / 2` -/
def arccos (x : ℝ) : ℝ :=
  pi / bit0 1 - arcsin x

theorem arccos_eq_pi_div_two_sub_arcsin (x : ℝ) : arccos x = pi / bit0 1 - arcsin x :=
  rfl

theorem arcsin_eq_pi_div_two_sub_arccos (x : ℝ) : arcsin x = pi / bit0 1 - arccos x := sorry

theorem arccos_le_pi (x : ℝ) : arccos x ≤ pi := sorry

theorem arccos_nonneg (x : ℝ) : 0 ≤ arccos x := sorry

theorem cos_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arccos x) = x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (cos (arccos x) = x)) (arccos.equations._eqn_1 x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (cos (pi / bit0 1 - arcsin x) = x)) (cos_pi_div_two_sub (arcsin x))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (sin (arcsin x) = x)) (sin_arcsin hx₁ hx₂))) (Eq.refl x)))

theorem arccos_cos {x : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ pi) : arccos (cos x) = x := sorry

theorem strict_mono_decr_on_arccos : strict_mono_decr_on arccos (set.Icc (-1) 1) :=
  fun (x : ℝ) (hx : x ∈ set.Icc (-1) 1) (y : ℝ) (hy : y ∈ set.Icc (-1) 1) (h : x < y) =>
    sub_lt_sub_left (strict_mono_incr_on_arcsin hx hy h) (pi / bit0 1)

theorem arccos_inj_on : set.inj_on arccos (set.Icc (-1) 1) :=
  strict_mono_decr_on.inj_on strict_mono_decr_on_arccos

theorem arccos_inj {x : ℝ} {y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) : arccos x = arccos y ↔ x = y :=
  set.inj_on.eq_iff arccos_inj_on { left := hx₁, right := hx₂ } { left := hy₁, right := hy₂ }

@[simp] theorem arccos_zero : arccos 0 = pi / bit0 1 := sorry

@[simp] theorem arccos_one : arccos 1 = 0 := sorry

@[simp] theorem arccos_neg_one : arccos (-1) = pi := sorry

@[simp] theorem arccos_eq_zero {x : ℝ} : arccos x = 0 ↔ 1 ≤ x := sorry

@[simp] theorem arccos_eq_pi_div_two {x : ℝ} : arccos x = pi / bit0 1 ↔ x = 0 := sorry

@[simp] theorem arccos_eq_pi {x : ℝ} : arccos x = pi ↔ x ≤ -1 := sorry

theorem arccos_neg (x : ℝ) : arccos (-x) = pi - arccos x := sorry

theorem sin_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arccos x) = sqrt (1 - x ^ bit0 1) := sorry

theorem continuous_arccos : continuous arccos :=
  continuous.sub continuous_const continuous_arcsin

theorem has_deriv_at_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) : has_deriv_at arccos (-(1 / sqrt (1 - x ^ bit0 1))) x :=
  has_deriv_at.const_sub (pi / bit0 1) (has_deriv_at_arcsin h₁ h₂)

theorem times_cont_diff_at_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : with_top ℕ} : times_cont_diff_at ℝ n arccos x :=
  times_cont_diff_at.sub times_cont_diff_at_const (times_cont_diff_at_arcsin h₁ h₂)

theorem has_deriv_within_at_arccos_Ici {x : ℝ} (h : x ≠ -1) : has_deriv_within_at arccos (-(1 / sqrt (1 - x ^ bit0 1))) (set.Ici x) x :=
  has_deriv_within_at.const_sub (pi / bit0 1) (has_deriv_within_at_arcsin_Ici h)

theorem has_deriv_within_at_arccos_Iic {x : ℝ} (h : x ≠ 1) : has_deriv_within_at arccos (-(1 / sqrt (1 - x ^ bit0 1))) (set.Iic x) x :=
  has_deriv_within_at.const_sub (pi / bit0 1) (has_deriv_within_at_arcsin_Iic h)

theorem differentiable_within_at_arccos_Ici {x : ℝ} : differentiable_within_at ℝ arccos (set.Ici x) x ↔ x ≠ -1 :=
  iff.trans (differentiable_within_at_const_sub_iff (pi / bit0 1)) differentiable_within_at_arcsin_Ici

theorem differentiable_within_at_arccos_Iic {x : ℝ} : differentiable_within_at ℝ arccos (set.Iic x) x ↔ x ≠ 1 :=
  iff.trans (differentiable_within_at_const_sub_iff (pi / bit0 1)) differentiable_within_at_arcsin_Iic

theorem differentiable_at_arccos {x : ℝ} : differentiable_at ℝ arccos x ↔ x ≠ -1 ∧ x ≠ 1 :=
  iff.trans (differentiable_at_const_sub_iff (pi / bit0 1)) differentiable_at_arcsin

@[simp] theorem deriv_arccos : deriv arccos = fun (x : ℝ) => -(1 / sqrt (1 - x ^ bit0 1)) := sorry

theorem differentiable_on_arccos : differentiable_on ℝ arccos (insert (-1) (singleton 1)ᶜ) :=
  differentiable_on.const_sub differentiable_on_arcsin (pi / bit0 1)

theorem times_cont_diff_on_arccos {n : with_top ℕ} : times_cont_diff_on ℝ n arccos (insert (-1) (singleton 1)ᶜ) :=
  times_cont_diff_on.sub times_cont_diff_on_const times_cont_diff_on_arcsin

theorem times_cont_diff_at_arccos_iff {x : ℝ} {n : with_top ℕ} : times_cont_diff_at ℝ n arccos x ↔ n = 0 ∨ x ≠ -1 ∧ x ≠ 1 := sorry

theorem measurable_arccos : measurable arccos :=
  continuous.measurable continuous_arccos

@[simp] theorem tan_pi_div_four : tan (pi / bit0 (bit0 1)) = 1 := sorry

@[simp] theorem tan_pi_div_two : tan (pi / bit0 1) = 0 := sorry

theorem tan_pos_of_pos_of_lt_pi_div_two {x : ℝ} (h0x : 0 < x) (hxp : x < pi / bit0 1) : 0 < tan x := sorry

theorem tan_nonneg_of_nonneg_of_le_pi_div_two {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ pi / bit0 1) : 0 ≤ tan x := sorry

theorem tan_neg_of_neg_of_pi_div_two_lt {x : ℝ} (hx0 : x < 0) (hpx : -(pi / bit0 1) < x) : tan x < 0 := sorry

theorem tan_nonpos_of_nonpos_of_neg_pi_div_two_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -(pi / bit0 1) ≤ x) : tan x ≤ 0 := sorry

theorem tan_lt_tan_of_nonneg_of_lt_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y < pi / bit0 1) (hxy : x < y) : tan x < tan y := sorry

theorem tan_lt_tan_of_lt_of_lt_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : -(pi / bit0 1) < x) (hy₂ : y < pi / bit0 1) (hxy : x < y) : tan x < tan y := sorry

theorem strict_mono_incr_on_tan : strict_mono_incr_on tan (set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) :=
  fun (x : ℝ) (hx : x ∈ set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) (y : ℝ)
    (hy : y ∈ set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) => tan_lt_tan_of_lt_of_lt_pi_div_two (and.left hx) (and.right hy)

theorem inj_on_tan : set.inj_on tan (set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) :=
  strict_mono_incr_on.inj_on strict_mono_incr_on_tan

theorem tan_inj_of_lt_of_lt_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : -(pi / bit0 1) < x) (hx₂ : x < pi / bit0 1) (hy₁ : -(pi / bit0 1) < y) (hy₂ : y < pi / bit0 1) (hxy : tan x = tan y) : x = y :=
  inj_on_tan { left := hx₁, right := hx₂ } { left := hy₁, right := hy₂ } hxy

end real


namespace complex


/-- `arg` returns values in the range (-π, π], such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
def arg (x : ℂ) : ℝ :=
  ite (0 ≤ re x) (real.arcsin (im x / abs x))
    (ite (0 ≤ im x) (real.arcsin (im (-x) / abs x) + real.pi) (real.arcsin (im (-x) / abs x) - real.pi))

theorem arg_le_pi (x : ℂ) : arg x ≤ real.pi := sorry

theorem neg_pi_lt_arg (x : ℂ) : -real.pi < arg x := sorry

theorem arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg {x : ℂ} (hxr : re x < 0) (hxi : 0 ≤ im x) : arg x = arg (-x) + real.pi := sorry

theorem arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg {x : ℂ} (hxr : re x < 0) (hxi : im x < 0) : arg x = arg (-x) - real.pi := sorry

@[simp] theorem arg_zero : arg 0 = 0 := sorry

@[simp] theorem arg_one : arg 1 = 0 := sorry

@[simp] theorem arg_neg_one : arg (-1) = real.pi := sorry

@[simp] theorem arg_I : arg I = real.pi / bit0 1 := sorry

@[simp] theorem arg_neg_I : arg (-I) = -(real.pi / bit0 1) := sorry

theorem sin_arg (x : ℂ) : real.sin (arg x) = im x / abs x := sorry

theorem cos_arg {x : ℂ} (hx : x ≠ 0) : real.cos (arg x) = re x / abs x := sorry

theorem tan_arg {x : ℂ} : real.tan (arg x) = im x / re x := sorry

theorem arg_cos_add_sin_mul_I {x : ℝ} (hx₁ : -real.pi < x) (hx₂ : x ≤ real.pi) : arg (cos ↑x + sin ↑x * I) = x := sorry

theorem arg_eq_arg_iff {x : ℂ} {y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) : arg x = arg y ↔ ↑(abs y) / ↑(abs x) * x = y := sorry

theorem arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (↑r * x) = arg x := sorry

theorem ext_abs_arg {x : ℂ} {y : ℂ} (h₁ : abs x = abs y) (h₂ : arg x = arg y) : x = y := sorry

theorem arg_of_real_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg ↑x = 0 := sorry

theorem arg_of_real_of_neg {x : ℝ} (hx : x < 0) : arg ↑x = real.pi := sorry

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0`-/
def log (x : ℂ) : ℂ :=
  ↑(real.log (abs x)) + ↑(arg x) * I

theorem log_re (x : ℂ) : re (log x) = real.log (abs x) := sorry

theorem log_im (x : ℂ) : im (log x) = arg x := sorry

theorem exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x := sorry

theorem range_exp : set.range exp = set_of fun (x : ℂ) => x ≠ 0 := sorry

theorem exp_inj_of_neg_pi_lt_of_le_pi {x : ℂ} {y : ℂ} (hx₁ : -real.pi < im x) (hx₂ : im x ≤ real.pi) (hy₁ : -real.pi < im y) (hy₂ : im y ≤ real.pi) (hxy : exp x = exp y) : x = y := sorry

theorem log_exp {x : ℂ} (hx₁ : -real.pi < im x) (hx₂ : im x ≤ real.pi) : log (exp x) = x := sorry

theorem of_real_log {x : ℝ} (hx : 0 ≤ x) : ↑(real.log x) = log ↑x := sorry

theorem log_of_real_re (x : ℝ) : re (log ↑x) = real.log x := sorry

@[simp] theorem log_zero : log 0 = 0 := sorry

@[simp] theorem log_one : log 1 = 0 := sorry

theorem log_neg_one : log (-1) = ↑real.pi * I := sorry

theorem log_I : log I = ↑real.pi / bit0 1 * I := sorry

theorem log_neg_I : log (-I) = -(↑real.pi / bit0 1) * I := sorry

theorem exists_pow_nat_eq (x : ℂ) {n : ℕ} (hn : 0 < n) : ∃ (z : ℂ), z ^ n = x := sorry

theorem exists_eq_mul_self (x : ℂ) : ∃ (z : ℂ), x = z * z :=
  Exists.dcases_on (exists_pow_nat_eq x zero_lt_two)
    fun (z : ℂ) (h : z ^ bit0 1 = x) => Eq._oldrec (Exists.intro z (pow_two z)) h

theorem two_pi_I_ne_zero : bit0 1 * ↑real.pi * I ≠ 0 := sorry

theorem exp_eq_one_iff {x : ℂ} : exp x = 1 ↔ ∃ (n : ℤ), x = ↑n * (bit0 1 * ↑real.pi * I) := sorry

theorem exp_eq_exp_iff_exp_sub_eq_one {x : ℂ} {y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (exp x = exp y ↔ exp (x - y) = 1)) (exp_sub x y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (exp x = exp y ↔ exp x / exp y = 1)) (propext (div_eq_one_iff_eq (exp_ne_zero y)))))
      (iff.refl (exp x = exp y)))

theorem exp_eq_exp_iff_exists_int {x : ℂ} {y : ℂ} : exp x = exp y ↔ ∃ (n : ℤ), x = y + ↑n * (bit0 1 * ↑real.pi * I) := sorry

@[simp] theorem cos_pi_div_two : cos (↑real.pi / bit0 1) = 0 := sorry

@[simp] theorem sin_pi_div_two : sin (↑real.pi / bit0 1) = 1 := sorry

@[simp] theorem sin_pi : sin ↑real.pi = 0 := sorry

@[simp] theorem cos_pi : cos ↑real.pi = -1 := sorry

@[simp] theorem sin_two_pi : sin (bit0 1 * ↑real.pi) = 0 := sorry

@[simp] theorem cos_two_pi : cos (bit0 1 * ↑real.pi) = 1 := sorry

theorem sin_add_pi (x : ℂ) : sin (x + ↑real.pi) = -sin x := sorry

theorem sin_add_two_pi (x : ℂ) : sin (x + bit0 1 * ↑real.pi) = sin x := sorry

theorem cos_add_two_pi (x : ℂ) : cos (x + bit0 1 * ↑real.pi) = cos x := sorry

theorem sin_pi_sub (x : ℂ) : sin (↑real.pi - x) = sin x := sorry

theorem cos_add_pi (x : ℂ) : cos (x + ↑real.pi) = -cos x := sorry

theorem cos_pi_sub (x : ℂ) : cos (↑real.pi - x) = -cos x := sorry

theorem sin_add_pi_div_two (x : ℂ) : sin (x + ↑real.pi / bit0 1) = cos x := sorry

theorem sin_sub_pi_div_two (x : ℂ) : sin (x - ↑real.pi / bit0 1) = -cos x := sorry

theorem sin_pi_div_two_sub (x : ℂ) : sin (↑real.pi / bit0 1 - x) = cos x := sorry

theorem cos_add_pi_div_two (x : ℂ) : cos (x + ↑real.pi / bit0 1) = -sin x := sorry

theorem cos_sub_pi_div_two (x : ℂ) : cos (x - ↑real.pi / bit0 1) = sin x := sorry

theorem cos_pi_div_two_sub (x : ℂ) : cos (↑real.pi / bit0 1 - x) = sin x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (cos (↑real.pi / bit0 1 - x) = sin x)) (Eq.symm (cos_neg (↑real.pi / bit0 1 - x)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (cos (-(↑real.pi / bit0 1 - x)) = sin x)) (neg_sub (↑real.pi / bit0 1) x)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (cos (x - ↑real.pi / bit0 1) = sin x)) (cos_sub_pi_div_two x))) (Eq.refl (sin x))))

theorem sin_nat_mul_pi (n : ℕ) : sin (↑n * ↑real.pi) = 0 := sorry

theorem sin_int_mul_pi (n : ℤ) : sin (↑n * ↑real.pi) = 0 := sorry

theorem cos_nat_mul_two_pi (n : ℕ) : cos (↑n * (bit0 1 * ↑real.pi)) = 1 := sorry

theorem cos_int_mul_two_pi (n : ℤ) : cos (↑n * (bit0 1 * ↑real.pi)) = 1 := sorry

theorem cos_int_mul_two_pi_add_pi (n : ℤ) : cos (↑n * (bit0 1 * ↑real.pi) + ↑real.pi) = -1 := sorry

theorem exp_pi_mul_I : exp (↑real.pi * I) = -1 := sorry

theorem cos_eq_zero_iff {θ : ℂ} : cos θ = 0 ↔ ∃ (k : ℤ), θ = (bit0 1 * ↑k + 1) * ↑real.pi / bit0 1 := sorry

theorem cos_ne_zero_iff {θ : ℂ} : cos θ ≠ 0 ↔ ∀ (k : ℤ), θ ≠ (bit0 1 * ↑k + 1) * ↑real.pi / bit0 1 := sorry

theorem sin_eq_zero_iff {θ : ℂ} : sin θ = 0 ↔ ∃ (k : ℤ), θ = ↑k * ↑real.pi := sorry

theorem sin_ne_zero_iff {θ : ℂ} : sin θ ≠ 0 ↔ ∀ (k : ℤ), θ ≠ ↑k * ↑real.pi := sorry

theorem sin_eq_zero_iff_cos_eq {z : ℂ} : sin z = 0 ↔ cos z = 1 ∨ cos z = -1 := sorry

theorem tan_eq_zero_iff {θ : ℂ} : tan θ = 0 ↔ ∃ (k : ℤ), θ = ↑k * ↑real.pi / bit0 1 := sorry

theorem tan_ne_zero_iff {θ : ℂ} : tan θ ≠ 0 ↔ ∀ (k : ℤ), θ ≠ ↑k * ↑real.pi / bit0 1 := sorry

theorem tan_int_mul_pi_div_two (n : ℤ) : tan (↑n * ↑real.pi / bit0 1) = 0 :=
  iff.mpr tan_eq_zero_iff (Exists.intro n (id (Eq.refl (↑n * ↑real.pi / bit0 1))))

theorem tan_int_mul_pi (n : ℤ) : tan (↑n * ↑real.pi) = 0 := sorry

theorem cos_eq_cos_iff {x : ℂ} {y : ℂ} : cos x = cos y ↔ ∃ (k : ℤ), y = bit0 1 * ↑k * ↑real.pi + x ∨ y = bit0 1 * ↑k * ↑real.pi - x := sorry

theorem sin_eq_sin_iff {x : ℂ} {y : ℂ} : sin x = sin y ↔ ∃ (k : ℤ), y = bit0 1 * ↑k * ↑real.pi + x ∨ y = (bit0 1 * ↑k + 1) * ↑real.pi - x := sorry

theorem tan_add {x : ℂ} {y : ℂ} (h : ((∀ (k : ℤ), x ≠ (bit0 1 * ↑k + 1) * ↑real.pi / bit0 1) ∧ ∀ (l : ℤ), y ≠ (bit0 1 * ↑l + 1) * ↑real.pi / bit0 1) ∨
  (∃ (k : ℤ), x = (bit0 1 * ↑k + 1) * ↑real.pi / bit0 1) ∧ ∃ (l : ℤ), y = (bit0 1 * ↑l + 1) * ↑real.pi / bit0 1) : tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := sorry

theorem tan_add' {x : ℂ} {y : ℂ} (h : (∀ (k : ℤ), x ≠ (bit0 1 * ↑k + 1) * ↑real.pi / bit0 1) ∧ ∀ (l : ℤ), y ≠ (bit0 1 * ↑l + 1) * ↑real.pi / bit0 1) : tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
  tan_add (Or.inl h)

theorem tan_two_mul {z : ℂ} : tan (bit0 1 * z) = bit0 1 * tan z / (1 - tan z ^ bit0 1) := sorry

theorem tan_add_mul_I {x : ℂ} {y : ℂ} (h : ((∀ (k : ℤ), x ≠ (bit0 1 * ↑k + 1) * ↑real.pi / bit0 1) ∧ ∀ (l : ℤ), y * I ≠ (bit0 1 * ↑l + 1) * ↑real.pi / bit0 1) ∨
  (∃ (k : ℤ), x = (bit0 1 * ↑k + 1) * ↑real.pi / bit0 1) ∧ ∃ (l : ℤ), y * I = (bit0 1 * ↑l + 1) * ↑real.pi / bit0 1) : tan (x + y * I) = (tan x + tanh y * I) / (1 - tan x * tanh y * I) := sorry

theorem tan_eq {z : ℂ} (h : ((∀ (k : ℤ), ↑(re z) ≠ (bit0 1 * ↑k + 1) * ↑real.pi / bit0 1) ∧
    ∀ (l : ℤ), ↑(im z) * I ≠ (bit0 1 * ↑l + 1) * ↑real.pi / bit0 1) ∨
  (∃ (k : ℤ), ↑(re z) = (bit0 1 * ↑k + 1) * ↑real.pi / bit0 1) ∧
    ∃ (l : ℤ), ↑(im z) * I = (bit0 1 * ↑l + 1) * ↑real.pi / bit0 1) : tan z = (tan ↑(re z) + tanh ↑(im z) * I) / (1 - tan ↑(re z) * tanh ↑(im z) * I) := sorry

theorem has_deriv_at_tan {x : ℂ} (h : cos x ≠ 0) : has_deriv_at tan (1 / cos x ^ bit0 1) x := sorry

theorem tendsto_abs_tan_of_cos_eq_zero {x : ℂ} (hx : cos x = 0) : filter.tendsto (fun (x : ℂ) => abs (tan x)) (nhds_within x (singleton xᶜ)) filter.at_top := sorry

theorem tendsto_abs_tan_at_top (k : ℤ) : filter.tendsto (fun (x : ℂ) => abs (tan x))
  (nhds_within ((bit0 1 * ↑k + 1) * ↑real.pi / bit0 1) (singleton ((bit0 1 * ↑k + 1) * ↑real.pi / bit0 1)ᶜ))
  filter.at_top :=
  tendsto_abs_tan_of_cos_eq_zero (iff.mpr cos_eq_zero_iff (Exists.intro k rfl))

@[simp] theorem continuous_at_tan {x : ℂ} : continuous_at tan x ↔ cos x ≠ 0 := sorry

@[simp] theorem differentiable_at_tan {x : ℂ} : differentiable_at ℂ tan x ↔ cos x ≠ 0 :=
  { mp := fun (h : differentiable_at ℂ tan x) => iff.mp continuous_at_tan (differentiable_at.continuous_at h),
    mpr := fun (h : cos x ≠ 0) => has_deriv_at.differentiable_at (has_deriv_at_tan h) }

@[simp] theorem deriv_tan (x : ℂ) : deriv tan x = 1 / cos x ^ bit0 1 := sorry

theorem continuous_on_tan : continuous_on tan (set_of fun (x : ℂ) => cos x ≠ 0) :=
  continuous_on.div continuous_on_sin continuous_on_cos fun (x : ℂ) => id

theorem continuous_tan : continuous fun (x : ↥(set_of fun (x : ℂ) => cos x ≠ 0)) => tan ↑x :=
  iff.mp continuous_on_iff_continuous_restrict continuous_on_tan

@[simp] theorem times_cont_diff_at_tan {x : ℂ} {n : with_top ℕ} : times_cont_diff_at ℂ n tan x ↔ cos x ≠ 0 := sorry

theorem cos_eq_iff_quadratic {z : ℂ} {w : ℂ} : cos z = w ↔ exp (z * I) ^ bit0 1 - bit0 1 * w * exp (z * I) + 1 = 0 := sorry

theorem cos_surjective : function.surjective cos := sorry

@[simp] theorem range_cos : set.range cos = set.univ :=
  function.surjective.range_eq cos_surjective

theorem sin_surjective : function.surjective sin := sorry

@[simp] theorem range_sin : set.range sin = set.univ :=
  function.surjective.range_eq sin_surjective

end complex


/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
theorem chebyshev₁_complex_cos (θ : ℂ) (n : ℕ) : polynomial.eval (complex.cos θ) (polynomial.chebyshev₁ ℂ n) = complex.cos (↑n * θ) := sorry

/-- `cos (n * θ)` is equal to the `n`-th Chebyshev polynomial of the first kind evaluated
on `cos θ`. -/
theorem cos_nat_mul (n : ℕ) (θ : ℂ) : complex.cos (↑n * θ) = polynomial.eval (complex.cos θ) (polynomial.chebyshev₁ ℂ n) :=
  Eq.symm (chebyshev₁_complex_cos θ n)

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n+1) * θ) / sin θ`. -/
theorem chebyshev₂_complex_cos (θ : ℂ) (n : ℕ) : polynomial.eval (complex.cos θ) (polynomial.chebyshev₂ ℂ n) * complex.sin θ = complex.sin ((↑n + 1) * θ) := sorry

/-- `sin ((n + 1) * θ)` is equal to `sin θ` multiplied with the `n`-th Chebyshev polynomial of the
second kind evaluated on `cos θ`. -/
theorem sin_nat_succ_mul (n : ℕ) (θ : ℂ) : complex.sin ((↑n + 1) * θ) = polynomial.eval (complex.cos θ) (polynomial.chebyshev₂ ℂ n) * complex.sin θ :=
  Eq.symm (chebyshev₂_complex_cos θ n)

namespace real


theorem tan_add {x : ℝ} {y : ℝ} (h : ((∀ (k : ℤ), x ≠ (bit0 1 * ↑k + 1) * pi / bit0 1) ∧ ∀ (l : ℤ), y ≠ (bit0 1 * ↑l + 1) * pi / bit0 1) ∨
  (∃ (k : ℤ), x = (bit0 1 * ↑k + 1) * pi / bit0 1) ∧ ∃ (l : ℤ), y = (bit0 1 * ↑l + 1) * pi / bit0 1) : tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := sorry

theorem tan_add' {x : ℝ} {y : ℝ} (h : (∀ (k : ℤ), x ≠ (bit0 1 * ↑k + 1) * pi / bit0 1) ∧ ∀ (l : ℤ), y ≠ (bit0 1 * ↑l + 1) * pi / bit0 1) : tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
  tan_add (Or.inl h)

theorem tan_two_mul {x : ℝ} : tan (bit0 1 * x) = bit0 1 * tan x / (1 - tan x ^ bit0 1) := sorry

theorem cos_eq_zero_iff {θ : ℝ} : cos θ = 0 ↔ ∃ (k : ℤ), θ = (bit0 1 * ↑k + 1) * pi / bit0 1 := sorry

theorem cos_ne_zero_iff {θ : ℝ} : cos θ ≠ 0 ↔ ∀ (k : ℤ), θ ≠ (bit0 1 * ↑k + 1) * pi / bit0 1 := sorry

theorem tan_ne_zero_iff {θ : ℝ} : tan θ ≠ 0 ↔ ∀ (k : ℤ), θ ≠ ↑k * pi / bit0 1 := sorry

theorem tan_eq_zero_iff {θ : ℝ} : tan θ = 0 ↔ ∃ (k : ℤ), θ = ↑k * pi / bit0 1 := sorry

theorem tan_int_mul_pi_div_two (n : ℤ) : tan (↑n * pi / bit0 1) = 0 :=
  iff.mpr tan_eq_zero_iff (Exists.intro n (id (Eq.refl (↑n * pi / bit0 1))))

theorem tan_int_mul_pi (n : ℤ) : tan (↑n * pi) = 0 := sorry

theorem cos_eq_cos_iff {x : ℝ} {y : ℝ} : cos x = cos y ↔ ∃ (k : ℤ), y = bit0 1 * ↑k * pi + x ∨ y = bit0 1 * ↑k * pi - x := sorry

theorem sin_eq_sin_iff {x : ℝ} {y : ℝ} : sin x = sin y ↔ ∃ (k : ℤ), y = bit0 1 * ↑k * pi + x ∨ y = (bit0 1 * ↑k + 1) * pi - x := sorry

theorem has_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) : has_deriv_at tan (1 / cos x ^ bit0 1) x := sorry

theorem tendsto_abs_tan_of_cos_eq_zero {x : ℝ} (hx : cos x = 0) : filter.tendsto (fun (x : ℝ) => abs (tan x)) (nhds_within x (singleton xᶜ)) filter.at_top := sorry

theorem tendsto_abs_tan_at_top (k : ℤ) : filter.tendsto (fun (x : ℝ) => abs (tan x))
  (nhds_within ((bit0 1 * ↑k + 1) * pi / bit0 1) (singleton ((bit0 1 * ↑k + 1) * pi / bit0 1)ᶜ)) filter.at_top :=
  tendsto_abs_tan_of_cos_eq_zero (iff.mpr cos_eq_zero_iff (Exists.intro k rfl))

theorem continuous_at_tan {x : ℝ} : continuous_at tan x ↔ cos x ≠ 0 := sorry

theorem differentiable_at_tan {x : ℝ} : differentiable_at ℝ tan x ↔ cos x ≠ 0 :=
  { mp := fun (h : differentiable_at ℝ tan x) => iff.mp continuous_at_tan (differentiable_at.continuous_at h),
    mpr := fun (h : cos x ≠ 0) => has_deriv_at.differentiable_at (has_deriv_at_tan h) }

@[simp] theorem deriv_tan (x : ℝ) : deriv tan x = 1 / cos x ^ bit0 1 := sorry

@[simp] theorem times_cont_diff_at_tan {n : with_top ℕ} {x : ℝ} : times_cont_diff_at ℝ n tan x ↔ cos x ≠ 0 := sorry

theorem continuous_on_tan : continuous_on tan (set_of fun (x : ℝ) => cos x ≠ 0) :=
  fun (x : ℝ) (hx : x ∈ set_of fun (x : ℝ) => cos x ≠ 0) =>
    continuous_at.continuous_within_at (iff.mpr continuous_at_tan hx)

theorem has_deriv_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) : has_deriv_at tan (1 / cos x ^ bit0 1) x :=
  has_deriv_at_tan (has_lt.lt.ne' (cos_pos_of_mem_Ioo h))

theorem differentiable_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) : differentiable_at ℝ tan x :=
  has_deriv_at.differentiable_at (has_deriv_at_tan_of_mem_Ioo h)

theorem continuous_on_tan_Ioo : continuous_on tan (set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) :=
  fun (x : ℝ) (hx : x ∈ set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) =>
    continuous_at.continuous_within_at (differentiable_at.continuous_at (differentiable_at_tan_of_mem_Ioo hx))

theorem tendsto_sin_pi_div_two : filter.tendsto sin (nhds_within (pi / bit0 1) (set.Iio (pi / bit0 1))) (nhds 1) := sorry

theorem tendsto_cos_pi_div_two : filter.tendsto cos (nhds_within (pi / bit0 1) (set.Iio (pi / bit0 1))) (nhds_within 0 (set.Ioi 0)) := sorry

theorem tendsto_tan_pi_div_two : filter.tendsto tan (nhds_within (pi / bit0 1) (set.Iio (pi / bit0 1))) filter.at_top := sorry

theorem tendsto_sin_neg_pi_div_two : filter.tendsto sin (nhds_within (-(pi / bit0 1)) (set.Ioi (-(pi / bit0 1)))) (nhds (-1)) := sorry

theorem tendsto_cos_neg_pi_div_two : filter.tendsto cos (nhds_within (-(pi / bit0 1)) (set.Ioi (-(pi / bit0 1)))) (nhds_within 0 (set.Ioi 0)) := sorry

theorem tendsto_tan_neg_pi_div_two : filter.tendsto tan (nhds_within (-(pi / bit0 1)) (set.Ioi (-(pi / bit0 1)))) filter.at_bot := sorry

theorem surj_on_tan : set.surj_on tan (set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) set.univ := sorry

theorem tan_surjective : function.surjective tan :=
  fun (x : ℝ) => set.surj_on.subset_range surj_on_tan trivial

theorem image_tan_Ioo : tan '' set.Ioo (-(pi / bit0 1)) (pi / bit0 1) = set.univ :=
  iff.mp set.univ_subset_iff surj_on_tan

/-- `real.tan` as an `order_iso` between `(-(π / 2), π / 2)` and `ℝ`. -/
def tan_order_iso : ↥(set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) ≃o ℝ :=
  order_iso.trans (strict_mono_incr_on.order_iso tan (set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) strict_mono_incr_on_tan)
    (order_iso.trans (order_iso.set_congr (tan '' set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) set.univ image_tan_Ioo)
      order_iso.set.univ)

/-- Inverse of the `tan` function, returns values in the range `-π / 2 < arctan x` and
`arctan x < π / 2` -/
def arctan (x : ℝ) : ℝ :=
  ↑(coe_fn (order_iso.symm tan_order_iso) x)

@[simp] theorem tan_arctan (x : ℝ) : tan (arctan x) = x :=
  order_iso.apply_symm_apply tan_order_iso x

theorem arctan_mem_Ioo (x : ℝ) : arctan x ∈ set.Ioo (-(pi / bit0 1)) (pi / bit0 1) :=
  subtype.coe_prop (coe_fn (order_iso.symm tan_order_iso) x)

theorem arctan_tan {x : ℝ} (hx₁ : -(pi / bit0 1) < x) (hx₂ : x < pi / bit0 1) : arctan (tan x) = x :=
  iff.mp subtype.ext_iff
    (order_iso.symm_apply_apply tan_order_iso { val := x, property := { left := hx₁, right := hx₂ } })

theorem cos_arctan_pos (x : ℝ) : 0 < cos (arctan x) :=
  cos_pos_of_mem_Ioo (arctan_mem_Ioo x)

theorem cos_sq_arctan (x : ℝ) : cos (arctan x) ^ bit0 1 = 1 / (1 + x ^ bit0 1) := sorry

theorem sin_arctan (x : ℝ) : sin (arctan x) = x / sqrt (1 + x ^ bit0 1) := sorry

theorem cos_arctan (x : ℝ) : cos (arctan x) = 1 / sqrt (1 + x ^ bit0 1) := sorry

theorem arctan_lt_pi_div_two (x : ℝ) : arctan x < pi / bit0 1 :=
  and.right (arctan_mem_Ioo x)

theorem neg_pi_div_two_lt_arctan (x : ℝ) : -(pi / bit0 1) < arctan x :=
  and.left (arctan_mem_Ioo x)

theorem arctan_eq_arcsin (x : ℝ) : arctan x = arcsin (x / sqrt (1 + x ^ bit0 1)) :=
  Eq.symm (arcsin_eq_of_sin_eq (sin_arctan x) (set.mem_Icc_of_Ioo (arctan_mem_Ioo x)))

@[simp] theorem arctan_zero : arctan 0 = 0 := sorry

theorem arctan_eq_of_tan_eq {x : ℝ} {y : ℝ} (h : tan x = y) (hx : x ∈ set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) : arctan y = x :=
  inj_on_tan (arctan_mem_Ioo y) hx
    (eq.mpr (id (Eq._oldrec (Eq.refl (tan (arctan y) = tan x)) (tan_arctan y)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (y = tan x)) h)) (Eq.refl y)))

@[simp] theorem arctan_one : arctan 1 = pi / bit0 (bit0 1) := sorry

@[simp] theorem arctan_neg (x : ℝ) : arctan (-x) = -arctan x := sorry

theorem continuous_arctan : continuous arctan :=
  continuous.comp continuous_subtype_coe (homeomorph.continuous_inv_fun (order_iso.to_homeomorph tan_order_iso))

theorem continuous_at_arctan {x : ℝ} : continuous_at arctan x :=
  continuous.continuous_at continuous_arctan

/-- `real.tan` as a `local_homeomorph` between `(-(π / 2), π / 2)` and the whole line. -/
def tan_local_homeomorph : local_homeomorph ℝ ℝ :=
  local_homeomorph.mk
    (local_equiv.mk tan arctan (set.Ioo (-(pi / bit0 1)) (pi / bit0 1)) set.univ sorry sorry sorry sorry) sorry sorry
    continuous_on_tan_Ioo sorry

@[simp] theorem coe_tan_local_homeomorph : ⇑tan_local_homeomorph = tan :=
  rfl

@[simp] theorem coe_tan_local_homeomorph_symm : ⇑(local_homeomorph.symm tan_local_homeomorph) = arctan :=
  rfl

theorem has_deriv_at_arctan (x : ℝ) : has_deriv_at arctan (1 / (1 + x ^ bit0 1)) x := sorry

theorem differentiable_at_arctan (x : ℝ) : differentiable_at ℝ arctan x :=
  has_deriv_at.differentiable_at (has_deriv_at_arctan x)

theorem differentiable_arctan : differentiable ℝ arctan :=
  differentiable_at_arctan

@[simp] theorem deriv_arctan : deriv arctan = fun (x : ℝ) => 1 / (1 + x ^ bit0 1) :=
  funext fun (x : ℝ) => has_deriv_at.deriv (has_deriv_at_arctan x)

theorem times_cont_diff_arctan {n : with_top ℕ} : times_cont_diff ℝ n arctan := sorry

theorem measurable_arctan : measurable arctan :=
  continuous.measurable continuous_arctan

end real


/-!
### Lemmas for derivatives of the composition of `real.arctan` with a differentiable function

In this section we register lemmas for the derivatives of the composition of `real.arctan` with a
differentiable function, for standalone use and use with `simp`. -/

theorem measurable.arctan {α : Type u_1} [measurable_space α] {f : α → ℝ} (hf : measurable f) : measurable fun (x : α) => real.arctan (f x) :=
  measurable.comp real.measurable_arctan hf

theorem has_deriv_at.arctan {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hf : has_deriv_at f f' x) : has_deriv_at (fun (x : ℝ) => real.arctan (f x)) (1 / (1 + f x ^ bit0 1) * f') x :=
  has_deriv_at.comp x (real.has_deriv_at_arctan (f x)) hf

theorem has_deriv_within_at.arctan {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} {s : set ℝ} (hf : has_deriv_within_at f f' s x) : has_deriv_within_at (fun (x : ℝ) => real.arctan (f x)) (1 / (1 + f x ^ bit0 1) * f') s x :=
  has_deriv_at.comp_has_deriv_within_at x (real.has_deriv_at_arctan (f x)) hf

theorem deriv_within_arctan {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} (hf : differentiable_within_at ℝ f s x) (hxs : unique_diff_within_at ℝ s x) : deriv_within (fun (x : ℝ) => real.arctan (f x)) s x = 1 / (1 + f x ^ bit0 1) * deriv_within f s x :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.arctan (differentiable_within_at.has_deriv_within_at hf)) hxs

@[simp] theorem deriv_arctan {f : ℝ → ℝ} {x : ℝ} (hc : differentiable_at ℝ f x) : deriv (fun (x : ℝ) => real.arctan (f x)) x = 1 / (1 + f x ^ bit0 1) * deriv f x :=
  has_deriv_at.deriv (has_deriv_at.arctan (differentiable_at.has_deriv_at hc))

theorem has_fderiv_at.arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : continuous_linear_map ℝ E ℝ} {x : E} (hf : has_fderiv_at f f' x) : has_fderiv_at (fun (x : E) => real.arctan (f x)) ((1 / (1 + f x ^ bit0 1)) • f') x :=
  has_deriv_at.comp_has_fderiv_at x (real.has_deriv_at_arctan (f x)) hf

theorem has_fderiv_within_at.arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : continuous_linear_map ℝ E ℝ} {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) : has_fderiv_within_at (fun (x : E) => real.arctan (f x)) ((1 / (1 + f x ^ bit0 1)) • f') s x :=
  has_deriv_at.comp_has_fderiv_within_at x (real.has_deriv_at_arctan (f x)) hf

theorem fderiv_within_arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) (hxs : unique_diff_within_at ℝ s x) : fderiv_within ℝ (fun (x : E) => real.arctan (f x)) s x = (1 / (1 + f x ^ bit0 1)) • fderiv_within ℝ f s x :=
  has_fderiv_within_at.fderiv_within (has_fderiv_within_at.arctan (differentiable_within_at.has_fderiv_within_at hf)) hxs

@[simp] theorem fderiv_arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} (hc : differentiable_at ℝ f x) : fderiv ℝ (fun (x : E) => real.arctan (f x)) x = (1 / (1 + f x ^ bit0 1)) • fderiv ℝ f x :=
  has_fderiv_at.fderiv (has_fderiv_at.arctan (differentiable_at.has_fderiv_at hc))

theorem differentiable_within_at.arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) : differentiable_within_at ℝ (fun (x : E) => real.arctan (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.arctan (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} (hc : differentiable_at ℝ f x) : differentiable_at ℝ (fun (x : E) => real.arctan (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.arctan (differentiable_at.has_fderiv_at hc))

theorem differentiable_on.arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} (hc : differentiable_on ℝ f s) : differentiable_on ℝ (fun (x : E) => real.arctan (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.arctan (hc x h)

@[simp] theorem differentiable.arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} (hc : differentiable ℝ f) : differentiable ℝ fun (x : E) => real.arctan (f x) :=
  fun (x : E) => differentiable_at.arctan (hc x)

theorem times_cont_diff_at.arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {n : with_top ℕ} (h : times_cont_diff_at ℝ n f x) : times_cont_diff_at ℝ n (fun (x : E) => real.arctan (f x)) x :=
  times_cont_diff_at.comp x (times_cont_diff.times_cont_diff_at real.times_cont_diff_arctan) h

theorem times_cont_diff.arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {n : with_top ℕ} (h : times_cont_diff ℝ n f) : times_cont_diff ℝ n fun (x : E) => real.arctan (f x) :=
  times_cont_diff.comp real.times_cont_diff_arctan h

theorem times_cont_diff_within_at.arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {s : set E} {n : with_top ℕ} (h : times_cont_diff_within_at ℝ n f s x) : times_cont_diff_within_at ℝ n (fun (x : E) => real.arctan (f x)) s x :=
  times_cont_diff.comp_times_cont_diff_within_at real.times_cont_diff_arctan h

theorem times_cont_diff_on.arctan {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} {n : with_top ℕ} (h : times_cont_diff_on ℝ n f s) : times_cont_diff_on ℝ n (fun (x : E) => real.arctan (f x)) s :=
  times_cont_diff.comp_times_cont_diff_on real.times_cont_diff_arctan h

