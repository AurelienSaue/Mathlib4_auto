/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.calculus.times_cont_diff
import Mathlib.analysis.complex.basic
import Mathlib.PostPort

namespace Mathlib

/-! # Real differentiability of complex-differentiable functions

`has_deriv_at.real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.
-/

/-! ### Differentiability of the restriction to `ℝ` of complex functions -/

/-- If a complex function is differentiable at a real point, then the induced real function is also
differentiable at this point, with a derivative equal to the real part of the complex derivative. -/
theorem has_deriv_at.real_of_complex {e : ℂ → ℂ} {e' : ℂ} {z : ℝ} (h : has_deriv_at e e' ↑z) : has_deriv_at (fun (x : ℝ) => complex.re (e ↑x)) (complex.re e') z := sorry

theorem times_cont_diff_at.real_of_complex {e : ℂ → ℂ} {z : ℝ} {n : with_top ℕ} (h : times_cont_diff_at ℂ n e ↑z) : times_cont_diff_at ℝ n (fun (x : ℝ) => complex.re (e ↑x)) z := sorry

theorem times_cont_diff.real_of_complex {e : ℂ → ℂ} {n : with_top ℕ} (h : times_cont_diff ℂ n e) : times_cont_diff ℝ n fun (x : ℝ) => complex.re (e ↑x) :=
  iff.mpr times_cont_diff_iff_times_cont_diff_at
    fun (x : ℝ) => times_cont_diff_at.real_of_complex (times_cont_diff.times_cont_diff_at h)

