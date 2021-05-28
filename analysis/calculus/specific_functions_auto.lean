/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.calculus.extend_deriv
import Mathlib.analysis.calculus.iterated_deriv
import Mathlib.analysis.special_functions.exp_log
import Mathlib.topology.algebra.polynomial
import PostPort

namespace Mathlib

/-!
# Smoothness of specific functions

The real function `exp_neg_inv_glue` given by `x ↦ exp (-1/x)` for `x > 0` and `0`
for `x ≤ 0` is a basic building block to construct smooth partitions of unity. We prove that it
is `C^∞` in `exp_neg_inv_glue.smooth`.
-/

/-- `exp_neg_inv_glue` is the real function given by `x ↦ exp (-1/x)` for `x > 0` and `0`
for `x ≤ 0`. is a basic building block to construct smooth partitions of unity. Its main property
is that it vanishes for `x ≤ 0`, it is positive for `x > 0`, and the junction between the two
behaviors is flat enough to retain smoothness. The fact that this function is `C^∞` is proved in
`exp_neg_inv_glue.smooth`. -/
def exp_neg_inv_glue (x : ℝ) : ℝ :=
  ite (x ≤ 0) 0 (real.exp (-(x⁻¹)))

namespace exp_neg_inv_glue


/-- Our goal is to prove that `exp_neg_inv_glue` is `C^∞`. For this, we compute its successive
derivatives for `x > 0`. The `n`-th derivative is of the form `P_aux n (x) exp(-1/x) / x^(2 n)`,
where `P_aux n` is computed inductively. -/
def P_aux : ℕ → polynomial ℝ :=
  sorry

/-- Formula for the `n`-th derivative of `exp_neg_inv_glue`, as an auxiliary function `f_aux`. -/
def f_aux (n : ℕ) (x : ℝ) : ℝ :=
  ite (x ≤ 0) 0 (polynomial.eval x (P_aux n) * real.exp (-(x⁻¹)) / x ^ (bit0 1 * n))

/-- The `0`-th auxiliary function `f_aux 0` coincides with `exp_neg_inv_glue`, by definition. -/
theorem f_aux_zero_eq : f_aux 0 = exp_neg_inv_glue := sorry

/-- For positive values, the derivative of the `n`-th auxiliary function `f_aux n`
(given in this statement in unfolded form) is the `n+1`-th auxiliary function, since
the polynomial `P_aux (n+1)` was chosen precisely to ensure this. -/
theorem f_aux_deriv (n : ℕ) (x : ℝ) (hx : x ≠ 0) : has_deriv_at (fun (x : ℝ) => polynomial.eval x (P_aux n) * real.exp (-(x⁻¹)) / x ^ (bit0 1 * n))
  (polynomial.eval x (P_aux (n + 1)) * real.exp (-(x⁻¹)) / x ^ (bit0 1 * (n + 1))) x := sorry

/-- For positive values, the derivative of the `n`-th auxiliary function `f_aux n`
is the `n+1`-th auxiliary function. -/
theorem f_aux_deriv_pos (n : ℕ) (x : ℝ) (hx : 0 < x) : has_deriv_at (f_aux n) (polynomial.eval x (P_aux (n + 1)) * real.exp (-(x⁻¹)) / x ^ (bit0 1 * (n + 1))) x := sorry

/-- To get differentiability at `0` of the auxiliary functions, we need to know that their limit
is `0`, to be able to apply general differentiability extension theorems. This limit is checked in
this lemma. -/
theorem f_aux_limit (n : ℕ) : filter.tendsto (fun (x : ℝ) => polynomial.eval x (P_aux n) * real.exp (-(x⁻¹)) / x ^ (bit0 1 * n))
  (nhds_within 0 (set.Ioi 0)) (nhds 0) := sorry

/-- Deduce from the limiting behavior at `0` of its derivative and general differentiability
extension theorems that the auxiliary function `f_aux n` is differentiable at `0`,
with derivative `0`. -/
theorem f_aux_deriv_zero (n : ℕ) : has_deriv_at (f_aux n) 0 0 := sorry

/-- At every point, the auxiliary function `f_aux n` has a derivative which is
equal to `f_aux (n+1)`. -/
theorem f_aux_has_deriv_at (n : ℕ) (x : ℝ) : has_deriv_at (f_aux n) (f_aux (n + 1) x) x := sorry

/-- The successive derivatives of the auxiliary function `f_aux 0` are the
functions `f_aux n`, by induction. -/
theorem f_aux_iterated_deriv (n : ℕ) : iterated_deriv n (f_aux 0) = f_aux n := sorry

/-- The function `exp_neg_inv_glue` is smooth. -/
theorem smooth : times_cont_diff ℝ ⊤ exp_neg_inv_glue := sorry

/-- The function `exp_neg_inv_glue` vanishes on `(-∞, 0]`. -/
theorem zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : exp_neg_inv_glue x = 0 := sorry

/-- The function `exp_neg_inv_glue` is positive on `(0, +∞)`. -/
theorem pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < exp_neg_inv_glue x := sorry

/-- The function exp_neg_inv_glue` is nonnegative. -/
theorem nonneg (x : ℝ) : 0 ≤ exp_neg_inv_glue x :=
  or.dcases_on (le_or_gt x 0) (fun (h : x ≤ 0) => ge_of_eq (zero_of_nonpos h)) fun (h : x > 0) => le_of_lt (pos_of_pos h)

