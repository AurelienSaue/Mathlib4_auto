/-
Copyright (c) 2020 James Arthur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Chris Hughes, Shing Tak Lam
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.special_functions.trigonometric
import PostPort

namespace Mathlib

/-!
# Inverse of the sinh function

In this file we prove that sinh is bijective and hence has an
inverse, arsinh.

## Main Results

- `sinh_injective`: The proof that `sinh` is injective
- `sinh_surjective`: The proof that `sinh` is surjective
- `sinh_bijective`: The proof `sinh` is bijective
- `arsinh`: The inverse function of `sinh`

## Tags

arsinh, arcsinh, argsinh, asinh, sinh injective, sinh bijective, sinh surjective
-/

namespace real


/-- `arsinh` is defined using a logarithm, `arsinh x = log (x + sqrt(1 + x^2))`. -/
def arsinh (x : ℝ) : ℝ :=
  log (x + sqrt (1 + x ^ bit0 1))

/-- `sinh` is injective, `∀ a b, sinh a = sinh b → a = b`. -/
theorem sinh_injective : function.injective sinh :=
  strict_mono.injective sinh_strict_mono

/-- `arsinh` is the right inverse of `sinh`. -/
theorem sinh_arsinh (x : ℝ) : sinh (arsinh x) = x := sorry

/-- `sinh` is surjective, `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b`. -/
theorem sinh_surjective : function.surjective sinh :=
  function.left_inverse.surjective sinh_arsinh

/-- `sinh` is bijective, both injective and surjective. -/
theorem sinh_bijective : function.bijective sinh :=
  { left := sinh_injective, right := sinh_surjective }

/-- A rearrangement and `sqrt` of `real.cosh_sq_sub_sinh_sq`. -/
theorem sqrt_one_add_sinh_sq (x : ℝ) : sqrt (1 + sinh x ^ bit0 1) = cosh x := sorry

/-- `arsinh` is the left inverse of `sinh`. -/
theorem arsinh_sinh (x : ℝ) : arsinh (sinh x) = x :=
  function.right_inverse_of_injective_of_left_inverse sinh_injective sinh_arsinh x

