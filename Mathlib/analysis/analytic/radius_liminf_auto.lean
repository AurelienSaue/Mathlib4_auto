/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.analytic.basic
import Mathlib.analysis.special_functions.pow
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Representation of `formal_multilinear_series.radius` as a `liminf`

In this file we prove that the radius of convergence of a `formal_multilinear_series` is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{∥p n∥}}$. This lemma can't go to `basic.lean` because this
would create a circular dependency once we redefine `exp` using `formal_multilinear_series`.
-/

namespace formal_multilinear_series


/-- The radius of a formal multilinear series is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{∥p n∥}}$. The actual statement uses `ℝ≥0` and some
coercions. -/
theorem radius_eq_liminf {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (p : formal_multilinear_series 𝕜 E F) :
    radius p = filter.liminf filter.at_top fun (n : ℕ) => 1 / ↑(nnnorm (p n) ^ (1 / ↑n)) :=
  sorry

end Mathlib