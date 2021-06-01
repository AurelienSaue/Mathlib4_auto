/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.operator_norm
import Mathlib.analysis.normed_space.extend
import Mathlib.analysis.convex.cone
import Mathlib.data.complex.is_R_or_C
import Mathlib.PostPort

universes u_1 u_2 u v 

namespace Mathlib

/-!
# Hahn-Banach theorem

In this file we prove a version of Hahn-Banach theorem for continuous linear
functions on normed spaces over `ℝ` and `ℂ`.

In order to state and prove its corollaries uniformly, we prove the statements for a field `𝕜`
satisfying `is_R_or_C 𝕜`.

In this setting, `exists_dual_vector` states that, for any nonzero `x`, there exists a continuous
linear form `g` of norm `1` with `g x = ∥x∥` (where the norm has to be interpreted as an element
of `𝕜`).

-/

/--
The norm of `x` as an element of `𝕜` (a normed algebra over `ℝ`). This is needed in particular to
state equalities of the form `g x = norm' 𝕜 x` when `g` is a linear function.

For the concrete cases of `ℝ` and `𝕜`, this is just `∥x∥` and `↑∥x∥`, respectively.
-/
def norm' (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜] {E : Type u_2}
    [normed_group E] (x : E) : 𝕜 :=
  coe_fn (algebra_map ℝ 𝕜) (norm x)

theorem norm'_def (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜] {E : Type u_2}
    [normed_group E] (x : E) : norm' 𝕜 x = coe_fn (algebra_map ℝ 𝕜) (norm x) :=
  rfl

theorem norm_norm' (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜] (A : Type u_2)
    [normed_group A] (x : A) : norm (norm' 𝕜 x) = norm x :=
  sorry

namespace real


/-- Hahn-Banach theorem for continuous linear functions over `ℝ`. -/
theorem exists_extension_norm_eq {E : Type u_1} [normed_group E] [normed_space ℝ E]
    (p : subspace ℝ E) (f : continuous_linear_map ℝ ↥p ℝ) :
    ∃ (g : continuous_linear_map ℝ E ℝ), (∀ (x : ↥p), coe_fn g ↑x = coe_fn f x) ∧ norm g = norm f :=
  sorry

end real


/-- Hahn-Banach theorem for continuous linear functions over `𝕜` satisyfing `is_R_or_C 𝕜`. -/
theorem exists_extension_norm_eq {𝕜 : Type u_1} [is_R_or_C 𝕜] {F : Type u_2} [normed_group F]
    [normed_space 𝕜 F] (p : subspace 𝕜 F) (f : continuous_linear_map 𝕜 (↥p) 𝕜) :
    ∃ (g : continuous_linear_map 𝕜 F 𝕜), (∀ (x : ↥p), coe_fn g ↑x = coe_fn f x) ∧ norm g = norm f :=
  sorry

theorem coord_norm' {𝕜 : Type v} [is_R_or_C 𝕜] {E : Type u} [normed_group E] [normed_space 𝕜 E]
    (x : E) (h : x ≠ 0) : norm (norm' 𝕜 x • continuous_linear_equiv.coord 𝕜 x h) = 1 :=
  sorry

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm `1`, whose value on `x` is `∥x∥`. -/
theorem exists_dual_vector {𝕜 : Type v} [is_R_or_C 𝕜] {E : Type u} [normed_group E]
    [normed_space 𝕜 E] (x : E) (h : x ≠ 0) :
    ∃ (g : continuous_linear_map 𝕜 E 𝕜), norm g = 1 ∧ coe_fn g x = norm' 𝕜 x :=
  sorry

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, and choosing
    the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' {𝕜 : Type v} [is_R_or_C 𝕜] {E : Type u} [normed_group E]
    [normed_space 𝕜 E] [nontrivial E] (x : E) :
    ∃ (g : continuous_linear_map 𝕜 E 𝕜), norm g = 1 ∧ coe_fn g x = norm' 𝕜 x :=
  sorry

end Mathlib