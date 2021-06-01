/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.complex.basic
import Mathlib.analysis.normed_space.operator_norm
import Mathlib.data.complex.is_R_or_C
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Extending a continuous `ℝ`-linear map to a continuous `𝕜`-linear map

In this file we provide a way to extend a continuous `ℝ`-linear map to a continuous `𝕜`-linear map
in a way that bounds the norm by the norm of the original map, when `𝕜` is either `ℝ` (the
extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `is_R_or_C 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`Re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `Im (fc x) = -Re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.
-/

/-- Extend `fr : F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜` in a way that will also be continuous and have its norm
bounded by `∥fr∥` if `fr` is continuous. -/
def linear_map.extend_to_𝕜 {𝕜 : Type u_1} [is_R_or_C 𝕜] {F : Type u_2} [normed_group F]
    [normed_space 𝕜 F] (fr : linear_map ℝ (restrict_scalars ℝ 𝕜 F) ℝ) : linear_map 𝕜 F 𝕜 :=
  let fc : F → 𝕜 := fun (x : F) => ↑(coe_fn fr x) - is_R_or_C.I * ↑(coe_fn fr (is_R_or_C.I • x));
  linear_map.mk fc sorry sorry

/-- The norm of the extension is bounded by `∥fr∥`. -/
theorem norm_bound {𝕜 : Type u_1} [is_R_or_C 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F]
    (fr : continuous_linear_map ℝ (restrict_scalars ℝ 𝕜 F) ℝ) (x : F) :
    norm (coe_fn (linear_map.extend_to_𝕜 (continuous_linear_map.to_linear_map fr)) x) ≤
        norm fr * norm x :=
  sorry

/-- Extend `fr : F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
def continuous_linear_map.extend_to_𝕜 {𝕜 : Type u_1} [is_R_or_C 𝕜] {F : Type u_2} [normed_group F]
    [normed_space 𝕜 F] (fr : continuous_linear_map ℝ (restrict_scalars ℝ 𝕜 F) ℝ) :
    continuous_linear_map 𝕜 F 𝕜 :=
  linear_map.mk_continuous (linear_map.extend_to_𝕜 (continuous_linear_map.to_linear_map fr))
    (norm fr) (norm_bound fr)

end Mathlib