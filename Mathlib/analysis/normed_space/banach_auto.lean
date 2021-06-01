/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.metric_space.baire
import Mathlib.analysis.normed_space.operator_norm
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Banach open mapping theorem

This file contains the Banach open mapping theorem, i.e., the fact that a bijective
bounded linear map between Banach spaces has a bounded inverse.
-/

/--
First step of the proof of the Banach open mapping theorem (using completeness of `F`):
by Baire's theorem, there exists a ball in `E` whose image closure has nonempty interior.
Rescaling everything, it follows that any `y ∈ F` is arbitrarily well approached by
images of elements of norm at most `C * ∥y∥`.
For further use, we will only need such an element whose image
is within distance `∥y∥/2` of `y`, to apply an iterative process. -/
theorem exists_approx_preimage_norm_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) [complete_space F] (surj : function.surjective ⇑f) :
    ∃ (C : ℝ),
        ∃ (H : C ≥ 0),
          ∀ (y : F), ∃ (x : E), dist (coe_fn f x) y ≤ 1 / bit0 1 * norm y ∧ norm x ≤ C * norm y :=
  sorry

/-- The Banach open mapping theorem: if a bounded linear map between Banach spaces is onto, then
any point has a preimage with controlled norm. -/
theorem exists_preimage_norm_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) [complete_space F] [complete_space E]
    (surj : function.surjective ⇑f) :
    ∃ (C : ℝ), ∃ (H : C > 0), ∀ (y : F), ∃ (x : E), coe_fn f x = y ∧ norm x ≤ C * norm y :=
  sorry

/-- The Banach open mapping theorem: a surjective bounded linear map between Banach spaces is
open. -/
theorem open_mapping {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) [complete_space F] [complete_space E]
    (surj : function.surjective ⇑f) : is_open_map ⇑f :=
  sorry

namespace linear_equiv


/-- If a bounded linear map is a bijection, then its inverse is also a bounded linear map. -/
theorem continuous_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F]
    [complete_space E] (e : linear_equiv 𝕜 E F) (h : continuous ⇑e) : continuous ⇑(symm e) :=
  sorry

/-- Associating to a linear equivalence between Banach spaces a continuous linear equivalence when
the direct map is continuous, thanks to the Banach open mapping theorem that ensures that the
inverse map is also continuous. -/
def to_continuous_linear_equiv_of_continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] [complete_space E] (e : linear_equiv 𝕜 E F)
    (h : continuous ⇑e) : continuous_linear_equiv 𝕜 E F :=
  continuous_linear_equiv.mk (mk (to_fun e) sorry sorry (inv_fun e) sorry sorry)

@[simp] theorem coe_fn_to_continuous_linear_equiv_of_continuous {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [complete_space F] [complete_space E]
    (e : linear_equiv 𝕜 E F) (h : continuous ⇑e) :
    ⇑(to_continuous_linear_equiv_of_continuous e h) = ⇑e :=
  rfl

@[simp] theorem coe_fn_to_continuous_linear_equiv_of_continuous_symm {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] [complete_space F] [complete_space E]
    (e : linear_equiv 𝕜 E F) (h : continuous ⇑e) :
    ⇑(continuous_linear_equiv.symm (to_continuous_linear_equiv_of_continuous e h)) = ⇑(symm e) :=
  rfl

end linear_equiv


namespace continuous_linear_equiv


/-- Convert a bijective continuous linear map `f : E →L[𝕜] F` between two Banach spaces
to a continuous linear equivalence. -/
def of_bijective {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F]
    [complete_space E] (f : continuous_linear_map 𝕜 E F) (hinj : continuous_linear_map.ker f = ⊥)
    (hsurj : continuous_linear_map.range f = ⊤) : continuous_linear_equiv 𝕜 E F :=
  linear_equiv.to_continuous_linear_equiv_of_continuous (linear_equiv.of_bijective (↑f) hinj hsurj)
    sorry

@[simp] theorem coe_fn_of_bijective {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    [complete_space F] [complete_space E] (f : continuous_linear_map 𝕜 E F)
    (hinj : continuous_linear_map.ker f = ⊥) (hsurj : continuous_linear_map.range f = ⊤) :
    ⇑(of_bijective f hinj hsurj) = ⇑f :=
  rfl

@[simp] theorem of_bijective_symm_apply_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] [complete_space E] (f : continuous_linear_map 𝕜 E F)
    (hinj : continuous_linear_map.ker f = ⊥) (hsurj : continuous_linear_map.range f = ⊤) (x : E) :
    coe_fn (continuous_linear_equiv.symm (of_bijective f hinj hsurj)) (coe_fn f x) = x :=
  symm_apply_apply (of_bijective f hinj hsurj) x

@[simp] theorem of_bijective_apply_symm_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] [complete_space F] [complete_space E] (f : continuous_linear_map 𝕜 E F)
    (hinj : continuous_linear_map.ker f = ⊥) (hsurj : continuous_linear_map.range f = ⊤) (y : F) :
    coe_fn f (coe_fn (continuous_linear_equiv.symm (of_bijective f hinj hsurj)) y) = y :=
  apply_symm_apply (of_bijective f hinj hsurj) y

end Mathlib