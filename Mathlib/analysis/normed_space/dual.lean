/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.hahn_banach
import Mathlib.analysis.normed_space.inner_product
import Mathlib.PostPort

universes u_1 u_2 u v 

namespace Mathlib

/-!
# The topological dual of a normed space

In this file we define the topological dual of a normed space, and the bounded linear map from
a normed space into its double dual.

We also prove that, for base field `𝕜` with `[is_R_or_C 𝕜]`, this map is an isometry.

We then consider inner product spaces, with base field over `ℝ` (the corresponding results for `ℂ`
will require the definition of conjugate-linear maps). We define `to_dual_map`, a continuous linear
map from `E` to its dual, which maps an element `x` of the space to `λ y, ⟪x, y⟫`. We check
(`to_dual_map_isometry`) that this map is an isometry onto its image, and particular is injective.
We also define `to_dual'` as the function taking taking a vector to its dual for a base field `𝕜`
with `[is_R_or_C 𝕜]`; this is a function and not a linear map.

Finally, under the hypothesis of completeness (i.e., for Hilbert spaces), we prove the Fréchet-Riesz
representation (`to_dual_map_eq_top`), which states the surjectivity: every element of the dual
of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.  This permits the map
`to_dual_map` to be upgraded to an (isometric) continuous linear equivalence, `to_dual`, between a
Hilbert space and its dual.

## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/

namespace normed_space


/-- The topological dual of a normed space `E`. -/
def dual (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E]  :=
  continuous_linear_map 𝕜 E 𝕜

protected instance dual.inhabited (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] : Inhabited (dual 𝕜 E) :=
  { default := 0 }

/-- The inclusion of a normed space in its double (topological) dual. -/
def inclusion_in_double_dual' (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] (x : E) : dual 𝕜 (dual 𝕜 E) :=
  linear_map.mk_continuous (linear_map.mk (fun (f : dual 𝕜 E) => coe_fn f x) sorry sorry) (norm x) sorry

@[simp] theorem dual_def (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] (x : E) (f : dual 𝕜 E) : coe_fn (inclusion_in_double_dual' 𝕜 E x) f = coe_fn f x :=
  rfl

theorem double_dual_bound (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] (x : E) : norm (inclusion_in_double_dual' 𝕜 E x) ≤ norm x := sorry

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusion_in_double_dual (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] : continuous_linear_map 𝕜 E (dual 𝕜 (dual 𝕜 E)) :=
  linear_map.mk_continuous (linear_map.mk (fun (x : E) => inclusion_in_double_dual' 𝕜 E x) sorry sorry) 1 sorry

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `continuous_linear_map.op_norm_le_bound`. -/
theorem norm_le_dual_bound {𝕜 : Type v} [is_R_or_C 𝕜] {E : Type u} [normed_group E] [normed_space 𝕜 E] (x : E) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ (f : dual 𝕜 E), norm (coe_fn f x) ≤ M * norm f) : norm x ≤ M := sorry

/-- The inclusion of a normed space in its double dual is an isometry onto its image.-/
theorem inclusion_in_double_dual_isometry {𝕜 : Type v} [is_R_or_C 𝕜] {E : Type u} [normed_group E] [normed_space 𝕜 E] (x : E) : norm (coe_fn (inclusion_in_double_dual 𝕜 E) x) = norm x := sorry

end normed_space


namespace inner_product_space


/--
Given some `x` in an inner product space, we can define its dual as the continuous linear map
`λ y, ⟪x, y⟫`. Consider using `to_dual` or `to_dual_map` instead in the real case.
-/
def to_dual' (𝕜 : Type u_1) {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] : E →+ normed_space.dual 𝕜 E :=
  add_monoid_hom.mk
    (fun (x : E) => linear_map.mk_continuous (linear_map.mk (fun (y : E) => inner x y) sorry sorry) (norm x) sorry) sorry
    sorry

@[simp] theorem to_dual'_apply (𝕜 : Type u_1) {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x : E} {y : E} : coe_fn (coe_fn (to_dual' 𝕜) x) y = inner x y :=
  rfl

/-- In an inner product space, the norm of the dual of a vector `x` is `∥x∥` -/
@[simp] theorem norm_to_dual'_apply (𝕜 : Type u_1) {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (x : E) : norm (coe_fn (to_dual' 𝕜) x) = norm x := sorry

theorem to_dual'_isometry (𝕜 : Type u_1) (E : Type u_2) [is_R_or_C 𝕜] [inner_product_space 𝕜 E] : isometry ⇑(to_dual' 𝕜) :=
  add_monoid_hom.isometry_of_norm (to_dual' 𝕜) (norm_to_dual'_apply 𝕜)

/--
Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form
`λ u, ⟪y, u⟫` for some `y : E`, i.e. `to_dual'` is surjective.
-/
theorem to_dual'_surjective (𝕜 : Type u_1) (E : Type u_2) [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [complete_space E] : function.surjective ⇑(to_dual' 𝕜) := sorry

/-- In a real inner product space `F`, the function that takes a vector `x` in `F` to its dual
`λ y, ⟪x, y⟫` is a continuous linear map. If the space is complete (i.e. is a Hilbert space),
consider using `to_dual` instead. -/
-- TODO extend to `is_R_or_C` (requires a definition of conjugate linear maps)

def to_dual_map {F : Type u_1} [inner_product_space ℝ F] : continuous_linear_map ℝ F (normed_space.dual ℝ F) :=
  linear_map.mk_continuous (linear_map.mk ⇑(to_dual' ℝ) sorry sorry) 1 sorry

@[simp] theorem to_dual_map_apply {F : Type u_1} [inner_product_space ℝ F] {x : F} {y : F} : coe_fn (coe_fn to_dual_map x) y = inner x y :=
  rfl

/-- In an inner product space, the norm of the dual of a vector `x` is `∥x∥` -/
@[simp] theorem norm_to_dual_map_apply {F : Type u_1} [inner_product_space ℝ F] (x : F) : norm (coe_fn to_dual_map x) = norm x :=
  norm_to_dual'_apply ℝ x

theorem to_dual_map_isometry {F : Type u_1} [inner_product_space ℝ F] : isometry ⇑to_dual_map :=
  add_monoid_hom.isometry_of_norm (to_dual' ℝ) norm_to_dual_map_apply

theorem to_dual_map_injective {F : Type u_1} [inner_product_space ℝ F] : function.injective ⇑to_dual_map :=
  isometry.injective to_dual_map_isometry

@[simp] theorem ker_to_dual_map {F : Type u_1} [inner_product_space ℝ F] : continuous_linear_map.ker to_dual_map = ⊥ :=
  iff.mpr linear_map.ker_eq_bot to_dual_map_injective

@[simp] theorem to_dual_map_eq_iff_eq {F : Type u_1} [inner_product_space ℝ F] {x : F} {y : F} : coe_fn to_dual_map x = coe_fn to_dual_map y ↔ x = y :=
  function.injective.eq_iff (iff.mp linear_map.ker_eq_bot ker_to_dual_map)

/--
Fréchet-Riesz representation: any `ℓ` in the dual of a real Hilbert space `F` is of the form
`λ u, ⟪y, u⟫` for some `y` in `F`.  See `inner_product_space.to_dual` for the continuous linear
equivalence thus induced.
-/
-- TODO extend to `is_R_or_C` (requires a definition of conjugate linear maps)

theorem range_to_dual_map {F : Type u_1} [inner_product_space ℝ F] [complete_space F] : continuous_linear_map.range to_dual_map = ⊤ :=
  iff.mpr linear_map.range_eq_top (to_dual'_surjective ℝ F)

/--
Fréchet-Riesz representation: If `F` is a Hilbert space, the function that takes a vector in `F` to
its dual is a continuous linear equivalence.  -/
def to_dual {F : Type u_1} [inner_product_space ℝ F] [complete_space F] : continuous_linear_equiv ℝ F (normed_space.dual ℝ F) :=
  continuous_linear_equiv.of_isometry (continuous_linear_map.to_linear_map to_dual_map) to_dual_map_isometry
    range_to_dual_map

/--
Fréchet-Riesz representation: If `F` is a Hilbert space, the function that takes a vector in `F` to
its dual is an isometry.  -/
def isometric.to_dual {F : Type u_1} [inner_product_space ℝ F] [complete_space F] : F ≃ᵢ normed_space.dual ℝ F :=
  isometric.mk (linear_equiv.to_equiv (continuous_linear_equiv.to_linear_equiv to_dual)) (to_dual'_isometry ℝ F)

@[simp] theorem to_dual_apply {F : Type u_1} [inner_product_space ℝ F] [complete_space F] {x : F} {y : F} : coe_fn (coe_fn to_dual x) y = inner x y :=
  rfl

@[simp] theorem to_dual_eq_iff_eq {F : Type u_1} [inner_product_space ℝ F] [complete_space F] {x : F} {y : F} : coe_fn to_dual x = coe_fn to_dual y ↔ x = y :=
  function.injective.eq_iff (continuous_linear_equiv.injective to_dual)

theorem to_dual_eq_iff_eq' {F : Type u_1} [inner_product_space ℝ F] [complete_space F] {x : F} {x' : F} : (∀ (y : F), inner x y = inner x' y) ↔ x = x' := sorry

@[simp] theorem norm_to_dual_apply {F : Type u_1} [inner_product_space ℝ F] [complete_space F] (x : F) : norm (coe_fn to_dual x) = norm x :=
  norm_to_dual_map_apply x

/-- In a Hilbert space, the norm of a vector in the dual space is the norm of its corresponding
primal vector. -/
theorem norm_to_dual_symm_apply {F : Type u_1} [inner_product_space ℝ F] [complete_space F] (ℓ : normed_space.dual ℝ F) : norm (coe_fn (continuous_linear_equiv.symm to_dual) ℓ) = norm ℓ := sorry

