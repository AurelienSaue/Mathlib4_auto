/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Continuous linear functions -- functions between normed vector spaces which are bounded and linear.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.normed_space.multilinear
import PostPort

universes u_5 u_6 u_7 l u_1 u_2 u_3 u_4 

namespace Mathlib

/-- A function `f` satisfies `is_bounded_linear_map 𝕜 f` if it is linear and satisfies the
inequality `∥ f x ∥ ≤ M * ∥ x ∥` for some positive constant `M`. -/
structure is_bounded_linear_map (𝕜 : Type u_5) [normed_field 𝕜] {E : Type u_6} [normed_group E] [normed_space 𝕜 E] {F : Type u_7} [normed_group F] [normed_space 𝕜 F] (f : E → F) 
extends is_linear_map 𝕜 f
where
  bound : ∃ (M : ℝ), 0 < M ∧ ∀ (x : E), norm (f x) ≤ M * norm x

theorem is_linear_map.with_bound {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (hf : is_linear_map 𝕜 f) (M : ℝ) (h : ∀ (x : E), norm (f x) ≤ M * norm x) : is_bounded_linear_map 𝕜 f := sorry

/-- A continuous linear map satisfies `is_bounded_linear_map` -/
theorem continuous_linear_map.is_bounded_linear_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : continuous_linear_map 𝕜 E F) : is_bounded_linear_map 𝕜 ⇑f := sorry

namespace is_bounded_linear_map


/-- Construct a linear map from a function `f` satisfying `is_bounded_linear_map 𝕜 f`. -/
def to_linear_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (h : is_bounded_linear_map 𝕜 f) : linear_map 𝕜 E F :=
  is_linear_map.mk' f sorry

/-- Construct a continuous linear map from is_bounded_linear_map -/
def to_continuous_linear_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (hf : is_bounded_linear_map 𝕜 f) : continuous_linear_map 𝕜 E F :=
  continuous_linear_map.mk (linear_map.mk (linear_map.to_fun (to_linear_map f hf)) sorry sorry)

theorem zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] : is_bounded_linear_map 𝕜 fun (x : E) => 0 := sorry

theorem id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] : is_bounded_linear_map 𝕜 fun (x : E) => x := sorry

theorem fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] : is_bounded_linear_map 𝕜 fun (x : E × F) => prod.fst x := sorry

theorem snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] : is_bounded_linear_map 𝕜 fun (x : E × F) => prod.snd x := sorry

theorem smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (c : 𝕜) (hf : is_bounded_linear_map 𝕜 f) : is_bounded_linear_map 𝕜 fun (e : E) => c • f e := sorry

theorem neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (hf : is_bounded_linear_map 𝕜 f) : is_bounded_linear_map 𝕜 fun (e : E) => -f e := sorry

theorem add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {g : E → F} (hf : is_bounded_linear_map 𝕜 f) (hg : is_bounded_linear_map 𝕜 g) : is_bounded_linear_map 𝕜 fun (e : E) => f e + g e := sorry

theorem sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {g : E → F} (hf : is_bounded_linear_map 𝕜 f) (hg : is_bounded_linear_map 𝕜 g) : is_bounded_linear_map 𝕜 fun (e : E) => f e - g e := sorry

theorem comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} {g : F → G} (hg : is_bounded_linear_map 𝕜 g) (hf : is_bounded_linear_map 𝕜 f) : is_bounded_linear_map 𝕜 (g ∘ f) :=
  continuous_linear_map.is_bounded_linear_map
    (continuous_linear_map.comp (to_continuous_linear_map hg) (to_continuous_linear_map hf))

protected theorem tendsto {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (x : E) (hf : is_bounded_linear_map 𝕜 f) : filter.tendsto f (nhds x) (nhds (f x)) := sorry

theorem continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (hf : is_bounded_linear_map 𝕜 f) : continuous f :=
  iff.mpr continuous_iff_continuous_at fun (_x : E) => is_bounded_linear_map.tendsto _x hf

theorem lim_zero_bounded_linear_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (hf : is_bounded_linear_map 𝕜 f) : filter.tendsto f (nhds 0) (nhds 0) :=
  linear_map.map_zero (is_linear_map.mk' f (to_is_linear_map hf)) ▸ iff.mp continuous_iff_continuous_at (continuous hf) 0

theorem is_O_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (h : is_bounded_linear_map 𝕜 f) (l : filter E) : asymptotics.is_O f (fun (x : E) => x) l := sorry

theorem is_O_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {E : Type u_2} {g : F → G} (hg : is_bounded_linear_map 𝕜 g) {f : E → F} (l : filter E) : asymptotics.is_O (fun (x' : E) => g (f x')) f l :=
  asymptotics.is_O.comp_tendsto (is_O_id hg ⊤) le_top

theorem is_O_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} (h : is_bounded_linear_map 𝕜 f) (l : filter E) (x : E) : asymptotics.is_O (fun (x' : E) => f (x' - x)) (fun (x' : E) => x' - x) l :=
  is_O_comp h l

end is_bounded_linear_map


/-- Taking the cartesian product of two continuous linear maps is a bounded linear operation. -/
theorem is_bounded_linear_map_prod_iso {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] : is_bounded_linear_map 𝕜
  fun (p : continuous_linear_map 𝕜 E F × continuous_linear_map 𝕜 E G) =>
    continuous_linear_map.prod (prod.fst p) (prod.snd p) := sorry

/-- Taking the cartesian product of two continuous multilinear maps is a bounded linear operation. -/
theorem is_bounded_linear_map_prod_multilinear {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {ι : Type u_5} [DecidableEq ι] [fintype ι] {E : ι → Type u_2} [(i : ι) → normed_group (E i)] [(i : ι) → normed_space 𝕜 (E i)] : is_bounded_linear_map 𝕜
  fun (p : continuous_multilinear_map 𝕜 E F × continuous_multilinear_map 𝕜 E G) =>
    continuous_multilinear_map.prod (prod.fst p) (prod.snd p) := sorry

/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation. -/
theorem is_bounded_linear_map_continuous_multilinear_map_comp_linear {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {ι : Type u_5} [DecidableEq ι] [fintype ι] (g : continuous_linear_map 𝕜 G E) : is_bounded_linear_map 𝕜
  fun (f : continuous_multilinear_map 𝕜 (fun (i : ι) => E) F) =>
    continuous_multilinear_map.comp_continuous_linear_map f fun (_x : ι) => g := sorry

/-- A map `f : E × F → G` satisfies `is_bounded_bilinear_map 𝕜 f` if it is bilinear and
continuous. -/
structure is_bounded_bilinear_map (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] (f : E × F → G) 
where
  add_left : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y)
  smul_left : ∀ (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y)
  add_right : ∀ (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂)
  smul_right : ∀ (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y)
  bound : ∃ (C : ℝ), ∃ (H : C > 0), ∀ (x : E) (y : F), norm (f (x, y)) ≤ C * norm x * norm y

protected theorem is_bounded_bilinear_map.is_O {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E × F → G} (h : is_bounded_bilinear_map 𝕜 f) : asymptotics.is_O f (fun (p : E × F) => norm (prod.fst p) * norm (prod.snd p)) ⊤ := sorry

theorem is_bounded_bilinear_map.is_O_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E × F → G} {α : Type u_5} (H : is_bounded_bilinear_map 𝕜 f) {g : α → E} {h : α → F} {l : filter α} : asymptotics.is_O (fun (x : α) => f (g x, h x)) (fun (x : α) => norm (g x) * norm (h x)) l :=
  asymptotics.is_O.comp_tendsto (is_bounded_bilinear_map.is_O H) le_top

protected theorem is_bounded_bilinear_map.is_O' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E × F → G} (h : is_bounded_bilinear_map 𝕜 f) : asymptotics.is_O f (fun (p : E × F) => norm p * norm p) ⊤ :=
  asymptotics.is_O.trans (is_bounded_bilinear_map.is_O h)
    (asymptotics.is_O.mul (asymptotics.is_O.norm_norm asymptotics.is_O_fst_prod')
      (asymptotics.is_O.norm_norm asymptotics.is_O_snd_prod'))

theorem is_bounded_bilinear_map.map_sub_left {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E × F → G} (h : is_bounded_bilinear_map 𝕜 f) {x : E} {y : E} {z : F} : f (x - y, z) = f (x, z) - f (y, z) := sorry

theorem is_bounded_bilinear_map.map_sub_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E × F → G} (h : is_bounded_bilinear_map 𝕜 f) {x : E} {y : F} {z : F} : f (x, y - z) = f (x, y) - f (x, z) := sorry

theorem is_bounded_bilinear_map.is_bounded_linear_map_left {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E × F → G} (h : is_bounded_bilinear_map 𝕜 f) (y : F) : is_bounded_linear_map 𝕜 fun (x : E) => f (x, y) := sorry

theorem is_bounded_bilinear_map.is_bounded_linear_map_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E × F → G} (h : is_bounded_bilinear_map 𝕜 f) (x : E) : is_bounded_linear_map 𝕜 fun (y : F) => f (x, y) := sorry

theorem is_bounded_bilinear_map_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] : is_bounded_bilinear_map 𝕜 fun (p : 𝕜 × E) => prod.fst p • prod.snd p := sorry

theorem is_bounded_bilinear_map_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] : is_bounded_bilinear_map 𝕜 fun (p : 𝕜' × E) => prod.fst p • prod.snd p := sorry

theorem is_bounded_bilinear_map_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] : is_bounded_bilinear_map 𝕜 fun (p : 𝕜 × 𝕜) => prod.fst p * prod.snd p :=
  is_bounded_bilinear_map_smul

theorem is_bounded_bilinear_map_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] : is_bounded_bilinear_map 𝕜
  fun (p : continuous_linear_map 𝕜 E F × continuous_linear_map 𝕜 F G) =>
    continuous_linear_map.comp (prod.snd p) (prod.fst p) := sorry

theorem continuous_linear_map.is_bounded_linear_map_comp_left {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] (g : continuous_linear_map 𝕜 F G) : is_bounded_linear_map 𝕜 fun (f : continuous_linear_map 𝕜 E F) => continuous_linear_map.comp g f :=
  is_bounded_bilinear_map.is_bounded_linear_map_left is_bounded_bilinear_map_comp g

theorem continuous_linear_map.is_bounded_linear_map_comp_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] (f : continuous_linear_map 𝕜 E F) : is_bounded_linear_map 𝕜 fun (g : continuous_linear_map 𝕜 F G) => continuous_linear_map.comp g f :=
  is_bounded_bilinear_map.is_bounded_linear_map_right is_bounded_bilinear_map_comp f

theorem is_bounded_bilinear_map_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] : is_bounded_bilinear_map 𝕜 fun (p : continuous_linear_map 𝕜 E F × E) => coe_fn (prod.fst p) (prod.snd p) := sorry

/-- The function `continuous_linear_map.smul_right`, associating to a continuous linear map
`f : E → 𝕜` and a scalar `c : F` the tensor product `f ⊗ c` as a continuous linear map from `E` to
`F`, is a bounded bilinear map. -/
theorem is_bounded_bilinear_map_smul_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] : is_bounded_bilinear_map 𝕜
  fun (p : continuous_linear_map 𝕜 E 𝕜 × F) => continuous_linear_map.smul_right (prod.fst p) (prod.snd p) := sorry

/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
theorem is_bounded_bilinear_map_comp_multilinear {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {ι : Type u_2} {E : ι → Type u_5} [DecidableEq ι] [fintype ι] [(i : ι) → normed_group (E i)] [(i : ι) → normed_space 𝕜 (E i)] : is_bounded_bilinear_map 𝕜
  fun (p : continuous_linear_map 𝕜 F G × continuous_multilinear_map 𝕜 E F) =>
    continuous_linear_map.comp_continuous_multilinear_map (prod.fst p) (prod.snd p) := sorry

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here a bounded linear map from `E × F` to `G`. The fact that this
is indeed the derivative of `f` is proved in `is_bounded_bilinear_map.has_fderiv_at` in
`fderiv.lean`-/
def is_bounded_bilinear_map.linear_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E × F → G} (h : is_bounded_bilinear_map 𝕜 f) (p : E × F) : linear_map 𝕜 (E × F) G :=
  linear_map.mk (fun (q : E × F) => f (prod.fst p, prod.snd q) + f (prod.fst q, prod.snd p)) sorry sorry

/-- The derivative of a bounded bilinear map at a point `p : E × F`, as a continuous linear map
from `E × F` to `G`. -/
def is_bounded_bilinear_map.deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E × F → G} (h : is_bounded_bilinear_map 𝕜 f) (p : E × F) : continuous_linear_map 𝕜 (E × F) G :=
  linear_map.mk_continuous_of_exists_bound (is_bounded_bilinear_map.linear_deriv h p) sorry

@[simp] theorem is_bounded_bilinear_map_deriv_coe {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E × F → G} (h : is_bounded_bilinear_map 𝕜 f) (p : E × F) (q : E × F) : coe_fn (is_bounded_bilinear_map.deriv h p) q = f (prod.fst p, prod.snd q) + f (prod.fst q, prod.snd p) :=
  rfl

/-- The function `lmul_left_right : 𝕜' × 𝕜' → (𝕜' →L[𝕜] 𝕜')` is a bounded bilinear map. -/
theorem continuous_linear_map.lmul_left_right_is_bounded_bilinear (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (𝕜' : Type u_2) [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] : is_bounded_bilinear_map 𝕜 (continuous_linear_map.lmul_left_right 𝕜 𝕜') := sorry

/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
theorem is_bounded_bilinear_map.is_bounded_linear_map_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E × F → G} (h : is_bounded_bilinear_map 𝕜 f) : is_bounded_linear_map 𝕜 fun (p : E × F) => is_bounded_bilinear_map.deriv h p := sorry

/-- A linear isometry preserves the norm. -/
theorem linear_map.norm_apply_of_isometry {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : linear_map 𝕜 E F) {x : E} (hf : isometry ⇑f) : norm (coe_fn f x) = norm x := sorry

/-- Construct a continuous linear equiv from a linear map that is also an isometry with full range. -/
def continuous_linear_equiv.of_isometry {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : linear_map 𝕜 E F) (hf : isometry ⇑f) (hfr : linear_map.range f = ⊤) : continuous_linear_equiv 𝕜 E F :=
  continuous_linear_equiv.of_homothety 𝕜 (linear_equiv.of_bijective f sorry hfr) 1 zero_lt_one sorry

