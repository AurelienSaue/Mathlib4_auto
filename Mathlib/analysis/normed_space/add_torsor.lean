/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.affine_space.midpoint
import Mathlib.topology.metric_space.isometry
import Mathlib.topology.instances.real_vector_space
import Mathlib.PostPort

universes u_1 u_2 l u_3 u_4 u_5 u_6 

namespace Mathlib

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.

-/

/-- A `normed_add_torsor V P` is a torsor of an additive normed group
action by a `normed_group V` on points `P`. We bundle the metric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a metric space, but
bundling just the distance and using an instance for the metric space
results in type class problems). -/
class normed_add_torsor (V : outParam (Type u_1)) (P : Type u_2) [outParam (normed_group V)] [metric_space P] 
extends add_torsor V P
where
  dist_eq_norm' : ∀ (x y : P), dist x y = norm (x -ᵥ y)

/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub` sometimes doesn't work. -/
theorem dist_eq_norm_vsub (V : Type u_2) {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (x : P) (y : P) : dist x y = norm (x -ᵥ y) :=
  normed_add_torsor.dist_eq_norm' x y

/-- A `normed_group` is a `normed_add_torsor` over itself. -/
protected instance normed_group.normed_add_torsor (V : Type u_2) [normed_group V] : normed_add_torsor V V :=
  normed_add_torsor.mk dist_eq_norm

@[simp] theorem dist_vadd_cancel_left {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (v : V) (x : P) (y : P) : dist (v +ᵥ x) (v +ᵥ y) = dist x y := sorry

@[simp] theorem dist_vadd_cancel_right {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (v₁ : V) (v₂ : V) (x : P) : dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ := sorry

@[simp] theorem dist_vadd_left {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (v : V) (x : P) : dist (v +ᵥ x) x = norm v := sorry

@[simp] theorem dist_vadd_right {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (v : V) (x : P) : dist x (v +ᵥ x) = norm v :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dist x (v +ᵥ x) = norm v)) (dist_comm x (v +ᵥ x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (dist (v +ᵥ x) x = norm v)) (dist_vadd_left v x))) (Eq.refl (norm v)))

@[simp] theorem dist_vsub_cancel_left {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (x : P) (y : P) (z : P) : dist (x -ᵥ y) (x -ᵥ z) = dist y z := sorry

@[simp] theorem dist_vsub_cancel_right {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (x : P) (y : P) (z : P) : dist (x -ᵥ z) (y -ᵥ z) = dist x y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dist (x -ᵥ z) (y -ᵥ z) = dist x y)) (dist_eq_norm (x -ᵥ z) (y -ᵥ z))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (norm (x -ᵥ z - (y -ᵥ z)) = dist x y)) (vsub_sub_vsub_cancel_right x y z)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (norm (x -ᵥ y) = dist x y)) (dist_eq_norm_vsub V x y))) (Eq.refl (norm (x -ᵥ y)))))

theorem dist_vadd_vadd_le {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (v : V) (v' : V) (p : P) (p' : P) : dist (v +ᵥ p) (v' +ᵥ p') ≤ dist v v' + dist p p' := sorry

theorem dist_vsub_vsub_le {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P) : dist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ dist p₁ p₃ + dist p₂ p₄ := sorry

theorem nndist_vadd_vadd_le {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (v : V) (v' : V) (p : P) (p' : P) : nndist (v +ᵥ p) (v' +ᵥ p') ≤ nndist v v' + nndist p p' := sorry

theorem nndist_vsub_vsub_le {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P) : nndist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ nndist p₁ p₃ + nndist p₂ p₄ := sorry

theorem edist_vadd_vadd_le {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (v : V) (v' : V) (p : P) (p' : P) : edist (v +ᵥ p) (v' +ᵥ p') ≤ edist v v' + edist p p' := sorry

theorem edist_vsub_vsub_le {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P) : edist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ edist p₁ p₃ + edist p₂ p₄ := sorry

/-- The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def metric_space_of_normed_group_of_add_torsor (V : Type u_1) (P : Type u_2) [normed_group V] [add_torsor V P] : metric_space P :=
  metric_space.mk sorry sorry sorry sorry (fun (x y : P) => ennreal.of_real ((fun (x y : P) => norm (x -ᵥ y)) x y))
    (uniform_space_of_dist (fun (x y : P) => norm (x -ᵥ y)) sorry sorry sorry)

namespace isometric


/-- The map `v ↦ v +ᵥ p` as an isometric equivalence between `V` and `P`. -/
def vadd_const {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (p : P) : V ≃ᵢ P :=
  mk (equiv.vadd_const p) sorry

@[simp] theorem coe_vadd_const {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (p : P) : ⇑(vadd_const p) = fun (v : V) => v +ᵥ p :=
  rfl

@[simp] theorem coe_vadd_const_symm {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (p : P) : ⇑(isometric.symm (vadd_const p)) = fun (p' : P) => p' -ᵥ p :=
  rfl

@[simp] theorem vadd_const_to_equiv {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (p : P) : to_equiv (vadd_const p) = equiv.vadd_const p :=
  rfl

/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
def const_vsub {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (p : P) : P ≃ᵢ V :=
  mk (equiv.const_vsub p) sorry

@[simp] theorem coe_const_vsub {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (p : P) : ⇑(const_vsub p) = has_vsub.vsub p :=
  rfl

@[simp] theorem coe_const_vsub_symm {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (p : P) : ⇑(isometric.symm (const_vsub p)) = fun (v : V) => -v +ᵥ p :=
  rfl

/-- The map `p ↦ v +ᵥ p` as an isometric automorphism of `P`. -/
def const_vadd {V : Type u_2} (P : Type u_3) [normed_group V] [metric_space P] [normed_add_torsor V P] (v : V) : P ≃ᵢ P :=
  mk (equiv.const_vadd P v) sorry

@[simp] theorem coe_const_vadd {V : Type u_2} (P : Type u_3) [normed_group V] [metric_space P] [normed_add_torsor V P] (v : V) : ⇑(const_vadd P v) = has_vadd.vadd v :=
  rfl

@[simp] theorem const_vadd_zero (V : Type u_2) (P : Type u_3) [normed_group V] [metric_space P] [normed_add_torsor V P] : const_vadd P 0 = isometric.refl P :=
  to_equiv_inj (equiv.const_vadd_zero V P)

/-- Point reflection in `x` as an `isometric` homeomorphism. -/
def point_reflection {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (x : P) : P ≃ᵢ P :=
  isometric.trans (const_vsub x) (vadd_const x)

theorem point_reflection_apply {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (x : P) (y : P) : coe_fn (point_reflection x) y = x -ᵥ y +ᵥ x :=
  rfl

@[simp] theorem point_reflection_to_equiv {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (x : P) : to_equiv (point_reflection x) = equiv.point_reflection x :=
  rfl

@[simp] theorem point_reflection_self {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (x : P) : coe_fn (point_reflection x) x = x :=
  equiv.point_reflection_self x

theorem point_reflection_involutive {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (x : P) : function.involutive ⇑(point_reflection x) :=
  equiv.point_reflection_involutive x

@[simp] theorem point_reflection_symm {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (x : P) : isometric.symm (point_reflection x) = point_reflection x :=
  to_equiv_inj (equiv.point_reflection_symm x)

@[simp] theorem dist_point_reflection_fixed {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (x : P) (y : P) : dist (coe_fn (point_reflection x) y) x = dist y x := sorry

theorem dist_point_reflection_self' {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (x : P) (y : P) : dist (coe_fn (point_reflection x) y) y = norm (bit0 (x -ᵥ y)) := sorry

theorem dist_point_reflection_self {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (𝕜 : Type u_1) [normed_field 𝕜] [normed_space 𝕜 V] (x : P) (y : P) : dist (coe_fn (point_reflection x) y) y = norm (bit0 1) * dist x y := sorry

theorem point_reflection_fixed_iff {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] (𝕜 : Type u_1) [normed_field 𝕜] [normed_space 𝕜 V] [invertible (bit0 1)] {x : P} {y : P} : coe_fn (point_reflection x) y = y ↔ y = x :=
  affine_equiv.point_reflection_fixed_iff_of_module 𝕜

theorem dist_point_reflection_self_real {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] [normed_space ℝ V] (x : P) (y : P) : dist (coe_fn (point_reflection x) y) y = bit0 1 * dist x y := sorry

@[simp] theorem point_reflection_midpoint_left {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] [normed_space ℝ V] (x : P) (y : P) : coe_fn (point_reflection (midpoint ℝ x y)) x = y :=
  affine_equiv.point_reflection_midpoint_left x y

@[simp] theorem point_reflection_midpoint_right {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] [normed_space ℝ V] (x : P) (y : P) : coe_fn (point_reflection (midpoint ℝ x y)) y = x :=
  affine_equiv.point_reflection_midpoint_right x y

end isometric


theorem lipschitz_with.vadd {α : Type u_1} {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] [emetric_space α] {f : α → V} {g : α → P} {Kf : nnreal} {Kg : nnreal} (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) : lipschitz_with (Kf + Kg) (f +ᵥ g) :=
  fun (x y : α) =>
    trans_rel_left LessEq (le_trans (edist_vadd_vadd_le (f x) (f y) (g x) (g y)) (add_le_add (hf x y) (hg x y)))
      (Eq.symm (add_mul (↑Kf) (↑Kg) (edist x y)))

theorem lipschitz_with.vsub {α : Type u_1} {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] [emetric_space α] {f : α → P} {g : α → P} {Kf : nnreal} {Kg : nnreal} (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) : lipschitz_with (Kf + Kg) (f -ᵥ g) :=
  fun (x y : α) =>
    trans_rel_left LessEq (le_trans (edist_vsub_vsub_le (f x) (g x) (f y) (g y)) (add_le_add (hf x y) (hg x y)))
      (Eq.symm (add_mul (↑Kf) (↑Kg) (edist x y)))

theorem uniform_continuous_vadd {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] : uniform_continuous fun (x : V × P) => prod.fst x +ᵥ prod.snd x :=
  lipschitz_with.uniform_continuous (lipschitz_with.vadd lipschitz_with.prod_fst lipschitz_with.prod_snd)

theorem uniform_continuous_vsub {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] : uniform_continuous fun (x : P × P) => prod.fst x -ᵥ prod.snd x :=
  lipschitz_with.uniform_continuous (lipschitz_with.vsub lipschitz_with.prod_fst lipschitz_with.prod_snd)

theorem continuous_vadd {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] : continuous fun (x : V × P) => prod.fst x +ᵥ prod.snd x :=
  uniform_continuous.continuous uniform_continuous_vadd

theorem continuous_vsub {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] : continuous fun (x : P × P) => prod.fst x -ᵥ prod.snd x :=
  uniform_continuous.continuous uniform_continuous_vsub

theorem filter.tendsto.vadd {α : Type u_1} {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {l : filter α} {f : α → V} {g : α → P} {v : V} {p : P} (hf : filter.tendsto f l (nhds v)) (hg : filter.tendsto g l (nhds p)) : filter.tendsto (f +ᵥ g) l (nhds (v +ᵥ p)) :=
  filter.tendsto.comp (continuous.tendsto continuous_vadd (v, p)) (filter.tendsto.prod_mk_nhds hf hg)

theorem filter.tendsto.vsub {α : Type u_1} {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {l : filter α} {f : α → P} {g : α → P} {x : P} {y : P} (hf : filter.tendsto f l (nhds x)) (hg : filter.tendsto g l (nhds y)) : filter.tendsto (f -ᵥ g) l (nhds (x -ᵥ y)) :=
  filter.tendsto.comp (continuous.tendsto continuous_vsub (x, y)) (filter.tendsto.prod_mk_nhds hf hg)

theorem continuous.vadd {α : Type u_1} {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] [topological_space α] {f : α → V} {g : α → P} (hf : continuous f) (hg : continuous g) : continuous (f +ᵥ g) :=
  continuous.comp continuous_vadd (continuous.prod_mk hf hg)

theorem continuous.vsub {α : Type u_1} {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] [topological_space α] {f : α → P} {g : α → P} (hf : continuous f) (hg : continuous g) : continuous (f -ᵥ g) :=
  continuous.comp continuous_vsub (continuous.prod_mk hf hg)

theorem continuous_at.vadd {α : Type u_1} {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] [topological_space α] {f : α → V} {g : α → P} {x : α} (hf : continuous_at f x) (hg : continuous_at g x) : continuous_at (f +ᵥ g) x :=
  filter.tendsto.vadd hf hg

theorem continuous_at.vsub {α : Type u_1} {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] [topological_space α] {f : α → P} {g : α → P} {x : α} (hf : continuous_at f x) (hg : continuous_at g x) : continuous_at (f -ᵥ g) x :=
  filter.tendsto.vsub hf hg

theorem continuous_within_at.vadd {α : Type u_1} {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] [topological_space α] {f : α → V} {g : α → P} {x : α} {s : set α} (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) : continuous_within_at (f +ᵥ g) s x :=
  filter.tendsto.vadd hf hg

theorem continuous_within_at.vsub {α : Type u_1} {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] [topological_space α] {f : α → P} {g : α → P} {x : α} {s : set α} (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) : continuous_within_at (f -ᵥ g) s x :=
  filter.tendsto.vsub hf hg

/-- The map `g` from `V1` to `V2` corresponding to a map `f` from `P1`
to `P2`, at a base point `p`, is an isometry if `f` is one. -/
theorem isometry.vadd_vsub {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {V' : Type u_4} {P' : Type u_5} [normed_group V'] [metric_space P'] [normed_add_torsor V' P'] {f : P → P'} (hf : isometry f) {p : P} {g : V → V'} (hg : ∀ (v : V), g v = f (v +ᵥ p) -ᵥ f p) : isometry g := sorry

/-- If `f` is an affine map, then its linear part is continuous iff `f` is continuous. -/
theorem affine_map.continuous_linear_iff {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {V' : Type u_4} {P' : Type u_5} [normed_group V'] [metric_space P'] [normed_add_torsor V' P'] {𝕜 : Type u_6} [normed_field 𝕜] [normed_space 𝕜 V] [normed_space 𝕜 V'] {f : affine_map 𝕜 P P'} : continuous ⇑(affine_map.linear f) ↔ continuous ⇑f := sorry

@[simp] theorem dist_center_homothety {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {𝕜 : Type u_6} [normed_field 𝕜] [normed_space 𝕜 V] (p₁ : P) (p₂ : P) (c : 𝕜) : dist p₁ (coe_fn (affine_map.homothety p₁ c) p₂) = norm c * dist p₁ p₂ := sorry

@[simp] theorem dist_homothety_center {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {𝕜 : Type u_6} [normed_field 𝕜] [normed_space 𝕜 V] (p₁ : P) (p₂ : P) (c : 𝕜) : dist (coe_fn (affine_map.homothety p₁ c) p₂) p₁ = norm c * dist p₁ p₂ := sorry

@[simp] theorem dist_homothety_self {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {𝕜 : Type u_6} [normed_field 𝕜] [normed_space 𝕜 V] (p₁ : P) (p₂ : P) (c : 𝕜) : dist (coe_fn (affine_map.homothety p₁ c) p₂) p₂ = norm (1 - c) * dist p₁ p₂ := sorry

@[simp] theorem dist_self_homothety {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {𝕜 : Type u_6} [normed_field 𝕜] [normed_space 𝕜 V] (p₁ : P) (p₂ : P) (c : 𝕜) : dist p₂ (coe_fn (affine_map.homothety p₁ c) p₂) = norm (1 - c) * dist p₁ p₂ := sorry

@[simp] theorem dist_left_midpoint {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {𝕜 : Type u_6} [normed_field 𝕜] [normed_space 𝕜 V] [invertible (bit0 1)] (p₁ : P) (p₂ : P) : dist p₁ (midpoint 𝕜 p₁ p₂) = norm (bit0 1)⁻¹ * dist p₁ p₂ := sorry

@[simp] theorem dist_midpoint_left {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {𝕜 : Type u_6} [normed_field 𝕜] [normed_space 𝕜 V] [invertible (bit0 1)] (p₁ : P) (p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₁ = norm (bit0 1)⁻¹ * dist p₁ p₂ := sorry

@[simp] theorem dist_midpoint_right {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {𝕜 : Type u_6} [normed_field 𝕜] [normed_space 𝕜 V] [invertible (bit0 1)] (p₁ : P) (p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₂ = norm (bit0 1)⁻¹ * dist p₁ p₂ := sorry

@[simp] theorem dist_right_midpoint {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {𝕜 : Type u_6} [normed_field 𝕜] [normed_space 𝕜 V] [invertible (bit0 1)] (p₁ : P) (p₂ : P) : dist p₂ (midpoint 𝕜 p₁ p₂) = norm (bit0 1)⁻¹ * dist p₁ p₂ := sorry

/-- A continuous map between two normed affine spaces is an affine map provided that
it sends midpoints to midpoints. -/
def affine_map.of_map_midpoint {V : Type u_2} {P : Type u_3} [normed_group V] [metric_space P] [normed_add_torsor V P] {V' : Type u_4} {P' : Type u_5} [normed_group V'] [metric_space P'] [normed_add_torsor V' P'] [normed_space ℝ V] [normed_space ℝ V'] (f : P → P') (h : ∀ (x y : P), f (midpoint ℝ x y) = midpoint ℝ (f x) (f y)) (hfc : continuous f) : affine_map ℝ P P' :=
  affine_map.mk' f
    (↑(add_monoid_hom.to_real_linear_map
        (add_monoid_hom.of_map_midpoint ℝ ℝ
          (⇑(affine_equiv.symm (affine_equiv.vadd_const ℝ (f (classical.arbitrary P)))) ∘
            f ∘ ⇑(affine_equiv.vadd_const ℝ (classical.arbitrary P)))
          sorry sorry)
        sorry))
    (classical.arbitrary P) sorry

