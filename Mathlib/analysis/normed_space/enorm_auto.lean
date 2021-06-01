/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.basic
import Mathlib.PostPort

universes u_1 u_2 l 

namespace Mathlib

/-!
# Extended norm

In this file we define a structure `enorm 𝕜 V` representing an extended norm (i.e., a norm that can
take the value `∞`) on a vector space `V` over a normed field `𝕜`. We do not use `class` for
an `enorm` because the same space can have more than one extended norm. For example, the space of
measurable functions `f : α → ℝ` has a family of `L_p` extended norms.

We prove some basic inequalities, then define

* `emetric_space` structure on `V` corresponding to `e : enorm 𝕜 V`;
* the subspace of vectors with finite norm, called `e.finite_subspace`;
* a `normed_space` structure on this space.

The last definition is an instance because the type involves `e`.

## Implementation notes

We do not define extended normed groups. They can be added to the chain once someone will need them.

## Tags

normed space, extended norm
-/

/-- Extended norm on a vector space. As in the case of normed spaces, we require only
`∥c • x∥ ≤ ∥c∥ * ∥x∥` in the definition, then prove an equality in `map_smul`. -/
structure enorm (𝕜 : Type u_1) (V : Type u_2) [normed_field 𝕜] [add_comm_group V] [vector_space 𝕜 V]
    where
  to_fun : V → ennreal
  eq_zero' : ∀ (x : V), to_fun x = 0 → x = 0
  map_add_le' : ∀ (x y : V), to_fun (x + y) ≤ to_fun x + to_fun y
  map_smul_le' : ∀ (c : 𝕜) (x : V), to_fun (c • x) ≤ ↑(nnnorm c) * to_fun x

namespace enorm


protected instance has_coe_to_fun {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] : has_coe_to_fun (enorm 𝕜 V) :=
  has_coe_to_fun.mk (fun (x : enorm 𝕜 V) => V → ennreal) to_fun

theorem injective_coe_fn {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] : function.injective fun (e : enorm 𝕜 V) (x : V) => coe_fn e x :=
  sorry

theorem ext {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V] [vector_space 𝕜 V]
    {e₁ : enorm 𝕜 V} {e₂ : enorm 𝕜 V} (h : ∀ (x : V), coe_fn e₁ x = coe_fn e₂ x) : e₁ = e₂ :=
  injective_coe_fn (funext h)

theorem ext_iff {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V] [vector_space 𝕜 V]
    {e₁ : enorm 𝕜 V} {e₂ : enorm 𝕜 V} : e₁ = e₂ ↔ ∀ (x : V), coe_fn e₁ x = coe_fn e₂ x :=
  { mp := fun (h : e₁ = e₂) (x : V) => h ▸ rfl, mpr := ext }

@[simp] theorem coe_inj {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] {e₁ : enorm 𝕜 V} {e₂ : enorm 𝕜 V} : ⇑e₁ = ⇑e₂ ↔ e₁ = e₂ :=
  function.injective.eq_iff injective_coe_fn

@[simp] theorem map_smul {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) (c : 𝕜) (x : V) :
    coe_fn e (c • x) = ↑(nnnorm c) * coe_fn e x :=
  sorry

@[simp] theorem map_zero {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) : coe_fn e 0 = 0 :=
  sorry

@[simp] theorem eq_zero_iff {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) {x : V} : coe_fn e x = 0 ↔ x = 0 :=
  { mp := eq_zero' e x, mpr := fun (h : x = 0) => Eq.symm h ▸ map_zero e }

@[simp] theorem map_neg {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) (x : V) : coe_fn e (-x) = coe_fn e x :=
  sorry

theorem map_sub_rev {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) (x : V) (y : V) : coe_fn e (x - y) = coe_fn e (y - x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn e (x - y) = coe_fn e (y - x))) (Eq.symm (neg_sub y x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn e (-(y - x)) = coe_fn e (y - x))) (map_neg e (y - x))))
      (Eq.refl (coe_fn e (y - x))))

theorem map_add_le {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) (x : V) (y : V) :
    coe_fn e (x + y) ≤ coe_fn e x + coe_fn e y :=
  map_add_le' e x y

theorem map_sub_le {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) (x : V) (y : V) :
    coe_fn e (x - y) ≤ coe_fn e x + coe_fn e y :=
  sorry

protected instance partial_order {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] : partial_order (enorm 𝕜 V) :=
  partial_order.mk (fun (e₁ e₂ : enorm 𝕜 V) => ∀ (x : V), coe_fn e₁ x ≤ coe_fn e₂ x)
    (preorder.lt._default fun (e₁ e₂ : enorm 𝕜 V) => ∀ (x : V), coe_fn e₁ x ≤ coe_fn e₂ x) sorry
    sorry sorry

/-- The `enorm` sending each non-zero vector to infinity. -/
protected instance has_top {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] : has_top (enorm 𝕜 V) :=
  has_top.mk (mk (fun (x : V) => ite (x = 0) 0 ⊤) sorry sorry sorry)

protected instance inhabited {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] : Inhabited (enorm 𝕜 V) :=
  { default := ⊤ }

theorem top_map {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V] [vector_space 𝕜 V]
    {x : V} (hx : x ≠ 0) : coe_fn ⊤ x = ⊤ :=
  if_neg hx

protected instance semilattice_sup_top {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜]
    [add_comm_group V] [vector_space 𝕜 V] : semilattice_sup_top (enorm 𝕜 V) :=
  semilattice_sup_top.mk ⊤ LessEq Less sorry sorry sorry sorry
    (fun (e₁ e₂ : enorm 𝕜 V) =>
      mk (fun (x : V) => max (coe_fn e₁ x) (coe_fn e₂ x)) sorry sorry sorry)
    sorry sorry sorry

@[simp] theorem coe_max {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e₁ : enorm 𝕜 V) (e₂ : enorm 𝕜 V) :
    ⇑(e₁ ⊔ e₂) = fun (x : V) => max (coe_fn e₁ x) (coe_fn e₂ x) :=
  rfl

theorem max_map {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V] [vector_space 𝕜 V]
    (e₁ : enorm 𝕜 V) (e₂ : enorm 𝕜 V) (x : V) :
    coe_fn (e₁ ⊔ e₂) x = max (coe_fn e₁ x) (coe_fn e₂ x) :=
  rfl

/-- Structure of an `emetric_space` defined by an extended norm. -/
def emetric_space {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) : emetric_space V :=
  emetric_space.mk sorry sorry (map_sub_rev e) sorry
    (uniform_space_of_edist (fun (x y : V) => coe_fn e (x - y)) sorry (map_sub_rev e) sorry)

/-- The subspace of vectors with finite enorm. -/
def finite_subspace {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) : subspace 𝕜 V :=
  submodule.mk (set_of fun (x : V) => coe_fn e x < ⊤) sorry sorry sorry

/-- Metric space structure on `e.finite_subspace`. We use `emetric_space.to_metric_space_of_dist`
to ensure that this definition agrees with `e.emetric_space`. -/
protected instance finite_subspace.metric_space {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜]
    [add_comm_group V] [vector_space 𝕜 V] (e : enorm 𝕜 V) : metric_space ↥(finite_subspace e) :=
  let _inst : emetric_space V := emetric_space e;
  emetric_space.to_metric_space_of_dist
    (fun (x y : ↥(finite_subspace e)) => ennreal.to_real (edist x y)) sorry sorry

theorem finite_dist_eq {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) (x : ↥(finite_subspace e)) (y : ↥(finite_subspace e)) :
    dist x y = ennreal.to_real (coe_fn e (↑x - ↑y)) :=
  rfl

theorem finite_edist_eq {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) (x : ↥(finite_subspace e)) (y : ↥(finite_subspace e)) :
    edist x y = coe_fn e (↑x - ↑y) :=
  rfl

/-- Normed group instance on `e.finite_subspace`. -/
protected instance finite_subspace.normed_group {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜]
    [add_comm_group V] [vector_space 𝕜 V] (e : enorm 𝕜 V) : normed_group ↥(finite_subspace e) :=
  normed_group.mk sorry

theorem finite_norm_eq {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜] [add_comm_group V]
    [vector_space 𝕜 V] (e : enorm 𝕜 V) (x : ↥(finite_subspace e)) :
    norm x = ennreal.to_real (coe_fn e ↑x) :=
  rfl

/-- Normed space instance on `e.finite_subspace`. -/
protected instance finite_subspace.normed_space {𝕜 : Type u_1} {V : Type u_2} [normed_field 𝕜]
    [add_comm_group V] [vector_space 𝕜 V] (e : enorm 𝕜 V) : normed_space 𝕜 ↥(finite_subspace e) :=
  normed_space.mk sorry

end Mathlib