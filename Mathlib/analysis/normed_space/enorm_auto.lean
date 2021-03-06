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

In this file we define a structure `enorm š V` representing an extended norm (i.e., a norm that can
take the value `ā`) on a vector space `V` over a normed field `š`. We do not use `class` for
an `enorm` because the same space can have more than one extended norm. For example, the space of
measurable functions `f : Ī± ā ā` has a family of `L_p` extended norms.

We prove some basic inequalities, then define

* `emetric_space` structure on `V` corresponding to `e : enorm š V`;
* the subspace of vectors with finite norm, called `e.finite_subspace`;
* a `normed_space` structure on this space.

The last definition is an instance because the type involves `e`.

## Implementation notes

We do not define extended normed groups. They can be added to the chain once someone will need them.

## Tags

normed space, extended norm
-/

/-- Extended norm on a vector space. As in the case of normed spaces, we require only
`ā„c ā¢ xā„ ā¤ ā„cā„ * ā„xā„` in the definition, then prove an equality in `map_smul`. -/
structure enorm (š : Type u_1) (V : Type u_2) [normed_field š] [add_comm_group V] [vector_space š V]
    where
  to_fun : V ā ennreal
  eq_zero' : ā (x : V), to_fun x = 0 ā x = 0
  map_add_le' : ā (x y : V), to_fun (x + y) ā¤ to_fun x + to_fun y
  map_smul_le' : ā (c : š) (x : V), to_fun (c ā¢ x) ā¤ ā(nnnorm c) * to_fun x

namespace enorm


protected instance has_coe_to_fun {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] : has_coe_to_fun (enorm š V) :=
  has_coe_to_fun.mk (fun (x : enorm š V) => V ā ennreal) to_fun

theorem injective_coe_fn {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] : function.injective fun (e : enorm š V) (x : V) => coe_fn e x :=
  sorry

theorem ext {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V] [vector_space š V]
    {eā : enorm š V} {eā : enorm š V} (h : ā (x : V), coe_fn eā x = coe_fn eā x) : eā = eā :=
  injective_coe_fn (funext h)

theorem ext_iff {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V] [vector_space š V]
    {eā : enorm š V} {eā : enorm š V} : eā = eā ā ā (x : V), coe_fn eā x = coe_fn eā x :=
  { mp := fun (h : eā = eā) (x : V) => h āø rfl, mpr := ext }

@[simp] theorem coe_inj {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] {eā : enorm š V} {eā : enorm š V} : āeā = āeā ā eā = eā :=
  function.injective.eq_iff injective_coe_fn

@[simp] theorem map_smul {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) (c : š) (x : V) :
    coe_fn e (c ā¢ x) = ā(nnnorm c) * coe_fn e x :=
  sorry

@[simp] theorem map_zero {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) : coe_fn e 0 = 0 :=
  sorry

@[simp] theorem eq_zero_iff {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) {x : V} : coe_fn e x = 0 ā x = 0 :=
  { mp := eq_zero' e x, mpr := fun (h : x = 0) => Eq.symm h āø map_zero e }

@[simp] theorem map_neg {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) (x : V) : coe_fn e (-x) = coe_fn e x :=
  sorry

theorem map_sub_rev {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) (x : V) (y : V) : coe_fn e (x - y) = coe_fn e (y - x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn e (x - y) = coe_fn e (y - x))) (Eq.symm (neg_sub y x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn e (-(y - x)) = coe_fn e (y - x))) (map_neg e (y - x))))
      (Eq.refl (coe_fn e (y - x))))

theorem map_add_le {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) (x : V) (y : V) :
    coe_fn e (x + y) ā¤ coe_fn e x + coe_fn e y :=
  map_add_le' e x y

theorem map_sub_le {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) (x : V) (y : V) :
    coe_fn e (x - y) ā¤ coe_fn e x + coe_fn e y :=
  sorry

protected instance partial_order {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] : partial_order (enorm š V) :=
  partial_order.mk (fun (eā eā : enorm š V) => ā (x : V), coe_fn eā x ā¤ coe_fn eā x)
    (preorder.lt._default fun (eā eā : enorm š V) => ā (x : V), coe_fn eā x ā¤ coe_fn eā x) sorry
    sorry sorry

/-- The `enorm` sending each non-zero vector to infinity. -/
protected instance has_top {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] : has_top (enorm š V) :=
  has_top.mk (mk (fun (x : V) => ite (x = 0) 0 ā¤) sorry sorry sorry)

protected instance inhabited {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] : Inhabited (enorm š V) :=
  { default := ā¤ }

theorem top_map {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V] [vector_space š V]
    {x : V} (hx : x ā  0) : coe_fn ā¤ x = ā¤ :=
  if_neg hx

protected instance semilattice_sup_top {š : Type u_1} {V : Type u_2} [normed_field š]
    [add_comm_group V] [vector_space š V] : semilattice_sup_top (enorm š V) :=
  semilattice_sup_top.mk ā¤ LessEq Less sorry sorry sorry sorry
    (fun (eā eā : enorm š V) =>
      mk (fun (x : V) => max (coe_fn eā x) (coe_fn eā x)) sorry sorry sorry)
    sorry sorry sorry

@[simp] theorem coe_max {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (eā : enorm š V) (eā : enorm š V) :
    ā(eā ā eā) = fun (x : V) => max (coe_fn eā x) (coe_fn eā x) :=
  rfl

theorem max_map {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V] [vector_space š V]
    (eā : enorm š V) (eā : enorm š V) (x : V) :
    coe_fn (eā ā eā) x = max (coe_fn eā x) (coe_fn eā x) :=
  rfl

/-- Structure of an `emetric_space` defined by an extended norm. -/
def emetric_space {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) : emetric_space V :=
  emetric_space.mk sorry sorry (map_sub_rev e) sorry
    (uniform_space_of_edist (fun (x y : V) => coe_fn e (x - y)) sorry (map_sub_rev e) sorry)

/-- The subspace of vectors with finite enorm. -/
def finite_subspace {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) : subspace š V :=
  submodule.mk (set_of fun (x : V) => coe_fn e x < ā¤) sorry sorry sorry

/-- Metric space structure on `e.finite_subspace`. We use `emetric_space.to_metric_space_of_dist`
to ensure that this definition agrees with `e.emetric_space`. -/
protected instance finite_subspace.metric_space {š : Type u_1} {V : Type u_2} [normed_field š]
    [add_comm_group V] [vector_space š V] (e : enorm š V) : metric_space ā„(finite_subspace e) :=
  let _inst : emetric_space V := emetric_space e;
  emetric_space.to_metric_space_of_dist
    (fun (x y : ā„(finite_subspace e)) => ennreal.to_real (edist x y)) sorry sorry

theorem finite_dist_eq {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) (x : ā„(finite_subspace e)) (y : ā„(finite_subspace e)) :
    dist x y = ennreal.to_real (coe_fn e (āx - āy)) :=
  rfl

theorem finite_edist_eq {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) (x : ā„(finite_subspace e)) (y : ā„(finite_subspace e)) :
    edist x y = coe_fn e (āx - āy) :=
  rfl

/-- Normed group instance on `e.finite_subspace`. -/
protected instance finite_subspace.normed_group {š : Type u_1} {V : Type u_2} [normed_field š]
    [add_comm_group V] [vector_space š V] (e : enorm š V) : normed_group ā„(finite_subspace e) :=
  normed_group.mk sorry

theorem finite_norm_eq {š : Type u_1} {V : Type u_2} [normed_field š] [add_comm_group V]
    [vector_space š V] (e : enorm š V) (x : ā„(finite_subspace e)) :
    norm x = ennreal.to_real (coe_fn e āx) :=
  rfl

/-- Normed space instance on `e.finite_subspace`. -/
protected instance finite_subspace.normed_space {š : Type u_1} {V : Type u_2} [normed_field š]
    [add_comm_group V] [vector_space š V] (e : enorm š V) : normed_space š ā„(finite_subspace e) :=
  normed_space.mk sorry

end Mathlib