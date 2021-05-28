/-
Copyright (c) 2019 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.filter.lift
import Mathlib.topology.opens
import Mathlib.topology.algebra.ring
import PostPort

universes u_1 l u_2 

namespace Mathlib

/-- The type of open subgroups of a topological additive group. -/
structure open_add_subgroup (G : Type u_1) [add_group G] [topological_space G] 
extends add_subgroup G
where
  is_open' : is_open carrier

/-- The type of open subgroups of a topological group. -/
structure open_subgroup (G : Type u_1) [group G] [topological_space G] 
extends subgroup G
where
  is_open' : is_open carrier

/-- Reinterpret an `open_subgroup` as a `subgroup`. -/
/-- Reinterpret an `open_add_subgroup` as an `add_subgroup`. -/
-- Tell Lean that `open_add_subgroup` is a namespace

namespace open_add_subgroup


end open_add_subgroup


namespace open_subgroup


protected instance has_coe_set {G : Type u_1} [group G] [topological_space G] : has_coe_t (open_subgroup G) (set G) :=
  has_coe_t.mk fun (U : open_subgroup G) => carrier U

protected instance has_mem {G : Type u_1} [group G] [topological_space G] : has_mem G (open_subgroup G) :=
  has_mem.mk fun (g : G) (U : open_subgroup G) => g ∈ ↑U

protected instance has_coe_subgroup {G : Type u_1} [group G] [topological_space G] : has_coe_t (open_subgroup G) (subgroup G) :=
  has_coe_t.mk to_subgroup

protected instance has_coe_opens {G : Type u_1} [group G] [topological_space G] : has_coe_t (open_subgroup G) (topological_space.opens G) :=
  has_coe_t.mk fun (U : open_subgroup G) => { val := ↑U, property := is_open' U }

@[simp] theorem mem_coe {G : Type u_1} [group G] [topological_space G] {U : open_subgroup G} {g : G} : g ∈ ↑U ↔ g ∈ U :=
  iff.rfl

@[simp] theorem mem_coe_opens {G : Type u_1} [group G] [topological_space G] {U : open_subgroup G} {g : G} : g ∈ ↑U ↔ g ∈ U :=
  iff.rfl

@[simp] theorem mem_coe_subgroup {G : Type u_1} [group G] [topological_space G] {U : open_subgroup G} {g : G} : g ∈ ↑U ↔ g ∈ U :=
  iff.rfl

theorem coe_injective {G : Type u_1} [group G] [topological_space G] : function.injective coe := sorry

theorem ext {G : Type u_1} [group G] [topological_space G] {U : open_subgroup G} {V : open_subgroup G} (h : ∀ (x : G), x ∈ U ↔ x ∈ V) : U = V :=
  coe_injective (set.ext h)

theorem ext_iff {G : Type u_1} [group G] [topological_space G] {U : open_subgroup G} {V : open_subgroup G} : U = V ↔ ∀ (x : G), x ∈ U ↔ x ∈ V :=
  { mp := fun (h : U = V) (x : G) => h ▸ iff.rfl, mpr := ext }

protected theorem is_open {G : Type u_1} [group G] [topological_space G] (U : open_subgroup G) : is_open ↑U :=
  is_open' U

protected theorem one_mem {G : Type u_1} [group G] [topological_space G] (U : open_subgroup G) : 1 ∈ U :=
  one_mem' U

protected theorem inv_mem {G : Type u_1} [group G] [topological_space G] (U : open_subgroup G) {g : G} (h : g ∈ U) : g⁻¹ ∈ U :=
  inv_mem' U h

protected theorem Mathlib.open_add_subgroup.add_mem {G : Type u_1} [add_group G] [topological_space G] (U : open_add_subgroup G) {g₁ : G} {g₂ : G} (h₁ : g₁ ∈ U) (h₂ : g₂ ∈ U) : g₁ + g₂ ∈ U :=
  open_add_subgroup.add_mem' U h₁ h₂

theorem mem_nhds_one {G : Type u_1} [group G] [topological_space G] (U : open_subgroup G) : ↑U ∈ nhds 1 :=
  mem_nhds_sets (open_subgroup.is_open U) (open_subgroup.one_mem U)

protected instance has_top {G : Type u_1} [group G] [topological_space G] : has_top (open_subgroup G) :=
  has_top.mk (mk (subgroup.carrier ⊤) sorry sorry sorry is_open_univ)

protected instance inhabited {G : Type u_1} [group G] [topological_space G] : Inhabited (open_subgroup G) :=
  { default := ⊤ }

theorem is_closed {G : Type u_1} [group G] [topological_space G] [has_continuous_mul G] (U : open_subgroup G) : is_closed ↑U := sorry

/-- The product of two open subgroups as an open subgroup of the product group. -/
def prod {G : Type u_1} [group G] [topological_space G] {H : Type u_2} [group H] [topological_space H] (U : open_subgroup G) (V : open_subgroup H) : open_subgroup (G × H) :=
  mk (set.prod ↑U ↑V) sorry sorry sorry sorry

protected instance partial_order {G : Type u_1} [group G] [topological_space G] : partial_order (open_subgroup G) :=
  partial_order.mk (fun (U V : open_subgroup G) => ∀ {x : G}, x ∈ U → x ∈ V) partial_order.lt sorry sorry sorry

protected instance semilattice_inf_top {G : Type u_1} [group G] [topological_space G] : semilattice_inf_top (open_subgroup G) :=
  semilattice_inf_top.mk ⊤ partial_order.le partial_order.lt sorry sorry sorry sorry
    (fun (U V : open_subgroup G) => mk (subgroup.carrier (↑U ⊓ ↑V)) sorry sorry sorry sorry) sorry sorry sorry

@[simp] theorem coe_inf {G : Type u_1} [group G] [topological_space G] {U : open_subgroup G} {V : open_subgroup G} : ↑(U ⊓ V) = ↑U ∩ ↑V :=
  rfl

@[simp] theorem coe_subset {G : Type u_1} [group G] [topological_space G] {U : open_subgroup G} {V : open_subgroup G} : ↑U ⊆ ↑V ↔ U ≤ V :=
  iff.rfl

@[simp] theorem coe_subgroup_le {G : Type u_1} [group G] [topological_space G] {U : open_subgroup G} {V : open_subgroup G} : ↑U ≤ ↑V ↔ U ≤ V :=
  iff.rfl

end open_subgroup


namespace subgroup


theorem Mathlib.add_subgroup.is_open_of_mem_nhds {G : Type u_1} [add_group G] [topological_space G] [has_continuous_add G] (H : add_subgroup G) {g : G} (hg : ↑H ∈ nhds g) : is_open ↑H := sorry

theorem is_open_of_open_subgroup {G : Type u_1} [group G] [topological_space G] [has_continuous_mul G] (H : subgroup G) {U : open_subgroup G} (h : open_subgroup.carrier U ≤ ↑H) : is_open ↑H :=
  is_open_of_mem_nhds H (filter.mem_sets_of_superset (open_subgroup.mem_nhds_one U) h)

theorem is_open_mono {G : Type u_1} [group G] [topological_space G] [has_continuous_mul G] {H₁ : subgroup G} {H₂ : subgroup G} (h : H₁ ≤ H₂) (h₁ : is_open ↑H₁) : is_open ↑H₂ :=
  is_open_of_open_subgroup H₂ h

end subgroup


namespace open_subgroup


protected instance semilattice_sup_top {G : Type u_1} [group G] [topological_space G] [has_continuous_mul G] : semilattice_sup_top (open_subgroup G) :=
  semilattice_sup_top.mk semilattice_inf_top.top semilattice_inf_top.le semilattice_inf_top.lt sorry sorry sorry sorry
    (fun (U V : open_subgroup G) => mk (subgroup.carrier (↑U ⊔ ↑V)) sorry sorry sorry sorry) sorry sorry sorry

end open_subgroup


namespace submodule


theorem is_open_mono {R : Type u_1} {M : Type u_2} [comm_ring R] [add_comm_group M] [topological_space M] [topological_add_group M] [module R M] {U : submodule R M} {P : submodule R M} (h : U ≤ P) (hU : is_open ↑U) : is_open ↑P :=
  add_subgroup.is_open_mono h hU

end submodule


namespace ideal


theorem is_open_of_open_subideal {R : Type u_1} [comm_ring R] [topological_space R] [topological_ring R] {U : ideal R} {I : ideal R} (h : U ≤ I) (hU : is_open ↑U) : is_open ↑I :=
  submodule.is_open_mono h hU

