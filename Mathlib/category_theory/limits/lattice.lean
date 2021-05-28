/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.finite_limits
import Mathlib.order.complete_lattice
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace category_theory.limits.complete_lattice


protected instance has_finite_limits_of_semilattice_inf_top {α : Type u} [semilattice_inf_top α] : has_finite_limits α :=
  fun (J : Type u) (𝒥₁ : small_category J) (𝒥₂ : fin_category J) =>
    has_limits_of_shape.mk
      fun (F : J ⥤ α) =>
        has_limit.mk
          (limit_cone.mk
            (cone.mk (finset.inf finset.univ (functor.obj F))
              (nat_trans.mk fun (j : J) => hom_of_le (finset.inf_le (fintype.complete j))))
            (is_limit.mk
              fun (s : cone F) =>
                hom_of_le
                  (finset.le_inf
                    fun (j : J) (_x : j ∈ finset.univ) => plift.down (ulift.down (nat_trans.app (cone.π s) j)))))

protected instance has_finite_colimits_of_semilattice_sup_bot {α : Type u} [semilattice_sup_bot α] : has_finite_colimits α :=
  fun (J : Type u) (𝒥₁ : small_category J) (𝒥₂ : fin_category J) =>
    has_colimits_of_shape.mk
      fun (F : J ⥤ α) =>
        has_colimit.mk
          (colimit_cocone.mk
            (cocone.mk (finset.sup finset.univ (functor.obj F))
              (nat_trans.mk fun (i : J) => hom_of_le (finset.le_sup (fintype.complete i))))
            (is_colimit.mk
              fun (s : cocone F) =>
                hom_of_le
                  (finset.sup_le
                    fun (j : J) (_x : j ∈ finset.univ) => plift.down (ulift.down (nat_trans.app (cocone.ι s) j)))))

/--
The limit cone over any functor into a complete lattice.
-/
def limit_cone {α : Type u} {J : Type u} [small_category J] [complete_lattice α] (F : J ⥤ α) : limit_cone F :=
  limit_cone.mk (cone.mk (infi (functor.obj F)) (nat_trans.mk fun (j : J) => hom_of_le sorry))
    (is_limit.mk fun (s : cone F) => hom_of_le sorry)

/--
The colimit cocone over any functor into a complete lattice.
-/
def colimit_cocone {α : Type u} {J : Type u} [small_category J] [complete_lattice α] (F : J ⥤ α) : colimit_cocone F :=
  colimit_cocone.mk (cocone.mk (supr (functor.obj F)) (nat_trans.mk fun (j : J) => hom_of_le sorry))
    (is_colimit.mk fun (s : cocone F) => hom_of_le sorry)

-- It would be nice to only use the `Inf` half of the complete lattice, but

-- this seems not to have been described separately.

protected instance has_limits_of_complete_lattice {α : Type u} [complete_lattice α] : has_limits α :=
  has_limits.mk
    fun (J : Type u) (𝒥 : small_category J) => has_limits_of_shape.mk fun (F : J ⥤ α) => has_limit.mk (limit_cone F)

protected instance has_colimits_of_complete_lattice {α : Type u} [complete_lattice α] : has_colimits α :=
  has_colimits.mk
    fun (J : Type u) (𝒥 : small_category J) =>
      has_colimits_of_shape.mk fun (F : J ⥤ α) => has_colimit.mk (colimit_cocone F)

/--
The limit of a functor into a complete lattice is the infimum of the objects in the image.
-/
def limit_iso_infi {α : Type u} {J : Type u} [small_category J] [complete_lattice α] (F : J ⥤ α) : limit F ≅ infi (functor.obj F) :=
  is_limit.cone_point_unique_up_to_iso (limit.is_limit F) (limit_cone.is_limit (limit_cone F))

@[simp] theorem limit_iso_infi_hom {α : Type u} {J : Type u} [small_category J] [complete_lattice α] (F : J ⥤ α) (j : J) : iso.hom (limit_iso_infi F) ≫ hom_of_le (infi_le (functor.obj F) j) = limit.π F j :=
  of_as_true trivial

@[simp] theorem limit_iso_infi_inv {α : Type u} {J : Type u} [small_category J] [complete_lattice α] (F : J ⥤ α) (j : J) : iso.inv (limit_iso_infi F) ≫ limit.π F j = hom_of_le (infi_le (functor.obj F) j) :=
  rfl

/--
The colimit of a functor into a complete lattice is the supremum of the objects in the image.
-/
def colimit_iso_supr {α : Type u} {J : Type u} [small_category J] [complete_lattice α] (F : J ⥤ α) : colimit F ≅ supr (functor.obj F) :=
  is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F) (colimit_cocone.is_colimit (colimit_cocone F))

@[simp] theorem colimit_iso_supr_hom {α : Type u} {J : Type u} [small_category J] [complete_lattice α] (F : J ⥤ α) (j : J) : colimit.ι F j ≫ iso.hom (colimit_iso_supr F) = hom_of_le (le_supr (functor.obj F) j) :=
  rfl

@[simp] theorem colimit_iso_supr_inv {α : Type u} {J : Type u} [small_category J] [complete_lattice α] (F : J ⥤ α) (j : J) : hom_of_le (le_supr (functor.obj F) j) ≫ iso.inv (colimit_iso_supr F) = colimit.ι F j :=
  of_as_true trivial

