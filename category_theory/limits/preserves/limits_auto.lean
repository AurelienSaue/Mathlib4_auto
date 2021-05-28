/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.preserves.basic
import PostPort

universes v u₁ u₂ 

namespace Mathlib

/-!
# Isomorphisms about functors which preserve (co)limits

If `G` preserves limits, and `C` and `D` have limits, then for any diagram `F : J ⥤ C` we have a
canonical isomorphism `preserves_limit_iso : G.obj (limit F) ≅ limit (F ⋙ G)`.
We also show that we can commute `is_limit.lift` of a preserved limit with `functor.map_cone`:
`(preserves_limit.preserves t).lift (G.map_cone c₂) = G.map (t.lift c₂)`.

The duals of these are also given. For functors which preserve (co)limits of specific shapes, see
`preserves/shapes.lean`.
-/

namespace category_theory


@[simp] theorem preserves_lift_map_cone {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {J : Type v} [small_category J] (F : J ⥤ C) [limits.preserves_limit F G] (c₁ : limits.cone F) (c₂ : limits.cone F) (t : limits.is_limit c₁) : limits.is_limit.lift (limits.preserves_limit.preserves t) (functor.map_cone G c₂) =
  functor.map G (limits.is_limit.lift t c₂) := sorry

/--
If `G` preserves limits, we have an isomorphism from the image of the limit of a functor `F`
to the limit of the functor `F ⋙ G`.
-/
def preserves_limit_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {J : Type v} [small_category J] (F : J ⥤ C) [limits.preserves_limit F G] [limits.has_limit F] [limits.has_limit (F ⋙ G)] : functor.obj G (limits.limit F) ≅ limits.limit (F ⋙ G) :=
  limits.is_limit.cone_point_unique_up_to_iso (limits.preserves_limit.preserves (limits.limit.is_limit F))
    (limits.limit.is_limit (F ⋙ G))

@[simp] theorem preserves_limits_iso_hom_π_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {J : Type v} [small_category J] (F : J ⥤ C) [limits.preserves_limit F G] [limits.has_limit F] [limits.has_limit (F ⋙ G)] (j : J) {X' : D} (f' : functor.obj (F ⋙ G) j ⟶ X') : iso.hom (preserves_limit_iso G F) ≫ limits.limit.π (F ⋙ G) j ≫ f' = functor.map G (limits.limit.π F j) ≫ f' := sorry

@[simp] theorem preserves_limits_iso_inv_π_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {J : Type v} [small_category J] (F : J ⥤ C) [limits.preserves_limit F G] [limits.has_limit F] [limits.has_limit (F ⋙ G)] (j : J) {X' : D} (f' : functor.obj G (functor.obj F j) ⟶ X') : iso.inv (preserves_limit_iso G F) ≫ functor.map G (limits.limit.π F j) ≫ f' = limits.limit.π (F ⋙ G) j ≫ f' := sorry

@[simp] theorem lift_comp_preserves_limits_iso_hom_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {J : Type v} [small_category J] (F : J ⥤ C) [limits.preserves_limit F G] [limits.has_limit F] [limits.has_limit (F ⋙ G)] (t : limits.cone F) {X' : D} (f' : limits.limit (F ⋙ G) ⟶ X') : functor.map G (limits.limit.lift F t) ≫ iso.hom (preserves_limit_iso G F) ≫ f' =
  limits.limit.lift (F ⋙ G) (functor.map_cone G t) ≫ f' := sorry

@[simp] theorem preserves_desc_map_cocone {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {J : Type v} [small_category J] (F : J ⥤ C) [limits.preserves_colimit F G] (c₁ : limits.cocone F) (c₂ : limits.cocone F) (t : limits.is_colimit c₁) : limits.is_colimit.desc (limits.preserves_colimit.preserves t) (functor.map_cocone G c₂) =
  functor.map G (limits.is_colimit.desc t c₂) := sorry

/--
If `G` preserves colimits, we have an isomorphism from the image of the colimit of a functor `F`
to the colimit of the functor `F ⋙ G`.
-/
-- TODO: think about swapping the order here

def preserves_colimit_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {J : Type v} [small_category J] (F : J ⥤ C) [limits.preserves_colimit F G] [limits.has_colimit F] [limits.has_colimit (F ⋙ G)] : functor.obj G (limits.colimit F) ≅ limits.colimit (F ⋙ G) :=
  limits.is_colimit.cocone_point_unique_up_to_iso (limits.preserves_colimit.preserves (limits.colimit.is_colimit F))
    (limits.colimit.is_colimit (F ⋙ G))

@[simp] theorem ι_preserves_colimits_iso_inv_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {J : Type v} [small_category J] (F : J ⥤ C) [limits.preserves_colimit F G] [limits.has_colimit F] [limits.has_colimit (F ⋙ G)] (j : J) {X' : D} (f' : functor.obj G (limits.colimit F) ⟶ X') : limits.colimit.ι (F ⋙ G) j ≫ iso.inv (preserves_colimit_iso G F) ≫ f' = functor.map G (limits.colimit.ι F j) ≫ f' := sorry

@[simp] theorem ι_preserves_colimits_iso_hom_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {J : Type v} [small_category J] (F : J ⥤ C) [limits.preserves_colimit F G] [limits.has_colimit F] [limits.has_colimit (F ⋙ G)] (j : J) {X' : D} (f' : limits.colimit (F ⋙ G) ⟶ X') : functor.map G (limits.colimit.ι F j) ≫ iso.hom (preserves_colimit_iso G F) ≫ f' = limits.colimit.ι (F ⋙ G) j ≫ f' := sorry

@[simp] theorem preserves_colimits_iso_inv_comp_desc {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {J : Type v} [small_category J] (F : J ⥤ C) [limits.preserves_colimit F G] [limits.has_colimit F] [limits.has_colimit (F ⋙ G)] (t : limits.cocone F) : iso.inv (preserves_colimit_iso G F) ≫ functor.map G (limits.colimit.desc F t) =
  limits.colimit.desc (F ⋙ G) (functor.map_cocone G t) := sorry

