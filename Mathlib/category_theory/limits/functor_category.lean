/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.preserves.limits
import Mathlib.PostPort

universes v v₂ u 

namespace Mathlib

namespace category_theory.limits


@[simp] theorem limit.lift_π_app {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] (H : J ⥤ K ⥤ C) [has_limit H] (c : cone H) (j : J) (k : K) : nat_trans.app (limit.lift H c) k ≫ nat_trans.app (limit.π H j) k = nat_trans.app (nat_trans.app (cone.π c) j) k :=
  congr_app (limit.lift_π c j) k

@[simp] theorem colimit.ι_desc_app_assoc {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] (H : J ⥤ K ⥤ C) [has_colimit H] (c : cocone H) (j : J) (k : K) {X' : C} (f' : functor.obj (cocone.X c) k ⟶ X') : nat_trans.app (colimit.ι H j) k ≫ nat_trans.app (colimit.desc H c) k ≫ f' =
  nat_trans.app (nat_trans.app (cocone.ι c) j) k ≫ f' := sorry

/--
The evaluation functors jointly reflect limits: that is, to show a cone is a limit of `F`
it suffices to show that each evaluation cone is a limit. In other words, to prove a cone is
limiting you can show it's pointwise limiting.
-/
def evaluation_jointly_reflects_limits {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] {F : J ⥤ K ⥤ C} (c : cone F) (t : (k : K) → is_limit (functor.map_cone (functor.obj (evaluation K C) k) c)) : is_limit c :=
  is_limit.mk
    fun (s : cone F) =>
      nat_trans.mk
        fun (k : K) =>
          is_limit.lift (t k)
            (cone.mk (functor.obj (cone.X s) k) (whisker_right (cone.π s) (functor.obj (evaluation K C) k)))

/--
Given a functor `F` and a collection of limit cones for each diagram `X ↦ F X k`, we can stitch
them together to give a cone for the diagram `F`.
`combined_is_limit` shows that the new cone is limiting, and `eval_combined` shows it is
(essentially) made up of the original cones.
-/
@[simp] theorem combine_cones_X_obj {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] (F : J ⥤ K ⥤ C) (c : (k : K) → limit_cone (functor.obj (functor.flip F) k)) (k : K) : functor.obj (cone.X (combine_cones F c)) k = cone.X (limit_cone.cone (c k)) :=
  Eq.refl (functor.obj (cone.X (combine_cones F c)) k)

/-- The stitched together cones each project down to the original given cones (up to iso). -/
def evaluate_combined_cones {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] (F : J ⥤ K ⥤ C) (c : (k : K) → limit_cone (functor.obj (functor.flip F) k)) (k : K) : functor.map_cone (functor.obj (evaluation K C) k) (combine_cones F c) ≅ limit_cone.cone (c k) :=
  cones.ext (iso.refl (cone.X (functor.map_cone (functor.obj (evaluation K C) k) (combine_cones F c)))) sorry

/-- Stitching together limiting cones gives a limiting cone. -/
def combined_is_limit {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] (F : J ⥤ K ⥤ C) (c : (k : K) → limit_cone (functor.obj (functor.flip F) k)) : is_limit (combine_cones F c) :=
  evaluation_jointly_reflects_limits (combine_cones F c)
    fun (k : K) => is_limit.of_iso_limit (limit_cone.is_limit (c k)) (iso.symm (evaluate_combined_cones F c k))

/--
The evaluation functors jointly reflect colimits: that is, to show a cocone is a colimit of `F`
it suffices to show that each evaluation cocone is a colimit. In other words, to prove a cocone is
colimiting you can show it's pointwise colimiting.
-/
def evaluation_jointly_reflects_colimits {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] {F : J ⥤ K ⥤ C} (c : cocone F) (t : (k : K) → is_colimit (functor.map_cocone (functor.obj (evaluation K C) k) c)) : is_colimit c :=
  is_colimit.mk
    fun (s : cocone F) =>
      nat_trans.mk
        fun (k : K) =>
          is_colimit.desc (t k)
            (cocone.mk (functor.obj (cocone.X s) k) (whisker_right (cocone.ι s) (functor.obj (evaluation K C) k)))

/--
Given a functor `F` and a collection of colimit cocones for each diagram `X ↦ F X k`, we can stitch
them together to give a cocone for the diagram `F`.
`combined_is_colimit` shows that the new cocone is colimiting, and `eval_combined` shows it is
(essentially) made up of the original cocones.
-/
def combine_cocones {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] (F : J ⥤ K ⥤ C) (c : (k : K) → colimit_cocone (functor.obj (functor.flip F) k)) : cocone F :=
  cocone.mk
    (functor.mk (fun (k : K) => cocone.X (colimit_cocone.cocone (c k)))
      fun (k₁ k₂ : K) (f : k₁ ⟶ k₂) =>
        is_colimit.desc (colimit_cocone.is_colimit (c k₁))
          (cocone.mk (cocone.X (colimit_cocone.cocone (c k₂)))
            (functor.map (functor.flip F) f ≫ cocone.ι (colimit_cocone.cocone (c k₂)))))
    (nat_trans.mk fun (j : J) => nat_trans.mk fun (k : K) => nat_trans.app (cocone.ι (colimit_cocone.cocone (c k))) j)

/-- The stitched together cocones each project down to the original given cocones (up to iso). -/
def evaluate_combined_cocones {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] (F : J ⥤ K ⥤ C) (c : (k : K) → colimit_cocone (functor.obj (functor.flip F) k)) (k : K) : functor.map_cocone (functor.obj (evaluation K C) k) (combine_cocones F c) ≅ colimit_cocone.cocone (c k) :=
  cocones.ext (iso.refl (cocone.X (functor.map_cocone (functor.obj (evaluation K C) k) (combine_cocones F c)))) sorry

/-- Stitching together colimiting cocones gives a colimiting cocone. -/
def combined_is_colimit {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] (F : J ⥤ K ⥤ C) (c : (k : K) → colimit_cocone (functor.obj (functor.flip F) k)) : is_colimit (combine_cocones F c) :=
  evaluation_jointly_reflects_colimits (combine_cocones F c)
    fun (k : K) =>
      is_colimit.of_iso_colimit (colimit_cocone.is_colimit (c k)) (iso.symm (evaluate_combined_cocones F c k))

protected instance functor_category_has_limits_of_shape {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] [has_limits_of_shape J C] : has_limits_of_shape J (K ⥤ C) :=
  has_limits_of_shape.mk
    fun (F : J ⥤ K ⥤ C) =>
      has_limit.mk
        (limit_cone.mk (combine_cones F fun (k : K) => get_limit_cone (functor.obj (functor.flip F) k))
          (combined_is_limit F fun (k : K) => get_limit_cone (functor.obj (functor.flip F) k)))

protected instance functor_category_has_colimits_of_shape {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] [has_colimits_of_shape J C] : has_colimits_of_shape J (K ⥤ C) :=
  has_colimits_of_shape.mk
    fun (F : J ⥤ K ⥤ C) =>
      has_colimit.mk
        (colimit_cocone.mk (combine_cocones F fun (k : K) => get_colimit_cocone (functor.obj (functor.flip F) k))
          (combined_is_colimit F fun (k : K) => get_colimit_cocone (functor.obj (functor.flip F) k)))

protected instance functor_category_has_limits {C : Type u} [category C] {K : Type v} [category K] [has_limits C] : has_limits (K ⥤ C) :=
  has_limits.mk fun (J : Type v) (𝒥 : small_category J) => limits.functor_category_has_limits_of_shape

protected instance functor_category_has_colimits {C : Type u} [category C] {K : Type v} [category K] [has_colimits C] : has_colimits (K ⥤ C) :=
  has_colimits.mk fun (J : Type v) (𝒥 : small_category J) => limits.functor_category_has_colimits_of_shape

protected instance evaluation_preserves_limits_of_shape {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] [has_limits_of_shape J C] (k : K) : preserves_limits_of_shape J (functor.obj (evaluation K C) k) :=
  preserves_limits_of_shape.mk
    fun (F : J ⥤ K ⥤ C) =>
      preserves_limit_of_preserves_limit_cone
        (combined_is_limit F fun (k : K) => get_limit_cone (F ⋙ functor.obj (evaluation K C) k))
        (is_limit.of_iso_limit (limit.is_limit (F ⋙ functor.obj (evaluation K C) k))
          (iso.symm (evaluate_combined_cones F (fun (k : K) => get_limit_cone (F ⋙ functor.obj (evaluation K C) k)) k)))

/--
If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a limit,
then the evaluation of that limit at `k` is the limit of the evaluations of `F.obj j` at `k`.
-/
def limit_obj_iso_limit_comp_evaluation {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) (k : K) : functor.obj (limit F) k ≅ limit (F ⋙ functor.obj (evaluation K C) k) :=
  preserves_limit_iso (functor.obj (evaluation K C) k) F

@[simp] theorem limit_obj_iso_limit_comp_evaluation_hom_π {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) : iso.hom (limit_obj_iso_limit_comp_evaluation F k) ≫ limit.π (F ⋙ functor.obj (evaluation K C) k) j =
  nat_trans.app (limit.π F j) k := sorry

@[simp] theorem limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) {X' : C} (f' : functor.obj (functor.obj F j) k ⟶ X') : iso.inv (limit_obj_iso_limit_comp_evaluation F k) ≫ nat_trans.app (limit.π F j) k ≫ f' =
  limit.π (F ⋙ functor.obj (evaluation K C) k) j ≫ f' := sorry

theorem limit_obj_ext {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] {H : J ⥤ K ⥤ C} [has_limits_of_shape J C] {k : K} {W : C} {f : W ⟶ functor.obj (limit H) k} {g : W ⟶ functor.obj (limit H) k} (w : ∀ (j : J), f ≫ nat_trans.app (limit.π H j) k = g ≫ nat_trans.app (limit.π H j) k) : f = g := sorry

protected instance evaluation_preserves_colimits_of_shape {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] [has_colimits_of_shape J C] (k : K) : preserves_colimits_of_shape J (functor.obj (evaluation K C) k) :=
  preserves_colimits_of_shape.mk
    fun (F : J ⥤ K ⥤ C) =>
      preserves_colimit_of_preserves_colimit_cocone
        (combined_is_colimit F fun (k : K) => get_colimit_cocone (F ⋙ functor.obj (evaluation K C) k))
        (is_colimit.of_iso_colimit (colimit.is_colimit (F ⋙ functor.obj (evaluation K C) k))
          (iso.symm
            (evaluate_combined_cocones F (fun (k : K) => get_colimit_cocone (F ⋙ functor.obj (evaluation K C) k)) k)))

/--
If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a colimit,
then the evaluation of that colimit at `k` is the colimit of the evaluations of `F.obj j` at `k`.
-/
def colimit_obj_iso_colimit_comp_evaluation {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) (k : K) : functor.obj (colimit F) k ≅ colimit (F ⋙ functor.obj (evaluation K C) k) :=
  preserves_colimit_iso (functor.obj (evaluation K C) k) F

@[simp] theorem colimit_obj_iso_colimit_comp_evaluation_ι_inv {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) : colimit.ι (F ⋙ functor.obj (evaluation K C) k) j ≫ iso.inv (colimit_obj_iso_colimit_comp_evaluation F k) =
  nat_trans.app (colimit.ι F j) k := sorry

@[simp] theorem colimit_obj_iso_colimit_comp_evaluation_ι_app_hom {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) : nat_trans.app (colimit.ι F j) k ≫ iso.hom (colimit_obj_iso_colimit_comp_evaluation F k) =
  colimit.ι (F ⋙ functor.obj (evaluation K C) k) j := sorry

theorem colimit_obj_ext {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [category K] {H : J ⥤ K ⥤ C} [has_colimits_of_shape J C] {k : K} {W : C} {f : functor.obj (colimit H) k ⟶ W} {g : functor.obj (colimit H) k ⟶ W} (w : ∀ (j : J), nat_trans.app (colimit.ι H j) k ≫ f = nat_trans.app (colimit.ι H j) k ≫ g) : f = g := sorry

protected instance evaluation_preserves_limits {C : Type u} [category C] {K : Type v} [category K] [has_limits C] (k : K) : preserves_limits (functor.obj (evaluation K C) k) :=
  preserves_limits.mk fun (J : Type v) (𝒥 : small_category J) => limits.evaluation_preserves_limits_of_shape k

protected instance evaluation_preserves_colimits {C : Type u} [category C] {K : Type v} [category K] [has_colimits C] (k : K) : preserves_colimits (functor.obj (evaluation K C) k) :=
  preserves_colimits.mk fun (J : Type v) (𝒥 : small_category J) => limits.evaluation_preserves_colimits_of_shape k

