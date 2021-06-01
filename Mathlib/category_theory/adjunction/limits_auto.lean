/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.adjunction.basic
import Mathlib.category_theory.limits.creates
import Mathlib.PostPort

universes u₁ u₂ v 

namespace Mathlib

namespace category_theory.adjunction


/--
The right adjoint of `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
def functoriality_right_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {J : Type v} [small_category J] (K : J ⥤ C) :
    limits.cocone (K ⋙ F) ⥤ limits.cocone K :=
  limits.cocones.functoriality (K ⋙ F) G ⋙
    limits.cocones.precompose
      (iso.inv (functor.right_unitor K) ≫
        whisker_left K (unit adj) ≫ iso.inv (functor.associator K F G))

/--
The unit for the adjunction for `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
def functoriality_unit {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {J : Type v} [small_category J] (K : J ⥤ C) :
    𝟭 ⟶ limits.cocones.functoriality K F ⋙ functoriality_right_adjoint adj K :=
  nat_trans.mk
    fun (c : limits.cocone K) =>
      limits.cocone_morphism.mk (nat_trans.app (unit adj) (limits.cocone.X c))

/--
The counit for the adjunction for `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
def functoriality_counit {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {J : Type v} [small_category J] (K : J ⥤ C) :
    functoriality_right_adjoint adj K ⋙ limits.cocones.functoriality K F ⟶ 𝟭 :=
  nat_trans.mk
    fun (c : limits.cocone (K ⋙ F)) =>
      limits.cocone_morphism.mk (nat_trans.app (counit adj) (limits.cocone.X c))

/-- The functor `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)` is a left adjoint. -/
def functoriality_is_left_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {J : Type v} [small_category J] (K : J ⥤ C) :
    is_left_adjoint (limits.cocones.functoriality K F) :=
  is_left_adjoint.mk (functoriality_right_adjoint adj K)
    (mk_of_unit_counit
      (core_unit_counit.mk (functoriality_unit adj K) (functoriality_counit adj K)))

/--
A left adjoint preserves colimits.

See https://stacks.math.columbia.edu/tag/0038.
-/
def left_adjoint_preserves_colimits {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : limits.preserves_colimits F :=
  limits.preserves_colimits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      limits.preserves_colimits_of_shape.mk
        fun (F_1 : J ⥤ C) =>
          limits.preserves_colimit.mk
            fun (c : limits.cocone F_1) (hc : limits.is_colimit c) =>
              iso.inv limits.is_colimit.iso_unique_cocone_morphism
                fun (s : limits.cocone (F_1 ⋙ F)) =>
                  equiv.unique (hom_equiv is_left_adjoint.adj c s)

protected instance is_equivalence_preserves_colimits {C : Type u₁} [category C] {D : Type u₂}
    [category D] (E : C ⥤ D) [is_equivalence E] : limits.preserves_colimits E :=
  left_adjoint_preserves_colimits (functor.adjunction E)

protected instance is_equivalence_reflects_colimits {C : Type u₁} [category C] {D : Type u₂}
    [category D] (E : D ⥤ C) [is_equivalence E] : limits.reflects_colimits E :=
  limits.reflects_colimits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      limits.reflects_colimits_of_shape.mk
        fun (K : J ⥤ D) =>
          limits.reflects_colimit.mk
            fun (c : limits.cocone K) (t : limits.is_colimit (functor.map_cocone E c)) =>
              limits.is_colimit.of_iso_colimit
                (coe_fn
                  (equiv.symm
                    (limits.is_colimit.precompose_inv_equiv (functor.right_unitor K)
                      (functor.map_cocone 𝟭 c)))
                  (limits.is_colimit.map_cocone_equiv (functor.fun_inv_id E)
                    (limits.is_colimit_of_preserves (functor.inv E) t)))
                (limits.cocones.ext sorry sorry)

protected instance is_equivalence_creates_colimits {C : Type u₁} [category C] {D : Type u₂}
    [category D] (H : D ⥤ C) [is_equivalence H] : creates_colimits H :=
  creates_colimits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      creates_colimits_of_shape.mk
        fun (F : J ⥤ D) =>
          creates_colimit.mk
            fun (c : limits.cocone (F ⋙ H)) (t : limits.is_colimit c) =>
              liftable_cocone.mk (functor.map_cocone_inv H c)
                (functor.map_cocone_map_cocone_inv H c)

-- verify the preserve_colimits instance works as expected:

protected instance has_colimit_comp_equivalence {C : Type u₁} [category C] {D : Type u₂}
    [category D] {J : Type v} [small_category J] (K : J ⥤ C) (E : C ⥤ D) [is_equivalence E]
    [limits.has_colimit K] : limits.has_colimit (K ⋙ E) :=
  limits.has_colimit.mk
    (limits.colimit_cocone.mk (functor.map_cocone E (limits.colimit.cocone K))
      (limits.preserves_colimit.preserves (limits.colimit.is_colimit K)))

theorem has_colimit_of_comp_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D]
    {J : Type v} [small_category J] (K : J ⥤ C) (E : C ⥤ D) [is_equivalence E]
    [limits.has_colimit (K ⋙ E)] : limits.has_colimit K :=
  limits.has_colimit_of_iso
    (iso.symm (functor.right_unitor K) ≪≫ iso.symm (iso_whisker_left K (functor.fun_inv_id E)))

/--
The left adjoint of `cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
def functoriality_left_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {J : Type v} [small_category J] (K : J ⥤ D) :
    limits.cone (K ⋙ G) ⥤ limits.cone K :=
  limits.cones.functoriality (K ⋙ G) F ⋙
    limits.cones.postcompose
      (iso.hom (functor.associator K G F) ≫
        whisker_left K (counit adj) ≫ iso.hom (functor.right_unitor K))

/--
The unit for the adjunction for`cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
@[simp] theorem functoriality_unit'_app_hom {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {J : Type v} [small_category J] (K : J ⥤ D)
    (c : limits.cone (K ⋙ G)) :
    limits.cone_morphism.hom (nat_trans.app (functoriality_unit' adj K) c) =
        nat_trans.app (unit adj) (limits.cone.X c) :=
  Eq.refl (limits.cone_morphism.hom (nat_trans.app (functoriality_unit' adj K) c))

/--
The counit for the adjunction for`cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
@[simp] theorem functoriality_counit'_app_hom {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {J : Type v} [small_category J] (K : J ⥤ D)
    (c : limits.cone K) :
    limits.cone_morphism.hom (nat_trans.app (functoriality_counit' adj K) c) =
        nat_trans.app (counit adj) (limits.cone.X c) :=
  Eq.refl (limits.cone_morphism.hom (nat_trans.app (functoriality_counit' adj K) c))

/-- The functor `cones.functoriality K G : cone K ⥤ cone (K ⋙ G)` is a right adjoint. -/
def functoriality_is_right_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {J : Type v} [small_category J] (K : J ⥤ D) :
    is_right_adjoint (limits.cones.functoriality K G) :=
  is_right_adjoint.mk (functoriality_left_adjoint adj K)
    (mk_of_unit_counit
      (core_unit_counit.mk (functoriality_unit' adj K) (functoriality_counit' adj K)))

/--
A right adjoint preserves limits.

See https://stacks.math.columbia.edu/tag/0038.
-/
def right_adjoint_preserves_limits {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) : limits.preserves_limits G :=
  limits.preserves_limits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      limits.preserves_limits_of_shape.mk
        fun (K : J ⥤ D) =>
          limits.preserves_limit.mk
            fun (c : limits.cone K) (hc : limits.is_limit c) =>
              iso.inv limits.is_limit.iso_unique_cone_morphism
                fun (s : limits.cone (K ⋙ G)) =>
                  equiv.unique (equiv.symm (hom_equiv is_right_adjoint.adj s c))

protected instance is_equivalence_preserves_limits {C : Type u₁} [category C] {D : Type u₂}
    [category D] (E : D ⥤ C) [is_equivalence E] : limits.preserves_limits E :=
  right_adjoint_preserves_limits (functor.adjunction (functor.inv E))

protected instance is_equivalence_reflects_limits {C : Type u₁} [category C] {D : Type u₂}
    [category D] (E : D ⥤ C) [is_equivalence E] : limits.reflects_limits E :=
  limits.reflects_limits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      limits.reflects_limits_of_shape.mk
        fun (K : J ⥤ D) =>
          limits.reflects_limit.mk
            fun (c : limits.cone K) (t : limits.is_limit (functor.map_cone E c)) =>
              limits.is_limit.of_iso_limit
                (coe_fn
                  (equiv.symm
                    (limits.is_limit.postcompose_hom_equiv (functor.left_unitor K)
                      (functor.map_cone 𝟭 c)))
                  (limits.is_limit.map_cone_equiv (functor.fun_inv_id E)
                    (limits.is_limit_of_preserves (functor.inv E) t)))
                (limits.cones.ext sorry sorry)

protected instance is_equivalence_creates_limits {C : Type u₁} [category C] {D : Type u₂}
    [category D] (H : D ⥤ C) [is_equivalence H] : creates_limits H :=
  creates_limits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      creates_limits_of_shape.mk
        fun (F : J ⥤ D) =>
          creates_limit.mk
            fun (c : limits.cone (F ⋙ H)) (t : limits.is_limit c) =>
              liftable_cone.mk (functor.map_cone_inv H c) (functor.map_cone_map_cone_inv H c)

-- verify the preserve_limits instance works as expected:

protected instance has_limit_comp_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D]
    {J : Type v} [small_category J] (K : J ⥤ D) (E : D ⥤ C) [is_equivalence E]
    [limits.has_limit K] : limits.has_limit (K ⋙ E) :=
  limits.has_limit.mk
    (limits.limit_cone.mk (functor.map_cone E (limits.limit.cone K))
      (limits.preserves_limit.preserves (limits.limit.is_limit K)))

theorem has_limit_of_comp_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D]
    {J : Type v} [small_category J] (K : J ⥤ D) (E : D ⥤ C) [is_equivalence E]
    [limits.has_limit (K ⋙ E)] : limits.has_limit K :=
  limits.has_limit_of_iso (iso_whisker_left K (functor.fun_inv_id E) ≪≫ functor.right_unitor K)

/-- auxiliary construction for `cocones_iso` -/
@[simp] theorem cocones_iso_component_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {J : Type v} [small_category J] {K : J ⥤ C} (Y : D)
    (t : functor.obj (functor.obj (cocones J D) (opposite.op (K ⋙ F))) Y) (j : J) :
    nat_trans.app (cocones_iso_component_hom adj Y t) j =
        coe_fn (hom_equiv adj (functor.obj K j) Y) (nat_trans.app t j) :=
  Eq.refl (nat_trans.app (cocones_iso_component_hom adj Y t) j)

/-- auxiliary construction for `cocones_iso` -/
def cocones_iso_component_inv {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {J : Type v} [small_category J] {K : J ⥤ C} (Y : D)
    (t : functor.obj (G ⋙ functor.obj (cocones J C) (opposite.op K)) Y) :
    functor.obj (functor.obj (cocones J D) (opposite.op (K ⋙ F))) Y :=
  nat_trans.mk
    fun (j : J) => coe_fn (equiv.symm (hom_equiv adj (functor.obj K j) Y)) (nat_trans.app t j)

/--
When `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/
-- Note: this is natural in K, but we do not yet have the tools to formulate that.

def cocones_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {J : Type v} [small_category J] {K : J ⥤ C} :
    functor.obj (cocones J D) (opposite.op (K ⋙ F)) ≅
        G ⋙ functor.obj (cocones J C) (opposite.op K) :=
  nat_iso.of_components
    (fun (Y : D) => iso.mk (cocones_iso_component_hom adj Y) (cocones_iso_component_inv adj Y))
    sorry

/-- auxiliary construction for `cones_iso` -/
@[simp] theorem cones_iso_component_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {J : Type v} [small_category J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : functor.obj (functor.op F ⋙ functor.obj (cones J D) K) X) (j : J) :
    nat_trans.app (cones_iso_component_hom adj X t) j =
        coe_fn (hom_equiv adj (opposite.unop X) (functor.obj K j)) (nat_trans.app t j) :=
  Eq.refl (nat_trans.app (cones_iso_component_hom adj X t) j)

/-- auxiliary construction for `cones_iso` -/
@[simp] theorem cones_iso_component_inv_app {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {J : Type v} [small_category J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : functor.obj (functor.obj (cones J C) (K ⋙ G)) X) (j : J) :
    nat_trans.app (cones_iso_component_inv adj X t) j =
        coe_fn (equiv.symm (hom_equiv adj (opposite.unop X) (functor.obj K j)))
          (nat_trans.app t j) :=
  Eq.refl (nat_trans.app (cones_iso_component_inv adj X t) j)

-- Note: this is natural in K, but we do not yet have the tools to formulate that.

/--
When `F ⊣ G`,
the functor associating to each `X` the cones over `K` with cone point `F.op.obj X`
is naturally isomorphic to
the functor associating to each `X` the cones over `K ⋙ G` with cone point `X`.
-/
def cones_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {J : Type v} [small_category J] {K : J ⥤ D} :
    functor.op F ⋙ functor.obj (cones J D) K ≅ functor.obj (cones J C) (K ⋙ G) :=
  nat_iso.of_components
    (fun (X : Cᵒᵖ) => iso.mk (cones_iso_component_hom adj X) (cones_iso_component_inv adj X)) sorry

end Mathlib