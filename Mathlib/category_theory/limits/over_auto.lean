/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.over
import Mathlib.category_theory.limits.preserves.basic
import Mathlib.category_theory.limits.creates
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Limits and colimits in the over and under categories

Show that the forgetful functor `forget X : over X ⥤ C` creates colimits, and hence `over X` has
any colimits that `C` has (as well as the dual that `forget X : under X ⟶ C` creates limits).

Note that the folder `category_theory.limits.shapes.constructions.over` further shows that
`forget X : over X ⥤ C` creates connected limits (so `over X` has connected limits), and that
`over X` has `J`-indexed products if `C` has `J`-indexed wide pullbacks.

TODO: If `C` has binary products, then `forget X : over X ⥤ C` has a right adjoint.
-/

namespace category_theory.functor


/-- We can interpret a functor `F` into the category of arrows with codomain `X` as a cocone over
    the diagram given by the domains of the arrows in the image of `F` such that the apex of the
    cocone is `X`. -/
@[simp] theorem to_cocone_X {J : Type v} [small_category J] {C : Type u} [category C] {X : C}
    (F : J ⥤ over X) : limits.cocone.X (to_cocone F) = X :=
  Eq.refl (limits.cocone.X (to_cocone F))

/-- We can interpret a functor `F` into the category of arrows with domain `X` as a cone over the
    diagram given by the codomains of the arrows in the image of `F` such that the apex of the cone
    is `X`. -/
@[simp] theorem to_cone_X {J : Type v} [small_category J] {C : Type u} [category C] {X : C}
    (F : J ⥤ under X) : limits.cone.X (to_cone F) = X :=
  Eq.refl (limits.cone.X (to_cone F))

end category_theory.functor


namespace category_theory.over


protected instance forget.category_theory.limits.reflects_colimits {C : Type u} [category C]
    {X : C} : limits.reflects_colimits (forget X) :=
  limits.reflects_colimits.mk
    fun (J : Type v) (𝒥₁ : small_category J) =>
      limits.reflects_colimits_of_shape.mk
        fun (F : J ⥤ over X) =>
          limits.reflects_colimit.mk
            fun (c : limits.cocone F) (t : limits.is_colimit (functor.map_cocone (forget X) c)) =>
              limits.is_colimit.mk
                fun (s : limits.cocone F) =>
                  hom_mk (limits.is_colimit.desc t (functor.map_cocone (forget X) s))

protected instance forget.category_theory.creates_colimits {C : Type u} [category C] {X : C} :
    creates_colimits (forget X) :=
  creates_colimits.mk
    fun (J : Type v) (𝒥₁ : small_category J) =>
      creates_colimits_of_shape.mk
        fun (K : J ⥤ over X) =>
          creates_colimit.mk
            fun (c : limits.cocone (K ⋙ forget X)) (t : limits.is_colimit c) =>
              liftable_cocone.mk
                (limits.cocone.mk (mk (limits.is_colimit.desc t (functor.to_cocone K)))
                  (nat_trans.mk fun (j : J) => hom_mk (nat_trans.app (limits.cocone.ι c) j)))
                (limits.cocones.ext
                  (iso.refl
                    (limits.cocone.X
                      (functor.map_cocone (forget X)
                        (limits.cocone.mk (mk (limits.is_colimit.desc t (functor.to_cocone K)))
                          (nat_trans.mk
                            fun (j : J) => hom_mk (nat_trans.app (limits.cocone.ι c) j))))))
                  sorry)

protected instance has_colimit {J : Type v} [small_category J] {C : Type u} [category C] {X : C}
    {F : J ⥤ over X} [limits.has_colimit (F ⋙ forget X)] : limits.has_colimit F :=
  has_colimit_of_created F (forget X)

protected instance has_colimits_of_shape {J : Type v} [small_category J] {C : Type u} [category C]
    {X : C} [limits.has_colimits_of_shape J C] : limits.has_colimits_of_shape J (over X) :=
  limits.has_colimits_of_shape.mk fun (F : J ⥤ over X) => over.has_colimit

protected instance has_colimits {C : Type u} [category C] {X : C} [limits.has_colimits C] :
    limits.has_colimits (over X) :=
  limits.has_colimits.mk fun (J : Type v) (𝒥 : small_category J) => over.has_colimits_of_shape

-- We can automatically infer that the forgetful functor preserves colimits

end category_theory.over


namespace category_theory.under


protected instance forget.category_theory.limits.reflects_limits {C : Type u} [category C] {X : C} :
    limits.reflects_limits (forget X) :=
  limits.reflects_limits.mk
    fun (J : Type v) (𝒥₁ : small_category J) =>
      limits.reflects_limits_of_shape.mk
        fun (F : J ⥤ under X) =>
          limits.reflects_limit.mk
            fun (c : limits.cone F) (t : limits.is_limit (functor.map_cone (forget X) c)) =>
              limits.is_limit.mk
                fun (s : limits.cone F) =>
                  hom_mk (limits.is_limit.lift t (functor.map_cone (forget X) s))

protected instance forget.category_theory.creates_limits {C : Type u} [category C] {X : C} :
    creates_limits (forget X) :=
  creates_limits.mk
    fun (J : Type v) (𝒥₁ : small_category J) =>
      creates_limits_of_shape.mk
        fun (K : J ⥤ under X) =>
          creates_limit.mk
            fun (c : limits.cone (K ⋙ forget X)) (t : limits.is_limit c) =>
              liftable_cone.mk
                (limits.cone.mk (mk (limits.is_limit.lift t (functor.to_cone K)))
                  (nat_trans.mk fun (j : J) => hom_mk (nat_trans.app (limits.cone.π c) j)))
                (limits.cones.ext
                  (iso.refl
                    (limits.cone.X
                      (functor.map_cone (forget X)
                        (limits.cone.mk (mk (limits.is_limit.lift t (functor.to_cone K)))
                          (nat_trans.mk
                            fun (j : J) => hom_mk (nat_trans.app (limits.cone.π c) j))))))
                  sorry)

protected instance has_limit {J : Type v} [small_category J] {C : Type u} [category C] {X : C}
    {F : J ⥤ under X} [limits.has_limit (F ⋙ forget X)] : limits.has_limit F :=
  has_limit_of_created F (forget X)

protected instance has_limits_of_shape {J : Type v} [small_category J] {C : Type u} [category C]
    {X : C} [limits.has_limits_of_shape J C] : limits.has_limits_of_shape J (under X) :=
  limits.has_limits_of_shape.mk fun (F : J ⥤ under X) => under.has_limit

protected instance has_limits {C : Type u} [category C] {X : C} [limits.has_limits C] :
    limits.has_limits (under X) :=
  limits.has_limits.mk fun (J : Type v) (𝒥 : small_category J) => under.has_limits_of_shape

end Mathlib