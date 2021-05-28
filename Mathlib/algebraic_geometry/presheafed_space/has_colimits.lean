/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebraic_geometry.presheafed_space
import Mathlib.topology.category.Top.limits
import Mathlib.topology.sheaves.limits
import Mathlib.category_theory.limits.concrete_category
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# `PresheafedSpace C` has colimits.

If `C` has limits, then the category `PresheafedSpace C` has colimits,
and the forgetful functor to `Top` preserves these colimits.

When restricted to a diagram where the underlying continuous maps are open embeddings,
this says that we can glue presheaved spaces.

Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the colimit of the underlying topological spaces,
as `colimit (F ⋙ PresheafedSpace.forget C)`. Call that colimit space `X`.

Our strategy is to push each of the presheaves `F.obj j`
forward along the continuous map `colimit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pushforward is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)

The limit of this diagram then constitutes the colimit presheaf.
-/

namespace algebraic_geometry


namespace PresheafedSpace


@[simp] theorem map_id_c_app {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] (F : J ⥤ PresheafedSpace C) (j : J) (U : topological_space.opens ↥(carrier (category_theory.functor.obj F j))) : category_theory.nat_trans.app (hom.c (category_theory.functor.map F 𝟙)) (opposite.op U) =
  category_theory.nat_trans.app
      (category_theory.iso.inv
        (Top.presheaf.pushforward.id (PresheafedSpace.presheaf (category_theory.functor.obj F j))))
      (opposite.op U) ≫
    category_theory.nat_trans.app
      (category_theory.iso.hom
        (Top.presheaf.pushforward_eq
          (eq.mpr
            (id
              ((fun (a a_1 : carrier (category_theory.functor.obj F j) ⟶ carrier (category_theory.functor.obj F j))
                  (e_1 : a = a_1)
                  (ᾰ ᾰ_1 : carrier (category_theory.functor.obj F j) ⟶ carrier (category_theory.functor.obj F j))
                  (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
                𝟙 𝟙 (Eq.refl 𝟙) (hom.base (category_theory.functor.map F 𝟙)) 𝟙
                (Eq.trans
                  ((fun (c c_1 : hom (category_theory.functor.obj F j) (category_theory.functor.obj F j))
                      (e_1 : c = c_1) => congr_arg hom.base e_1)
                    (category_theory.functor.map F 𝟙) 𝟙 (category_theory.functor.map_id F j))
                  (id_base (category_theory.functor.obj F j)))))
            (Eq.refl 𝟙))
          (PresheafedSpace.presheaf (category_theory.functor.obj F j))))
      (opposite.op U) := sorry

@[simp] theorem map_comp_c_app {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] (F : J ⥤ PresheafedSpace C) {j₁ : J} {j₂ : J} {j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) (U : topological_space.opens ↥(carrier (category_theory.functor.obj F j₃))) : category_theory.nat_trans.app (hom.c (category_theory.functor.map F (f ≫ g))) (opposite.op U) =
  category_theory.nat_trans.app (hom.c (category_theory.functor.map F g)) (opposite.op U) ≫
    category_theory.nat_trans.app
        (Top.presheaf.pushforward_map (hom.base (category_theory.functor.map F g))
          (hom.c (category_theory.functor.map F f)))
        (opposite.op U) ≫
      category_theory.nat_trans.app
          (category_theory.iso.inv
            (Top.presheaf.pushforward.comp (PresheafedSpace.presheaf (category_theory.functor.obj F j₁))
              (hom.base (category_theory.functor.map F f)) (hom.base (category_theory.functor.map F g))))
          (opposite.op U) ≫
        category_theory.nat_trans.app
          (category_theory.iso.hom
            (Top.presheaf.pushforward_eq
              (eq.mpr
                (id
                  (Eq._oldrec
                    (Eq.refl
                      (hom.base (category_theory.functor.map F f) ≫ hom.base (category_theory.functor.map F g) =
                        hom.base (category_theory.functor.map F (f ≫ g))))
                    (category_theory.functor.map_comp F f g)))
                (Eq.refl (hom.base (category_theory.functor.map F f) ≫ hom.base (category_theory.functor.map F g))))
              (PresheafedSpace.presheaf (category_theory.functor.obj F j₁))))
          (opposite.op U) := sorry

/--
Given a diagram of presheafed spaces,
we can push all the presheaves forward to the colimit `X` of the underlying topological spaces,
obtaining a diagram in `(presheaf C X)ᵒᵖ`.
-/
@[simp] theorem pushforward_diagram_to_colimit_obj {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] (F : J ⥤ PresheafedSpace C) (j : J) : category_theory.functor.obj (pushforward_diagram_to_colimit F) j =
  opposite.op
    (category_theory.limits.colimit.ι (F ⋙ forget C) j _* PresheafedSpace.presheaf (category_theory.functor.obj F j)) :=
  Eq.refl (category_theory.functor.obj (pushforward_diagram_to_colimit F) j)

/--
Auxilliary definition for `PresheafedSpace.has_colimits`.
-/
def colimit {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] (F : J ⥤ PresheafedSpace C) : PresheafedSpace C :=
  mk (category_theory.limits.colimit (F ⋙ forget C))
    (category_theory.limits.limit (category_theory.functor.left_op (pushforward_diagram_to_colimit F)))

/--
Auxilliary definition for `PresheafedSpace.has_colimits`.
-/
@[simp] theorem colimit_cocone_X {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] (F : J ⥤ PresheafedSpace C) : category_theory.limits.cocone.X (colimit_cocone F) = colimit F :=
  Eq.refl (category_theory.limits.cocone.X (colimit_cocone F))

namespace colimit_cocone_is_colimit


/--
Auxilliary definition for `PresheafedSpace.colimit_cocone_is_colimit`.
-/
def desc_c_app {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] (F : J ⥤ PresheafedSpace C) (s : category_theory.limits.cocone F) (U : topological_space.opens ↥(carrier (category_theory.limits.cocone.X s))ᵒᵖ) : category_theory.functor.obj (PresheafedSpace.presheaf (category_theory.limits.cocone.X s)) U ⟶
  category_theory.functor.obj
    (category_theory.limits.colimit.desc (F ⋙ forget C) (category_theory.functor.map_cocone (forget C) s) _*
      category_theory.limits.limit (category_theory.functor.left_op (pushforward_diagram_to_colimit F)))
    U := sorry

theorem desc_c_naturality {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] (F : J ⥤ PresheafedSpace C) (s : category_theory.limits.cocone F) {U : topological_space.opens ↥(carrier (category_theory.limits.cocone.X s))ᵒᵖ} {V : topological_space.opens ↥(carrier (category_theory.limits.cocone.X s))ᵒᵖ} (i : U ⟶ V) : category_theory.functor.map (PresheafedSpace.presheaf (category_theory.limits.cocone.X s)) i ≫ desc_c_app F s V =
  desc_c_app F s U ≫
    category_theory.functor.map
      (category_theory.limits.colimit.desc (F ⋙ forget C) (category_theory.functor.map_cocone (forget C) s) _*
        PresheafedSpace.presheaf (category_theory.limits.cocone.X (colimit_cocone F)))
      i := sorry

end colimit_cocone_is_colimit


/--
Auxilliary definition for `PresheafedSpace.has_colimits`.
-/
def colimit_cocone_is_colimit {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] (F : J ⥤ PresheafedSpace C) : category_theory.limits.is_colimit (colimit_cocone F) :=
  category_theory.limits.is_colimit.mk
    fun (s : category_theory.limits.cocone F) =>
      hom.mk (category_theory.limits.colimit.desc (F ⋙ forget C) (category_theory.functor.map_cocone (forget C) s))
        (category_theory.nat_trans.mk
          fun (U : topological_space.opens ↥(carrier (category_theory.limits.cocone.X s))ᵒᵖ) => sorry)

/--
When `C` has limits, the category of presheaved spaces with values in `C` itself has colimits.
-/
protected instance category_theory.limits.has_colimits {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] : category_theory.limits.has_colimits (PresheafedSpace C) :=
  category_theory.limits.has_colimits.mk
    fun (J : Type v) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_colimits_of_shape.mk
        fun (F : J ⥤ PresheafedSpace C) =>
          category_theory.limits.has_colimit.mk
            (category_theory.limits.colimit_cocone.mk (colimit_cocone F) (colimit_cocone_is_colimit F))

/--
The underlying topological space of a colimit of presheaved spaces is
the colimit of the underlying topological spaces.
-/
protected instance forget_preserves_colimits {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] : category_theory.limits.preserves_colimits (forget C) :=
  category_theory.limits.preserves_colimits.mk
    fun (J : Type v) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_colimits_of_shape.mk
        fun (F : J ⥤ PresheafedSpace C) =>
          category_theory.limits.preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
            (category_theory.limits.is_colimit.of_iso_colimit (category_theory.limits.colimit.is_colimit (F ⋙ forget C))
              (category_theory.limits.cocones.ext
                (category_theory.iso.refl
                  (category_theory.limits.cocone.X (category_theory.limits.colimit.cocone (F ⋙ forget C))))
                sorry))

