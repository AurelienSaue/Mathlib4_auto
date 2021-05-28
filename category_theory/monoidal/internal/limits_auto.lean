/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.monoidal.internal.functor_category
import Mathlib.category_theory.monoidal.limits
import Mathlib.category_theory.limits.preserves.basic
import PostPort

universes v u 

namespace Mathlib

/-!
# Limits of monoid objects.

If `C` has limits, so does `Mon_ C`, and the forgetful functor preserves these limits.

(This could potentially replace many individual constructions for concrete categories,
in particular `Mon`, `SemiRing`, `Ring`, and `Algebra R`.)
-/

namespace Mon_


/--
We construct the (candidate) limit of a functor `F : J ⥤ Mon_ C`
by interpreting it as a functor `Mon_ (J ⥤ C)`,
and noting that taking limits is a lax monoidal functor,
and hence sends monoid objects to monoid objects.
-/
def limit {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] [category_theory.monoidal_category C] (F : J ⥤ Mon_ C) : Mon_ C :=
  category_theory.functor.obj (category_theory.lax_monoidal_functor.map_Mon category_theory.limits.lim_lax)
    (category_theory.functor.obj category_theory.monoidal.Mon_functor_category_equivalence.inverse F)

/--
Implementation of `Mon_.has_limits`: a limiting cone over a functor `F : J ⥤ Mon_ C`.
-/
def limit_cone {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] [category_theory.monoidal_category C] (F : J ⥤ Mon_ C) : category_theory.limits.cone F :=
  category_theory.limits.cone.mk (limit F)
    (category_theory.nat_trans.mk fun (j : J) => hom.mk (category_theory.limits.limit.π (F ⋙ forget C) j))

/--
The image of the proposed limit cone for `F : J ⥤ Mon_ C` under the forgetful functor
`forget C : Mon_ C ⥤ C` is isomorphic to the limit cone of `F ⋙ forget C`.
-/
def forget_map_cone_limit_cone_iso {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] [category_theory.monoidal_category C] (F : J ⥤ Mon_ C) : category_theory.functor.map_cone (forget C) (limit_cone F) ≅ category_theory.limits.limit.cone (F ⋙ forget C) :=
  category_theory.limits.cones.ext
    (category_theory.iso.refl
      (category_theory.limits.cone.X (category_theory.functor.map_cone (forget C) (limit_cone F))))
    sorry

/--
Implementation of `Mon_.has_limits`:
the proposed cone over a functor `F : J ⥤ Mon_ C` is a limit cone.
-/
def limit_cone_is_limit {J : Type v} [category_theory.small_category J] {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] [category_theory.monoidal_category C] (F : J ⥤ Mon_ C) : category_theory.limits.is_limit (limit_cone F) :=
  category_theory.limits.is_limit.mk
    fun (s : category_theory.limits.cone F) =>
      hom.mk (category_theory.limits.limit.lift (F ⋙ forget C) (category_theory.functor.map_cone (forget C) s))

protected instance has_limits {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] [category_theory.monoidal_category C] : category_theory.limits.has_limits (Mon_ C) :=
  category_theory.limits.has_limits.mk
    fun (J : Type v) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_limits_of_shape.mk
        fun (F : J ⥤ Mon_ C) =>
          category_theory.limits.has_limit.mk
            (category_theory.limits.limit_cone.mk (limit_cone F) (limit_cone_is_limit F))

protected instance forget_preserves_limits {C : Type u} [category_theory.category C] [category_theory.limits.has_limits C] [category_theory.monoidal_category C] : category_theory.limits.preserves_limits (forget C) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type v) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ Mon_ C) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
            (category_theory.limits.is_limit.of_iso_limit (category_theory.limits.limit.is_limit (F ⋙ forget C))
              (category_theory.iso.symm (forget_map_cone_limit_cone_iso F)))

