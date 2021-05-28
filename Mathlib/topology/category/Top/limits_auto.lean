/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.category.Top.basic
import Mathlib.category_theory.limits.types
import Mathlib.category_theory.limits.preserves.basic
import PostPort

universes u 

namespace Mathlib

namespace Top


/--
A choice of limit cone for a functor `F : J ⥤ Top`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone {J : Type u} [category_theory.small_category J] (F : J ⥤ Top) : category_theory.limits.cone F :=
  category_theory.limits.cone.mk
    (category_theory.bundled.mk
      (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget Top))))
    (category_theory.nat_trans.mk
      fun (j : J) =>
        continuous_map.mk
          (category_theory.nat_trans.app
            (category_theory.limits.cone.π (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget Top))) j))

/--
The chosen cone `Top.limit_cone F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_is_limit {J : Type u} [category_theory.small_category J] (F : J ⥤ Top) : category_theory.limits.is_limit (limit_cone F) :=
  category_theory.limits.is_limit.of_faithful (category_theory.forget Top)
    (category_theory.limits.types.limit_cone_is_limit (F ⋙ category_theory.forget Top))
    (fun (s : category_theory.limits.cone F) =>
      continuous_map.mk
        fun (v : category_theory.limits.cone.X (category_theory.functor.map_cone (category_theory.forget Top) s)) =>
          { val :=
              fun (j : J) =>
                category_theory.nat_trans.app
                  (category_theory.limits.cone.π (category_theory.functor.map_cone (category_theory.forget Top) s)) j v,
            property := sorry })
    sorry

protected instance Top_has_limits : category_theory.limits.has_limits Top :=
  category_theory.limits.has_limits.mk
    fun (J : Type u) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_limits_of_shape.mk
        fun (F : J ⥤ Top) =>
          category_theory.limits.has_limit.mk
            (category_theory.limits.limit_cone.mk (limit_cone F) (limit_cone_is_limit F))

protected instance forget_preserves_limits : category_theory.limits.preserves_limits (category_theory.forget Top) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ Top) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
            (category_theory.limits.types.limit_cone_is_limit (F ⋙ category_theory.forget Top))

/--
A choice of colimit cocone for a functor `F : J ⥤ Top`.
Generally you should just use `colimit.coone F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone`).
-/
def colimit_cocone {J : Type u} [category_theory.small_category J] (F : J ⥤ Top) : category_theory.limits.cocone F :=
  category_theory.limits.cocone.mk
    (category_theory.bundled.mk
      (category_theory.limits.cocone.X (category_theory.limits.types.colimit_cocone (F ⋙ category_theory.forget Top))))
    (category_theory.nat_trans.mk
      fun (j : J) =>
        continuous_map.mk
          (category_theory.nat_trans.app
            (category_theory.limits.cocone.ι
              (category_theory.limits.types.colimit_cocone (F ⋙ category_theory.forget Top)))
            j))

/--
The chosen cocone `Top.colimit_cocone F` for a functor `F : J ⥤ Top` is a colimit cocone.
Generally you should just use `colimit.is_colimit F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone_is_colimit`).
-/
def colimit_cocone_is_colimit {J : Type u} [category_theory.small_category J] (F : J ⥤ Top) : category_theory.limits.is_colimit (colimit_cocone F) :=
  category_theory.limits.is_colimit.of_faithful (category_theory.forget Top)
    (category_theory.limits.types.colimit_cocone_is_colimit (F ⋙ category_theory.forget Top))
    (fun (s : category_theory.limits.cocone F) =>
      continuous_map.mk
        (Quot.lift
          (fun (p : sigma fun (j : J) => category_theory.functor.obj (F ⋙ category_theory.forget Top) j) =>
            category_theory.nat_trans.app
              (category_theory.limits.cocone.ι (category_theory.functor.map_cocone (category_theory.forget Top) s))
              (sigma.fst p) (sigma.snd p))
          sorry))
    sorry

protected instance Top_has_colimits : category_theory.limits.has_colimits Top :=
  category_theory.limits.has_colimits.mk
    fun (J : Type u) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_colimits_of_shape.mk
        fun (F : J ⥤ Top) =>
          category_theory.limits.has_colimit.mk
            (category_theory.limits.colimit_cocone.mk (colimit_cocone F) (colimit_cocone_is_colimit F))

protected instance forget_preserves_colimits : category_theory.limits.preserves_colimits (category_theory.forget Top) :=
  category_theory.limits.preserves_colimits.mk
    fun (J : Type u) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_colimits_of_shape.mk
        fun (F : J ⥤ Top) =>
          category_theory.limits.preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
            (category_theory.limits.types.colimit_cocone_is_colimit (F ⋙ category_theory.forget Top))

