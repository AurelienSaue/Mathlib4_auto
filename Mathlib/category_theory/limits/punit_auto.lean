/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.punit
import Mathlib.category_theory.limits.limits
import Mathlib.PostPort

universes v u_1 

namespace Mathlib

/-!
# `discrete punit` has limits and colimits

Mostly for the sake of constructing trivial examples,
we show all (co)cones into `discrete punit` are (co)limit (co)cones,
and `discrete punit` has all (co)limits.
-/

namespace category_theory.limits


/--
Any cone over a functor into `punit` is a limit cone.
-/
def punit_cone_is_limit {J : Type v} [small_category J] {F : J ⥤ discrete PUnit} {c : cone F} :
    is_limit c :=
  is_limit.mk sorry

/--
Any cocone over a functor into `punit` is a colimit cocone.
-/
def punit_cocone_is_colimit {J : Type v} [small_category J] {F : J ⥤ discrete PUnit}
    {c : cocone F} : is_colimit c :=
  is_colimit.mk sorry

protected instance category_theory.discrete.has_limits : has_limits (discrete PUnit) :=
  has_limits.mk
    fun (J : Type u_1) (𝒥 : small_category J) =>
      has_limits_of_shape.mk
        fun (F : J ⥤ discrete PUnit) =>
          has_limit.mk' (Nonempty.intro (limit_cone.mk sorry (is_limit.mk sorry)))

protected instance category_theory.discrete.has_colimits : has_colimits (discrete PUnit) :=
  has_colimits.mk
    fun (J : Type u_1) (𝒥 : small_category J) =>
      has_colimits_of_shape.mk
        fun (F : J ⥤ discrete PUnit) =>
          has_colimit.mk' (Nonempty.intro (colimit_cocone.mk sorry (is_colimit.mk sorry)))

end Mathlib