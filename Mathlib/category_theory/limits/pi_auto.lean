/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.pi.basic
import Mathlib.category_theory.limits.limits
import Mathlib.PostPort

universes u₁ v₁ 

namespace Mathlib

/-!
# Limits in the category of indexed families of objects.

Given a functor `F : J ⥤ Π i, C i` into a category of indexed families,
1. we can assemble a collection of cones over `F ⋙ pi.eval C i` into a cone over `F`
2. if all those cones are limit cones, the assembled cone is a limit cone, and
3. if we have limits for each of `F ⋙ pi.eval C i`, we can produce a
   `has_limit F` instance
-/

namespace category_theory.pi


/--
A cone over `F : J ⥤ Π i, C i` has as its components cones over each of the `F ⋙ pi.eval C i`.
-/
def cone_comp_eval {I : Type v₁} {C : I → Type u₁} [(i : I) → category (C i)] {J : Type v₁}
    [small_category J] {F : J ⥤ ((i : I) → C i)} (c : limits.cone F) (i : I) :
    limits.cone (F ⋙ eval C i) :=
  limits.cone.mk (limits.cone.X c i)
    (nat_trans.mk fun (j : J) => nat_trans.app (limits.cone.π c) j i)

/--
A cocone over `F : J ⥤ Π i, C i` has as its components cocones over each of the `F ⋙ pi.eval C i`.
-/
def cocone_comp_eval {I : Type v₁} {C : I → Type u₁} [(i : I) → category (C i)] {J : Type v₁}
    [small_category J] {F : J ⥤ ((i : I) → C i)} (c : limits.cocone F) (i : I) :
    limits.cocone (F ⋙ eval C i) :=
  limits.cocone.mk (limits.cocone.X c i)
    (nat_trans.mk fun (j : J) => nat_trans.app (limits.cocone.ι c) j i)

/--
Given a family of cones over the `F ⋙ pi.eval C i`, we can assemble these together as a `cone F`.
-/
def cone_of_cone_comp_eval {I : Type v₁} {C : I → Type u₁} [(i : I) → category (C i)] {J : Type v₁}
    [small_category J] {F : J ⥤ ((i : I) → C i)} (c : (i : I) → limits.cone (F ⋙ eval C i)) :
    limits.cone F :=
  limits.cone.mk (fun (i : I) => limits.cone.X (c i))
    (nat_trans.mk fun (j : J) (i : I) => nat_trans.app (limits.cone.π (c i)) j)

/--
Given a family of cocones over the `F ⋙ pi.eval C i`, we can assemble these together as a `cocone F`.
-/
def cocone_of_cocone_comp_eval {I : Type v₁} {C : I → Type u₁} [(i : I) → category (C i)]
    {J : Type v₁} [small_category J] {F : J ⥤ ((i : I) → C i)}
    (c : (i : I) → limits.cocone (F ⋙ eval C i)) : limits.cocone F :=
  limits.cocone.mk (fun (i : I) => limits.cocone.X (c i))
    (nat_trans.mk fun (j : J) (i : I) => nat_trans.app (limits.cocone.ι (c i)) j)

/--
Given a family of limit cones over the `F ⋙ pi.eval C i`,
assembling them together as a `cone F` produces a limit cone.
-/
def cone_of_cone_eval_is_limit {I : Type v₁} {C : I → Type u₁} [(i : I) → category (C i)]
    {J : Type v₁} [small_category J] {F : J ⥤ ((i : I) → C i)}
    {c : (i : I) → limits.cone (F ⋙ eval C i)} (P : (i : I) → limits.is_limit (c i)) :
    limits.is_limit (cone_of_cone_comp_eval c) :=
  limits.is_limit.mk
    fun (s : limits.cone F) (i : I) => limits.is_limit.lift (P i) (cone_comp_eval s i)

/--
Given a family of colimit cocones over the `F ⋙ pi.eval C i`,
assembling them together as a `cocone F` produces a colimit cocone.
-/
def cocone_of_cocone_eval_is_colimit {I : Type v₁} {C : I → Type u₁} [(i : I) → category (C i)]
    {J : Type v₁} [small_category J] {F : J ⥤ ((i : I) → C i)}
    {c : (i : I) → limits.cocone (F ⋙ eval C i)} (P : (i : I) → limits.is_colimit (c i)) :
    limits.is_colimit (cocone_of_cocone_comp_eval c) :=
  limits.is_colimit.mk
    fun (s : limits.cocone F) (i : I) => limits.is_colimit.desc (P i) (cocone_comp_eval s i)

/--
If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and we have limits for each of the `F ⋙ pi.eval C i`,
then `F` has a limit.
-/
theorem has_limit_of_has_limit_comp_eval {I : Type v₁} {C : I → Type u₁} [(i : I) → category (C i)]
    {J : Type v₁} [small_category J] {F : J ⥤ ((i : I) → C i)}
    [∀ (i : I), limits.has_limit (F ⋙ eval C i)] : limits.has_limit F :=
  limits.has_limit.mk
    (limits.limit_cone.mk
      (cone_of_cone_comp_eval fun (i : I) => limits.limit.cone (F ⋙ eval (fun (i : I) => C i) i))
      (cone_of_cone_eval_is_limit
        fun (i : I) => limits.limit.is_limit (F ⋙ eval (fun (i : I) => C i) i)))

/--
If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and colimits exist for each of the `F ⋙ pi.eval C i`,
there is a colimit for `F`.
-/
theorem has_colimit_of_has_colimit_comp_eval {I : Type v₁} {C : I → Type u₁}
    [(i : I) → category (C i)] {J : Type v₁} [small_category J] {F : J ⥤ ((i : I) → C i)}
    [∀ (i : I), limits.has_colimit (F ⋙ eval C i)] : limits.has_colimit F :=
  sorry

end Mathlib