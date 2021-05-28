/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group.pi
import Mathlib.algebra.category.Mon.basic
import Mathlib.group_theory.submonoid.default
import Mathlib.category_theory.limits.types
import Mathlib.category_theory.limits.creates
import PostPort

universes u u_1 

namespace Mathlib

/-!
# The category of (commutative) (additive) monoids has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

namespace Mon


protected instance monoid_obj {J : Type u} [category_theory.small_category J] (F : J ⥤ Mon) (j : J) : monoid (category_theory.functor.obj (F ⋙ category_theory.forget Mon) j) :=
  id (Mon.monoid (category_theory.functor.obj F j))

/--
The flat sections of a functor into `Mon` form a submonoid of all sections.
-/
def Mathlib.AddMon.sections_add_submonoid {J : Type u} [category_theory.small_category J] (F : J ⥤ AddMon) : add_submonoid ((j : J) → ↥(category_theory.functor.obj F j)) :=
  add_submonoid.mk (category_theory.functor.sections (F ⋙ category_theory.forget AddMon)) sorry sorry

protected instance Mathlib.AddMon.limit_add_monoid {J : Type u} [category_theory.small_category J] (F : J ⥤ AddMon) : add_monoid (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget AddMon))) :=
  add_submonoid.to_add_monoid (AddMon.sections_add_submonoid F)

/-- `limit.π (F ⋙ forget Mon) j` as a `monoid_hom`. -/
def Mathlib.AddMon.limit_π_add_monoid_hom {J : Type u} [category_theory.small_category J] (F : J ⥤ AddMon) (j : J) : category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget AddMon)) →+
  category_theory.functor.obj (F ⋙ category_theory.forget AddMon) j :=
  add_monoid_hom.mk
    (category_theory.nat_trans.app
      (category_theory.limits.cone.π (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget AddMon))) j)
    sorry sorry

namespace has_limits


-- The next two definitions are used in the construction of `has_limits Mon`.

-- After that, the limits should be constructed using the generic limits API,

-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Mon`.
(Internal use only; use the limits API.)
-/
def Mathlib.AddMon.has_limits.limit_cone {J : Type u} [category_theory.small_category J] (F : J ⥤ AddMon) : category_theory.limits.cone F :=
  category_theory.limits.cone.mk
    (AddMon.of
      (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget AddMon))))
    (category_theory.nat_trans.mk (AddMon.limit_π_add_monoid_hom F))

/--
Witness that the limit cone in `Mon` is a limit cone.
(Internal use only; use the limits API.)
-/
def Mathlib.AddMon.has_limits.limit_cone_is_limit {J : Type u} [category_theory.small_category J] (F : J ⥤ AddMon) : category_theory.limits.is_limit (AddMon.has_limits.limit_cone F) :=
  category_theory.limits.is_limit.of_faithful (category_theory.forget AddMon)
    (category_theory.limits.types.limit_cone_is_limit (F ⋙ category_theory.forget AddMon))
    (fun (s : category_theory.limits.cone F) =>
      add_monoid_hom.mk
        (fun (v : category_theory.limits.cone.X (category_theory.functor.map_cone (category_theory.forget AddMon) s)) =>
          { val :=
              fun (j : J) =>
                category_theory.nat_trans.app
                  (category_theory.limits.cone.π (category_theory.functor.map_cone (category_theory.forget AddMon) s)) j
                  v,
            property := sorry })
        sorry sorry)
    sorry

end has_limits


/-- The category of monoids has all limits. -/
protected instance Mathlib.AddMon.has_limits : category_theory.limits.has_limits AddMon :=
  category_theory.limits.has_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_limits_of_shape.mk
        fun (F : J ⥤ AddMon) => category_theory.limits.has_limit.mk (category_theory.limits.limit_cone.mk sorry sorry)

/--
The forgetful functor from monoids to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
protected instance Mathlib.AddMon.forget_preserves_limits : category_theory.limits.preserves_limits (category_theory.forget AddMon) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ AddMon) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone (AddMon.has_limits.limit_cone_is_limit F)
            (category_theory.limits.types.limit_cone_is_limit (F ⋙ category_theory.forget AddMon))

end Mon


namespace CommMon


protected instance comm_monoid_obj {J : Type u} [category_theory.small_category J] (F : J ⥤ CommMon) (j : J) : comm_monoid (category_theory.functor.obj (F ⋙ category_theory.forget CommMon) j) :=
  id (CommMon.comm_monoid (category_theory.functor.obj F j))

protected instance limit_comm_monoid {J : Type u} [category_theory.small_category J] (F : J ⥤ CommMon) : comm_monoid
  (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget CommMon))) :=
  submonoid.to_comm_monoid (Mon.sections_submonoid (F ⋙ category_theory.forget₂ CommMon Mon))

/--
We show that the forgetful functor `CommMon ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `comm_monoid` instance available,
and then reuse the existing limit.
-/
protected instance category_theory.forget₂.category_theory.creates_limit {J : Type u} [category_theory.small_category J] (F : J ⥤ CommMon) : category_theory.creates_limit F (category_theory.forget₂ CommMon Mon) := sorry

/--
A choice of limit cone for a functor into `CommMon`.
(Generally, you'll just want to use `limit F`.)
-/
def Mathlib.AddCommMon.limit_cone {J : Type u} [category_theory.small_category J] (F : J ⥤ AddCommMon) : category_theory.limits.cone F :=
  category_theory.lift_limit (category_theory.limits.limit.is_limit (F ⋙ category_theory.forget₂ AddCommMon AddMon))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def Mathlib.AddCommMon.limit_cone_is_limit {J : Type u} [category_theory.small_category J] (F : J ⥤ AddCommMon) : category_theory.limits.is_limit (AddCommMon.limit_cone F) :=
  category_theory.lifted_limit_is_limit
    (category_theory.limits.limit.is_limit (F ⋙ category_theory.forget₂ AddCommMon AddMon))

/-- The category of commutative monoids has all limits. -/
protected instance has_limits : category_theory.limits.has_limits CommMon :=
  category_theory.limits.has_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_limits_of_shape.mk
        fun (F : J ⥤ CommMon) => category_theory.has_limit_of_created F (category_theory.forget₂ CommMon Mon)

/--
The forgetful functor from commutative monoids to monoids preserves all limits.
(That is, the underlying monoid could have been computed instead as limits in the category
of monoids.)
-/
protected instance Mathlib.AddCommMon.forget₂_AddMon_preserves_limits : category_theory.limits.preserves_limits (category_theory.forget₂ AddCommMon AddMon) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ AddCommMon) =>
          category_theory.preserves_limit_of_creates_limit_and_has_limit F (category_theory.forget₂ AddCommMon AddMon)

/--
The forgetful functor from commutative monoids to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
protected instance forget_preserves_limits : category_theory.limits.preserves_limits (category_theory.forget CommMon) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ CommMon) =>
          category_theory.limits.comp_preserves_limit (category_theory.forget₂ CommMon Mon) (category_theory.forget Mon)

