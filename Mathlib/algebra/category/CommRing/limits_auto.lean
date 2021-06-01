/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.ring.pi
import Mathlib.algebra.category.CommRing.basic
import Mathlib.algebra.category.Group.limits
import Mathlib.ring_theory.subring
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# The category of (commutative) rings has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

namespace SemiRing


protected instance semiring_obj {J : Type u} [category_theory.small_category J] (F : J ⥤ SemiRing)
    (j : J) : semiring (category_theory.functor.obj (F ⋙ category_theory.forget SemiRing) j) :=
  id (SemiRing.semiring (category_theory.functor.obj F j))

/--
The flat sections of a functor into `SemiRing` form a subsemiring of all sections.
-/
def sections_subsemiring {J : Type u} [category_theory.small_category J] (F : J ⥤ SemiRing) :
    subsemiring ((j : J) → ↥(category_theory.functor.obj F j)) :=
  subsemiring.mk (category_theory.functor.sections (F ⋙ category_theory.forget SemiRing)) sorry
    sorry sorry sorry

protected instance limit_semiring {J : Type u} [category_theory.small_category J]
    (F : J ⥤ SemiRing) :
    semiring
        (category_theory.limits.cone.X
          (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget SemiRing))) :=
  subsemiring.to_semiring (sections_subsemiring F)

/-- `limit.π (F ⋙ forget SemiRing) j` as a `ring_hom`. -/
def limit_π_ring_hom {J : Type u} [category_theory.small_category J] (F : J ⥤ SemiRing) (j : J) :
    category_theory.limits.cone.X
          (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget SemiRing)) →+*
        category_theory.functor.obj (F ⋙ category_theory.forget SemiRing) j :=
  ring_hom.mk
    (category_theory.nat_trans.app
      (category_theory.limits.cone.π
        (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget SemiRing)))
      j)
    sorry sorry sorry sorry

namespace has_limits


-- The next two definitions are used in the construction of `has_limits SemiRing`.

-- After that, the limits should be constructed using the generic limits API,

-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `SemiRing`.
(Internal use only; use the limits API.)
-/
def limit_cone {J : Type u} [category_theory.small_category J] (F : J ⥤ SemiRing) :
    category_theory.limits.cone F :=
  category_theory.limits.cone.mk
    (of
      (category_theory.limits.cone.X
        (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget SemiRing))))
    (category_theory.nat_trans.mk (limit_π_ring_hom F))

/--
Witness that the limit cone in `SemiRing` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit {J : Type u} [category_theory.small_category J] (F : J ⥤ SemiRing) :
    category_theory.limits.is_limit (limit_cone F) :=
  category_theory.limits.is_limit.of_faithful (category_theory.forget SemiRing)
    (category_theory.limits.types.limit_cone_is_limit (F ⋙ category_theory.forget SemiRing))
    (fun (s : category_theory.limits.cone F) =>
      ring_hom.mk
        (fun
          (v :
          category_theory.limits.cone.X
            (category_theory.functor.map_cone (category_theory.forget SemiRing) s)) =>
          { val :=
              fun (j : J) =>
                category_theory.nat_trans.app
                  (category_theory.limits.cone.π
                    (category_theory.functor.map_cone (category_theory.forget SemiRing) s))
                  j v,
            property := sorry })
        sorry sorry sorry sorry)
    sorry

end has_limits


/-- The category of rings has all limits. -/
protected instance has_limits : category_theory.limits.has_limits SemiRing :=
  category_theory.limits.has_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_limits_of_shape.mk
        fun (F : J ⥤ SemiRing) =>
          category_theory.limits.has_limit.mk (category_theory.limits.limit_cone.mk sorry sorry)

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_AddCommMon_preserves_limits_aux {J : Type u} [category_theory.small_category J]
    (F : J ⥤ SemiRing) :
    category_theory.limits.is_limit
        (category_theory.functor.map_cone (category_theory.forget₂ SemiRing AddCommMon)
          (has_limits.limit_cone F)) :=
  AddCommMon.limit_cone_is_limit (F ⋙ category_theory.forget₂ SemiRing AddCommMon)

/--
The forgetful functor from semirings to additive commutative monoids preserves all limits.
-/
protected instance forget₂_AddCommMon_preserves_limits :
    category_theory.limits.preserves_limits (category_theory.forget₂ SemiRing AddCommMon) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ SemiRing) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone
            (has_limits.limit_cone_is_limit F) (forget₂_AddCommMon_preserves_limits_aux F)

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_Mon_preserves_limits_aux {J : Type u} [category_theory.small_category J]
    (F : J ⥤ SemiRing) :
    category_theory.limits.is_limit
        (category_theory.functor.map_cone (category_theory.forget₂ SemiRing Mon)
          (has_limits.limit_cone F)) :=
  Mon.has_limits.limit_cone_is_limit (F ⋙ category_theory.forget₂ SemiRing Mon)

/--
The forgetful functor from semirings to monoids preserves all limits.
-/
protected instance forget₂_Mon_preserves_limits :
    category_theory.limits.preserves_limits (category_theory.forget₂ SemiRing Mon) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ SemiRing) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone
            (has_limits.limit_cone_is_limit F) (forget₂_Mon_preserves_limits_aux F)

/--
The forgetful functor from semirings to types preserves all limits.
-/
protected instance forget_preserves_limits :
    category_theory.limits.preserves_limits (category_theory.forget SemiRing) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ SemiRing) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone
            (has_limits.limit_cone_is_limit F)
            (category_theory.limits.types.limit_cone_is_limit (F ⋙ category_theory.forget SemiRing))

end SemiRing


namespace CommSemiRing


protected instance comm_semiring_obj {J : Type u} [category_theory.small_category J]
    (F : J ⥤ CommSemiRing) (j : J) :
    comm_semiring (category_theory.functor.obj (F ⋙ category_theory.forget CommSemiRing) j) :=
  id (CommSemiRing.comm_semiring (category_theory.functor.obj F j))

protected instance limit_comm_semiring {J : Type u} [category_theory.small_category J]
    (F : J ⥤ CommSemiRing) :
    comm_semiring
        (category_theory.limits.cone.X
          (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget CommSemiRing))) :=
  subsemiring.to_comm_semiring
    (SemiRing.sections_subsemiring (F ⋙ category_theory.forget₂ CommSemiRing SemiRing))

/--
We show that the forgetful functor `CommSemiRing ⥤ SemiRing` creates limits.

All we need to do is notice that the limit point has a `comm_semiring` instance available,
and then reuse the existing limit.
-/
protected instance category_theory.forget₂.category_theory.creates_limit {J : Type u}
    [category_theory.small_category J] (F : J ⥤ CommSemiRing) :
    category_theory.creates_limit F (category_theory.forget₂ CommSemiRing SemiRing) :=
  sorry

/--
A choice of limit cone for a functor into `CommSemiRing`.
(Generally, you'll just want to use `limit F`.)
-/
def limit_cone {J : Type u} [category_theory.small_category J] (F : J ⥤ CommSemiRing) :
    category_theory.limits.cone F :=
  category_theory.lift_limit
    (category_theory.limits.limit.is_limit (F ⋙ category_theory.forget₂ CommSemiRing SemiRing))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limit_cone_is_limit {J : Type u} [category_theory.small_category J] (F : J ⥤ CommSemiRing) :
    category_theory.limits.is_limit (limit_cone F) :=
  category_theory.lifted_limit_is_limit
    (category_theory.limits.limit.is_limit (F ⋙ category_theory.forget₂ CommSemiRing SemiRing))

/-- The category of rings has all limits. -/
protected instance has_limits : category_theory.limits.has_limits CommSemiRing :=
  category_theory.limits.has_limits.mk
    fun (J : Type u) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_limits_of_shape.mk
        fun (F : J ⥤ CommSemiRing) =>
          category_theory.has_limit_of_created F (category_theory.forget₂ CommSemiRing SemiRing)

/--
The forgetful functor from rings to semirings preserves all limits.
-/
protected instance forget₂_SemiRing_preserves_limits :
    category_theory.limits.preserves_limits (category_theory.forget₂ CommSemiRing SemiRing) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ CommSemiRing) =>
          category_theory.preserves_limit_of_creates_limit_and_has_limit F
            (category_theory.forget₂ CommSemiRing SemiRing)

/--
The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
protected instance forget_preserves_limits :
    category_theory.limits.preserves_limits (category_theory.forget CommSemiRing) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ CommSemiRing) =>
          category_theory.limits.comp_preserves_limit
            (category_theory.forget₂ CommSemiRing SemiRing) (category_theory.forget SemiRing)

end CommSemiRing


namespace Ring


protected instance ring_obj {J : Type u} [category_theory.small_category J] (F : J ⥤ Ring) (j : J) :
    ring (category_theory.functor.obj (F ⋙ category_theory.forget Ring) j) :=
  id (Ring.ring (category_theory.functor.obj F j))

/--
The flat sections of a functor into `Ring` form a subring of all sections.
-/
def sections_subring {J : Type u} [category_theory.small_category J] (F : J ⥤ Ring) :
    subring ((j : J) → ↥(category_theory.functor.obj F j)) :=
  subring.mk (category_theory.functor.sections (F ⋙ category_theory.forget Ring)) sorry sorry sorry
    sorry sorry

protected instance limit_ring {J : Type u} [category_theory.small_category J] (F : J ⥤ Ring) :
    ring
        (category_theory.limits.cone.X
          (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget Ring))) :=
  subring.to_ring (sections_subring F)

/--
We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `ring` instance available,
and then reuse the existing limit.
-/
protected instance category_theory.forget₂.category_theory.creates_limit {J : Type u}
    [category_theory.small_category J] (F : J ⥤ Ring) :
    category_theory.creates_limit F (category_theory.forget₂ Ring SemiRing) :=
  sorry

/--
A choice of limit cone for a functor into `Ring`.
(Generally, you'll just want to use `limit F`.)
-/
def limit_cone {J : Type u} [category_theory.small_category J] (F : J ⥤ Ring) :
    category_theory.limits.cone F :=
  category_theory.lift_limit
    (category_theory.limits.limit.is_limit (F ⋙ category_theory.forget₂ Ring SemiRing))

/--
The chosen cone