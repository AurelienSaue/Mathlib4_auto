/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Mon.limits
import Mathlib.algebra.category.Group.preadditive
import Mathlib.category_theory.over
import Mathlib.category_theory.limits.concrete_category
import Mathlib.category_theory.limits.shapes.concrete_category
import Mathlib.group_theory.subgroup
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# The category of (commutative) (additive) groups has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

namespace Group


protected instance Mathlib.AddGroup.add_group_obj {J : Type u} [category_theory.small_category J]
    (F : J ⥤ AddGroup) (j : J) :
    add_group (category_theory.functor.obj (F ⋙ category_theory.forget AddGroup) j) :=
  id (AddGroup.add_group (category_theory.functor.obj F j))

/--
The flat sections of a functor into `Group` form a subgroup of all sections.
-/
def Mathlib.AddGroup.sections_add_subgroup {J : Type u} [category_theory.small_category J]
    (F : J ⥤ AddGroup) : add_subgroup ((j : J) → ↥(category_theory.functor.obj F j)) :=
  add_subgroup.mk (category_theory.functor.sections (F ⋙ category_theory.forget AddGroup)) sorry
    sorry sorry

protected instance limit_group {J : Type u} [category_theory.small_category J] (F : J ⥤ Group) :
    group
        (category_theory.limits.cone.X
          (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget Group))) :=
  id (subgroup.to_group (sections_subgroup F))

/--
We show that the forgetful functor `Group ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `group` instance available,
and then reuse the existing limit.
-/
protected instance category_theory.forget₂.category_theory.creates_limit {J : Type u}
    [category_theory.small_category J] (F : J ⥤ Group) :
    category_theory.creates_limit F (category_theory.forget₂ Group Mon) :=
  sorry

/--
A choice of limit cone for a functor into `Group`.
(Generally, you'll just want to use `limit F`.)
-/
def Mathlib.AddGroup.limit_cone {J : Type u} [category_theory.small_category J] (F : J ⥤ AddGroup) :
    category_theory.limits.cone F :=
  category_theory.lift_limit
    (category_theory.limits.limit.is_limit (F ⋙ category_theory.forget₂ AddGroup AddMon))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def Mathlib.AddGroup.limit_cone_is_limit {J : Type u} [category_theory.small_category J]
    (F : J ⥤ AddGroup) : category_theory.limits.is_limit (AddGroup.limit_cone F) :=
  category_theory.lifted_limit_is_limit
    (category_theory.limits.limit.is_limit (F ⋙ category_theory.forget₂ AddGroup AddMon))

/-- The category of groups has all limits. -/
protected instance has_limits : category_theory.limits.has_limits Group :=
  category_theory.limits.has_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_limits_of_shape.mk
        fun (F : J ⥤ Group) =>
          category_theory.has_limit_of_created F (category_theory.forget₂ Group Mon)

/--
The forgetful functor from groups to monoids preserves all limits.
(That is, the underlying monoid could have been computed instead as limits in the category
of monoids.)
-/
protected instance Mathlib.AddGroup.forget₂_AddMon_preserves_limits :
    category_theory.limits.preserves_limits (category_theory.forget₂ AddGroup AddMon) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ AddGroup) =>
          category_theory.preserves_limit_of_creates_limit_and_has_limit F
            (category_theory.forget₂ AddGroup AddMon)

/--
The forgetful functor from groups to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
protected instance forget_preserves_limits :
    category_theory.limits.preserves_limits (category_theory.forget Group) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ Group) =>
          category_theory.limits.comp_preserves_limit (category_theory.forget₂ Group Mon)
            (category_theory.forget Mon)

end Group


namespace CommGroup


protected instance Mathlib.AddCommGroup.add_comm_group_obj {J : Type u}
    [category_theory.small_category J] (F : J ⥤ AddCommGroup) (j : J) :
    add_comm_group (category_theory.functor.obj (F ⋙ category_theory.forget AddCommGroup) j) :=
  id (AddCommGroup.add_comm_group_instance (category_theory.functor.obj F j))

protected instance limit_comm_group {J : Type u} [category_theory.small_category J]
    (F : J ⥤ CommGroup) :
    comm_group
        (category_theory.limits.cone.X
          (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget CommGroup))) :=
  subgroup.to_comm_group (Group.sections_subgroup (F ⋙ category_theory.forget₂ CommGroup Group))

/--
We show that the forgetful functor `CommGroup ⥤ Group` creates limits.

All we need to do is notice that the limit point has a `comm_group` instance available,
and then reuse the existing limit.
-/
protected instance Mathlib.AddCommGroup.category_theory.forget₂.category_theory.creates_limit
    {J : Type u} [category_theory.small_category J] (F : J ⥤ AddCommGroup) :
    category_theory.creates_limit F (category_theory.forget₂ AddCommGroup AddGroup) :=
  sorry

/--
A choice of limit cone for a functor into `CommGroup`.
(Generally, you'll just want to use `limit F`.)
-/
def Mathlib.AddCommGroup.limit_cone {J : Type u} [category_theory.small_category J]
    (F : J ⥤ AddCommGroup) : category_theory.limits.cone F :=
  category_theory.lift_limit
    (category_theory.limits.limit.is_limit (F ⋙ category_theory.forget₂ AddCommGroup AddGroup))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limit_cone_is_limit {J : Type u} [category_theory.small_category J] (F : J ⥤ CommGroup) :
    category_theory.limits.is_limit (limit_cone F) :=
  category_theory.lifted_limit_is_limit
    (category_theory.limits.limit.is_limit (F ⋙ category_theory.forget₂ CommGroup Group))

/-- The category of commutative groups has all limits. -/
protected instance has_limits : category_theory.limits.has_limits CommGroup :=
  category_theory.limits.has_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_limits_of_shape.mk
        fun (F : J ⥤ CommGroup) =>
          category_theory.has_limit_of_created F (category_theory.forget₂ CommGroup Group)

/--
The forgetful functor from commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category
of groups.)
-/
protected instance Mathlib.AddCommGroup.forget₂_AddGroup_preserves_limits :
    category_theory.limits.preserves_limits (category_theory.forget₂ AddCommGroup AddGroup) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ AddCommGroup) =>
          category_theory.preserves_limit_of_creates_limit_and_has_limit F
            (category_theory.forget₂ AddCommGroup AddGroup)

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_CommMon_preserves_limits_aux {J : Type u} [category_theory.small_category J]
    (F : J ⥤ CommGroup) :
    category_theory.limits.is_limit
        (category_theory.functor.map_cone (category_theory.forget₂ CommGroup CommMon)
          (limit_cone F)) :=
  CommMon.limit_cone_is_limit (F ⋙ category_theory.forget₂ CommGroup CommMon)

/--
The forgetful functor from commutative groups to commutative monoids preserves all limits.
(That is, the underlying commutative monoids could have been computed instead as limits
in the category of commutative monoids.)
-/
protected instance forget₂_CommMon_preserves_limits :
    category_theory.limits.preserves_limits (category_theory.forget₂ CommGroup CommMon) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ CommGroup) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
            (forget₂_CommMon_preserves_limits_aux F)

/--
The forgetful functor from commutative groups to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
protected instance forget_preserves_limits :
    category_theory.limits.preserves_limits (category_theory.forget CommGroup) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ CommGroup) =>
          category_theory.limits.comp_preserves_limit (category_theory.forget₂ CommGroup Group)
            (category_theory.forget Group)

end CommGroup


namespace AddCommGroup


/--
The categorical kernel of a morphism in `AddCommGroup`
agrees with the usual group-theoretical kernel.
-/
def kernel_iso_ker {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) :
    category_theory.limits.kernel f ≅ of ↥(add_monoid_hom.ker f) :=
  category_theory.iso.mk
    (add_monoid_hom.mk
      (fun (g : ↥(category_theory.limits.kernel f)) =>
        { val := coe_fn (category_theory.limits.kernel.ι f) g, property := sorry })
      sorry sorry)
    (category_theory.limits.kernel.lift f (add_subgroup.subtype (add_monoid_hom.ker f)) sorry)

@[simp] theorem kernel_iso_ker_hom_comp_subtype {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) :
    category_theory.iso.hom (kernel_iso_ker f) ≫ add_subgroup.subtype (add_monoid_hom.ker f) =
        category_theory.limits.kernel.ι f :=
  sorry

@[simp] theorem kernel_iso_ker_inv_comp_ι {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) :
    category_theory.iso.inv (kernel_iso_ker f) ≫ category_theory.limits.kernel.ι f =
        add_subgroup.subtype (add_monoid_hom.ker f) :=
  sorry

/--
The categorical kernel inclusion for `f : G ⟶ H`, as an object over `G`,
agrees with the `subtype` map.
-/
@[simp] theorem kernel_iso_ker_over_inv_left {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) :
    category_theory.comma_morphism.left (category_theory.iso.inv (kernel_iso_ker_over f)) =
        category_theory.iso.inv (kernel_iso_ker f) :=
  Eq.refl (category_theory.iso.inv (kernel_iso_ker f))

end Mathlib