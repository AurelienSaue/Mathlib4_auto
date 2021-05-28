/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.category.Group.abelian
import Mathlib.category_theory.limits.shapes.images
import Mathlib.category_theory.limits.types
import PostPort

namespace Mathlib

/-!
# The category of commutative additive groups has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `AddCommGroup` is an abelian category.
-/

namespace AddCommGroup


-- Note that because `injective_of_mono` is currently only proved in `Type 0`,

-- we restrict to the lowest universe here for now.

/-- the image of a morphism in AddCommGroup is just the bundling of `add_monoid_hom.range f` -/
def image {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) : AddCommGroup :=
  of ↥(add_monoid_hom.range f)

/-- the inclusion of `image f` into the target -/
def image.ι {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) : image f ⟶ H :=
  add_subgroup.subtype (add_monoid_hom.range f)

protected instance image.ι.category_theory.mono {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) : category_theory.mono (image.ι f) :=
  category_theory.concrete_category.mono_of_injective (image.ι f) subtype.val_injective

/-- the corestriction map to the image -/
def factor_thru_image {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) : G ⟶ image f :=
  add_monoid_hom.to_range f

theorem image.fac {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) : factor_thru_image f ≫ image.ι f = f :=
  ext G H (factor_thru_image f ≫ image.ι f) f fun (x : ↥G) => Eq.refl (coe_fn (factor_thru_image f ≫ image.ι f) x)

/-- the universal property for the image factorisation -/
def image.lift {G : AddCommGroup} {H : AddCommGroup} {f : G ⟶ H} (F' : category_theory.limits.mono_factorisation f) : image f ⟶ category_theory.limits.mono_factorisation.I F' :=
  add_monoid_hom.mk
    (fun (x : ↥(image f)) =>
      coe_fn (category_theory.limits.mono_factorisation.e F')
        (subtype.val (classical.indefinite_description (fun (x_1 : ↥G) => coe_fn f x_1 = subtype.val x) sorry)))
    sorry sorry

theorem image.lift_fac {G : AddCommGroup} {H : AddCommGroup} {f : G ⟶ H} (F' : category_theory.limits.mono_factorisation f) : image.lift F' ≫ category_theory.limits.mono_factorisation.m F' = image.ι f := sorry

/-- the factorisation of any morphism in AddCommGroup through a mono. -/
def mono_factorisation {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) : category_theory.limits.mono_factorisation f :=
  category_theory.limits.mono_factorisation.mk (image f) (image.ι f) (factor_thru_image f)

/-- the factorisation of any morphism in AddCommGroup through a mono has the universal property of
the image. -/
def is_image {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) : category_theory.limits.is_image (mono_factorisation f) :=
  category_theory.limits.is_image.mk image.lift

/--
The categorical image of a morphism in `AddCommGroup`
agrees with the usual group-theoretical range.
-/
def image_iso_range {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H) : category_theory.limits.image f ≅ of ↥(add_monoid_hom.range f) :=
  category_theory.limits.is_image.iso_ext (category_theory.limits.image.is_image f) (is_image f)

