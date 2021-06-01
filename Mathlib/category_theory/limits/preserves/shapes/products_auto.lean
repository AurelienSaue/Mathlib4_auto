/-
Copyright (c) 2020 Scott Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.products
import Mathlib.category_theory.limits.preserves.basic
import Mathlib.PostPort

universes u₁ u₂ v 

namespace Mathlib

/-!
# Preserving products

Constructions to relate the notions of preserving products and reflecting products
to concrete fans.

In particular, we show that `pi_comparison G f` is an isomorphism iff `G` preserves
the limit of `f`.
-/

namespace category_theory.limits


/--
The map of a fan is a limit iff the fan consisting of the mapped morphisms is a limit. This
essentially lets us commute `fan.mk` with `functor.map_cone`.
-/
def is_limit_map_cone_fan_mk_equiv {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D)
    {J : Type v} (f : J → C) {P : C} (g : (j : J) → P ⟶ f j) :
    is_limit (functor.map_cone G (fan.mk P g)) ≃
        is_limit (fan.mk (functor.obj G P) fun (j : J) => functor.map G (g j)) :=
  equiv.trans
    (equiv.symm
      (is_limit.postcompose_hom_equiv
        (discrete.nat_iso fun (j : discrete J) => iso.refl (functor.obj G (f j)))
        (functor.map_cone G (fan.mk P g))))
    (is_limit.equiv_iso_limit
      (cones.ext
        (iso.refl
          (cone.X
            (functor.obj
              (cones.postcompose
                (iso.hom (discrete.nat_iso fun (j : discrete J) => iso.refl (functor.obj G (f j)))))
              (functor.map_cone G (fan.mk P g)))))
        sorry))

/-- The property of preserving products expressed in terms of fans. -/
def is_limit_fan_mk_obj_of_is_limit {C : Type u₁} [category C] {D : Type u₂} [category D]
    (G : C ⥤ D) {J : Type v} (f : J → C) [preserves_limit (discrete.functor f) G] {P : C}
    (g : (j : J) → P ⟶ f j) (t : is_limit (fan.mk P g)) :
    is_limit (fan.mk (functor.obj G P) fun (j : J) => functor.map G (g j)) :=
  coe_fn (is_limit_map_cone_fan_mk_equiv G (fun (j : J) => f j) g) (preserves_limit.preserves t)

/-- The property of reflecting products expressed in terms of fans. -/
def is_limit_of_is_limit_fan_mk_obj {C : Type u₁} [category C] {D : Type u₂} [category D]
    (G : C ⥤ D) {J : Type v} (f : J → C) [reflects_limit (discrete.functor f) G] {P : C}
    (g : (j : J) → P ⟶ f j)
    (t : is_limit (fan.mk (functor.obj G P) fun (j : J) => functor.map G (g j))) :
    is_limit (fan.mk P g) :=
  reflects_limit.reflects
    (coe_fn (equiv.symm (is_limit_map_cone_fan_mk_equiv G (fun (j : J) => f j) fun (j : J) => g j))
      t)

/--
If `G` preserves products and `C` has them, then the fan constructed of the mapped projection of a
product is a limit.
-/
def is_limit_of_has_product_of_preserves_limit {C : Type u₁} [category C] {D : Type u₂} [category D]
    (G : C ⥤ D) {J : Type v} (f : J → C) [has_product f] [preserves_limit (discrete.functor f) G] :
    is_limit (fan.mk (functor.obj G (∏ f)) fun (j : J) => functor.map G (pi.π f j)) :=
  is_limit_fan_mk_obj_of_is_limit G f (fun (j : J) => pi.π f j)
    (product_is_product fun (j : J) => f j)

/-- If `pi_comparison G f` is an isomorphism, then `G` preserves the limit of `f`. -/
def preserves_product.of_iso_comparison {C : Type u₁} [category C] {D : Type u₂} [category D]
    (G : C ⥤ D) {J : Type v} (f : J → C) [has_product f]
    [has_product fun (j : J) => functor.obj G (f j)] [i : is_iso (pi_comparison G f)] :
    preserves_limit (discrete.functor f) G :=
  preserves_limit_of_preserves_limit_cone (product_is_product f)
    (coe_fn (equiv.symm (is_limit_map_cone_fan_mk_equiv G (fun (b : J) => f b) (pi.π f)))
      (is_limit.of_point_iso
        (limit.is_limit (discrete.functor fun (j : J) => functor.obj G (f j)))))

/--
If `G` preserves limits, we have an isomorphism from the image of a product to the product of the
images.
-/
def preserves_product.iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D)
    {J : Type v} (f : J → C) [has_product f] [has_product fun (j : J) => functor.obj G (f j)]
    [preserves_limit (discrete.functor f) G] :
    functor.obj G (∏ f) ≅ ∏ fun (j : J) => functor.obj G (f j) :=
  is_limit.cone_point_unique_up_to_iso (is_limit_of_has_product_of_preserves_limit G f)
    (limit.is_limit (discrete.functor fun (j : J) => functor.obj G (f j)))

@[simp] theorem preserves_product.iso_hom {C : Type u₁} [category C] {D : Type u₂} [category D]
    (G : C ⥤ D) {J : Type v} (f : J → C) [has_product f]
    [has_product fun (j : J) => functor.obj G (f j)] [preserves_limit (discrete.functor f) G] :
    iso.hom (preserves_product.iso G f) = pi_comparison G f :=
  rfl

protected instance pi_comparison.category_theory.is_iso {C : Type u₁} [category C] {D : Type u₂}
    [category D] (G : C ⥤ D) {J : Type v} (f : J → C) [has_product f]
    [has_product fun (j : J) => functor.obj G (f j)] [preserves_limit (discrete.functor f) G] :
    is_iso (pi_comparison G f) :=
  eq.mpr sorry (is_iso.of_iso (preserves_product.iso G f))

end Mathlib