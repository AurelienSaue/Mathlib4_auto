/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.limits.preserves.basic
import Mathlib.PostPort

universes u₁ u₂ v 

namespace Mathlib

/-!
# Preserving binary products

Constructions to relate the notions of preserving binary products and reflecting binary products
to concrete binary fans.

In particular, we show that `prod_comparison G X Y` is an isomorphism iff `G` preserves
the product of `X` and `Y`.
-/

namespace category_theory.limits


/--
The map of a binary fan is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `binary_fan.mk` with `functor.map_cone`.
-/
def is_limit_map_cone_binary_fan_equiv {C : Type u₁} [category C] {D : Type u₂} [category D]
    (G : C ⥤ D) {P : C} {X : C} {Y : C} (f : P ⟶ X) (g : P ⟶ Y) :
    is_limit (functor.map_cone G (binary_fan.mk f g)) ≃
        is_limit (binary_fan.mk (functor.map G f) (functor.map G g)) :=
  equiv.trans
    (equiv.symm
      (is_limit.postcompose_hom_equiv (diagram_iso_pair (pair X Y ⋙ G))
        (functor.map_cone G (binary_fan.mk f g))))
    (is_limit.equiv_iso_limit
      (cones.ext
        (iso.refl
          (cone.X
            (functor.obj (cones.postcompose (iso.hom (diagram_iso_pair (pair X Y ⋙ G))))
              (functor.map_cone G (binary_fan.mk f g)))))
        sorry))

/-- The property of preserving products expressed in terms of binary fans. -/
def map_is_limit_of_preserves_of_is_limit {C : Type u₁} [category C] {D : Type u₂} [category D]
    (G : C ⥤ D) {P : C} {X : C} {Y : C} (f : P ⟶ X) (g : P ⟶ Y) [preserves_limit (pair X Y) G]
    (l : is_limit (binary_fan.mk f g)) :
    is_limit (binary_fan.mk (functor.map G f) (functor.map G g)) :=
  coe_fn (is_limit_map_cone_binary_fan_equiv G f g) (preserves_limit.preserves l)

/-- The property of reflecting products expressed in terms of binary fans. -/
def is_limit_of_reflects_of_map_is_limit {C : Type u₁} [category C] {D : Type u₂} [category D]
    (G : C ⥤ D) {P : C} {X : C} {Y : C} (f : P ⟶ X) (g : P ⟶ Y) [reflects_limit (pair X Y) G]
    (l : is_limit (binary_fan.mk (functor.map G f) (functor.map G g))) :
    is_limit (binary_fan.mk f g) :=
  reflects_limit.reflects (coe_fn (equiv.symm (is_limit_map_cone_binary_fan_equiv G f g)) l)

/--
If `G` preserves binary products and `C` has them, then the binary fan constructed of the mapped
morphisms of the binary product cone is a limit.
-/
def is_limit_of_has_binary_product_of_preserves_limit {C : Type u₁} [category C] {D : Type u₂}
    [category D] (G : C ⥤ D) (X : C) (Y : C) [has_binary_product X Y]
    [preserves_limit (pair X Y) G] :
    is_limit (binary_fan.mk (functor.map G prod.fst) (functor.map G prod.snd)) :=
  map_is_limit_of_preserves_of_is_limit G prod.fst prod.snd (prod_is_prod X Y)

/--
If the product comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
def preserves_pair.of_iso_comparison {C : Type u₁} [category C] {D : Type u₂} [category D]
    (G : C ⥤ D) (X : C) (Y : C) [has_binary_product X Y]
    [has_binary_product (functor.obj G X) (functor.obj G Y)] [i : is_iso (prod_comparison G X Y)] :
    preserves_limit (pair X Y) G :=
  preserves_limit_of_preserves_limit_cone (prod_is_prod X Y)
    (coe_fn (equiv.symm (is_limit_map_cone_binary_fan_equiv G prod.fst prod.snd))
      (is_limit.of_point_iso (limit.is_limit (pair (functor.obj G X) (functor.obj G Y)))))

/--
If `G` preserves the product of `(X,Y)`, then the product comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
def preserves_pair.iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) (X : C)
    (Y : C) [has_binary_product X Y] [has_binary_product (functor.obj G X) (functor.obj G Y)]
    [preserves_limit (pair X Y) G] : functor.obj G (X ⨯ Y) ≅ functor.obj G X ⨯ functor.obj G Y :=
  is_limit.cone_point_unique_up_to_iso (is_limit_of_has_binary_product_of_preserves_limit G X Y)
    (limit.is_limit (pair (functor.obj G X) (functor.obj G Y)))

@[simp] theorem preserves_pair.iso_hom {C : Type u₁} [category C] {D : Type u₂} [category D]
    (G : C ⥤ D) (X : C) (Y : C) [has_binary_product X Y]
    [has_binary_product (functor.obj G X) (functor.obj G Y)] [preserves_limit (pair X Y) G] :
    iso.hom (preserves_pair.iso G X Y) = prod_comparison G X Y :=
  rfl

protected instance prod_comparison.category_theory.is_iso {C : Type u₁} [category C] {D : Type u₂}
    [category D] (G : C ⥤ D) (X : C) (Y : C) [has_binary_product X Y]
    [has_binary_product (functor.obj G X) (functor.obj G Y)] [preserves_limit (pair X Y) G] :
    is_iso (prod_comparison G X Y) :=
  eq.mpr sorry (is_iso.of_iso (preserves_pair.iso G X Y))

end Mathlib