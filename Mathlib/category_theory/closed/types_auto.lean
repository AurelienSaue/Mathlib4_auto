/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.presheaf
import Mathlib.category_theory.limits.preserves.functor_category
import Mathlib.category_theory.limits.shapes.types
import Mathlib.category_theory.closed.cartesian
import Mathlib.PostPort

universes v₁ u₁ 

namespace Mathlib

/-!
# Cartesian closure of Type

Show that `Type u₁` is cartesian closed, and `C ⥤ Type u₁` is cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is cartesian closed.
-/

namespace category_theory


protected instance obj.is_left_adjoint (X : Type v₁) :
    is_left_adjoint (functor.obj limits.types.binary_product_functor X) :=
  is_left_adjoint.mk
    (functor.mk (fun (Y : Type v₁) => X ⟶ Y)
      fun (Y₁ Y₂ : Type v₁) (f : Y₁ ⟶ Y₂) (g : X ⟶ Y₁) => g ≫ f)
    (adjunction.mk_of_unit_counit
      (adjunction.core_unit_counit.mk (nat_trans.mk fun (Z : Type v₁) (z : Z) (x : X) => (x, z))
        (nat_trans.mk
          fun (Z : Type v₁)
            (xf :
            functor.obj
              ((functor.mk (fun (Y : Type v₁) => X ⟶ Y)
                  fun (Y₁ Y₂ : Type v₁) (f : Y₁ ⟶ Y₂) (g : X ⟶ Y₁) => g ≫ f) ⋙
                functor.obj limits.types.binary_product_functor X)
              Z) =>
            prod.snd xf (prod.fst xf))))

protected instance sort.limits.has_finite_products : limits.has_finite_products (Type v₁) :=
  limits.has_finite_products_of_has_products (Type v₁)

protected instance sort.cartesian_closed : cartesian_closed (Type v₁) :=
  monoidal_closed.mk
    fun (X : Type v₁) =>
      closed.mk
        (adjunction.left_adjoint_of_nat_iso (iso.app limits.types.binary_product_iso_prod X))

protected instance functor.limits.has_finite_products {C : Type u₁} [category C] :
    limits.has_finite_products (C ⥤ Type u₁) :=
  limits.has_finite_products_of_has_products (C ⥤ Type u₁)

protected instance functor.cartesian_closed {C : Type v₁} [small_category C] :
    cartesian_closed (C ⥤ Type v₁) :=
  monoidal_closed.mk
    fun (F : C ⥤ Type v₁) =>
      closed.mk
        (let _inst : limits.preserves_colimits (functor.obj limits.prod.functor F) :=
          functor_category.prod_preserves_colimits F;
        is_left_adjoint_of_preserves_colimits (functor.obj limits.prod.functor F))

end Mathlib