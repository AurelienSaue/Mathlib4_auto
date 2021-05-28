/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.category.Group.limits
import Mathlib.algebra.category.Group.preadditive
import Mathlib.category_theory.limits.shapes.biproducts
import Mathlib.category_theory.limits.shapes.types
import Mathlib.algebra.group.pi
import PostPort

universes u u_1 

namespace Mathlib

/-!
# The category of abelian groups has finite biproducts
-/

namespace AddCommGroup


/--
Construct limit data for a binary product in `AddCommGroup`, using `AddCommGroup.of (G × H)`.
-/
def binary_product_limit_cone (G : AddCommGroup) (H : AddCommGroup) : category_theory.limits.limit_cone (category_theory.limits.pair G H) :=
  category_theory.limits.limit_cone.mk
    (category_theory.limits.cone.mk (of (↥G × ↥H))
      (category_theory.nat_trans.mk
        fun (j : category_theory.discrete category_theory.limits.walking_pair) =>
          category_theory.limits.walking_pair.cases_on j (add_monoid_hom.fst ↥G ↥H) (add_monoid_hom.snd ↥G ↥H)))
    (category_theory.limits.is_limit.mk
      fun (s : category_theory.limits.cone (category_theory.limits.pair G H)) =>
        add_monoid_hom.prod
          (category_theory.nat_trans.app (category_theory.limits.cone.π s) category_theory.limits.walking_pair.left)
          (category_theory.nat_trans.app (category_theory.limits.cone.π s) category_theory.limits.walking_pair.right))

protected instance has_binary_product (G : AddCommGroup) (H : AddCommGroup) : category_theory.limits.has_binary_product G H :=
  category_theory.limits.has_limit.mk (binary_product_limit_cone G H)

protected instance category_theory.limits.has_binary_biproduct (G : AddCommGroup) (H : AddCommGroup) : category_theory.limits.has_binary_biproduct G H :=
  category_theory.limits.has_binary_biproduct.of_has_binary_product G H

/--
We verify that the biproduct in AddCommGroup is isomorphic to
the cartesian product of the underlying types:
-/
def biprod_iso_prod (G : AddCommGroup) (H : AddCommGroup) : G ⊞ H ≅ of (↥G × ↥H) :=
  category_theory.limits.is_limit.cone_point_unique_up_to_iso (category_theory.limits.binary_biproduct.is_limit G H)
    (category_theory.limits.limit_cone.is_limit (binary_product_limit_cone G H))

-- Furthermore, our biproduct will automatically function as a coproduct.

namespace has_limit


/--
The map from an arbitrary cone over a indexed family of abelian groups
to the cartesian product of those groups.
-/
def lift {J : Type u} (F : category_theory.discrete J ⥤ AddCommGroup) (s : category_theory.limits.cone F) : category_theory.limits.cone.X s ⟶ of ((j : category_theory.discrete J) → ↥(category_theory.functor.obj F j)) :=
  add_monoid_hom.mk
    (fun (x : ↥(category_theory.limits.cone.X s)) (j : category_theory.discrete J) =>
      coe_fn (category_theory.nat_trans.app (category_theory.limits.cone.π s) j) x)
    sorry sorry

@[simp] theorem lift_apply {J : Type u} (F : category_theory.discrete J ⥤ AddCommGroup) (s : category_theory.limits.cone F) (x : ↥(category_theory.limits.cone.X s)) (j : J) : coe_fn (lift F s) x j = coe_fn (category_theory.nat_trans.app (category_theory.limits.cone.π s) j) x :=
  rfl

/--
Construct limit data for a product in `AddCommGroup`, using `AddCommGroup.of (Π j, F.obj j)`.
-/
def product_limit_cone {J : Type u} (F : category_theory.discrete J ⥤ AddCommGroup) : category_theory.limits.limit_cone F :=
  category_theory.limits.limit_cone.mk
    (category_theory.limits.cone.mk (of ((j : category_theory.discrete J) → ↥(category_theory.functor.obj F j)))
      (category_theory.discrete.nat_trans
        fun (j : category_theory.discrete J) =>
          add_monoid_hom.apply (fun (j : category_theory.discrete J) => ↥(category_theory.functor.obj F j)) j))
    (category_theory.limits.is_limit.mk (lift F))

end has_limit


protected instance category_theory.limits.has_biproduct {J : Type u} [DecidableEq J] [fintype J] (f : J → AddCommGroup) : category_theory.limits.has_biproduct f :=
  category_theory.limits.has_biproduct.of_has_product f

/--
We verify that the biproduct we've just defined is isomorphic to the AddCommGroup structure
on the dependent function type
-/
def biproduct_iso_pi {J : Type u} [DecidableEq J] [fintype J] (f : J → AddCommGroup) : ⨁ f ≅ of ((j : J) → ↥(f j)) :=
  category_theory.limits.is_limit.cone_point_unique_up_to_iso (category_theory.limits.biproduct.is_limit f)
    (category_theory.limits.limit_cone.is_limit (has_limit.product_limit_cone (category_theory.discrete.functor f)))

protected instance category_theory.limits.has_finite_biproducts : category_theory.limits.has_finite_biproducts AddCommGroup :=
  category_theory.limits.has_finite_biproducts.mk
    fun (J : Type u_1) (_x : DecidableEq J) (_x_1 : fintype J) =>
      category_theory.limits.has_biproducts_of_shape.mk
        fun (f : J → AddCommGroup) => category_theory.limits.has_biproduct f

