/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.omega_complete_partial_order
import Mathlib.order.category.Preorder
import Mathlib.category_theory.limits.shapes.products
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.limits.constructions.limits_of_products_and_equalizers
import PostPort

universes u u_1 v u_2 

namespace Mathlib

/-!
# Category of types with a omega complete partial order

In this file, we bundle the class `omega_complete_partial_order` into a
concrete category and prove that continuous functions also form
a `omega_complete_partial_order`.

## Main definitions

 * `ωCPO`
   * an instance of `category` and `concrete_category`

 -/

/-- The category of types with a omega complete partial order. -/
def ωCPO  :=
  category_theory.bundled omega_complete_partial_order

namespace ωCPO


protected instance omega_complete_partial_order.continuous_hom.category_theory.bundled_hom : category_theory.bundled_hom omega_complete_partial_order.continuous_hom :=
  category_theory.bundled_hom.mk omega_complete_partial_order.continuous_hom.to_fun
    omega_complete_partial_order.continuous_hom.id omega_complete_partial_order.continuous_hom.comp

protected instance large_category : category_theory.large_category ωCPO :=
  category_theory.bundled_hom.category omega_complete_partial_order.continuous_hom

/-- Construct a bundled ωCPO from the underlying type and typeclass. -/
def of (α : Type u_1) [omega_complete_partial_order α] : ωCPO :=
  category_theory.bundled.of α

protected instance inhabited : Inhabited ωCPO :=
  { default := of PUnit }

protected instance omega_complete_partial_order (α : ωCPO) : omega_complete_partial_order ↥α :=
  category_theory.bundled.str α

namespace has_products


/-- The pi-type gives a cone for a product. -/
def product {J : Type v} (f : J → ωCPO) : category_theory.limits.fan f :=
  category_theory.limits.fan.mk (of ((j : J) → ↥(f j)))
    fun (j : J) => omega_complete_partial_order.continuous_hom.of_mono (pi.monotone_apply j) sorry

/-- The pi-type is a limit cone for the product. -/
def is_product (J : Type v) (f : J → ωCPO) : category_theory.limits.is_limit (product f) :=
  category_theory.limits.is_limit.mk
    fun (s : category_theory.limits.cone (category_theory.discrete.functor f)) =>
      omega_complete_partial_order.continuous_hom.mk
        (fun (t : ↥(category_theory.limits.cone.X s)) (j : J) =>
          coe_fn (category_theory.nat_trans.app (category_theory.limits.cone.π s) j) t)
        sorry sorry

protected instance category_theory.limits.has_product (J : Type v) (f : J → ωCPO) : category_theory.limits.has_product f :=
  category_theory.limits.has_limit.mk (category_theory.limits.limit_cone.mk (product f) (is_product J f))

end has_products


protected instance omega_complete_partial_order_equalizer {α : Type u_1} {β : Type u_2} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α →𝒄 β) (g : α →𝒄 β) : omega_complete_partial_order (Subtype fun (a : α) => coe_fn f a = coe_fn g a) :=
  omega_complete_partial_order.subtype (fun (a : α) => coe_fn f a = coe_fn g a) sorry

namespace has_equalizers


/-- The equalizer inclusion function as a `continuous_hom`. -/
def equalizer_ι {α : Type u_1} {β : Type u_2} [omega_complete_partial_order α] [omega_complete_partial_order β] (f : α →𝒄 β) (g : α →𝒄 β) : (Subtype fun (a : α) => coe_fn f a = coe_fn g a) →𝒄 α :=
  omega_complete_partial_order.continuous_hom.of_mono (preorder_hom.subtype.val fun (a : α) => coe_fn f a = coe_fn g a)
    sorry

/-- A construction of the equalizer fork. -/
def equalizer {X : ωCPO} {Y : ωCPO} (f : X ⟶ Y) (g : X ⟶ Y) : category_theory.limits.fork f g :=
  category_theory.limits.fork.of_ι (equalizer_ι f g) sorry

/-- The equalizer fork is a limit. -/
def is_equalizer {X : ωCPO} {Y : ωCPO} (f : X ⟶ Y) (g : X ⟶ Y) : category_theory.limits.is_limit (equalizer f g) :=
  category_theory.limits.fork.is_limit.mk' (equalizer f g)
    fun (s : category_theory.limits.fork f g) =>
      { val :=
          omega_complete_partial_order.continuous_hom.mk
            (fun
              (x :
              ↥(category_theory.functor.obj
                  (category_theory.functor.obj
                    (category_theory.functor.const category_theory.limits.walking_parallel_pair)
                    (category_theory.limits.cone.X s))
                  category_theory.limits.walking_parallel_pair.zero)) =>
              { val := coe_fn (category_theory.limits.fork.ι s) x, property := sorry })
            sorry sorry,
        property := sorry }

end has_equalizers


protected instance category_theory.limits.has_products : category_theory.limits.has_products ωCPO :=
  fun (J : Type v) =>
    category_theory.limits.has_limits_of_shape.mk
      fun (F : category_theory.discrete J ⥤ ωCPO) =>
        category_theory.limits.has_limit_of_iso (category_theory.iso.symm category_theory.discrete.nat_iso_functor)

protected instance category_theory.limits.parallel_pair.category_theory.limits.has_limit {X : ωCPO} {Y : ωCPO} (f : X ⟶ Y) (g : X ⟶ Y) : category_theory.limits.has_limit (category_theory.limits.parallel_pair f g) :=
  category_theory.limits.has_limit.mk
    (category_theory.limits.limit_cone.mk (has_equalizers.equalizer f g) (has_equalizers.is_equalizer f g))

protected instance category_theory.limits.has_equalizers : category_theory.limits.has_equalizers ωCPO :=
  category_theory.limits.has_equalizers_of_has_limit_parallel_pair ωCPO

protected instance category_theory.limits.has_limits : category_theory.limits.has_limits ωCPO :=
  category_theory.limits.limits_from_equalizers_and_products

