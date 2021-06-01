/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.category.Preorder
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-! # Category of partially ordered types -/

/-- The category of partially ordered types. -/
def PartialOrder := category_theory.bundled partial_order

namespace PartialOrder


protected instance partial_order.to_preorder.category_theory.bundled_hom.parent_projection :
    category_theory.bundled_hom.parent_projection partial_order.to_preorder :=
  category_theory.bundled_hom.parent_projection.mk

protected instance concrete_category : category_theory.concrete_category PartialOrder :=
  category_theory.bundled_hom.category_theory.bundled.category_theory.concrete_category
    (category_theory.bundled_hom.map_hom preorder_hom partial_order.to_preorder)

/-- Construct a bundled PartialOrder from the underlying type and typeclass. -/
def of (α : Type u_1) [partial_order α] : PartialOrder := category_theory.bundled.of α

protected instance inhabited : Inhabited PartialOrder := { default := of PUnit }

protected instance partial_order (α : PartialOrder) : partial_order ↥α :=
  category_theory.bundled.str α

end Mathlib