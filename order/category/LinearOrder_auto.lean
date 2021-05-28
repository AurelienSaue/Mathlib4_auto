/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.category.PartialOrder
import PostPort

universes u_1 

namespace Mathlib

/-! # Category of linearly ordered types -/

/-- The category of linearly ordered types. -/
def LinearOrder  :=
  category_theory.bundled linear_order

namespace LinearOrder


protected instance linear_order.to_partial_order.category_theory.bundled_hom.parent_projection : category_theory.bundled_hom.parent_projection linear_order.to_partial_order :=
  category_theory.bundled_hom.parent_projection.mk

protected instance large_category : category_theory.large_category LinearOrder :=
  category_theory.bundled_hom.category
    (category_theory.bundled_hom.map_hom (category_theory.bundled_hom.map_hom preorder_hom partial_order.to_preorder)
      linear_order.to_partial_order)

/-- Construct a bundled LinearOrder from the underlying type and typeclass. -/
def of (α : Type u_1) [linear_order α] : LinearOrder :=
  category_theory.bundled.of α

protected instance inhabited : Inhabited LinearOrder :=
  { default := of PUnit }

protected instance linear_order (α : LinearOrder) : linear_order ↥α :=
  category_theory.bundled.str α

