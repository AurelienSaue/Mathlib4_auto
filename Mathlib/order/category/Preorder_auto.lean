/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.preorder_hom
import Mathlib.category_theory.concrete_category.default
import Mathlib.algebra.punit_instances
import PostPort

universes u_1 

namespace Mathlib

/-! # Category of preorders -/

/-- The category of preorders. -/
def Preorder  :=
  category_theory.bundled preorder

namespace Preorder


protected instance preorder_hom.category_theory.bundled_hom : category_theory.bundled_hom preorder_hom :=
  category_theory.bundled_hom.mk preorder_hom.to_fun preorder_hom.id preorder_hom.comp

protected instance concrete_category : category_theory.concrete_category Preorder :=
  category_theory.bundled_hom.category_theory.bundled.category_theory.concrete_category preorder_hom

/-- Construct a bundled Preorder from the underlying type and typeclass. -/
def of (α : Type u_1) [preorder α] : Preorder :=
  category_theory.bundled.of α

protected instance inhabited : Inhabited Preorder :=
  { default := of PUnit }

protected instance preorder (α : Preorder) : preorder ↥α :=
  category_theory.bundled.str α

