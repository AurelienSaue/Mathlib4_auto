/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.sort
import Mathlib.data.fin
import Mathlib.order.category.LinearOrder
import Mathlib.PostPort

universes u_1 l u v 

namespace Mathlib

/-! # Nonempty finite linear orders

Nonempty finite linear orders form the index category for simplicial objects.
-/

/-- A typeclass for nonempty finite linear orders. -/
class nonempty_fin_lin_ord (α : Type u_1)
    extends order_bot α, fintype α, order_top α, linear_order α where

protected instance punit.nonempty_fin_lin_ord : nonempty_fin_lin_ord PUnit :=
  nonempty_fin_lin_ord.mk (fintype.elems PUnit) fintype.complete
    linear_ordered_cancel_add_comm_monoid.le linear_ordered_cancel_add_comm_monoid.lt
    linear_ordered_cancel_add_comm_monoid.le_refl linear_ordered_cancel_add_comm_monoid.le_trans
    linear_ordered_cancel_add_comm_monoid.le_antisymm linear_ordered_cancel_add_comm_monoid.le_total
    linear_ordered_cancel_add_comm_monoid.decidable_le
    linear_ordered_cancel_add_comm_monoid.decidable_eq
    linear_ordered_cancel_add_comm_monoid.decidable_lt PUnit.unit sorry PUnit.unit sorry

protected instance fin.nonempty_fin_lin_ord (n : ℕ) : nonempty_fin_lin_ord (fin (n + 1)) :=
  nonempty_fin_lin_ord.mk (fintype.elems (fin (n + 1))) sorry linear_order.le linear_order.lt sorry
    sorry sorry sorry linear_order.decidable_le linear_order.decidable_eq linear_order.decidable_lt
    0 fin.zero_le (fin.last n) fin.le_last

protected instance ulift.nonempty_fin_lin_ord (α : Type u) [nonempty_fin_lin_ord α] :
    nonempty_fin_lin_ord (ulift α) :=
  nonempty_fin_lin_ord.mk (fintype.elems (ulift α)) sorry linear_order.le linear_order.lt sorry
    sorry sorry sorry linear_order.decidable_le linear_order.decidable_eq linear_order.decidable_lt
    (ulift.up ⊥) sorry (ulift.up ⊤) sorry

/-- The category of nonempty finite linear orders. -/
def NonemptyFinLinOrd := category_theory.bundled nonempty_fin_lin_ord

namespace NonemptyFinLinOrd


protected instance nonempty_fin_lin_ord.to_linear_order.category_theory.bundled_hom.parent_projection :
    category_theory.bundled_hom.parent_projection nonempty_fin_lin_ord.to_linear_order :=
  category_theory.bundled_hom.parent_projection.mk

protected instance large_category : category_theory.large_category NonemptyFinLinOrd :=
  category_theory.bundled_hom.category
    (category_theory.bundled_hom.map_hom
      (category_theory.bundled_hom.map_hom
        (category_theory.bundled_hom.map_hom preorder_hom partial_order.to_preorder)
        linear_order.to_partial_order)
      nonempty_fin_lin_ord.to_linear_order)

/-- Construct a bundled NonemptyFinLinOrd from the underlying type and typeclass. -/
def of (α : Type u_1) [nonempty_fin_lin_ord α] : NonemptyFinLinOrd := category_theory.bundled.of α

protected instance inhabited : Inhabited NonemptyFinLinOrd := { default := of PUnit }

protected instance nonempty_fin_lin_ord (α : NonemptyFinLinOrd) : nonempty_fin_lin_ord ↥α :=
  category_theory.bundled.str α

end Mathlib