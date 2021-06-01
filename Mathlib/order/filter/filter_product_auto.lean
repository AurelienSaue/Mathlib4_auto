/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.filter.ultrafilter
import Mathlib.order.filter.germ
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Ultraproducts

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `order.filter.germ`.

## Tags

ultrafilter, ultraproduct
-/

namespace filter


namespace germ


/-- If `φ` is an ultrafilter then the ultraproduct is a division ring. -/
protected instance division_ring {α : Type u} {β : Type v} {φ : ultrafilter α} [division_ring β] :
    division_ring (germ (↑φ) β) :=
  division_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry
    ring.one sorry sorry sorry sorry div_inv_monoid.inv div_inv_monoid.div sorry sorry sorry

/-- If `φ` is an ultrafilter then the ultraproduct is a field. -/
protected instance field {α : Type u} {β : Type v} {φ : ultrafilter α} [field β] :
    field (germ (↑φ) β) :=
  field.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry
    comm_ring.mul sorry comm_ring.one sorry sorry sorry sorry sorry division_ring.inv sorry sorry
    sorry

/-- If `φ` is an ultrafilter then the ultraproduct is a linear order. -/
protected instance linear_order {α : Type u} {β : Type v} {φ : ultrafilter α} [linear_order β] :
    linear_order (germ (↑φ) β) :=
  linear_order.mk partial_order.le partial_order.lt sorry sorry sorry sorry
    (fun (a b : germ (↑φ) β) => classical.prop_decidable (a ≤ b))
    Mathlib.decidable_eq_of_decidable_le Mathlib.decidable_lt_of_decidable_le

@[simp] theorem const_div {α : Type u} {β : Type v} {φ : ultrafilter α} [division_ring β] (x : β)
    (y : β) : ↑(x / y) = ↑x / ↑y :=
  rfl

theorem coe_lt {α : Type u} {β : Type v} {φ : ultrafilter α} [preorder β] {f : α → β} {g : α → β} :
    ↑f < ↑g ↔ filter.eventually (fun (x : α) => f x < g x) ↑φ :=
  sorry

theorem coe_pos {α : Type u} {β : Type v} {φ : ultrafilter α} [preorder β] [HasZero β] {f : α → β} :
    0 < ↑f ↔ filter.eventually (fun (x : α) => 0 < f x) ↑φ :=
  coe_lt

theorem const_lt {α : Type u} {β : Type v} {φ : ultrafilter α} [preorder β] {x : β} {y : β} :
    ↑x < ↑y ↔ x < y :=
  iff.trans coe_lt lift_rel_const_iff

theorem lt_def {α : Type u} {β : Type v} {φ : ultrafilter α} [preorder β] : Less = lift_rel Less :=
  sorry

/-- If `φ` is an ultrafilter then the ultraproduct is an ordered ring. -/
protected instance ordered_ring {α : Type u} {β : Type v} {φ : ultrafilter α} [ordered_ring β] :
    ordered_ring (germ (↑φ) β) :=
  ordered_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry
    ring.one sorry sorry sorry sorry ordered_add_comm_group.le ordered_add_comm_group.lt sorry sorry
    sorry sorry sorry sorry

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered ring. -/
protected instance linear_ordered_ring {α : Type u} {β : Type v} {φ : ultrafilter α}
    [linear_ordered_ring β] : linear_ordered_ring (germ (↑φ) β) :=
  linear_ordered_ring.mk ordered_ring.add sorry ordered_ring.zero sorry sorry ordered_ring.neg
    ordered_ring.sub sorry sorry ordered_ring.mul sorry ordered_ring.one sorry sorry sorry sorry
    ordered_ring.le ordered_ring.lt sorry sorry sorry sorry sorry sorry sorry
    linear_order.decidable_le linear_order.decidable_eq linear_order.decidable_lt sorry

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered field. -/
protected instance linear_ordered_field {α : Type u} {β : Type v} {φ : ultrafilter α}
    [linear_ordered_field β] : linear_ordered_field (germ (↑φ) β) :=
  linear_ordered_field.mk linear_ordered_ring.add sorry linear_ordered_ring.zero sorry sorry
    linear_ordered_ring.neg linear_ordered_ring.sub sorry sorry linear_ordered_ring.mul sorry
    linear_ordered_ring.one sorry sorry sorry sorry linear_ordered_ring.le linear_ordered_ring.lt
    sorry sorry sorry sorry sorry sorry sorry linear_ordered_ring.decidable_le
    linear_ordered_ring.decidable_eq linear_ordered_ring.decidable_lt sorry sorry field.inv sorry
    sorry

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered commutative ring. -/
protected instance linear_ordered_comm_ring {α : Type u} {β : Type v} {φ : ultrafilter α}
    [linear_ordered_comm_ring β] : linear_ordered_comm_ring (germ (↑φ) β) :=
  linear_ordered_comm_ring.mk linear_ordered_ring.add sorry linear_ordered_ring.zero sorry sorry
    linear_ordered_ring.neg linear_ordered_ring.sub sorry sorry linear_ordered_ring.mul sorry
    linear_ordered_ring.one sorry sorry sorry sorry linear_ordered_ring.le linear_ordered_ring.lt
    sorry sorry sorry sorry sorry sorry sorry linear_ordered_ring.decidable_le
    linear_ordered_ring.decidable_eq linear_ordered_ring.decidable_lt sorry sorry

/-- If `φ` is an ultrafilter then the ultraproduct is a decidable linear ordered commutative
group. -/
protected instance linear_ordered_add_comm_group {α : Type u} {β : Type v} {φ : ultrafilter α}
    [linear_ordered_add_comm_group β] : linear_ordered_add_comm_group (germ (↑φ) β) :=
  linear_ordered_add_comm_group.mk ordered_add_comm_group.add sorry ordered_add_comm_group.zero
    sorry sorry ordered_add_comm_group.neg ordered_add_comm_group.sub sorry sorry
    ordered_add_comm_group.le ordered_add_comm_group.lt sorry sorry sorry sorry
    linear_order.decidable_le linear_order.decidable_eq linear_order.decidable_lt sorry

theorem max_def {α : Type u} {β : Type v} {φ : ultrafilter α} [linear_order β] (x : germ (↑φ) β)
    (y : germ (↑φ) β) : max x y = map₂ max x y :=
  sorry

theorem min_def {α : Type u} {β : Type v} {φ : ultrafilter α} [K : linear_order β] (x : germ (↑φ) β)
    (y : germ (↑φ) β) : min x y = map₂ min x y :=
  sorry

theorem abs_def {α : Type u} {β : Type v} {φ : ultrafilter α} [linear_ordered_add_comm_group β]
    (x : germ (↑φ) β) : abs x = map abs x :=
  sorry

@[simp] theorem const_max {α : Type u} {β : Type v} {φ : ultrafilter α} [linear_order β] (x : β)
    (y : β) : ↑(max x y) = max ↑x ↑y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(max x y) = max ↑x ↑y)) (max_def ↑x ↑y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(max x y) = map₂ max ↑x ↑y)) (map₂_const (↑φ) x y max)))
      (Eq.refl ↑(max x y)))

@[simp] theorem const_min {α : Type u} {β : Type v} {φ : ultrafilter α} [linear_order β] (x : β)
    (y : β) : ↑(min x y) = min ↑x ↑y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(min x y) = min ↑x ↑y)) (min_def ↑x ↑y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(min x y) = map₂ min ↑x ↑y)) (map₂_const (↑φ) x y min)))
      (Eq.refl ↑(min x y)))

@[simp] theorem const_abs {α : Type u} {β : Type v} {φ : ultrafilter α}
    [linear_ordered_add_comm_group β] (x : β) : ↑(abs x) = abs ↑x :=
  const_max x (-x)

end Mathlib