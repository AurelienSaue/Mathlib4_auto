/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.ordered_pi
import Mathlib.order.well_founded
import Mathlib.algebra.order_functions
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
  and each `β i` is ordered by `s`. -/
def pi.lex {ι : Type u_1} {β : ι → Type u_2} (r : ι → ι → Prop) (s : {i : ι} → β i → β i → Prop) (x : (i : ι) → β i) (y : (i : ι) → β i)  :=
  ∃ (i : ι), (∀ (j : ι), r j i → x j = y j) ∧ s (x i) (y i)

/-- The cartesian product of an indexed family, equipped with the lexicographic order. -/
def pilex (α : Type u_1) (β : α → Type u_2)  :=
  (a : α) → β a

protected instance pilex.has_lt {ι : Type u_1} {β : ι → Type u_2} [HasLess ι] [(a : ι) → HasLess (β a)] : HasLess (pilex ι β) :=
  { Less := pi.lex Less fun (_x : ι) => Less }

protected instance pilex.inhabited {ι : Type u_1} {β : ι → Type u_2} [(a : ι) → Inhabited (β a)] : Inhabited (pilex ι β) :=
  eq.mpr sorry (pi.inhabited ι)

protected instance pilex.partial_order {ι : Type u_1} {β : ι → Type u_2} [linear_order ι] [(a : ι) → partial_order (β a)] : partial_order (pilex ι β) :=
  (fun (lt_not_symm : ∀ {x y : pilex ι β}, ¬(x < y ∧ y < x)) =>
      partial_order.mk (fun (x y : pilex ι β) => x < y ∨ x = y) Less sorry sorry sorry)
    sorry

/-- `pilex` is a linear order if the original order is well-founded.
This cannot be an instance, since it depends on the well-foundedness of `<`. -/
protected def pilex.linear_order {ι : Type u_1} {β : ι → Type u_2} [linear_order ι] (wf : well_founded Less) [(a : ι) → linear_order (β a)] : linear_order (pilex ι β) :=
  linear_order.mk partial_order.le partial_order.lt sorry sorry sorry sorry (classical.dec_rel LessEq)
    Mathlib.decidable_eq_of_decidable_le Mathlib.decidable_lt_of_decidable_le

protected instance pilex.ordered_add_comm_group {ι : Type u_1} {β : ι → Type u_2} [linear_order ι] [(a : ι) → ordered_add_comm_group (β a)] : ordered_add_comm_group (pilex ι β) :=
  ordered_add_comm_group.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub
    sorry sorry partial_order.le partial_order.lt sorry sorry sorry sorry

