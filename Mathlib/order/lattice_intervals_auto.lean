/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.bounded_lattice
import Mathlib.data.set.intervals.basic
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Intervals in Lattices

In this file, we provide instances of lattice structures on intervals within lattices.
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances. These are probably not all of the lattice instances that could be placed on these
intervals, but more can be added easily along the same lines when needed.

## Main definitions
In the following, `*` can represent either `c`, `o`, or `i`.
  * `set.Ic*.semilattice_inf_bot`
  * `set.Ii*.semillatice_inf`
  * `set.I*c.semilattice_sup_top`
  * `set.I*c.semillatice_inf`
  * `set.Iic.bounded_lattice`, within a `bounded_lattice`
  * `set.Ici.bounded_lattice`, within a `bounded_lattice`

-/

namespace set


namespace Ico


protected instance semilattice_inf {α : Type u_1} {a : α} {b : α} [semilattice_inf α] :
    semilattice_inf ↥(Ico a b) :=
  subtype.semilattice_inf sorry

/-- `Ico a b` has a bottom element whenever `a < b`. -/
def order_bot {α : Type u_1} {a : α} {b : α} [partial_order α] (h : a < b) : order_bot ↥(Ico a b) :=
  order_bot.mk { val := a, property := sorry } partial_order.le partial_order.lt sorry sorry sorry
    sorry

/-- `Ico a b` is a `semilattice_inf_bot` whenever `a < b`. -/
def semilattice_inf_bot {α : Type u_1} {a : α} {b : α} [semilattice_inf α] (h : a < b) :
    semilattice_inf_bot ↥(Ico a b) :=
  semilattice_inf_bot.mk order_bot.bot semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

end Ico


namespace Iio


protected instance semilattice_inf {α : Type u_1} [semilattice_inf α] {a : α} :
    semilattice_inf ↥(Iio a) :=
  subtype.semilattice_inf sorry

end Iio


namespace Ioc


protected instance semilattice_sup {α : Type u_1} {a : α} {b : α} [semilattice_sup α] :
    semilattice_sup ↥(Ioc a b) :=
  subtype.semilattice_sup sorry

/-- `Ioc a b` has a top element whenever `a < b`. -/
def order_top {α : Type u_1} {a : α} {b : α} [partial_order α] (h : a < b) : order_top ↥(Ioc a b) :=
  order_top.mk { val := b, property := sorry } partial_order.le partial_order.lt sorry sorry sorry
    sorry

/-- `Ioc a b` is a `semilattice_sup_top` whenever `a < b`. -/
def semilattice_sup_top {α : Type u_1} {a : α} {b : α} [semilattice_sup α] (h : a < b) :
    semilattice_sup_top ↥(Ioc a b) :=
  semilattice_sup_top.mk order_top.top semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry
    semilattice_sup.sup sorry sorry sorry

end Ioc


namespace Iio


protected instance set.Ioi.semilattice_sup {α : Type u_1} [semilattice_sup α] {a : α} :
    semilattice_sup ↥(Ioi a) :=
  subtype.semilattice_sup sorry

end Iio


namespace Iic


protected instance semilattice_inf {α : Type u_1} {a : α} [semilattice_inf α] :
    semilattice_inf ↥(Iic a) :=
  subtype.semilattice_inf sorry

protected instance semilattice_sup {α : Type u_1} {a : α} [semilattice_sup α] :
    semilattice_sup ↥(Iic a) :=
  subtype.semilattice_sup sorry

protected instance lattice {α : Type u_1} {a : α} [lattice α] : lattice ↥(Iic a) :=
  lattice.mk semilattice_sup.sup semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry sorry
    sorry semilattice_inf.inf sorry sorry sorry

protected instance order_top {α : Type u_1} {a : α} [partial_order α] : order_top ↥(Iic a) :=
  order_top.mk { val := a, property := sorry } partial_order.le partial_order.lt sorry sorry sorry
    sorry

@[simp] theorem coe_top {α : Type u_1} [partial_order α] {a : α} : ↑⊤ = a := rfl

protected instance semilattice_inf_top {α : Type u_1} {a : α} [semilattice_inf α] :
    semilattice_inf_top ↥(Iic a) :=
  semilattice_inf_top.mk order_top.top semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

protected instance semilattice_sup_top {α : Type u_1} {a : α} [semilattice_sup α] :
    semilattice_sup_top ↥(Iic a) :=
  semilattice_sup_top.mk order_top.top semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry
    semilattice_sup.sup sorry sorry sorry

protected instance order_bot {α : Type u_1} {a : α} [order_bot α] : order_bot ↥(Iic a) :=
  order_bot.mk { val := ⊥, property := bot_le } partial_order.le partial_order.lt sorry sorry sorry
    sorry

@[simp] theorem coe_bot {α : Type u_1} [order_bot α] {a : α} : ↑⊥ = ⊥ := rfl

protected instance semilattice_inf_bot {α : Type u_1} {a : α} [semilattice_inf_bot α] :
    semilattice_inf_bot ↥(Iic a) :=
  semilattice_inf_bot.mk order_bot.bot semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

protected instance semilattice_sup_bot {α : Type u_1} {a : α} [semilattice_sup_bot α] :
    semilattice_sup_bot ↥(Iic a) :=
  semilattice_sup_bot.mk order_bot.bot semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry
    semilattice_sup.sup sorry sorry sorry

protected instance bounded_lattice {α : Type u_1} {a : α} [bounded_lattice α] :
    bounded_lattice ↥(Iic a) :=
  bounded_lattice.mk lattice.sup order_top.le order_top.lt sorry sorry sorry sorry sorry sorry
    lattice.inf sorry sorry sorry order_top.top sorry order_bot.bot sorry

end Iic


namespace Ici


protected instance semilattice_inf {α : Type u_1} {a : α} [semilattice_inf α] :
    semilattice_inf ↥(Ici a) :=
  subtype.semilattice_inf sorry

protected instance semilattice_sup {α : Type u_1} {a : α} [semilattice_sup α] :
    semilattice_sup ↥(Ici a) :=
  subtype.semilattice_sup sorry

protected instance lattice {α : Type u_1} {a : α} [lattice α] : lattice ↥(Ici a) :=
  lattice.mk semilattice_sup.sup semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry sorry
    sorry semilattice_inf.inf sorry sorry sorry

protected instance order_bot {α : Type u_1} {a : α} [partial_order α] : order_bot ↥(Ici a) :=
  order_bot.mk { val := a, property := sorry } partial_order.le partial_order.lt sorry sorry sorry
    sorry

@[simp] theorem coe_bot {α : Type u_1} [partial_order α] {a : α} : ↑⊥ = a := rfl

protected instance semilattice_inf_bot {α : Type u_1} {a : α} [semilattice_inf α] :
    semilattice_inf_bot ↥(Ici a) :=
  semilattice_inf_bot.mk order_bot.bot semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

protected instance semilattice_sup_bot {α : Type u_1} {a : α} [semilattice_sup α] :
    semilattice_sup_bot ↥(Ici a) :=
  semilattice_sup_bot.mk order_bot.bot semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry
    semilattice_sup.sup sorry sorry sorry

protected instance order_top {α : Type u_1} {a : α} [order_top α] : order_top ↥(Ici a) :=
  order_top.mk { val := ⊤, property := le_top } partial_order.le partial_order.lt sorry sorry sorry
    sorry

@[simp] theorem coe_top {α : Type u_1} [order_top α] {a : α} : ↑⊤ = ⊤ := rfl

protected instance semilattice_sup_top {α : Type u_1} {a : α} [semilattice_sup_top α] :
    semilattice_sup_top ↥(Ici a) :=
  semilattice_sup_top.mk order_top.top semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry
    semilattice_sup.sup sorry sorry sorry

protected instance semilattice_inf_top {α : Type u_1} {a : α} [semilattice_inf_top α] :
    semilattice_inf_top ↥(Ici a) :=
  semilattice_inf_top.mk order_top.top semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

protected instance bounded_lattice {α : Type u_1} {a : α} [bounded_lattice α] :
    bounded_lattice ↥(Ici a) :=
  bounded_lattice.mk lattice.sup order_top.le order_top.lt sorry sorry sorry sorry sorry sorry
    lattice.inf sorry sorry sorry order_top.top sorry order_bot.bot sorry

end Ici


namespace Icc


protected instance semilattice_inf {α : Type u_1} [semilattice_inf α] {a : α} {b : α} :
    semilattice_inf ↥(Icc a b) :=
  subtype.semilattice_inf sorry

protected instance semilattice_sup {α : Type u_1} [semilattice_sup α] {a : α} {b : α} :
    semilattice_sup ↥(Icc a b) :=
  subtype.semilattice_sup sorry

protected instance lattice {α : Type u_1} [lattice α] {a : α} {b : α} : lattice ↥(Icc a b) :=
  lattice.mk semilattice_sup.sup semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry sorry
    sorry semilattice_inf.inf sorry sorry sorry

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
def order_bot {α : Type u_1} [partial_order α] {a : α} {b : α} (h : a ≤ b) : order_bot ↥(Icc a b) :=
  order_bot.mk { val := a, property := sorry } partial_order.le partial_order.lt sorry sorry sorry
    sorry

/-- `Icc a b` has a top element whenever `a ≤ b`. -/
def order_top {α : Type u_1} [partial_order α] {a : α} {b : α} (h : a ≤ b) : order_top ↥(Icc a b) :=
  order_top.mk { val := b, property := sorry } partial_order.le partial_order.lt sorry sorry sorry
    sorry

/-- `Icc a b` is a `semilattice_inf_bot` whenever `a ≤ b`. -/
def semilattice_inf_bot {α : Type u_1} [semilattice_inf α] {a : α} {b : α} (h : a ≤ b) :
    semilattice_inf_bot ↥(Icc a b) :=
  semilattice_inf_bot.mk order_bot.bot order_bot.le order_bot.lt sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

/-- `Icc a b` is a `semilattice_inf_top` whenever `a ≤ b`. -/
def semilattice_inf_top {α : Type u_1} [semilattice_inf α] {a : α} {b : α} (h : a ≤ b) :
    semilattice_inf_top ↥(Icc a b) :=
  semilattice_inf_top.mk order_top.top order_top.le order_top.lt sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

/-- `Icc a b` is a `semilattice_sup_bot` whenever `a ≤ b`. -/
def semilattice_sup_bot {α : Type u_1} [semilattice_sup α] {a : α} {b : α} (h : a ≤ b) :
    semilattice_sup_bot ↥(Icc a b) :=
  semilattice_sup_bot.mk order_bot.bot order_bot.le order_bot.lt sorry sorry sorry sorry
    semilattice_sup.sup sorry sorry sorry

/-- `Icc a b` is a `semilattice_sup_top` whenever `a ≤ b`. -/
def semilattice_sup_top {α : Type u_1} [semilattice_sup α] {a : α} {b : α} (h : a ≤ b) :
    semilattice_sup_top ↥(Icc a b) :=
  semilattice_sup_top.mk order_top.top order_top.le order_top.lt sorry sorry sorry sorry
    semilattice_sup.sup sorry sorry sorry

/-- `Icc a b` is a `bounded_lattice` whenever `a ≤ b`. -/
def bounded_lattice {α : Type u_1} [lattice α] {a : α} {b : α} (h : a ≤ b) :
    bounded_lattice ↥(Icc a b) :=
  bounded_lattice.mk semilattice_sup_top.sup semilattice_inf_bot.le semilattice_inf_bot.lt sorry
    sorry sorry sorry sorry sorry semilattice_inf_bot.inf sorry sorry sorry semilattice_sup_top.top
    sorry semilattice_inf_bot.bot sorry

end Mathlib