/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.set_theory.pgame
import Mathlib.PostPort

universes u_1 u 

namespace Mathlib

/-!
# Combinatorial games.

In this file we define the quotient of pre-games by the equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤
p`, and construct an instance `add_comm_group game`, as well as an instance `partial_order game`
(although note carefully the warning that the `<` field in this instance is not the usual relation
on combinatorial games).
-/

protected instance pgame.setoid : setoid pgame :=
  setoid.mk (fun (x y : pgame) => pgame.equiv x y) sorry

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by the equivalence
  `x ≈ y ↔ x ≤ y ∧ y ≤ x`. -/
def game :=
  quotient pgame.setoid

namespace game


/-- The relation `x ≤ y` on games. -/
def le : game → game → Prop :=
  quotient.lift₂ (fun (x y : pgame) => x ≤ y) sorry

protected instance has_le : HasLessEq game :=
  { LessEq := le }

theorem le_refl (x : game) : x ≤ x :=
  quot.induction_on x fun (x : pgame) => pgame.le_refl x

theorem le_trans (x : game) (y : game) (z : game) : x ≤ y → y ≤ z → x ≤ z :=
  quot.induction_on x
    fun (x : pgame) => quot.induction_on y fun (y : pgame) => quot.induction_on z fun (z : pgame) => pgame.le_trans

theorem le_antisymm (x : game) (y : game) : x ≤ y → y ≤ x → x = y := sorry

/-- The relation `x < y` on games. -/
-- We don't yet make this into an instance, because it will conflict with the (incorrect) notion

-- of `<` provided by `partial_order` later.

def lt : game → game → Prop :=
  quotient.lift₂ (fun (x y : pgame) => x < y) sorry

theorem not_le {x : game} {y : game} : ¬x ≤ y ↔ lt y x :=
  quot.induction_on x fun (x : pgame) => quot.induction_on y fun (y : pgame) => pgame.not_le

protected instance has_zero : HasZero game :=
  { zero := quotient.mk 0 }

protected instance inhabited : Inhabited game :=
  { default := 0 }

protected instance has_one : HasOne game :=
  { one := quotient.mk 1 }

/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : game → game :=
  Quot.lift (fun (x : pgame) => quotient.mk (-x)) sorry

protected instance has_neg : Neg game :=
  { neg := neg }

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add : game → game → game :=
  quotient.lift₂ (fun (x y : pgame) => quotient.mk (x + y)) sorry

protected instance has_add : Add game :=
  { add := add }

theorem add_assoc (x : game) (y : game) (z : game) : x + y + z = x + (y + z) :=
  quot.induction_on x
    fun (x : pgame) =>
      quot.induction_on y fun (y : pgame) => quot.induction_on z fun (z : pgame) => quot.sound pgame.add_assoc_equiv

protected instance add_semigroup : add_semigroup game :=
  add_semigroup.mk Add.add add_assoc

theorem add_zero (x : game) : x + 0 = x :=
  quot.induction_on x fun (x : pgame) => quot.sound (pgame.add_zero_equiv x)

theorem zero_add (x : game) : 0 + x = x :=
  quot.induction_on x fun (x : pgame) => quot.sound (pgame.zero_add_equiv x)

protected instance add_monoid : add_monoid game :=
  add_monoid.mk add_semigroup.add add_semigroup.add_assoc 0 zero_add add_zero

theorem add_left_neg (x : game) : -x + x = 0 :=
  quot.induction_on x fun (x : pgame) => quot.sound pgame.add_left_neg_equiv

protected instance add_group : add_group game :=
  add_group.mk add_monoid.add add_monoid.add_assoc add_monoid.zero add_monoid.zero_add add_monoid.add_zero Neg.neg
    (sub_neg_monoid.sub._default add_monoid.add add_monoid.add_assoc add_monoid.zero add_monoid.zero_add
      add_monoid.add_zero Neg.neg)
    add_left_neg

theorem add_comm (x : game) (y : game) : x + y = y + x :=
  quot.induction_on x fun (x : pgame) => quot.induction_on y fun (y : pgame) => quot.sound pgame.add_comm_equiv

protected instance add_comm_semigroup : add_comm_semigroup game :=
  add_comm_semigroup.mk add_semigroup.add add_semigroup.add_assoc add_comm

protected instance add_comm_group : add_comm_group game :=
  add_comm_group.mk add_comm_semigroup.add add_comm_semigroup.add_assoc add_group.zero add_group.zero_add
    add_group.add_zero add_group.neg add_group.sub add_group.add_left_neg add_comm_semigroup.add_comm

theorem add_le_add_left (a : game) (b : game) : a ≤ b → ∀ (c : game), c + a ≤ c + b := sorry

-- While it is very tempting to define a `partial_order` on games, and prove

-- that games form an `ordered_add_comm_group`, it is a bit dangerous.

-- The relations `≤` and `<` on games do not satisfy

-- `lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a)`

-- (Consider `a = 0`, `b = star`.)

-- (`lt_iff_le_not_le` is satisfied by surreal numbers, however.)

-- Thus we can not use `<` when defining a `partial_order`.

-- Because of this issue, we define the `partial_order` and `ordered_add_comm_group` instances,

-- but do not actually mark them as instances, for safety.

/-- The `<` operation provided by this partial order is not the usual `<` on games! -/
def game_partial_order : partial_order game :=
  partial_order.mk LessEq (preorder.lt._default LessEq) le_refl le_trans le_antisymm

/-- The `<` operation provided by this `ordered_add_comm_group` is not the usual `<` on games! -/
def ordered_add_comm_group_game : ordered_add_comm_group game :=
  ordered_add_comm_group.mk add_comm_group.add add_comm_group.add_assoc add_comm_group.zero add_comm_group.zero_add
    add_comm_group.add_zero add_comm_group.neg add_comm_group.sub add_comm_group.add_left_neg add_comm_group.add_comm
    partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans partial_order.le_antisymm
    add_le_add_left

