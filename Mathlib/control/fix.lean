/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.upto
import Mathlib.data.stream.basic
import Mathlib.data.pfun
import Mathlib.PostPort

universes u_3 l u_1 u_2 

namespace Mathlib

/-!
# Fixed point

This module defines a generic `fix` operator for defining recursive
computations that are not necessarily well-founded or productive.
An instance is defined for `roption`.

## Main definition

 * class `has_fix`
 * `roption.fix`
-/

/-- `has_fix α` gives us a way to calculate the fixed point
of function of type `α → α`. -/
class has_fix (α : Type u_3) 
where
  fix : (α → α) → α

namespace roption


/-- A series of successive, finite approximation of the fixed point of `f`, defined by
`approx f n = f^[n] ⊥`. The limit of this chain is the fixed point of `f`. -/
def fix.approx {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) → (a : α) → roption (β a)) : stream ((a : α) → roption (β a)) :=
  sorry

/-- loop body for finding the fixed point of `f` -/
def fix_aux {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) → (a : α) → roption (β a)) {p : ℕ → Prop} (i : nat.upto p) (g : (j : nat.upto p) → i < j → (a : α) → roption (β a)) (a : α) : roption (β a) :=
  f fun (x : α) => assert (¬p (subtype.val i)) fun (h : ¬p (subtype.val i)) => g (nat.upto.succ i h) sorry x

/-- The least fixed point of `f`.

If `f` is a continuous function (according to complete partial orders),
it satisfies the equations:

  1. `fix f = f (fix f)`          (is a fixed point)
  2. `∀ X, f X ≤ X → fix f ≤ X`   (least fixed point)
-/
protected def fix {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) → (a : α) → roption (β a)) (x : α) : roption (β x) :=
  assert (∃ (i : ℕ), dom sorry) fun (h : ∃ (i : ℕ), dom sorry) => well_founded.fix sorry (fix_aux f) nat.upto.zero x

protected theorem fix_def {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) → (a : α) → roption (β a)) {x : α} (h' : ∃ (i : ℕ), dom (fix.approx f i x)) : roption.fix f x = fix.approx f (Nat.succ (nat.find h')) x := sorry

theorem fix_def' {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) → (a : α) → roption (β a)) {x : α} (h' : ¬∃ (i : ℕ), dom (fix.approx f i x)) : roption.fix f x = none := sorry

end roption


namespace roption


protected instance has_fix {α : Type u_1} : has_fix (roption α) :=
  has_fix.mk fun (f : roption α → roption α) => roption.fix (fun (x : Unit → roption α) (u : Unit) => f (x u)) Unit.unit

end roption


namespace pi


protected instance roption.has_fix {α : Type u_1} {β : Type u_2} : has_fix (α → roption β) :=
  has_fix.mk roption.fix

