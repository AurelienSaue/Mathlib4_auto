/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.equiv.list
import PostPort

universes u_1 u_2 l 

namespace Mathlib

/-!
# W types

Given `α : Type` and `β : α → Type`, the W type determined by this data, `W_type β`, is the
inductively defined type of trees where the nodes are labeled by elements of `α` and the children of
a node labeled `a` are indexed by elements of `β a`.

This file is currently a stub, awaiting a full development of the theory. Currently, the main result
is that if `α` is an encodable fintype and `β a` is encodable for every `a : α`, then `W_type β` is
encodable. This can be used to show the encodability of other inductive types, such as those that
are commonly used to formalize syntax, e.g. terms and expressions in a given language. The strategy
is illustrated in the example found in the file `prop_encodable` in the `archive/examples` folder of
mathlib.

## Implementation details

While the name `W_type` is somewhat verbose, it is preferable to putting a single character
identifier `W` in the root namespace.
-/

/--
Given `β : α → Type*`, `W_type β` is the type of finitely branching trees where nodes are labeled by
elements of `α` and the children of a node labeled `a` are indexed by elements of `β a`.
-/
inductive W_type {α : Type u_1} (β : α → Type u_2) 
where
| mk : (a : α) → (β a → W_type β) → W_type β

protected instance W_type.inhabited : Inhabited (W_type fun (_x : Unit) => empty) :=
  { default := W_type.mk Unit.unit empty.elim }

namespace W_type


/-- The depth of a finitely branching tree. -/
def depth {α : Type u_1} {β : α → Type u_2} [(a : α) → fintype (β a)] : W_type β → ℕ :=
  sorry

theorem depth_pos {α : Type u_1} {β : α → Type u_2} [(a : α) → fintype (β a)] (t : W_type β) : 0 < depth t :=
  W_type.cases_on t
    fun (t_a : α) (t_f : β t_a → W_type β) => nat.succ_pos (finset.sup finset.univ fun (n : β t_a) => depth (t_f n))

theorem depth_lt_depth_mk {α : Type u_1} {β : α → Type u_2} [(a : α) → fintype (β a)] (a : α) (f : β a → W_type β) (i : β a) : depth (f i) < depth (mk a f) :=
  nat.lt_succ_of_le (finset.le_sup (finset.mem_univ i))

end W_type


/-
Show that W types are encodable when `α` is an encodable fintype and for every `a : α`, `β a` is
encodable.

We define an auxiliary type `W_type' β n` of trees of depth at most `n`, and then we show by
induction on `n` that these are all encodable. These auxiliary constructions are not interesting in
and of themselves, so we mark them as `private`.
-/

namespace encodable


/-- `W_type` is encodable when `α` is an encodable fintype and for every `a : α`, `β a` is
encodable. -/
protected instance W_type.encodable {α : Type u_1} {β : α → Type u_2} [(a : α) → fintype (β a)] [(a : α) → encodable (β a)] [encodable α] : encodable (W_type β) :=
  let f : W_type β → sigma fun (n : ℕ) => W_type' β n :=
    fun (t : W_type β) => sigma.mk (W_type.depth t) { val := t, property := sorry };
  let finv : (sigma fun (n : ℕ) => W_type' β n) → W_type β :=
    fun (p : sigma fun (n : ℕ) => W_type' β n) => subtype.val (sigma.snd p);
  of_left_inverse f finv sorry

