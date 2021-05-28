/-
Copyright (c) 2019 Mathlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.num.basic
import Mathlib.PostPort

universes u l u_1 

namespace Mathlib

/-!
# Binary tree

Provides binary tree storage for values of any type, with O(lg n) retrieval.
See also `data.rbtree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

## References

<https://leanprover-community.github.io/archive/113488general/62193tacticquestion.html>
-/

/-- A binary tree with values stored in non-leaf nodes. -/
inductive tree (α : Type u) 
where
| nil : tree α
| node : α → tree α → tree α → tree α

namespace tree


/-- Construct a string representation of a tree. Provides a `has_repr` instance. -/
def repr {α : Type u} [has_repr α] : tree α → string :=
  sorry

protected instance has_repr {α : Type u} [has_repr α] : has_repr (tree α) :=
  has_repr.mk repr

protected instance inhabited {α : Type u} : Inhabited (tree α) :=
  { default := nil }

/-- Makes a `tree α` out of a red-black tree. -/
def of_rbnode {α : Type u} : rbnode α → tree α :=
  sorry

/-- Finds the index of an element in the tree assuming the tree has been
constructed according to the provided decidable order on its elements.
If it hasn't, the result will be incorrect. If it has, but the element
is not in the tree, returns none. -/
def index_of {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (x : α) : tree α → Option pos_num :=
  sorry

/-- Retrieves an element uniquely determined by a `pos_num` from the tree,
taking the following path to get to the element:
- `bit0` - go to left child
- `bit1` - go to right child
- `pos_num.one` - retrieve from here -/
def get {α : Type u} : pos_num → tree α → Option α :=
  sorry

/-- Retrieves an element from the tree, or the provided default value
if the index is invalid. See `tree.get`. -/
def get_or_else {α : Type u} (n : pos_num) (t : tree α) (v : α) : α :=
  option.get_or_else (get n t) v

/-- Apply a function to each value in the tree.  This is the `map` function for the `tree` functor.
TODO: implement `traversable tree`. -/
def map {α : Type u} {β : Type u_1} (f : α → β) : tree α → tree β :=
  sorry

