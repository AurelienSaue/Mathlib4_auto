/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.rewrite_search.types
import Mathlib.tactic.converter.interactive
import Mathlib.PostPort

universes u l 

namespace Mathlib

/-!
# Tools to extract valid Lean code from a path found by rewrite search.
-/

namespace tactic.rewrite_search


/--
A `dir_pair` is a pair of items designed to be accessed according to
`dir`, a "direction" defined in the `expr_lens` library.
-/
structure dir_pair (α : Type u) 
where
  l : α
  r : α

namespace dir_pair


/-- Get one side of the pair, picking the side according to the direction. -/
def get {α : Type} (p : dir_pair α) : expr_lens.dir → α :=
  sorry

/-- Set one side of the pair, picking the side according to the direction. -/
def set {α : Type} (p : dir_pair α) : expr_lens.dir → α → dir_pair α :=
  sorry

/-- Convert the pair to a list of its elements. -/
def to_list {α : Type} (p : dir_pair α) : List α :=
  [l p, r p]

/-- Convert the pair to a readable string format. -/
def to_string {α : Type} [has_to_string α] (p : dir_pair α) : string :=
  to_string (l p) ++ string.str string.empty (char.of_nat (bit1 (bit0 (bit1 (bit1 (bit0 1)))))) ++ to_string (r p)

protected instance has_to_string {α : Type} [has_to_string α] : has_to_string (dir_pair α) :=
  has_to_string.mk to_string

end dir_pair


/-- Helper for getting the nth item in a list of rules -/
/-- Convert a rule into the string of Lean code used to refer to this rule. -/
/-- Explain a single rewrite using `nth_rewrite`. -/
/-- Explain a list of rewrites using `nth_rewrite`. -/
namespace using_conv


/-- `app_addr` represents a tree structure that `conv` tactics use for a rewrite. -/
def app_addr  :=
  _nest_1_1.tactic.rewrite_search.using_conv.app_addr

/--
A data structure for the result of a splice operation.
obstructed:  There was more of the addr to be added left, but we hit a rw
contained:   The added addr was already contained, and did not terminate at an existing rw
new:         The added addr terminated at an existing rw or we could create a new one for it
-/
inductive splice_result 
where
| obstructed : splice_result
| contained : splice_result
| new : app_addr → splice_result

