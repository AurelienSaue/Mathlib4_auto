/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.nth_rewrite.default
import Mathlib.PostPort

universes l 

namespace Mathlib

/-!
# Types used in rewrite search.
-/

namespace tactic.rewrite_search


/--
`side` represents the side of an equation, either the left or the right.
-/
inductive side 
where
| L : side
| R : side

/-- Convert a side to a human-readable string. -/
/-- Convert a side to the string "lhs" or "rhs", for use in tactic name generation. -/
def side.to_xhs : side → string :=
  sorry

/--
A `how` contains information needed by the explainer to generate code for a rewrite.
`rule_index` denotes which rule in the static list of rules is used.
`location` describes which match of that rule was used, to work with `nth_rewrite`.
`addr` is a list of "left" and "right" describing which subexpression is rewritten.
-/
/-- Convert a `how` to a human-readable string. -/
/-- `rewrite` represents a single step of rewriting, that proves `exp` using `proof`. -/
/--
`proof_unit` represents a sequence of steps that can be applied to one side of the
equation to prove a particular expression.
-/
/--
Configuration options for a rewrite search.
`max_iterations` controls how many vertices are expanded in the graph search.
`explain` generates Lean code to replace the call to `rewrite_search`.
`explain_using_conv` changes the nature of the explanation.
-/
