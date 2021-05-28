/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.buffer.basic
import Mathlib.meta.rb_map
import Mathlib.tactic.rewrite_search.discovery
import Mathlib.tactic.rewrite_search.types
import Mathlib.PostPort

namespace Mathlib

/-!
# The graph algorithm part of rewrite search

`search.lean` contains the logic to do a graph search. The search algorithm
starts with an equation to prove, treats the left hand side and right hand side as
two vertices in a graph, and uses rewrite rules to find a path that connects the two sides.
-/

namespace tactic.rewrite_search


/--
An edge represents a proof that can get from one expression to another.
It represents the fact that, starting from the vertex `fr`, the expression in `proof`
can prove the vertex `to`.
`how` contains information that the explainer will use to generate Lean code for the
proof.
-/
