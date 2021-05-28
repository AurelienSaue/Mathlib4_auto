/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.default
import Mathlib.data.finset.basic
import PostPort

universes u_1 l 

namespace Mathlib

/-!
# Constructions involving sets of sets.

## Finite Intersections

We define a structure `has_finite_inter` which asserts that a set `S` of subsets of `α` is
closed under finite intersections.

We define `finite_inter_closure` which, given a set `S` of subsets of `α`, is the smallest
set of subsets of `α` which is closed under finite intersections.

`finite_inter_closure S` is endowed with a term of type `has_finite_inter` using
`finite_inter_closure_has_finite_inter`.

-/

/-- A structure encapsulating the fact that a set of sets is closed under finite intersection. -/
structure has_finite_inter {α : Type u_1} (S : set (set α)) 
where
  univ_mem : set.univ ∈ S
  inter_mem : ∀ {s t : set α}, s ∈ S → t ∈ S → s ∩ t ∈ S

namespace has_finite_inter


-- Satisfying the inhabited linter...

protected instance inhabited {α : Type u_1} : Inhabited (has_finite_inter (singleton set.univ)) :=
  { default := mk sorry sorry }

/-- The smallest set of sets containing `S` which is closed under finite intersections. -/
inductive finite_inter_closure {α : Type u_1} (S : set (set α)) : set (set α)
where
| basic : ∀ {s : set α}, s ∈ S → finite_inter_closure S s
| univ : finite_inter_closure S set.univ
| inter : ∀ {s t : set α}, finite_inter_closure S s → finite_inter_closure S t → finite_inter_closure S (s ∩ t)

/-- Defines `has_finite_inter` for `finite_inter_closure S`. -/
def finite_inter_closure_has_finite_inter {α : Type u_1} (S : set (set α)) : has_finite_inter (finite_inter_closure S) :=
  mk finite_inter_closure.univ sorry

theorem finite_inter_mem {α : Type u_1} {S : set (set α)} (cond : has_finite_inter S) (F : finset (set α)) : ↑F ⊆ S → ⋂₀↑F ∈ S := sorry

theorem finite_inter_closure_insert {α : Type u_1} {S : set (set α)} {A : set α} (cond : has_finite_inter S) (P : set α) (H : P ∈ finite_inter_closure (insert A S)) : P ∈ S ∨ ∃ (Q : set α), ∃ (H : Q ∈ S), P = A ∩ Q := sorry

