/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.hint
import Mathlib.PostPort

namespace Mathlib

namespace tactic


/--
  find all assumptions of the shape `¬ (p ∧ q)` or `¬ (p ∨ q)` and
  replace them using de Morgan's law.
-/
/-!
  The following definitions maintain a path compression datastructure, i.e. a forest such that:
    - every node is the type of a hypothesis
    - there is a edge between two nodes only if they are provably equivalent
    - every edge is labelled with a proof of equivalence for its vertices
    - edges are added when normalizing propositions.
-/

/--
  If there exists a symmetry lemma that can be applied to the hypothesis `e`,
  store it.
-/
/--
  Retrieve the root of the hypothesis `e` from the proof forest.
  If `e` has not been internalized, add it to the proof forest.
-/
/--
  Given hypotheses `a` and `b`, build a proof that `a` is equivalent to `b`,
  applying congruence and recursing into arguments if `a` and `b`
  are applications of function symbols.
-/
/--
  Configuration options for `tauto`.
  If `classical` is `tt`, runs `classical` before the rest of `tauto`.
  `closer` is run on any remaining subgoals left by `tauto_core; basic_tauto_tacs`.
-/
namespace interactive


/--
`tautology` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `reflexivity` or `solve_by_elim`.
This is a finishing tactic: it either closes the goal or raises an error.
The variant `tautology!` uses the law of excluded middle.

`tautology {closer := tac}` will use `tac` on any subgoals created by `tautology`
that it is unable to solve before failing.
-/
-- Now define a shorter name for the tactic `tautology`.

/--
`tauto` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `reflexivity` or `solve_by_elim`.
This is a finishing tactic: it either closes the goal or raises an error.
The variant `tauto!` uses the law of excluded middle.

`tauto {closer := tac}` will use `tac` on any subgoals created by `tauto`
that it is unable to solve before failing.
-/
/--
This tactic (with shorthand `tauto`) breaks down assumptions of the form
