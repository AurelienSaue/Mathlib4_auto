/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Jesse Michael Han
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.hint
import Mathlib.PostPort

universes l u 

namespace Mathlib

/-!
# The `finish` family of tactics

These tactics do straightforward things: they call the simplifier, split conjunctive assumptions,
eliminate existential quantifiers on the left, and look for contradictions. They rely on ematching
and congruence closure to try to finish off a goal at the end.

The procedures *do* split on disjunctions and recreate the smt state for each terminal call, so
they are only meant to be used on small, straightforward problems.

## Main definitions

We provide the following tactics:

* `finish`  -- solves the goal or fails
* `clarify` -- makes as much progress as possible while not leaving more than one goal
* `safe`    -- splits freely, finishes off whatever subgoals it can, and leaves the rest

All accept an optional list of simplifier rules, typically definitions that should be expanded.
(The equations and identities should not refer to the local context.)

-/

namespace tactic


namespace interactive


end interactive


end tactic


namespace auto


/-! ### Utilities -/

-- stolen from interactive.lean

/--
Configuration information for the auto tactics.
* `(use_simp := tt)`: call the simplifier
* `(max_ematch_rounds := 20)`: for the "done" tactic
-/
structure auto_config where
  use_simp : Bool
  max_ematch_rounds : ℕ

/-!
### Preprocess goal.

We want to move everything to the left of the sequent arrow. For intuitionistic logic,
we replace the goal `p` with `∀ f, (p → f) → f` and introduce.
-/

theorem by_contradiction_trick (p : Prop) (h : ∀ (f : Prop), (p → f) → f) : p := h p id

/-!
### Normalize hypotheses

Bring conjunctions to the outside (for splitting),
bring universal quantifiers to the outside (for ematching). The classical normalizer
eliminates `a → b` in favor of `¬ a ∨ b`.

For efficiency, we push negations inwards from the top down. (For example, consider
simplifying `¬ ¬ (p ∨ q)`.)
-/

theorem not_not_eq (p : Prop) : (¬¬p) = p := propext not_not

theorem not_and_eq (p : Prop) (q : Prop) : (¬(p ∧ q)) = (¬p ∨ ¬q) := propext not_and_distrib

theorem not_or_eq (p : Prop) (q : Prop) : (¬(p ∨ q)) = (¬p ∧ ¬q) := propext not_or_distrib

theorem not_forall_eq {α : Type u} (s : α → Prop) : (¬∀ (x : α), s x) = ∃ (x : α), ¬s x :=
  propext not_forall

theorem not_exists_eq {α : Type u} (s : α → Prop) : (¬∃ (x : α), s x) = ∀ (x : α), ¬s x :=
  propext not_exists

theorem not_implies_eq (p : Prop) (q : Prop) : (¬(p → q)) = (p ∧ ¬q) := propext not_imp

theorem classical.implies_iff_not_or (p : Prop) (q : Prop) : p → q ↔ ¬p ∨ q := imp_iff_not_or

def common_normalize_lemma_names : List name := sorry

def classical_normalize_lemma_names : List name := sorry

/-- optionally returns an equivalent expression and proof of equivalence -/
/-- given an expr `e`, returns a new expression and a proof of equality -/
/-!
### Eliminate existential quantifiers
-/

/-- eliminate an existential quantifier if there is one -/
/-- eliminate all existential quantifiers, fails if there aren't any -/
/-!
### Substitute if there is a hypothesis `x = t` or `t = x`
-/

/-- carries out a subst if there is one, fails otherwise -/
/-!
### Split all conjunctions
-/

/-- Assumes `pr` is a proof of `t`. Adds the consequences of `t` to the context
 and returns `tt` if anything nontrivial has been added. -/
/-- return `tt` if any progress is made -/
/-- return `tt` if any progress is made -/
/-- fail if no progress is made -/
/-!
### Eagerly apply all the preprocessing rules
-/

/-- Eagerly apply all the preprocessing rules -/
/-!
### Terminal tactic
-/

/--
The terminal tactic, used to try to finish off goals:
- Call the contradiction tactic.
- Open an SMT state, and use ematching and congruence closure, with all the universal
  statements in the context.

TODO(Jeremy): allow users to specify attribute for ematching lemmas?
-/
/--
`done` first attempts to close the goal using `contradiction`. If this fails, it creates an
SMT state and will repeatedly use `ematch` (using `ematch` lemmas in the environment,
universally quantified assumptions, and the supplied lemmas `ps`) and congruence closure.
-/
/-!
### Tactics that perform case splits
-/

inductive case_option where
| force : case_option
| at_most_one : case_option
| accept : case_option

-- three possible outcomes:

--   finds something to case, the continuations succeed ==> returns tt

--   finds something to case, the continutations fail ==> fails

--   doesn't find anything to case ==> returns ff

/-!
### The main tactics
-/

/--
`safe_core s ps cfg opt` negates the goal, normalizes hypotheses
(by splitting conjunctions, eliminating existentials, pushing negations inwards,
and calling `simp` with the supplied lemmas `s`), and then tries `contradiction`.

If this fails, it will create an SMT state and repeatedly use `ematch`
(using `ematch` lemmas in the environment, universally quantified assumptions,
and the supplied lemmas `ps`) and congruence closure.

`safe_core` is complete for propositional logic. Depending on the form of `opt`
it will:

- (if `opt` is `case_option.force`) fail if it does not close the goal,
- (if `opt` is `case_option.at_most_one`) fail if it produces more than one goal, and
- (if `opt` is `case_option.accept`) ignore the number of goals it produces.
-/
/--
`clarify` is `safe_core`, but with the `(opt : case_option)`
parameter fixed at `case_option.at_most_one`.
-/
/--
`safe` is `safe_core`, but with the `(opt : case_option)`
parameter fixed at `case_option.accept`.
-/
/--
`finish` is `safe_core`, but with the `(opt : case_option)`
parameter fixed at `case_option.force`.
-/
end auto


/-! ### interactive versions -/

namespace tactic


namespace interactive


/--
`clarify [h1,...,hn] using [e1,...,en]` negates the goal, normalizes hypotheses
(by splitting conjunctions, eliminating existentials, pushing negations inwards,
and calling `simp` with the supplied lemmas `h1,...,hn`), and then tries `contradiction`.

If this fails, it will create an SMT state and repeatedly use `ematch`
(using `ematch` lemmas in the environment, universally quantified assumptions,
and the supplied lemmas `e1,...,en`) and congruence closure.

`clarify` is complete for propositional logic.

Either of the supplied simp lemmas or the supplied ematch lemmas are optional.

`clarify` will fail if it produces more than one goal.
-/
/--
`safe [h1,...,hn] using [e1,...,en]` negates the goal, normalizes hypotheses
(by splitting conjunctions, eliminating existentials, pushing negations inwards,
and calling `simp` with the supplied lemmas `h1,...,hn`), and then tries `contradiction`.

If this fails, it will create an SMT state and repeatedly use `ematch`
(using `ematch` lemmas in the environment, universally quantified assumptions,
and the supplied lemmas `e1,...,en`) and congruence closure.

`safe` is complete for propositional logic.

Either of the supplied simp lemmas or the supplied ematch lemmas are optional.

`safe` ignores the number of goals it produces, and should never fail.
-/
/--
`finish [h1,...,hn] using [e1,...,en]` negates the goal, normalizes hypotheses
(by splitting conjunctions, eliminating existentials, pushing negations inwards,
and calling `simp` with the supplied lemmas `h1,...,hn`), and then tries `contradiction`.

If this fails, it will create an SMT state and repeatedly use `ematch`
(using `ematch` lemmas in the environment, universally quantified assumptions,
and the supplied lemmas `e1,...,en`) and congruence closure.

`finish` is complete for propositional logic.

Either of the supplied simp lemmas or the supplied ematch lemmas are optional.

`finish` will fail if it does not close the goal.
-/
/--
These tactics do straightforward things: they call the simplifier, split conjunctive assumptions,
end Mathlib