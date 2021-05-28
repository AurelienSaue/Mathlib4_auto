/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bryan Gin-ge Chen, Robert Y. Lewis, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.doc_commands
import PostPort

namespace Mathlib

/-!

# Core tactic documentation

This file adds the majority of the interactive tactics from core Lean (i.e. pre-mathlib) to
the API documentation.

## TODO

* Make a PR to core changing core docstrings to the docstrings below,
and also changing the docstrings of `cc`, `simp` and `conv` to the ones
already in the API docs.

* SMT tactics are currently not documented.

* `rsimp` and `constructor_matching` are currently not documented.

* `dsimp` deserves better documentation.
-/

/-- Proves a goal of the form `s = t` when `s` and `t` are expressions built up out of a binary
operation, and equality can be proved using associativity and commutativity of that operation. -/
/--
`by_cases p` splits the main goal into two cases, assuming `h : p` in the first branch, and
`h : ¬ p` in the second branch. You can specify the name of the new hypothesis using the syntax
`by_cases h : p`.

If `p` is not already decidable, `by_cases` will use the instance `classical.prop_decidable p`.
-/
/--
If the target of the main goal is a proposition `p`, `by_contra h` reduces the goal to proving
`false` using the additional hypothesis `h : ¬ p`. If `h` is omitted, a name is generated
automatically.

This tactic requires that `p` is decidable. To ensure that all propositions are decidable via
classical reasoning, use `open_locale classical`
(or `local attribute [instance, priority 10] classical.prop_decidable` if you are not using
mathlib).
-/
/--
`cases_matching p` applies the `cases` tactic to a hypothesis `h : type`
if `type` matches the pattern `p`.

`cases_matching [p_1, ..., p_n]` applies the `cases` tactic to a hypothesis `h : type`
if `type` matches one of the given patterns.

`cases_matching* p` is a more efficient and compact version
of `focus1 { repeat { cases_matching p } }`.
It is more efficient because the pattern is compiled once.

`casesm` is shorthand for `cases_matching`.

Example: The following tactic destructs all conjunctions and disjunctions in the current context.
```
cases_matching* [_ ∨ _, _ ∧ _]
```
-/
/--
* `cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`
* `cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis
  `h : (I_1 ...)` or ... or `h : (I_n ...)`
* `cases_type* I` is shorthand for `focus1 { repeat { cases_type I } }`
* `cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.

Example: The following tactic destructs all conjunctions and disjunctions in the current context.
```
cases_type* or and
```
-/
/--
Close goals of the form `n ≠ m` when `n` and `m` have type `nat`, `char`, `string`, `int`
or `fin sz`, and they are literals. It also closes goals of the form `n < m`, `n > m`, `n ≤ m` and
`n ≥ m` for `nat`. If the goal is of the form `n = m`, then it tries to close it using reflexivity.

In mathlib, consider using `norm_num` instead for numeric types.
-/
/--
The `congr` tactic attempts to identify both sides of an equality goal `A = B`,
leaving as new goals the subterms of `A` and `B` which are not definitionally equal.
Example: suppose the goal is `x * f y = g w * f z`. Then `congr` will produce two goals:
`x = g w` and `y = z`.

If `x y : t`, and an instance `subsingleton t` is in scope, then any goals of the form
`x = y` are solved automatically.

Note that `congr` can be over-aggressive at times; the `congr'` tactic in mathlib
provides a more refined approach, by taking a parameter that limits the recursion depth.
-/
/--
A variant of `rw` that uses the unifier more aggressively, unfolding semireducible definitions.
-/
/--
`existsi e` will instantiate an existential quantifier in the target with `e` and leave the
instantiated body as the new target. More generally, it applies to any inductive type with one
constructor and at least two arguments, applying the constructor with `e` as the first argument
and leaving the remaining arguments as goals.

`existsi [e₁, ..., eₙ]` iteratively does the same for each expression in the list.

Note: in mathlib, the `use` tactic is an equivalent tactic which sometimes is smarter with
unification.
-/
/--
Apply function extensionality and introduce new hypotheses.
The tactic `funext` will keep applying new the `funext` lemma until the goal target is not reducible
to
```
  |-  ((fun x, ...) = (fun x, ...))
```
The variant `funext h₁ ... hₙ` applies `funext` `n` times, and uses the given identifiers to name
the new hypotheses.

Note also the mathlib tactic `ext`, which applies as many extensionality lemmas as possible.
-/
/--
If the current goal is a Pi/forall `∀ x : t, u` (resp. `let x := t in u`) then `intro` puts
`x : t` (resp. `x := t`) in the local context. The new subgoal target is `u`.

If the goal is an arrow `t → u`, then it puts `h : t` in the local context and the new goal
target is `u`.

If the goal is neither a Pi/forall nor begins with a let binder, the tactic `intro` applies the
tactic `whnf` until an introduction can be applied or the goal is not head reducible. In the latter
case, the tactic fails.

The variant `intro z` uses the identifier `z` to name the new hypothesis.

The variant `intros` will keep introducing new hypotheses until the goal target is not a Pi/forall
or let binder.

The variant `intros h₁ ... hₙ` introduces `n` new hypotheses using the given identifiers to name
them.
-/
/--
`left` applies the first constructor when the type of the target is an inductive data type with
two constructors.

Similarly, `right` applies the second constructor.
-/
/--
`let h : t := p` adds the hypothesis `h : t := p` to the current goal if `p` a term of type `t`.
If `t` is omitted, it will be inferred.

`let h : t` adds the hypothesis `h : t := ?M` to the current goal and opens a new subgoal `?M : t`.
The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh
metavariable.

If `h` is omitted, the name `this` is used.

Note the related mathlib tactic `set a := t with h`, which adds the hypothesis `h : a = t` to
the local context and replaces `t` with `a` everywhere it can.
-/
/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a reflexive relation,
that is, a relation which has a reflexivity lemma tagged with the attribute `[refl]`.
The tactic checks whether `t` and `u` are definitionally equal and then solves the goal.
-/
/--
`rw e` applies an equation or iff `e` as a rewrite rule to the main goal. If `e` is preceded by
left arrow (`←` or `<-`), the rewrite is applied in the reverse direction. If `e` is a defined
constant, then the equational lemmas associated with `e` are used. This provides a convenient
way to unfold `e`.

`rw [e₁, ..., eₙ]` applies the given rules sequentially.

`rw e at l` rewrites `e` at location(s) `l`, where `l` is either `*` or a list of hypotheses
in the local context. In the latter case, a turnstile `⊢` or `|-` can also be used, to signify
the target of the goal.

`rewrite` is synonymous with `rw`.
-/
/- conv mode tactics -/

/--
Navigate to the left-hand-side of a relation.
A goal of `| a = b` will turn into the the goal `| a`.
-/
/--
Navigate to the right-hand-side of a relation.
A goal of `| a = b` will turn into the the goal `| b`.
-/
/--
Navigate into every argument of the current head function.
A target of `| (a * b) * c` will turn into the two targets `| a * b` and `| c`.
-/
/--
Navigate into the contents of top-level `λ` binders.
A target of `| λ a, a + b` will turn into the target `| a + b` and introduce `a` into the local
context.
If there are multiple binders, all of them will be entered, and if there are none, this tactic is a no-op.
-/
/--
Navigate into the first scope matching the expression.

For a target of `| ∀ c, a + (b + c) = 1`, `find (b + _) { ... }` will run the tactics within the
`{}` with a target of `| b + c`.
-/
/--
Navigate into the numbered scopes matching the expression.

For a target of `| λ c, 10 * c + 20 * c + 30 * c`, `for (_ * _) [1, 3] { ... }` will run the
tactics within the `{}` with first a target of `| 10 * c`, then a target of `| 30 * c`.
-/
/--
End conversion of the current goal. This is often what is needed when muscle memory would type `sorry`.
