/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.Lean3Lib.data.dlist
import Mathlib.tactic.core
import Mathlib.tactic.clear
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!

# Recursive cases (`rcases`) tactic and related tactics

`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* An alteration pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

The patterns are fairly liberal about the exact shape of the constructors, and will insert
additional alternation branches and tuple arguments if there are not enough arguments provided, and
reuse the tail for further matches if there are too many arguments provided to alternation and
tuple patterns.

This file also contains the `obtain` and `rintro` tactics, which use the same syntax of `rcases`
patterns but with a slightly different use case:

* `rintro` (or `rintros`) is used like `rintro x ⟨y, z⟩` and is the same as `intros` followed by
  `rcases` on the newly introduced arguments.
* `obtain` is the same as `rcases` but with a syntax styled after `have` rather than `cases`.
  `obtain ⟨hx, hy⟩ | hz := foo` is equivalent to `rcases foo with ⟨hx, hy⟩ | hz`. Unlike `rcases`,
  `obtain` also allows one to omit `:= foo`, although a type must be provided in this case,
  as in `obtain ⟨hx, hy⟩ | hz : a ∧ b ∨ c`, in which case it produces a subgoal for proving
  `a ∧ b ∨ c` in addition to the subgoals `hx : a, hy : b |- goal` and `hz : c |- goal`.

## Tags

rcases, rintro, obtain, destructuring, cases, pattern matching, match
-/

namespace tactic


/-!
These synonyms for `list` are used to clarify the meanings of the many
usages of lists in this module.

- `listΣ` is used where a list represents a disjunction, such as the
  list of possible constructors of an inductive type.

- `listΠ` is used where a list represents a conjunction, such as the
  list of arguments of an individual constructor.

These are merely type synonyms, and so are not checked for consistency
by the compiler.

The `def`/`local notation` combination makes Lean retain these
annotations in reported types.
-/

/-- A list, with a disjunctive meaning (like a list of inductive constructors, or subgoals) -/
def list_Sigma (T : Type u_1) :=
  List

/-- A list, with a conjunctive meaning (like a list of constructor arguments, or hypotheses) -/
def list_Pi (T : Type u_1) :=
  List

/-- A metavariable representing a subgoal, together with a list of local constants to clear. -/
/--
An `rcases` pattern can be one of the following, in a nested combination:

* A name like `foo`
* The special keyword `rfl` (for pattern matching on equality using `subst`)
* A hyphen `-`, which clears the active hypothesis and any dependents.
* A type ascription like `pat : ty` (parentheses are optional)
* A tuple constructor like `⟨p1, p2, p3⟩`
* An alternation / variant pattern `p1 | p2 | p3`

Parentheses can be used for grouping; alternation is higher precedence than type ascription, so
`p1 | p2 | p3 : ty` means `(p1 | p2 | p3) : ty`.

N-ary alternations are treated as a group, so `p1 | p2 | p3` is not the same as `p1 | (p2 | p3)`,
and similarly for tuples. However, note that an n-ary alternation or tuple can match an n-ary
conjunction or disjunction, because if the number of patterns exceeds the number of constructors in
the type being destructed, the extra patterns will match on the last element, meaning that
`p1 | p2 | p3` will act like `p1 | (p2 | p3)` when matching `a1 ∨ a2 ∨ a3`. If matching against a
type with 3 constructors,  `p1 | (p2 | p3)` will act like `p1 | (p2 | p3) | _` instead.
-/
namespace rcases_patt


/-- Get the name from a pattern, if provided -/
/-- Interpret an rcases pattern as a tuple, where `p` becomes `⟨p⟩`
if `p` is not already a tuple. -/
/-- Interpret an rcases pattern as an alternation, where non-alternations are treated as one
alternative. -/
/-- Convert a list of patterns to a tuple pattern, but mapping `[p]` to `p` instead of `⟨p⟩`. -/
/-- Convert a list of patterns to an alternation pattern, but mapping `[p]` to `p` instead of
a unary alternation `|p`. -/
/-- This function is used for producing rcases patterns based on a case tree. Suppose that we have
a list of patterns `ps` that will match correctly against the branches of the case tree for one
constructor. This function will merge tuples at the end of the list, so that `[a, b, ⟨c, d⟩]`
becomes `⟨a, b, c, d⟩` instead of `⟨a, b, ⟨c, d⟩⟩`.

We must be careful to turn `[a, ⟨⟩]` into `⟨a, ⟨⟩⟩` instead of `⟨a⟩` (which will not perform the
nested match). -/
/-- This function is used for producing rcases patterns based on a case tree. This is like
`tuple₁_core` but it produces a pattern instead of a tuple pattern list, converting `[n]` to `n`
instead of `⟨n⟩` and `[]` to `_`, and otherwise just converting `[a, b, c]` to `⟨a, b, c⟩`. -/
/-- This function is used for producing rcases patterns based on a case tree. Here we are given
the list of patterns to apply to each argument of each constructor after the main case, and must
produce a list of alternatives with the same effect. This function calls `tuple₁` to make the
individual alternatives, and handles merging `[a, b, c | d]` to `a | b | c | d` instead of
`a | b | (c | d)`. -/
/-- This function is used for producing rcases patterns based on a case tree. This is like
`alts₁_core`, but it produces a cases pattern directly instead of a list of alternatives. We
specially translate the empty alternation to `⟨⟩`, and translate `|(a | b)` to `⟨a | b⟩` (because we
don't have any syntax for unary alternation). Otherwise we can use the regular merging of
alternations at the last argument so that `a | b | (c | d)` becomes `a | b | c | d`. -/
/-- Formats an `rcases` pattern. If the `bracket` argument is true, then it will be
printed at high precedence, i.e. it will have parentheses around it if it is not already a tuple
or atomic name. -/
end rcases_patt


/-- Takes the number of fields of a single constructor and patterns to match its fields against
(not necessarily the same number). The returned lists each contain one element per field of the
constructor. The `name` is the name which will be used in the top-level `cases` tactic, and the
`rcases_patt` is the pattern which the field will be matched against by subsequent `cases`
tactics. -/
-- The interesting case: we matched the last field against multiple

-- patterns, so split off the remaining patterns into a subsequent

-- match. This handles matching `α × β × γ` against `⟨a, b, c⟩`.

/-- Takes a list of constructor names, and an (alternation) list of patterns, and matches each
pattern against its constructor. It returns the list of names that will be passed to `cases`,
and the list of `(constructor name, patterns)` for each constructor, where `patterns` is the
(conjunctive) list of patterns to apply to each constructor argument. -/
/-- Like `zip`, but only elements satisfying a matching predicate `p` will go in the list,
and elements of the first list that fail to match the second list will be skipped. -/
/-- Given a local constant `e`, get its type. *But* if `e` does not exist, go find a hypothesis
with the same pretty name as `e` and get it instead. This is needed because we can sometimes lose
track of the unique names of hypotheses when they are revert/intro'd by `change` and `cases`. (A
better solution would be for these tactics to return a map of renamed hypotheses so that we don't
lose track of them.) -/
/--
* `rcases_core p e` will match a pattern `p` against a local hypothesis `e`.
  It returns the list of subgoals that were produced.
* `rcases.continue pes` will match a (conjunctive) list of `(p, e)` pairs which refer to
  patterns and local hypotheses to match against, and applies all of them. Note that this can
  involve matching later arguments multiple times given earlier arguments, for example
  `⟨a | b, ⟨c, d⟩⟩` performs the `⟨c, d⟩` match twice, once on the `a` branch and once on `b`.
-/
-- If the pattern is any other name, we already bound the name in the

-- top-level `cases` tactic, so there is no more work to do for it.

/-- Given a list of `uncleared_goal`s, each of which is a goal metavariable and
a list of variables to clear, actually perform the clear and set the goals with the result. -/
/-- `rcases h e pat` performs case distinction on `e` using `pat` to
name the arising new variables and assumptions. If `h` is `some` name,
a new assumption `h : e = pat` will relate the expression `e` with the
current pattern. See the module comment for the syntax of `pat`. -/
/-- `rcases_many es pats` performs case distinction on the `es` using `pat` to
name the arising new variables and assumptions.
See the module comment for the syntax of `pat`. -/
/-- `rintro pat₁ pat₂ ... patₙ` introduces `n` arguments, then pattern matches on the `patᵢ` using
the same syntax as `rcases`. -/
/-- Like `zip_with`, but if the lists don't match in length, the excess elements will be put at the
end of the result. -/
def merge_list {α : Type u_1} (m : α → α → α) : List α → List α → List α :=
  sorry

/-- Merge two `rcases` patterns. This is used to underapproximate a case tree by an `rcases`
pattern. The two patterns come from cases in two branches, that due to the syntax of `rcases`
patterns are forced to overlap. The rule here is that we take only the case splits that are in
common between both branches. For example if one branch does `⟨a, b⟩` and the other does `c`,
then we return `c` because we don't know that a case on `c` would be safe to do. -/
/--
* `rcases_hint_core depth e` does the same as `rcases p e`, except the pattern `p` is an output
  instead of an input, controlled only by the case depth argument `depth`. We use `cases` to depth
  `depth` and then reconstruct an `rcases` pattern `p` that would, if passed to `rcases`, perform
  the same thing as the case tree we just constructed (or at least, the nearest expressible
  approximation to this.)
* `rcases_hint.process_constructors depth cs l` takes a list of constructor names `cs` and a
  matching list `l` of elements `(g, c', hs, _)` where  `c'` is a constructor name (used for
  alignment with `cs`), `g` is the subgoal, and `hs` is the list of local hypotheses created by
  `cases` in that subgoal. It matches on all of them, and then produces a `ΣΠ`-list of `rcases`
  patterns describing the result, and the list of generated subgoals.
* `rcases_hint.continue depth es` does the same as `rcases.continue (ps.zip es)`, except the
  patterns `ps` are an output instead of an input, created by matching on everything to depth
  `depth` and recording the successful cases. It returns `ps`, and the list of generated subgoals.
-/
/--
* `rcases? e` is like `rcases e with ...`, except it generates `...` by matching on everything it
can, and it outputs an `rcases` invocation that should have the same effect.
* `rcases? e : n` can be used to control the depth of case splits (especially important for
recursive types like `nat`, which can be cased as many times as you like). -/
/--
* `rcases? ⟨e1, e2, e3⟩` is like `rcases ⟨e1, e2, e3⟩ with ...`, except it
  generates `...` by matching on everything it can, and it outputs an `rcases`
  invocation that should have the same effect.
* `rcases? ⟨e1, e2, e3⟩ : n` can be used to control the depth of case splits
  (especially important for recursive types like `nat`, which can be cased as many
  times as you like). -/
/--
* `rintro?` is like `rintro ...`, except it generates `...` by introducing and matching on
everything it can, and it outputs an `rintro` invocation that should have the same effect.
* `rintro? : n` can be used to control the depth of case splits (especially important for
recursive types like `nat`, which can be cased as many times as you like). -/
/--
* `rcases_patt_parse tt` will parse a high precedence `rcases` pattern, `patt_hi`.
  This means only tuples and identifiers are allowed; alternations and type ascriptions
  require `(...)` instead, which switches to `patt`.
* `rcases_patt_parse ff` will parse a low precedence `rcases` pattern, `patt`. This consists of a
  `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
  expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
  example in `rcases e with x : ty <|> skip`.
* `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
  patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
  `(a | b) : ty` where `a | b` is the `patt_med` part.
* `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.

```lean
patt ::= patt_med (":" expr)?
patt_med ::= (patt_hi "|")* patt_hi
patt_hi ::= id | "rfl" | "_" | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
```
-/
/-- Parse the optional depth argument `(: n)?` of `rcases?` and `rintro?`, with default depth 5. -/
/-- The arguments to `rcases`, which in fact dispatch to several other tactics.
* `rcases? expr (: n)?` or `rcases? ⟨expr, ...⟩ (: n)?` calls `rcases_hint`
* `rcases? ⟨expr, ...⟩ (: n)?` calls `rcases_hint_many`
* `rcases (h :)? expr (with patt)?` calls `rcases`
* `rcases ⟨expr, ...⟩ (with patt)?` calls `rcases_many`
-/
/-- Syntax for a `rcases` pattern:
* `rcases? expr (: n)?`
* `rcases (h :)? expr (with patt_list (: expr)?)?`. -/
/--
`rintro_patt_parse_hi` and `rintro_patt_parse` are like `rcases_patt_parse`, but is used for
parsing top level `rintro` patterns, which allow sequences like `(x y : t)` in addition to simple
`rcases` patterns.

* `rintro_patt_parse_hi` will parse a high precedence `rcases` pattern, `rintro_patt_hi` below.
  This means only tuples and identifiers are allowed; alternations and type ascriptions
  require `(...)` instead, which switches to `patt`.
* `rintro_patt_parse tt` will parse a low precedence `rcases` pattern, `rintro_patt` below.
  This consists of either a sequence of patterns `p1 p2 p3` or an alternation list `p1 | p2 | p3`
  treated as a single pattern, optionally followed by a `: ty` type ascription, which applies to
  every pattern in the list.
* `rintro_patt_parse ff` parses `rintro_patt_low`, which is the same as `rintro_patt_parse tt` but
  it does not permit an unparenthesized alternation list, it must have the form `p1 p2 p3 (: ty)?`.

```lean
rintro_patt ::= (rintro_patt_hi+ | patt_med) (":" expr)?
rintro_patt_low ::= rintro_patt_hi* (":" expr)?
rintro_patt_hi ::= patt_hi | "(" rintro_patt ")"
```
-/
/-- Syntax for a `rintro` pattern: `('?' (: n)?) | rintro_patt`. -/
namespace interactive


/--
`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* An alteration pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
naming the first three parameters of the first constructor as `a,b,c` and the
first two of the second constructor `d,e`. If the list is not as long as the
number of arguments to the constructor or the number of constructors, the
remaining variables will be automatically named. If there are nested brackets
such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
`∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
parameter as necessary.

`rcases` also has special support for quotient types: quotient induction into Prop works like
matching on the constructor `quot.mk`.

`rcases h : e with PAT` will do the same as `rcases e with PAT` with the exception that an
assumption `h : e = PAT` will be added to the context.

`rcases? e` will perform case splits on `e` in the same way as `rcases e`,
but rather than accepting a pattern, it does a maximal cases and prints the
pattern that would produce this case splitting. The default maximum depth is 5,
but this can be modified with `rcases? e : n`.
-/
/--
The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintro (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro`, unlike `rcases`, also supports the form `(x y : ty)` for introducing
and type-ascripting multiple variables at once, similar to binders.

`rintro?` will introduce and case split on variables in the same way as
`rintro`, but will also print the `rintro` invocation that would have the same
result. Like `rcases?`, `rintro? : n` allows for modifying the
depth of splitting; the default is 5.

`rintros` is an alias for `rintro`.
-/
/-- Alias for `rintro`. -/
/-- Parses `patt? (: expr)? (:= expr)?`, the arguments for `obtain`.
 (This is almost the same as `rcases_patt_parse ff`,
but it allows the pattern part to be empty.) -/
/--
The `obtain` tactic is a combination of `have` and `rcases`. See `rcases` for
a description of supported patterns.

```lean
obtain ⟨patt⟩ : type,
{ ... }
```
is equivalent to
```lean
have h : type,
{ ... },
rcases h with ⟨patt⟩
```

The syntax `obtain ⟨patt⟩ : type := proof` is also supported.

If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

If `type` is omitted, `:= proof` is required.
-/
