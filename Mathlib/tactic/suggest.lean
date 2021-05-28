/-
Copyright (c) 2019 Lucas Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen and Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mllist
import Mathlib.tactic.solve_by_elim
import Mathlib.PostPort

universes l 

namespace Mathlib

/-!
# `suggest` and `library_search`

`suggest` and `library_search` are a pair of tactics for applying lemmas from the library to the
current goal.

* `suggest` prints a list of `exact ...` or `refine ...` statements, which may produce new goals
* `library_search` prints a single `exact ...` which closes the goal, or fails
-/

namespace tactic


namespace suggest


/-- Map a name (typically a head symbol) to a "canonical" definitional synonym.
Given a name `n`, we want a name `n'` such that a sufficiently applied
expression with head symbol `n` is always definitionally equal to an expression
with head symbol `n'`.
Thus, we can search through all lemmas with a result type of `n'`
to solve a goal with head symbol `n`.

For example, `>` is mapped to `<` because `a > b` is definitionally equal to `b < a`,
and `not` is mapped to `false` because `¬ a` is definitionally equal to `p → false`
The default is that the original argument is returned, so `<` is just mapped to `<`.

`normalize_synonym` is called for every lemma in the library, so it needs to be fast.
-/
-- TODO this is a hack; if you suspect more cases here would help, please report them

/--
Compute the head symbol of an expression, then normalise synonyms.

This is only used when analysing the goal, so it is okay to do more expensive analysis here.
-/
-- We may want to tweak this further?

-- We first have a various "customisations":

--   Because in `ℕ` `a.succ ≤ b` is definitionally `a < b`,

--   we add some special cases to allow looking for `<` lemmas even when the goal has a `≤`.

--   Note we only do this in the `ℕ` case, for performance.

-- And then the generic cases:

/--
A declaration can match the head symbol of the current goal in four possible ways:
* `ex`  : an exact match
* `mp`  : the declaration returns an `iff`, and the right hand side matches the goal
* `mpr` : the declaration returns an `iff`, and the left hand side matches the goal
* `both`: the declaration returns an `iff`, and the both sides match the goal
-/
inductive head_symbol_match 
where
| ex : head_symbol_match
| mp : head_symbol_match
| mpr : head_symbol_match
| both : head_symbol_match

/-- a textual representation of a `head_symbol_match`, for trace debugging. -/
def head_symbol_match.to_string : head_symbol_match → string :=
  sorry

/-- Determine if, and in which way, a given expression matches the specified head symbol. -/
/-- A package of `declaration` metadata, including the way in which its type matches the head symbol
which we are searching for. -/
/--
Generate a `decl_data` from the given declaration if
it matches the head symbol `hs` for the current goal.
-/
-- We used to check here for private declarations, or declarations with certain suffixes.

-- It turns out `apply` is so fast, it's better to just try them all.

/-- Retrieve all library definitions with a given head symbol. -/
/--
We unpack any element of a list of `decl_data` corresponding to an `↔` statement that could apply
in both directions into two separate elements.

This ensures that both directions can be independently returned by `suggest`,
and avoids a problem where the application of one direction prevents
the application of the other direction. (See `exp_le_exp` in the tests.)
-/
/--
Apply the lemma `e`, then attempt to close all goals using
`solve_by_elim opt`, failing if `close_goals = tt`
and there are any goals remaining.

Returns the number of subgoals which were closed using `solve_by_elim`.
-/
-- Implementation note: as this is used by both `library_search` and `suggest`,

-- we first run `solve_by_elim` separately on the independent goals,

-- whether or not `close_goals` is set,

-- and then run `solve_by_elim { all_goals := tt }`,

-- requiring that it succeeds if `close_goals = tt`.

/--
Apply the declaration `d` (or the forward and backward implications separately, if it is an `iff`),
and then attempt to solve the subgoal using `apply_and_solve`.

Returns the number of subgoals successfully closed.
-/
/-- An `application` records the result of a successful application of a library lemma. -/
end suggest


-- Call `apply_declaration`, then prepare the tactic script and

-- count the number of local hypotheses used.

-- (This tactic block is only executed when we evaluate the mllist,

-- so we need to do the `focus1` here.)

-- implementation note: we produce a `tactic (mllist tactic application)` first,

-- because it's easier to work in the tactic monad, but in a moment we squash this

-- down to an `mllist tactic application`.

/--
The core `suggest` tactic.
It attempts to apply a declaration from the library,
then solve new goals using `solve_by_elim`.

It returns a list of `application`s consisting of fields:
* `state`, a tactic state resulting from the successful application of a declaration from
  the library,
* `script`, a string of the form `Try this: refine ...` or `Try this: exact ...` which will
  reproduce that tactic state,
* `decl`, an `option declaration` indicating the declaration that was applied
  (or none, if `solve_by_elim` succeeded),
* `num_goals`, the number of remaining goals, and
* `hyps_used`, the number of local hypotheses used in the solution.
-/
/--
See `suggest_core`.

Returns a list of at most `limit` `application`s,
sorted by number of goals, and then (reverse) number of hypotheses used.
-/
/--
Returns a list of at most `limit` strings, of the form `Try this: exact ...` or
`Try this: refine ...`, which make progress on the current goal using a declaration
from the library.
-/
/--
Returns a string of the form `Try this: exact ...`, which closes the current goal.
-/
namespace interactive


/--
`suggest` tries to apply suitable theorems/defs from the library, and generates
a list of `exact ...` or `refine ...` scripts that could be used at this step.
It leaves the tactic state unchanged. It is intended as a complement of the search
function in your editor, the `#find` tactic, and `library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num`
(or less, if all possibilities are exhausted) possibilities ordered by length of lemma names.
The default for `num` is `50`.
For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that
`suggest` might miss some results if `num` is not large enough. However, because
`suggest` uses monadic lazy lists, smaller values of `num` run faster than larger values.

You can add additional lemmas to be used along with local hypotheses
after the application of a library lemma,
using the same syntax as for `solve_by_elim`, e.g.
```
example {a b c d: nat} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
begin
  suggest [add_lt_add], -- Says: `Try this: exact max_eq_left_of_lt (add_lt_add h₁ h₂)`
end
```
You can also use `suggest with attr` to include all lemmas with the attribute `attr`.
-/
/--
`suggest` lists possible usages of the `refine` tactic and leaves the tactic state unchanged.
It is intended as a complement of the search function in your editor, the `#find` tactic, and
`library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num` (or less, if
all possibilities are exhausted) possibilities ordered by length of lemma names.
The default for `num` is `50`.

For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that `suggest`
might miss some results if `num` is not large enough. However, because `suggest` uses monadic
lazy lists, smaller values of `num` run faster than larger values.

An example of `suggest` in action,

```lean
example (n : nat) : n < n + 1 :=
begin suggest, sorry end
```

prints the list,

```lean
Try this: exact nat.lt.base n
Try this: exact nat.lt_succ_self n
Try this: refine not_le.mp _
Try this: refine gt_iff_lt.mp _
Try this: refine nat.lt.step _
Try this: refine lt_of_not_ge _
...
```
-/
-- Turn off `Try this: exact ...` trace message for `library_search`

/--
`library_search` is a tactic to identify existing lemmas in the library. It tries to close the
current goal by applying a lemma from the library, then discharging any new goals using
`solve_by_elim`.

If it succeeds, it prints a trace message `exact ...` which can replace the invocation
of `library_search`.

Typical usage is:
```lean
example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by library_search -- Try this: exact nat.mul_sub_left_distrib n m k
```

By default `library_search` only unfolds `reducible` definitions
when attempting to match lemmas against the goal.
Previously, it would unfold most definitions, sometimes giving surprising answers, or slow answers.
The old behaviour is still available via `library_search!`.

You can add additional lemmas to be used along with local hypotheses
after the application of a library lemma,
using the same syntax as for `solve_by_elim`, e.g.
```
example {a b c d: nat} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
begin
  library_search [add_lt_add], -- Says: `Try this: exact max_eq_left_of_lt (add_lt_add h₁ h₂)`
end
```
You can also use `library_search with attr` to include all lemmas with the attribute `attr`.
-/
end interactive


/-- Invoking the hole command `library_search` ("Use `library_search` to complete the goal") calls
the tactic `library_search` to produce a proof term with the type of the hole.

Running it on

```lean
example : 0 < 1 :=
{!!}
```

produces

```lean
example : 0 < 1 :=
nat.one_pos
```
-/
