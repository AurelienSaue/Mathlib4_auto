/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.control.traversable.basic
import Mathlib.tactic.simpa
import PostPort

namespace Mathlib

/-- pretty print a `loc` -/
/-- shift `pos` `n` columns to the left -/
namespace tactic


/-- parse structure instance of the shape `{ field1 := value1, .. , field2 := value2 }` -/
/-- pretty print structure instance -/
/-- Attribute containing a table that accumulates multiple `squeeze_simp` suggestions -/
/-- dummy declaration used as target of `squeeze_loc` attribute -/
def squeeze_loc_attr_carrier : Unit :=
  Unit.unit

/-- Format a list of arguments for use with `simp` and friends. This omits the
list entirely if it is empty. -/
/-- Emit a suggestion to the user. If inside a `squeeze_scope` block,
the suggestions emitted through `mk_suggestion` will be aggregated so that
every tactic that makes a suggestion can consider multiple execution of the
same invocation.
If `at_pos` is true, make the suggestion at `p` instead of the current position. -/
/-- translate a `pexpr` into a `simp` configuration -/
/-- translate a `pexpr` into a `dsimp` configuration -/
/-- `same_result proof tac` runs tactic `tac` and checks if the proof
produced by `tac` is equivalent to `proof`. -/
/--
`filter_simp_set g call_simp user_args simp_args` returns `args'` such that, when calling
`call_simp tt /- only -/ args'` on the goal `g` (`g` is a meta var) we end up in the same
state as if we had called `call_simp ff (user_args ++ simp_args)` and removing any one
element of `args'` changes the resulting proof.
-/
/-- make a `simp_arg_type` that references the name given as an argument -/
/-- tactic combinator to create a `simp`-like tactic that minimizes its
argument list.

 * `slow`: adds all rfl-lemmas from the environment to the initial list (this is a slower but more accurate strategy)
 * `no_dflt`: did the user use the `only` keyword?
 * `args`:    list of `simp` arguments
 * `tac`:     how to invoke the underlying `simp` tactic

-/
namespace interactive


/-- Turn a `simp_arg_type` into a string. -/
/-- combinator meant to aggregate the suggestions issued by multiple calls
of `squeeze_simp` (due, for instance, to `;`).

Can be used as:

```lean
example {α β} (xs ys : list α) (f : α → β) :
  (xs ++ ys.tail).map f = xs.map f ∧ (xs.tail.map f).length = xs.length :=
begin
  have : xs = ys, admit,
  squeeze_scope
  { split; squeeze_simp, -- `squeeze_simp` is run twice, the first one requires
                         -- `list.map_append` and the second one `[list.length_map, list.length_tail]`
                         -- prints only one message and combine the suggestions:
                         -- > Try this: simp only [list.length_map, list.length_tail, list.map_append]
    squeeze_simp [this]  -- `squeeze_simp` is run only once
                         -- prints:
                         -- > Try this: simp only [this]
 },
end
```

-/
/--
`squeeze_simp`, `squeeze_simpa` and `squeeze_dsimp` perform the same
task with the difference that `squeeze_simp` relates to `simp` while
`squeeze_simpa` relates to `simpa` and `squeeze_dsimp` relates to
`dsimp`. The following applies to `squeeze_simp`, `squeeze_simpa` and
`squeeze_dsimp`.

`squeeze_simp` behaves like `simp` (including all its arguments)
and prints a `simp only` invocation to skip the search through the
`simp` lemma list.

For instance, the following is easily solved with `simp`:

```lean
example : 0 + 1 = 1 + 0 := by simp
```

To guide the proof search and speed it up, we may replace `simp`
with `squeeze_simp`:

```lean
example : 0 + 1 = 1 + 0 := by squeeze_simp
-- prints:

-- prints:
-- Try this: simp only [add_zero, eq_self_iff_true, zero_add]

-- Try this: simp only [add_zero, eq_self_iff_true, zero_add]
```

`squeeze_simp` suggests a replacement which we can use instead of
`squeeze_simp`.

```lean
example : 0 + 1 = 1 + 0 := by simp only [add_zero, eq_self_iff_true, zero_add]
```

`squeeze_simp only` prints nothing as it already skips the `simp` list.

This tactic is useful for speeding up the compilation of a complete file.
Steps:

   1. search and replace ` simp` with ` squeeze_simp` (the space helps avoid the
      replacement of `simp` in `@[simp]`) throughout the file.
   2. Starting at the beginning of the file, go to each printout in turn, copy
      the suggestion in place of `squeeze_simp`.
   3. after all the suggestions were applied, search and replace `squeeze_simp` with
      `simp` to remove the occurrences of `squeeze_simp` that did not produce a suggestion.

Known limitation(s):
  * in cases where `squeeze_simp` is used after a `;` (e.g. `cases x; squeeze_simp`),
    `squeeze_simp` will produce as many suggestions as the number of goals it is applied to.
    It is likely that none of the suggestion is a good replacement but they can all be
    combined by concatenating their list of lemmas. `squeeze_scope` can be used to
    combine the suggestions: `by squeeze_scope { cases x; squeeze_simp }`
  * sometimes, `simp` lemmas are also `_refl_lemma` and they can be used without appearing in the
    resulting proof. `squeeze_simp` won't know to try that lemma unless it is called as `squeeze_simp?`

-/
/-- see `squeeze_simp` -/
/-- `squeeze_dsimp` behaves like `dsimp` (including all its arguments)
and prints a `dsimp only` invocation to skip the search through the
`simp` lemma list. See the doc string of `squeeze_simp` for examples.
 -/
end interactive


end tactic


