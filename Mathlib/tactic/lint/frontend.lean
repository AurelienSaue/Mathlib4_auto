/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.lint.basic
import Mathlib.PostPort

universes l 

namespace Mathlib

/-!
# Linter frontend and commands

This file defines the linter commands which spot common mistakes in the code.
* `#lint`: check all declarations in the current file
* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint_all`: check all declarations in the environment (the current file and all
  imported files)

For a list of default / non-default linters, see the "Linting Commands" user command doc entry.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint_mathlib*`) to omit the slow tests (4).

You can append a `-` to any command (e.g. `#lint_mathlib-`) to run a silent lint
that suppresses the output if all checks pass.
A silent lint will fail if any test fails.

You can append a `+` to any command (e.g. `#lint_mathlib+`) to run a verbose lint
that reports the result of each linter, including  the successes.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments`

You can add custom linters by defining a term of type `linter` in the `linter` namespace.
A linter defined with the name `linter.my_new_check` can be run with `#lint my_new_check`
or `lint only my_new_check`.
If you add the attribute `@[linter]` to `linter.my_new_check` it will run by default.

Adding the attribute `@[nolint doc_blame unused_arguments]` to a declaration
omits it from only the specified linter checks.

## Tags

sanity check, lint, cleanup, command, tactic
-/

/--
Verbosity for the linter output.
* `low`: only print failing checks, print nothing on success.
* `medium`: only print failing checks, print confirmation on success.
* `high`: print output of every check.
-/
inductive lint_verbosity 
where
| low : lint_verbosity
| medium : lint_verbosity
| high : lint_verbosity

/-- `get_checks slow extra use_only` produces a list of linters.
`extras` is a list of names that should resolve to declarations with type `linter`.
If `use_only` is true, it only uses the linters in `extra`.
Otherwise, it uses all linters in the environment tagged with `@[linter]`.
If `slow` is false, it only uses the fast default tests. -/
/--
`lint_core all_decls non_auto_decls checks` applies the linters `checks` to the list of
declarations.
If `auto_decls` is false for a linter (default) the linter is applied to `non_auto_decls`.
If `auto_decls` is true, then it is applied to `all_decls`.
The resulting list has one element for each linter, containing the linter as
well as a map from declaration name to warning.
-/
/-- Sorts a map with declaration keys as names by line number. -/
/-- Formats a linter warning as `#print` command with comment. -/
/-- Formats a map of linter warnings using `print_warning`, sorted by line number. -/
/--
Formats a map of linter warnings grouped by filename with `-- filename` comments.
The first `drop_fn_chars` characters are stripped from the filename.
-/
/--
Formats the linter results as Lean code with comments and `#print` commands.
-/
/-- The common denominator of `#lint[|mathlib|all]`.
The different commands have different configurations for `l`,
`group_by_filename` and `where_desc`.
If `slow` is false, doesn't do the checks that take a lot of time.
If `verbose` is false, it will suppress messages from passing checks.
By setting `checks` you can customize which checks are performed.

Returns a `name_set` containing the names of all declarations that fail any check in `check`,
and a `format` object describing the failures. -/
/-- Return the message printed by `#lint` and a `name_set` containing all declarations that fail. -/
/-- Returns the declarations considered by the mathlib linter. -/
/-- Return the message printed by `#lint_mathlib` and a `name_set` containing all declarations
that fail. -/
/-- Return the message printed by `#lint_all` and a `name_set` containing all declarations
that fail. -/
/-- Parses an optional `only`, followed by a sequence of zero or more identifiers.
Prepends `linter.` to each of these identifiers. -/
/--
Parses a "-" or "+", returning `lint_verbosity.low` or `lint_verbosity.high` respectively,
or returns `none`.
-/
/-- The common denominator of `lint_cmd`, `lint_mathlib_cmd`, `lint_all_cmd` -/
/-- The command `#lint` at the bottom of a file will warn you about some common mistakes
in that file. Usage: `#lint`, `#lint linter_1 linter_2`, `#lint only linter_1 linter_2`.
`#lint-` will suppress the output if all checks pass.
`#lint+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
/-- The command `#lint_mathlib` checks all of mathlib for certain mistakes.
Usage: `#lint_mathlib`, `#lint_mathlib linter_1 linter_2`, `#lint_mathlib only linter_1 linter_2`.
`#lint_mathlib-` will suppress the output if all checks pass.
`lint_mathlib+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
/-- The command `#lint_all` checks all imported files for certain mistakes.
Usage: `#lint_all`, `#lint_all linter_1 linter_2`, `#lint_all only linter_1 linter_2`.
`#lint_all-` will suppress the output if all checks pass.
`lint_all+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
/-- The command `#list_linters` prints a list of all available linters. -/
/--
Invoking the hole command `lint` ("Find common mistakes in current file") will print text that
indicates mistakes made in the file above the command. It is equivalent to copying and pasting the
output of `#lint`. On large files, it may take some time before the output appears.
-/
