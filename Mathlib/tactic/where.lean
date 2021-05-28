/-
Copyright (c) 2019 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

/-!
# The `where` command

When working in a Lean file with namespaces, parameters, and variables, it can be confusing to
identify what the current "parser context" is. The command `#where` identifies and prints
information about the current location, including the active namespace, open namespaces, and
declared variables.

It is a bug for `#where` to incorrectly report this information (this was not formerly the case);
please file an issue on GitHub if you observe a failure.
-/

namespace where


/-- Assigns a priority to each binder for determining the order in which variables are traced. -/
/-- The relation on binder priorities. -/
/-- Selects the elements of the given `list α` which under the image of `p : α → β × γ` have `β`
component equal to `b'`. Returns the `γ` components of the selected elements under the image of `p`,
and the elements of the original `list α` which were not selected. -/
def select_for_which {α : Type} {β : Type} {γ : Type} (p : α → β × γ) [DecidableEq β] (b' : β) : List α → List γ × List α :=
  sorry

/-- Helper function for `collect_by`. -/
/-- Returns the elements of `l` under the image of `p`, collecting together elements with the same
`β` component, deleting duplicates. -/
/-- Sort the variables by their priority as defined by `where.binder_priority`. -/
/-- Separate out the names of implicit variables (commonly instances with no name). -/
/-- Format an individual variable definition for printing. -/
/-- Turn a list of triples of variable names, binder info, and types, into a pretty list. -/
/-- Strips the namespace prefix `ns` from `n`. -/
/-- `get_open_namespaces ns` returns a list of the open namespaces, given that we are currently in
the namespace `ns` (which we do not include). -/
/-- Give a slightly friendlier name for `name.anonymous` in the context of your current namespace.
-/
/-- `#where` output helper which traces the current namespace. -/
/-- `#where` output helper which traces the open namespaces. -/
/-- `#where` output helper which traces the variables. -/
/-- `#where` output helper which traces the includes. -/
/-- `#where` output helper which traces the namespace end. -/
/-- `#where` output helper which traces newlines. -/
/-- `#where` output helper which traces lines, adding a newline if nonempty. -/
/-- `#where` output main function. -/
/--
When working in a Lean file with namespaces, parameters, and variables, it can be confusing to
identify what the current "parser context" is. The command `#where` identifies and prints
information about the current location, including the active namespace, open namespaces, and
declared variables.

It is a bug for `#where` to incorrectly report this information (this was not formerly the case);
please file an issue on GitHub if you observe a failure.
-/
