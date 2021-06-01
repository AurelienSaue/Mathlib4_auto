/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.tactic

namespace Mathlib

/--
The front-end (e.g., Emacs, VS Code) can invoke commands for holes `{! ... !}` in
a declaration. A command is a tactic that takes zero or more pre-terms in the
hole, and returns a list of pair (s, descr) where 's' is a substitution and 'descr' is
a short explanation for the substitution.
Each string 's' represents a different way to fill the hole.
The front-end is responsible for replacing the hole with the string/alternative selected by the user.

This infra-structure can be use to implement auto-fill and/or refine commands.

An action may return an empty list. This is useful for actions that just return
information such as: the type of an expression, its normal form, etc.
-/
end Mathlib