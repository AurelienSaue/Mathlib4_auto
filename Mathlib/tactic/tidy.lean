/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.auto_cases
import Mathlib.tactic.chain
import Mathlib.tactic.norm_cast
import Mathlib.PostPort

namespace Mathlib

namespace tactic


namespace tidy


/-- Tag interactive tactics (locally) with `[tidy]` to add them to the list of default tactics
called by `tidy`. -/
end tidy


namespace interactive


/-- Use a variety of conservative tactics to solve goals.

`tidy?` reports back the tactic script it found. As an example
```lean
example : ∀ x : unit, x = unit.star :=
begin
  tidy? -- Prints the trace message: "Try this: intros x, exact dec_trivial"
end
```

The default list of tactics is stored in `tactic.tidy.default_tidy_tactics`.
This list can be overridden using `tidy { tactics := ... }`.
(The list must be a `list` of `tactic string`, so that `tidy?`
can report a usable tactic script.)

Tactics can also be added to the list by tagging them (locally) with the
`[tidy]` attribute. -/
end interactive


/-- Invoking the hole command `tidy` ("Use `tidy` to complete the goal") runs the tactic of
the same name, replacing the hole with the tactic script `tidy` produces.
-/
