/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

/-!
# `pretty_cases` tactic

When using `induction` and `cases`, `pretty_cases` prints a `"Try
this:"` advice that shows how to structure the proof with
`case { ... }` commands.  In the following example, we apply induction on a
permutation assumption about lists. `pretty_cases` gives us a proof
skeleton that explicit selects the branches and explicit names the
new local constants:

```lean
example {α} (xs ys : list α) (h : xs ~ ys) : true :=
begin
  induction h,
  pretty_cases,
    -- Try this:
    --   case list.perm.nil :
    --   { admit },
    --   case list.perm.cons : h_x h_l₁ h_l₂ h_a h_ih
    --   { admit },
    --   case list.perm.swap : h_x h_y h_l
    --   { admit },
    --   case list.perm.trans : h_l₁ h_l₂ h_l₃ h_a h_a_1 h_ih_a h_ih_a_1
    --   { admit },
end
```

## Main definitions

 * `pretty_cases_advice` return `pretty_cases` advice without printing it
 * `pretty_cases` main tactic
-/

namespace tactic


/-- Query the proof goal and print the skeleton of a proof by cases. -/
namespace interactive


/--
Query the proof goal and print the skeleton of a proof by
cases.

For example, let us consider the following proof:

```lean
example {α} (xs ys : list α) (h : xs ~ ys) : true :=
begin
  induction h,
  pretty_cases,
    -- Try this:
    --   case list.perm.nil :
    --   { admit },
    --   case list.perm.cons : h_x h_l₁ h_l₂ h_a h_ih
    --   { admit },
    --   case list.perm.swap : h_x h_y h_l
    --   { admit },
    --   case list.perm.trans : h_l₁ h_l₂ h_l₃ h_a h_a_1 h_ih_a h_ih_a_1
    --   { admit },
end
```

The output helps the user layout the cases and rename the
introduced variables.
-/
