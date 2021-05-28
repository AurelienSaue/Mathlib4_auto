/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.core
import PostPort

universes u_1 

namespace Mathlib

/-!
This file provides an alternative implementation for `apply` to fix the so-called "apply bug".

The issue arises when the goals is a Π-type -- whether it is visible or hidden behind a definition.

For instance, consider the following proof:

```
example {α β} (x y z : α → β) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  apply le_trans,
end
```

Because `x ≤ z` is definitionally equal to `∀ i, x i ≤ z i`, `apply` will fail. The alternative
definition, `apply'` fixes this. When `apply` would work, `apply` is used and otherwise,
a different strategy is deployed
-/

namespace tactic


/-- With `gs` a list of proof goals, `reorder_goals gs new_g` will use the `new_goals` policy
`new_g` to rearrange the dependent goals to either drop them, push them to the end of the list
or leave them in place. The `bool` values in `gs` indicates whether the goal is dependent or not. -/
def reorder_goals {α : Type u_1} (gs : List (Bool × α)) : new_goals → List α :=
  sorry

