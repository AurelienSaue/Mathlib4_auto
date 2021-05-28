/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.interactive
import Mathlib.PostPort

namespace Mathlib

/-!
# Rename bound variable tactic

This files defines a tactic `rename_var` whose main purpose is to teach
renaming of bound variables.

* `rename_var old new` renames all bound variables named `old` to `new` in the goal.
* `rename_var old new at h` does the same in hypothesis `h`.

```lean
example (P : ℕ →  ℕ → Prop) (h : ∀ n, ∃ m, P n m) : ∀ l, ∃ m, P l m :=
begin
  rename_var n q at h, -- h is now ∀ (q : ℕ), ∃ (m : ℕ), P q m,
  rename_var m n, -- goal is now ∀ (l : ℕ), ∃ (n : ℕ), P k n,
  exact h -- Lean does not care about those bound variable names
end
```

## Tags

teaching, tactic
-/

/-- Rename bound variable `old` to `new` in an `expr`-/
namespace tactic


/-- Rename bound variable `old` to `new` in goal -/
/-- Rename bound variable `old` to `new` in assumption `h` -/
end tactic


namespace tactic.interactive


/--
`rename_var old new` renames all bound variables named `old` to `new` in the goal.
`rename_var old new at h` does the same in hypothesis `h`.
-/
end tactic.interactive


/--
`rename_var old new` renames all bound variables named `old` to `new` in the goal.
