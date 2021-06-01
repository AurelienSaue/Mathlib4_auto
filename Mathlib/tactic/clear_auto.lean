/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

/-!
# Better `clear` tactics

We define two variants of the standard `clear` tactic:

* `clear'` works like `clear` but the hypotheses that should be cleared can be
  given in any order. In contrast, `clear` can fail if hypotheses that depend on
  each other are given in the wrong order, even if all of them could be cleared.

* `clear_dependent` works like `clear'` but also clears any hypotheses that
  depend on the given hypotheses.

## Implementation notes

The implementation (ab)uses the native `revert_lst`, which can figure out
dependencies between hypotheses. This implementation strategy was suggested by
Simon Hudon.
-/

/-- Clears all the hypotheses in `hyps`. The tactic fails if any of the `hyps`
is not a local or if the target depends on any of the `hyps`. It also fails if
`hyps` contains duplicates.

If there are local hypotheses or definitions, say `H`, which are not in `hyps`
but depend on one of the `hyps`, what we do depends on `clear_dependent`. If it
is true, `H` is implicitly also cleared. If it is false, `clear'` fails. -/
-- Check if the target depends on any of the hyps. Doing this (instead of

-- letting one of the later tactics fail) lets us give a much more informative

-- error message.

-- If revert_lst reverted more hypotheses than we wanted to clear, there must

-- have been other hypotheses dependent on some of the hyps.

namespace tactic.interactive


/--
An improved version of the standard `clear` tactic. `clear` is sensitive to the
order of its arguments: `clear x y` may fail even though both `x` and `y` could
be cleared (if the type of `y` depends on `x`). `clear'` lifts this limitation.

```lean
example {α} {β : α → Type} (a : α) (b : β a) : unit :=
begin
  try { clear a b }, -- fails since `b` depends on `a`
  clear' a b,        -- succeeds
  exact ()
end
```
-/
/--
A variant of `clear'` which clears not only the given hypotheses, but also any
other hypotheses depending on them.

```lean
example {α} {β : α → Type} (a : α) (b : β a) : unit :=
begin
  try { clear' a },  -- fails since `b` depends on `a`
  clear_dependent a, -- succeeds, clearing `a` and `b`
  exact ()
end
```
 -/
end Mathlib