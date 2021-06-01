/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.tidy
import Mathlib.tactic.replacer
import Mathlib.PostPort

namespace Mathlib

/-!
# The `obviously` tactic

This file sets up a tactic called `obviously`,
which is subsequently used throughout the category theory library
as an `auto_param` to discharge easy proof obligations when building structures.

In this file, we set up `obviously` as a "replacer" tactic,
whose implementation can be modified after the fact.
Then we set the default implementation to be `tidy`.

## Implementation note
At present we don't actually take advantage of the replacer mechanism in mathlib.
In the past it had been used by an external category theory library which wanted to incorporate
`rewrite_search` as part of `obviously`.
-/

/-
The propositional fields of `category` are annotated with the auto_param `obviously`,
which is defined here as a
[`replacer` tactic](https://leanprover-community.github.io/mathlib_docs/commands.html#def_replacer).
We then immediately set up `obviously` to call `tidy`. Later, this can be replaced with more
powerful tactics.

(In fact, at present this mechanism is not actually used, and the implementation of
`obviously` below stays in place throughout mathlib.)
-/

end Mathlib