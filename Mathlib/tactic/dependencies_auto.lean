/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.core
import PostPort

namespace Mathlib

/-!
# Tactics About Dependencies

This module provides tactics to compute dependencies and reverse dependencies of
hypotheses. An expression `e` depends on a hypothesis `h` if `e` would not be
valid if `h` were removed from the context. For example, the expression
`e := x > 0` depends on `x`. We say that `x` is a dependency of `e` and that `e`
is a reverse dependency of `x`.

It is sometimes useful to consider *inclusive* dependency: `e` inclusively
depends on `h` iff `e` depends on `h` or `e = h` (so inclusive dependency is the
reflexive closure of regular dependency).

Note that the standard library does not use quite the same terminology:

* `kdependencies`/`kdeps` from the standard library compute reverse
  dependencies, not dependencies.
* `kdepends_on` and functions derived from it ignore local definitions and
  therefore compute a weaker dependency relation (see next section).

## Local Definitions

Determining dependencies of hypotheses is usually straightforward: a hypothesis
`r : R` depends on another hypothesis `d : D` if `d` occurs in `R`. The
implementation is more involved, however, in the presence of local definitions.
Consider this context:

```lean
n m : ℕ
k : ℕ := m
o : ℕ := k
h : o > 0
```

`h` depends on `o`, `k` and `m`, but only the dependency on `o` is syntactically
obvious. `kdepends_on` ignores this complication and claims that `h` does not
depend on `k` or `m`. We do not follow this example but process local
definitions properly. This means that if the context contains a local
definition, we need to compute the syntactic dependencies of `h`, then their
dependencies, and so on.

## Direct Dependencies

If you want to ignore local definitions while computing dependencies, this
module also provides tactics to find the *direct* dependencies of a hypothesis.
These are the hypotheses that syntactically appear in the hypothesis's type (or
value, if the hypothesis is a local definition).
-/

namespace tactic


/-! ### Direct Dependencies -/

/-! #### Checking whether hypotheses directly depend on each other -/

/--
`type_has_local_in_name_set h ns` returns true iff the type of `h` contains a
local constant whose unique name appears in `ns`.
-/
