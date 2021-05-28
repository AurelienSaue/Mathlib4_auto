/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.meta.interactive_base
import Lean3Lib.init.function
import PostPort

namespace Mathlib

namespace tactic


/-- A pattern is an expression `target` containing temporary metavariables.
A pattern also contains a list of `outputs` which also depend on these temporary metavariables.
When we run `match p e`, the system will match `p.target` with `e` and assign
the temporary metavariables. It then returns the outputs with the assigned variables.

## Fields

- `target` Term to match. Contains temporary metavariables.
- `uoutput` List of universes that are returned on a successful match.
- `moutput` List of expressions that are returned on a successful match.
- `nuvars` Number of (temporary) universe metavariables in this pattern.
- `nmvars` Number of (temporary) metavariables in this pattern.

## Example

The pattern for `list.cons h t` returning `h` and `t` would be
```
{ target  := `(@list.cons ?x_0 ?x_1 ?x_2),
  uoutput := [],
  moutput := [?x_1,?x_2],
  nuvars  := 0,
  nmvars  := 3
}
```

-/
