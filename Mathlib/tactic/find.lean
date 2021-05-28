/-
Copyright (c) 2017 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

/--
The `find` command from `tactic.find` allows to find definitions lemmas using
pattern matching on the type. For instance:

```lean
import tactic.find

run_cmd tactic.skip

#find _ + _ = _ + _
#find (_ : ℕ) + _ = _ + _
#find ℕ → ℕ
```

The tactic `library_search` is an alternate way to find lemmas in the library.
-/
