/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.Lean3Lib.data.buffer.parser
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

/-!
# The `alias` command

This file defines an `alias` command, which can be used to create copies
of a theorem or definition with different names.

Syntax:

```lean
/-- doc string -/

alias my_theorem ← alias1 alias2 ...
```

This produces defs or theorems of the form:

```lean
/-- doc string -/
/-- doc string -/
namespace tactic.alias


/--
The `alias` command can be used to create copies
of a theorem or definition with different names.

Syntax:

```lean
/-- doc string -/
/-- doc string -/
/-- doc string -/
end Mathlib