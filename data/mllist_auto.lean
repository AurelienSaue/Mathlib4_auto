/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Keeley Hoek, Simon Hudon, Scott Morrison

Monadic lazy lists.

The inductive construction is not allowed outside of meta (indeed, we can build infinite objects).
This isn't so bad, as the typical use is with the tactic monad, in any case.

As we're in meta anyway, we don't bother with proofs about these constructions.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.option.defs
import PostPort

namespace Mathlib

