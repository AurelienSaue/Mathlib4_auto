/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Oliver Nash
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.abel
import Mathlib.PostPort

namespace Mathlib

namespace tactic


namespace interactive


/-- A tactic for simplifying identities in not-necessarily-commutative rings.

An example:
```lean
example {R : Type*} [ring R] (a b c : R) : a * (b + c + c - b) = 2*a*c :=
by noncomm_ring
```
-/
end Mathlib