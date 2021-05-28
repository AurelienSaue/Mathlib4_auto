/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Provides a `subtype_instance` tactic which builds instances for algebraic substructures
(sub-groups, sub-rings...).
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.string.basic
import Mathlib.PostPort

namespace Mathlib

namespace tactic


/-- makes the substructure axiom name from field name, by postfacing with `_mem`-/
def mk_mem_name (sub : name) : name → name :=
  sorry

namespace interactive


/-- builds instances for algebraic substructures

Example:
```lean
variables {α : Type*} [monoid α] {s : set α}

class is_submonoid (s : set α) : Prop :=
(one_mem : (1:α) ∈ s)
(mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s)

instance subtype.monoid {s : set α} [is_submonoid s] : monoid s :=
by subtype_instance
```
-/
