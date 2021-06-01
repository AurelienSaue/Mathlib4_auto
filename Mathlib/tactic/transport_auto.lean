/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Simon Hudon, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.equiv_rw
import Mathlib.PostPort

namespace Mathlib

/-!
## The `transport` tactic

`transport` attempts to move an `s : S α` expression across an equivalence `e : α ≃ β` to solve
a goal of the form `S β`, by building the new object field by field, taking each field of `s`
and rewriting it along `e` using the `equiv_rw` tactic.

We try to ensure good definitional properties, so that, for example, when we transport a `monoid α`
to a `monoid β`, the new multiplication is definitionally `λ x y, e (e.symm a * e.symm b)`.
-/

namespace tactic


/--
Given `s : S α` for some structure `S` depending on a type `α`,
and an equivalence `e : α ≃ β`,
try to produce an `S β`,
by transporting data and axioms across `e` using `equiv_rw`.
-/
namespace interactive


/--
Given a goal `⊢ S β` for some type class `S`, and an equivalence `e : α ≃ β`.
`transport using e` will look for a hypothesis `s : S α`,
and attempt to close the goal by transporting `s` across the equivalence `e`.

```lean
example {α : Type} [ring α] {β : Type} (e : α ≃ β) : ring β :=
by transport using e.
```

You can specify the object to transport using `transport s using e`.

`transport` works by attempting to copy each of the operations and axiom fields of `s`,
rewriting them using `equiv_rw e` and defining a new structure using these rewritten fields.

If it fails to fill in all the new fields, `transport` will produce new subgoals.
It's probably best to think about which missing `simp` lemmas would have allowed `transport`
to finish, rather than solving these goals by hand.
(This may require looking at the implementation of `tranport` to understand its algorithm;
there are several examples of "transport-by-hand" at the end of `test/equiv_rw.lean`,
which `transport` is an abstraction of.)
-/
end Mathlib