/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Lean3Lib.data.dlist
import Mathlib.tactic.core
import PostPort

namespace Mathlib

namespace tactic


-- TODO(Simon): visit expressions built of `fn` nested inside other such expressions:

-- e.g.: x + f (a + b + c) + y should generate two rewrite candidates

namespace interactive


/--
`assoc_rewrite [h₀,← h₁] at ⊢ h₂` behaves like `rewrite [h₀,← h₁] at ⊢ h₂`
with the exception that associativity is used implicitly to make rewriting
possible.

It works for any function `f` for which an `is_associative f` instance can be found.

```
example {α : Type*} (f : α → α → α) [is_associative α f] (a b c d x : α) :
  let infix `~` := f in
  b ~ c = x → (a ~ b ~ c ~ d) = (a ~ x ~ d) :=
begin
  intro h,
  assoc_rw h, 
end
```
-/
/-- synonym for `assoc_rewrite` -/
