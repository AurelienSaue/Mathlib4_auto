/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison

Case bashing:
* on `x ∈ A`, for `A : finset α` or `A : list α`, or
* on `x : A`, with `[fintype A]`.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.tactic.norm_num
import Mathlib.PostPort

namespace Mathlib

namespace tactic


/-- Checks that the expression looks like `x ∈ A` for `A : finset α`, `multiset α` or `A : list α`,
    and returns the type α. -/
/--
`expr_list_to_list_expr` converts an `expr` of type `list α`
to a list of `expr`s each with type `α`.

TODO: this should be moved, and possibly duplicates an existing definition.
-/
/--
`fin_cases_at with_list e` performs case analysis on `e : α`, where `α` is a fintype.
The optional list of expressions `with_list` provides descriptions for the cases of `e`,
for example, to display nats as `n.succ` instead of `n+1`.
These should be defeq to and in the same order as the terms in the enumeration of `α`.
-/
namespace interactive


/--
`fin_cases h` performs case analysis on a hypothesis of the form
`h : A`, where `[fintype A]` is available, or
`h ∈ A`, where `A : finset X`, `A : multiset X` or `A : list X`.

`fin_cases *` performs case analysis on all suitable hypotheses.

As an example, in
```
example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases *; simp,
  all_goals { assumption }
end
```
after `fin_cases p; simp`, there are three goals, `f 0`, `f 1`, and `f 2`.
-/
end interactive


end Mathlib