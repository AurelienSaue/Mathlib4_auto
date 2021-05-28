/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.level
import Mathlib.Lean3Lib.init.control.monad
import Mathlib.Lean3Lib.init.meta.rb_map
import PostPort

universes l 

namespace Mathlib

/-- Column and line position in a Lean source file. -/
structure pos 
where
  line : ℕ
  column : ℕ

protected instance pos.decidable_eq : DecidableEq pos :=
  sorry

/-- Auxiliary annotation for binders (Lambda and Pi).
    This information is only used for elaboration.
      The difference between `{}` and `⦃⦄` is how implicit arguments are treated that are *not* followed by explicit arguments.
  `{}` arguments are applied eagerly, while `⦃⦄` arguments are left partially applied:
```lean
def foo {x : ℕ} : ℕ := x
def bar ⦃x : ℕ⦄ : ℕ := x
#check foo -- foo : ℕ
#check bar -- bar : Π ⦃x : ℕ⦄, ℕ
```
    -/
/- `(x : α)` -/

inductive binder_info 
where
| default : binder_info
| implicit : binder_info
| strict_implicit : binder_info
| inst_implicit : binder_info
| aux_decl : binder_info

/- `{x : α}` -/

/- `⦃x:α⦄` -/

/- `[x : α]`. Should be inferred with typeclass resolution. -/

/- Auxiliary internal attribute used to mark local constants representing recursive functions
        in recursive equations and `match` statements. -/

protected instance binder_info.has_repr : has_repr binder_info :=
  has_repr.mk fun (bi : binder_info) => sorry

