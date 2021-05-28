/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.declaration
import Mathlib.Lean3Lib.init.meta.exceptional
import Mathlib.Lean3Lib.init.data.option.basic
import Mathlib.Lean3Lib.init.meta.rb_map
import PostPort

universes l 

namespace Mathlib

/-- An __environment__ contains all of the declarations and notation that have been defined so far.   -/
namespace environment


/--
Consider a type `ψ` which is an inductive datatype using a single constructor `mk (a : α) (b : β) : ψ`.
Lean will automatically make two projection functions `a : ψ → α`, `b : ψ → β`.
Lean tags these declarations as __projections__.
This helps the simplifier / rewriter not have to expand projectors.
Eg `a (mk x y)` will automatically reduce to `x`.
If you `extend` a structure, all of the projections on the parent will also be created for the child.
Projections are also treated differently in the VM for efficiency.

Note that projections have nothing to do with the dot `mylist.map` syntax.

You can find out if a declaration is a projection using `environment.is_projection` which returns `projection_info`.

Data for a projection declaration:
- `cname`    is the name of the constructor associated with the projection.
- `nparams`  is the number of constructor parameters. Eg `and.intro` has two type parameters.
- `idx`      is the parameter being projected by this projection.
- `is_class` is tt iff this is a typeclass projection.

### Examples:

- `and.right` is a projection with ``{cname := `and.intro, nparams := 2, idx := 1, is_class := ff}``
- `ordered_ring.neg` is a projection with ``{cname := `ordered_ring.mk, nparams := 1, idx := 5, is_class := tt}``.

-/
structure projection_info 
where
  cname : name
  nparams : ℕ
  idx : ℕ
  is_class : Bool

/-- A marking on the binders of structures and inductives indicating
   how this constructor should mark its parameters.

       inductive foo
       | one {} : foo -> foo   -- relaxed_implicit
       | two ( ) : foo -> foo  -- explicit
       | two [] : foo -> foo   -- implicit
       | three : foo -> foo    -- relaxed implicit (default)
-/
inductive implicit_infer_kind 
where
| implicit : implicit_infer_kind
| relaxed_implicit : implicit_infer_kind
| none : implicit_infer_kind

protected instance implicit_infer_kind.inhabited : Inhabited implicit_infer_kind :=
  { default := implicit_infer_kind.implicit }

/-- One introduction rule in an inductive declaration -/
