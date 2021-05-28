/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.logic.basic
import PostPort

universes r s u v u_1 u_2 

namespace Mathlib

/-!
# Derive handler for `inhabited` instances

This file introduces a derive handler to automatically generate `inhabited`
instances for structures and inductives. We also add various `inhabited`
instances for types in the core library.
-/

namespace tactic


/--
Tries to derive an `inhabited` instance for inductives and structures.

For example:
```
@[derive inhabited]
structure foo :=
(a : ℕ := 42)
(b : list ℕ)
```
Here, `@[derive inhabited]` adds the instance `foo.inhabited`, which is defined as
`⟨⟨42, default (list ℕ)⟩⟩`.  For inductives, the default value is the first constructor.

If the structure/inductive has a type parameter `α`, then the generated instance will have an
argument `inhabited α`, even if it is not used.  (This is due to the implementation using
`instance_derive_handler`.)
-/
end tactic


protected instance ordering.inhabited : Inhabited ordering :=
  { default := ordering.lt }

protected instance bin_tree.inhabited {α : Type u_1} : Inhabited (bin_tree α) :=
  { default := bin_tree.empty }

protected instance unsigned.inhabited : Inhabited unsigned :=
  { default := 0 }

protected instance string.iterator.inhabited : Inhabited string.iterator :=
  string.iterator_imp.inhabited

protected instance rbnode.inhabited {α : Type u_1} : Inhabited (rbnode α) :=
  { default := rbnode.leaf }

protected instance rbtree.inhabited {α : Type u_1} {lt : autoParam (α → α → Prop)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.rbtree.default_lt")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbtree") "default_lt") [])} : Inhabited (rbtree α) :=
  { default := mk_rbtree α }

protected instance rbmap.inhabited {α : Type u_1} {β : Type u_2} {lt : autoParam (α → α → Prop)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.rbtree.default_lt")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "rbtree") "default_lt") [])} : Inhabited (rbmap α β) :=
  { default := mk_rbmap α β }

