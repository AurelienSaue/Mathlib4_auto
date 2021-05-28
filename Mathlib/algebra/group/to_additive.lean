/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.transform_decl
import Mathlib.tactic.algebra
import Mathlib.PostPort

universes l 

namespace Mathlib

/-!
# Transport multiplicative to additive

This file defines an attribute `to_additive` that can be used to
automatically transport theorems and definitions (but not inductive
types and structures) from a multiplicative theory to an additive theory.

Usage information is contained in the doc string of `to_additive.attr`.

### Missing features

* Automatically transport structures and other inductive types.

* For structures, automatically generate theorems like `group α ↔
  add_group (additive α)`.

* Rewrite rules for the last part of the name that work in more
  cases. E.g., we can replace `monoid` with `add_monoid` etc.
-/

namespace to_additive


/-- An auxiliary attribute used to store the names of the additive versions of declarations
that have been processed by `to_additive`. -/
/-- A command that can be used to have future uses of `to_additive` change the `src` namespace
to the `tgt` namespace.

For example:
```
run_cmd to_additive.map_namespace `quotient_group `quotient_add_group
```

Later uses of `to_additive` on declarations in the `quotient_group` namespace will be created
in the `quotient_add_group` namespaces.
-/
/-- `value_type` is the type of the arguments that can be provided to `to_additive`.
`to_additive.parser` parses the provided arguments into `name` for the target and an
optional doc string. -/
structure value_type 
where
  tgt : name
  doc : Option string

/-- `add_comm_prefix x s` returns `"comm_" ++ s` if `x = tt` and `s` otherwise. -/
/-- Dictionary used by `to_additive.guess_name` to autogenerate names. -/
/-- Autogenerate target name for `to_additive`. -/
/-- Return the provided target name or autogenerate one if one was not provided. -/
/-- the parser for the arguments to `to_additive` -/
/-- Add the `aux_attr` attribute to the structure fields of `src`
so that future uses of `to_additive` will map them to the corresponding `tgt` fields. -/
/--
The attribute `to_additive` can be used to automatically transport theorems
and definitions (but not inductive types and structures) from a multiplicative
theory to an additive theory.

To use this attribute, just write:

```
@[to_additive]
theorem mul_comm' {α} [comm_semigroup α] (x y : α) : x * y = y * x := comm_semigroup.mul_comm
```

This code will generate a theorem named `add_comm'`.  It is also
possible to manually specify the name of the new declaration, and
provide a documentation string:

```
@[to_additive add_foo "add_foo doc string"]
/-- foo doc string -/
