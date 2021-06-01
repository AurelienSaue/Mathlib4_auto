/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

/-!
## `protected` and `protect_proj` user attributes

`protected` is an attribute to protect a declaration.
If a declaration `foo.bar` is marked protected, then it must be referred to
by its full name `foo.bar`, even when the `foo` namespace is open.

`protect_proj` attribute to protect the projections of a structure.
If a structure `foo` is marked with the `protect_proj` user attribute, then
all of the projections become protected.

`protect_proj without bar baz` will protect all projections except for `bar` and `baz`.

# Examples

In this example all of `foo.bar`, `foo.baz` and `foo.qux` will be protected.
```
@[protect_proj] structure foo : Type :=
(bar : unit) (baz : unit) (qux : unit)
```

The following code example define the structure `foo`, and the projections `foo.qux`
will be protected, but not `foo.baz` or `foo.bar`

```
@[protect_proj without baz bar] structure foo : Type :=
(bar : unit) (baz : unit) (qux : unit)
```
-/

namespace tactic


/--
Attribute to protect a declaration.
If a declaration `foo.bar` is marked protected, then it must be referred to
by its full name `foo.bar`, even when the `foo` namespace is open.

Protectedness is a built in parser feature that is independent of this attribute.
A declaration may be protected even if it does not have the `@[protected]` attribute.
This provides a convenient way to protect many declarations at once.
-/
/-- Tactic that is executed when a structure is marked with the `protect_proj` attribute -/
/--
Attribute to protect the projections of a structure.
If a structure `foo` is marked with the `protect_proj` user attribute, then
all of the projections become protected, meaning they must always be referred to by
their full name `foo.bar`, even when the `foo` namespace is open.

`protect_proj without bar baz` will protect all projections except for `bar` and `baz`.

```lean
@[protect_proj without baz bar] structure foo : Type :=
(bar : unit) (baz : unit) (qux : unit)
```
-/
end Mathlib