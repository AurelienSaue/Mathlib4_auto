/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import PrePort
import Lean3Lib.init.default
import PostPort

namespace Mathlib

/-!
# Changing universes of types in meta-code

This file defines the meta type `uchange (α : Type v) : Type u`, which
permits us to change the universe of a type analogously to `ulift`.
However since `uchange` is meta, it can both lift and lower the universe.

The implementation of `uchange` is efficient. Both `uchange.up` and
`uchange.down` compile to no-ops.
-/

/--
`unchecked_cast' a : β` performs an unchecked cast of `(a : α)` to `β`.

Unlike `unchecked_cast`, it can cast across universes. The VM implementation
is guaranteed to be the identity.
-/
