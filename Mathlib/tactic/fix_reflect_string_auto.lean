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

# Workaround for stack overflows with `has_reflect string`

The default `has_reflect string` instance in Lean only work for strings up to
few thousand characters.  Anything larger than that will trigger a stack overflow because
the string is represented as a very deeply nested expression:
https://github.com/leanprover-community/lean/issues/144

This file adds a higher-priority instance for `has_reflect string`, which
behaves exactly the same for small strings (up to 256 characters). Larger
strings are carefully converted into a call to `string.join`.

-/

/--
Splits a string into chunks of at most `size` characters.
-/
