/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.option.defs
import Mathlib.data.list.defs
import PostPort

namespace Mathlib

/-!
# rb_map

This file defines additional operations on native rb_maps and rb_sets.
These structures are defined in core in `init.meta.rb_map`. They are meta objects,
and are generally the most efficient dictionary structures to use for pure metaprogramming right now.
-/

namespace native


/-! ### Declarations about `rb_set` -/

namespace rb_set


