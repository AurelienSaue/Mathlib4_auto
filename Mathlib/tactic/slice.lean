/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.category.default
import Mathlib.PostPort

namespace Mathlib

-- TODO someone might like to generalise this tactic to work with other associative structures.

namespace tactic


end tactic


namespace conv


namespace interactive


/--
`slice` is a conv tactic; if the current focus is a composition of several morphisms,
`slice a b` reassociates as needed, and zooms in on the `a`-th through `b`-th morphisms.

Thus if the current focus is `(a ≫ b) ≫ ((c ≫ d) ≫ e)`, then `slice 2 3` zooms to `b ≫ c`.
 -/
end interactive


end conv


namespace tactic


namespace interactive


/--
`slice_lhs a b { tac }` zooms to the left hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
/--
`slice_rhs a b { tac }` zooms to the right hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
end interactive


end tactic


/--
`slice_lhs a b { tac }` zooms to the left hand side, uses associativity for categorical
