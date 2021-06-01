/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Simon Hudon

"The Following Are Equivalent" (tfae) :
Tactic for proving the equivalence of a set of proposition
using various implications between them.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.tfae
import Mathlib.tactic.scc
import Mathlib.PostPort

universes l 

namespace Mathlib

namespace tactic


namespace tfae


inductive arrow where
| right : arrow
| left_right : arrow
| left : arrow

end tfae


namespace interactive


/-- In a goal of the form `tfae [a₀, a₁, a₂]`,
`tfae_have : i → j` creates the assertion `aᵢ → aⱼ`. The other possible
notations are `tfae_have : i ← j` and `tfae_have : i ↔ j`. The user can
also provide a label for the assertion, as with `have`: `tfae_have h : i ↔ j`.
-/
/-- Finds all implications and equivalences in the context
to prove a goal of the form `tfae [...]`.
-/
end interactive


end tactic


/--
The `tfae` tactic suite is a set of tactics that help with proving that certain
end Mathlib