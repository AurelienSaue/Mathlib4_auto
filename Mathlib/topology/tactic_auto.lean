/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.auto_cases
import Mathlib.tactic.tidy
import Mathlib.tactic.with_local_reducibility
import Mathlib.tactic.show_term
import Mathlib.topology.basic
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Tactics for topology

Currently we have one domain-specific tactic for topology: `continuity`.

-/

/-!
### `continuity` tactic

Automatically solve goals of the form `continuous f`.

Mark lemmas with `@[continuity]` to add them to the set of lemmas
used by `continuity`. Note: `to_additive` doesn't know yet how to
copy the attribute to the additive version.
-/

/-- User attribute used to mark tactics used by `continuity`. -/
-- Mark some continuity lemmas already defined in `topology.basic`

-- As we will be using `apply_rules` with `md := semireducible`,

-- we need another version of `continuous_id`.

theorem continuous_id' {α : Type u_1} [topological_space α] : continuous fun (a : α) => a :=
  continuous_id

namespace tactic


/--
Tactic to apply `continuous.comp` when appropriate.

Applying `continuous.comp` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove continuous is actually
  constant, and that constant is a function application `f z`, then
  continuous.comp would produce new goals `continuous f`, `continuous
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply continuous_const.

* continuous.comp will always succeed on `continuous (λ x, f x)` and
  produce new goals `continuous (λ x, x)`, `continuous f`. We detect
  this by failing if a new goal can be closed by applying
  continuous_id.
-/
/-- List of tactics used by `continuity` internally. -/
namespace interactive


/--
Solve goals of the form `continuous f`. `continuity?` reports back the proof term it found.
-/
/-- Version of `continuity` for use with auto_param. -/
/--
`continuity` solves goals of the form `continuous f` by applying lemmas tagged with the
end Mathlib