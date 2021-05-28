/-
This file imports many useful tactics ("the kitchen sink").

You can use `import tactic` at the beginning of your file to get everything.
(Although you may want to strip things down when you're polishing.)

Because this file imports some complicated tactics, it has many transitive dependencies
(which of course may not use `import tactic`, and must import selectively).

As (non-exhaustive) examples, these includes things like:
* algebra.group_power
* algebra.ordered_ring
* data.rat
* data.nat.prime
* data.list.perm
* data.set.lattice
* data.equiv.encodable.basic
* order.complete_lattice
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.basic
import Mathlib.tactic.abel
import Mathlib.tactic.ring_exp
import Mathlib.tactic.noncomm_ring
import Mathlib.tactic.linarith.default
import Mathlib.tactic.omega.default
import Mathlib.tactic.tfae
import Mathlib.tactic.apply_fun
import Mathlib.tactic.interval_cases
import Mathlib.tactic.reassoc_axiom
import Mathlib.tactic.slice
import Mathlib.tactic.subtype_instance
import Mathlib.tactic.derive_fintype
import Mathlib.tactic.group
import Mathlib.tactic.cancel_denoms
import Mathlib.tactic.zify
import Mathlib.tactic.transport
import Mathlib.tactic.unfold_cases
import Mathlib.tactic.field_simp
import PostPort

namespace Mathlib

