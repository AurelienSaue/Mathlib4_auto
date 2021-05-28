/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.uniform_space.separation
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Compact separated uniform spaces

## Main statements

* `compact_space_uniformity`: On a separated compact uniform space, the topology determines the
  uniform structure, entourages are exactly the neighborhoods of the diagonal.
* `uniform_space_of_compact_t2`: every compact T2 topological structure is induced by a uniform
  structure. This uniform structure is described in the previous item.
* Heine-Cantor theorem: continuous functions on compact separated uniform spaces with values in
  uniform spaces are automatically uniformly continuous. There are several variations, the main one
  is `compact_space.uniform_continuous_of_continuous`.

## Implementation notes

The construction `uniform_space_of_compact_t2` is not declared as an instance, as it would badly
loop.

## tags

uniform space, uniform continuity, compact space
-/

/-!
### Uniformity on compact separated spaces
-/

/-- On a separated compact uniform space, the topology determines the uniform structure, entourages
are exactly the neighborhoods of the diagonal. -/
theorem compact_space_uniformity {α : Type u_1} [uniform_space α] [compact_space α] [separated_space α] : uniformity α = supr fun (x : α) => nhds (x, x) := sorry

theorem unique_uniformity_of_compact_t2 {α : Type u_1} [t : topological_space α] [compact_space α] [t2_space α] {u : uniform_space α} {u' : uniform_space α} (h : uniform_space.to_topological_space = t) (h' : uniform_space.to_topological_space = t) : u = u' := sorry

/-- The unique uniform structure inducing a given compact Hausdorff topological structure. -/
def uniform_space_of_compact_t2 {α : Type (max (max u_1 u_2 u_3) u_2)} [topological_space α] [compact_space α] [t2_space α] : uniform_space α :=
  uniform_space.mk (uniform_space.core.mk (supr fun (x : α) => nhds (x, x)) sorry sorry sorry) sorry

/-!
### Heine-Cantor theorem
-/

/-- Heine-Cantor: a continuous function on a compact separated uniform space is uniformly
continuous. -/
theorem compact_space.uniform_continuous_of_continuous {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] [compact_space α] [separated_space α] {f : α → β} (h : continuous f) : uniform_continuous f := sorry

/-- Heine-Cantor: a continuous function on a compact separated set of a uniform space is
uniformly continuous. -/
theorem is_compact.uniform_continuous_on_of_continuous' {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] {s : set α} {f : α → β} (hs : is_compact s) (hs' : is_separated s) (hf : continuous_on f s) : uniform_continuous_on f s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (uniform_continuous_on f s)) (propext uniform_continuous_on_iff_restrict)))
    (compact_space.uniform_continuous_of_continuous
      (eq.mp (Eq._oldrec (Eq.refl (continuous_on f s)) (propext continuous_on_iff_continuous_restrict)) hf))

/-- Heine-Cantor: a continuous function on a compact set of a separated uniform space
is uniformly continuous. -/
theorem is_compact.uniform_continuous_on_of_continuous {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β] [separated_space α] {s : set α} {f : α → β} (hs : is_compact s) (hf : continuous_on f s) : uniform_continuous_on f s :=
  is_compact.uniform_continuous_on_of_continuous' hs (is_separated_of_separated_space s) hf

