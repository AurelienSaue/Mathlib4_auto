/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.dynamics.fixed_points.basic
import Mathlib.topology.separation
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Topological properties of fixed points

Currently this file contains two lemmas:

- `is_fixed_pt_of_tendsto_iterate`: if `f^n(x) → y` and `f` is continuous at `y`, then `f y = y`;
- `is_closed_fixed_points`: the set of fixed points of a continuous map is a closed set.

## TODO

fixed points, iterates
-/

/-- If the iterates `f^[n] x` converge to `y` and `f` is continuous at `y`,
then `y` is a fixed point for `f`. -/
theorem is_fixed_pt_of_tendsto_iterate {α : Type u_1} [topological_space α] [t2_space α] {f : α → α}
    {x : α} {y : α} (hy : filter.tendsto (fun (n : ℕ) => nat.iterate f n x) filter.at_top (nhds y))
    (hf : continuous_at f y) : function.is_fixed_pt f y :=
  sorry

/-- The set of fixed points of a continuous map is a closed set. -/
theorem is_closed_fixed_points {α : Type u_1} [topological_space α] [t2_space α] {f : α → α}
    (hf : continuous f) : is_closed (function.fixed_points f) :=
  is_closed_eq hf continuous_id

end Mathlib