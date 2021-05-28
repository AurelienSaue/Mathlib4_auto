/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.algebra.continuous_functions
import Mathlib.linear_algebra.affine_space.affine_map
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Topological properties of affine spaces and maps

For now, this contains only a few facts regarding the continuity of affine maps in the special
case when the point space and vector space are the same.
-/

namespace affine_map


/-
TODO: Deal with the case where the point spaces are different from the vector spaces.
-/

/-- An affine map is continuous iff its underlying linear map is continuous. -/
theorem continuous_iff {R : Type u_1} {E : Type u_2} {F : Type u_3} [ring R] [add_comm_group E] [semimodule R E] [topological_space E] [add_comm_group F] [semimodule R F] [topological_space F] [topological_add_group F] {f : affine_map R E F} : continuous ⇑f ↔ continuous ⇑(linear f) := sorry

/-- The line map is continuous. -/
theorem line_map_continuous {R : Type u_1} {F : Type u_3} [ring R] [add_comm_group F] [semimodule R F] [topological_space F] [topological_add_group F] [topological_space R] [topological_semimodule R F] {p : F} {v : F} : continuous ⇑(line_map p v) :=
  iff.mpr continuous_iff (continuous.add (continuous.smul continuous_id continuous_const) continuous_const)

