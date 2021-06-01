/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.algebra.module
import Mathlib.topology.instances.real
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Continuous additive maps are `ℝ`-linear

In this file we prove that a continuous map `f : E →+ F` between two topological vector spaces
over `ℝ` is `ℝ`-linear
-/

namespace add_monoid_hom


/-- A continuous additive map between two vector spaces over `ℝ` is `ℝ`-linear. -/
theorem map_real_smul {E : Type u_1} [add_comm_group E] [vector_space ℝ E] [topological_space E]
    [topological_vector_space ℝ E] {F : Type u_2} [add_comm_group F] [vector_space ℝ F]
    [topological_space F] [topological_vector_space ℝ F] [t2_space F] (f : E →+ F)
    (hf : continuous ⇑f) (c : ℝ) (x : E) : coe_fn f (c • x) = c • coe_fn f x :=
  sorry

/-- Reinterpret a continuous additive homomorphism between two real vector spaces
as a continuous real-linear map. -/
def to_real_linear_map {E : Type u_1} [add_comm_group E] [vector_space ℝ E] [topological_space E]
    [topological_vector_space ℝ E] {F : Type u_2} [add_comm_group F] [vector_space ℝ F]
    [topological_space F] [topological_vector_space ℝ F] [t2_space F] (f : E →+ F)
    (hf : continuous ⇑f) : continuous_linear_map ℝ E F :=
  continuous_linear_map.mk (linear_map.mk ⇑f sorry (map_real_smul f hf))

@[simp] theorem coe_to_real_linear_map {E : Type u_1} [add_comm_group E] [vector_space ℝ E]
    [topological_space E] [topological_vector_space ℝ E] {F : Type u_2} [add_comm_group F]
    [vector_space ℝ F] [topological_space F] [topological_vector_space ℝ F] [t2_space F]
    (f : E →+ F) (hf : continuous ⇑f) : ⇑(to_real_linear_map f hf) = ⇑f :=
  rfl

end Mathlib