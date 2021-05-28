/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.calculus.local_extr
import Mathlib.topology.algebra.affine
import PostPort

universes u_2 u_1 

namespace Mathlib

/-!
# Minima and maxima of convex functions

We show that if a function `f : E → β` is convex, then a local minimum is also
a global minimum, and likewise for concave functions.
-/

/--
Helper lemma for the more general case: `is_min_on.of_is_local_min_on_of_convex_on`.
-/
theorem is_min_on.of_is_local_min_on_of_convex_on_Icc {β : Type u_2} [linear_ordered_add_comm_group β] [semimodule ℝ β] [ordered_semimodule ℝ β] {f : ℝ → β} {a : ℝ} {b : ℝ} (a_lt_b : a < b) (h_local_min : is_local_min_on f (set.Icc a b) a) (h_conv : convex_on (set.Icc a b) f) (x : ℝ) (H : x ∈ set.Icc a b) : f a ≤ f x := sorry

/--
A local minimum of a convex function is a global minimum, restricted to a set `s`.
-/
theorem is_min_on.of_is_local_min_on_of_convex_on {E : Type u_1} {β : Type u_2} [add_comm_group E] [topological_space E] [module ℝ E] [topological_add_group E] [topological_vector_space ℝ E] [linear_ordered_add_comm_group β] [semimodule ℝ β] [ordered_semimodule ℝ β] {s : set E} {f : E → β} {a : E} (a_in_s : a ∈ s) (h_localmin : is_local_min_on f s a) (h_conv : convex_on s f) (x : E) (H : x ∈ s) : f a ≤ f x := sorry

/-- A local maximum of a concave function is a global maximum, restricted to a set `s`. -/
theorem is_max_on.of_is_local_max_on_of_concave_on {E : Type u_1} {β : Type u_2} [add_comm_group E] [topological_space E] [module ℝ E] [topological_add_group E] [topological_vector_space ℝ E] [linear_ordered_add_comm_group β] [semimodule ℝ β] [ordered_semimodule ℝ β] {s : set E} {f : E → β} {a : E} (a_in_s : a ∈ s) (h_localmax : is_local_max_on f s a) (h_conc : concave_on s f) (x : E) (H : x ∈ s) : f x ≤ f a :=
  is_min_on.of_is_local_min_on_of_convex_on a_in_s h_localmax h_conc

/-- A local minimum of a convex function is a global minimum. -/
theorem is_min_on.of_is_local_min_of_convex_univ {E : Type u_1} {β : Type u_2} [add_comm_group E] [topological_space E] [module ℝ E] [topological_add_group E] [topological_vector_space ℝ E] [linear_ordered_add_comm_group β] [semimodule ℝ β] [ordered_semimodule ℝ β] {f : E → β} {a : E} (h_local_min : is_local_min f a) (h_conv : convex_on set.univ f) (x : E) : f a ≤ f x :=
  is_min_on.of_is_local_min_on_of_convex_on (set.mem_univ a) (is_local_min.on h_local_min set.univ) h_conv x
    (set.mem_univ x)

/-- A local maximum of a concave function is a global maximum. -/
theorem is_max_on.of_is_local_max_of_convex_univ {E : Type u_1} {β : Type u_2} [add_comm_group E] [topological_space E] [module ℝ E] [topological_add_group E] [topological_vector_space ℝ E] [linear_ordered_add_comm_group β] [semimodule ℝ β] [ordered_semimodule ℝ β] {f : E → β} {a : E} (h_local_max : is_local_max f a) (h_conc : concave_on set.univ f) (x : E) : f x ≤ f a :=
  is_min_on.of_is_local_min_of_convex_univ h_local_max h_conc

