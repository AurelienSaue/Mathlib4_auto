/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.algebra.ordered
import Mathlib.data.set.intervals.proj_Icc
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Projection onto a closed interval

In this file we prove that the projection `set.proj_Icc f a b h` is a quotient map, and use it
to show that `Icc_extend h f` is continuous if and only if `f` is continuous.
-/

theorem continuous_proj_Icc {α : Type u_1} [topological_space α] [linear_order α] [order_topology α]
    {a : α} {b : α} {h : a ≤ b} : continuous (set.proj_Icc a b h) :=
  continuous_subtype_mk (fun (x : α) => set.proj_Icc._proof_1 a b h x)
    (continuous.max continuous_const (continuous.min continuous_const continuous_id))

theorem quotient_map_proj_Icc {α : Type u_1} [topological_space α] [linear_order α]
    [order_topology α] {a : α} {b : α} {h : a ≤ b} : quotient_map (set.proj_Icc a b h) :=
  sorry

@[simp] theorem continuous_Icc_extend_iff {α : Type u_1} {β : Type u_2} [topological_space α]
    [linear_order α] [order_topology α] [topological_space β] {a : α} {b : α} {h : a ≤ b}
    {f : ↥(set.Icc a b) → β} : continuous (set.Icc_extend h f) ↔ continuous f :=
  iff.symm (quotient_map.continuous_iff quotient_map_proj_Icc)

theorem continuous.Icc_extend {α : Type u_1} {β : Type u_2} [topological_space α] [linear_order α]
    [order_topology α] [topological_space β] {a : α} {b : α} {h : a ≤ b} {f : ↥(set.Icc a b) → β}
    (hf : continuous f) : continuous (set.Icc_extend h f) :=
  continuous.comp hf continuous_proj_Icc

end Mathlib