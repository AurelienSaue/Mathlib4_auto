/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.metric_space.emetric_space
import PostPort

universes u_1 u_4 u_2 

namespace Mathlib

/-!
# `Gδ` sets

In this file we define `Gδ` sets and prove their basic properties.

## Main definitions

* `is_Gδ`: a set `s` is a `Gδ` set if it can be represented as an intersection
  of countably many open sets;

* `residual`: the filter of residual sets. A set `s` is called *residual* if it includes a dense
  `Gδ` set. In a Baire space (e.g., in a complete (e)metric space), residual sets form a filter.

  For technical reasons, we define `residual` in any topological space but the definition agrees
  with the description above only in Baire spaces.

## Main results

We prove that finite or countable intersections of Gδ sets is a Gδ set. We also prove that the
continuity set of a function from a topological space to an (e)metric space is a Gδ set.

## Tags

Gδ set, residual set
-/

/-- A Gδ set is a countable intersection of open sets. -/
def is_Gδ {α : Type u_1} [topological_space α] (s : set α)  :=
  ∃ (T : set (set α)), (∀ (t : set α), t ∈ T → is_open t) ∧ set.countable T ∧ s = ⋂₀T

/-- An open set is a Gδ set. -/
theorem is_open.is_Gδ {α : Type u_1} [topological_space α] {s : set α} (h : is_open s) : is_Gδ s := sorry

theorem is_Gδ_univ {α : Type u_1} [topological_space α] : is_Gδ set.univ :=
  is_open.is_Gδ is_open_univ

theorem is_Gδ_bInter_of_open {α : Type u_1} {ι : Type u_4} [topological_space α] {I : set ι} (hI : set.countable I) {f : ι → set α} (hf : ∀ (i : ι), i ∈ I → is_open (f i)) : is_Gδ (set.Inter fun (i : ι) => set.Inter fun (H : i ∈ I) => f i) := sorry

theorem is_Gδ_Inter_of_open {α : Type u_1} {ι : Type u_4} [topological_space α] [encodable ι] {f : ι → set α} (hf : ∀ (i : ι), is_open (f i)) : is_Gδ (set.Inter fun (i : ι) => f i) := sorry

/-- A countable intersection of Gδ sets is a Gδ set. -/
theorem is_Gδ_sInter {α : Type u_1} [topological_space α] {S : set (set α)} (h : ∀ (s : set α), s ∈ S → is_Gδ s) (hS : set.countable S) : is_Gδ (⋂₀S) := sorry

theorem is_Gδ_Inter {α : Type u_1} {ι : Type u_4} [topological_space α] [encodable ι] {s : ι → set α} (hs : ∀ (i : ι), is_Gδ (s i)) : is_Gδ (set.Inter fun (i : ι) => s i) :=
  is_Gδ_sInter (iff.mpr set.forall_range_iff hs) (set.countable_range s)

theorem is_Gδ_bInter {α : Type u_1} {ι : Type u_4} [topological_space α] {s : set ι} (hs : set.countable s) {t : (i : ι) → i ∈ s → set α} (ht : ∀ (i : ι) (H : i ∈ s), is_Gδ (t i H)) : is_Gδ (set.Inter fun (i : ι) => set.Inter fun (H : i ∈ s) => t i H) := sorry

theorem is_Gδ.inter {α : Type u_1} [topological_space α] {s : set α} {t : set α} (hs : is_Gδ s) (ht : is_Gδ t) : is_Gδ (s ∩ t) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_Gδ (s ∩ t))) set.inter_eq_Inter))
    (is_Gδ_Inter (iff.mpr bool.forall_bool { left := ht, right := hs }))

/-- The union of two Gδ sets is a Gδ set. -/
theorem is_Gδ.union {α : Type u_1} [topological_space α] {s : set α} {t : set α} (hs : is_Gδ s) (ht : is_Gδ t) : is_Gδ (s ∪ t) := sorry

theorem is_Gδ_set_of_continuous_at_of_countably_generated_uniformity {α : Type u_1} {β : Type u_2} [topological_space α] [uniform_space β] (hU : filter.is_countably_generated (uniformity β)) (f : α → β) : is_Gδ (set_of fun (x : α) => continuous_at f x) := sorry

/-- The set of points where a function is continuous is a Gδ set. -/
theorem is_Gδ_set_of_continuous_at {α : Type u_1} {β : Type u_2} [topological_space α] [emetric_space β] (f : α → β) : is_Gδ (set_of fun (x : α) => continuous_at f x) :=
  is_Gδ_set_of_continuous_at_of_countably_generated_uniformity emetric.uniformity_has_countable_basis f

/-- A set `s` is called *residual* if it includes a dense `Gδ` set. If `α` is a Baire space
(e.g., a complete metric space), then residual sets form a filter, see `mem_residual`.

For technical reasons we define the filter `residual` in any topological space but in a non-Baire
space it is not useful because it may contain some non-residual sets. -/
def residual (α : Type u_1) [topological_space α] : filter α :=
  infi fun (t : set α) => infi fun (ht : is_Gδ t) => infi fun (ht' : dense t) => filter.principal t

