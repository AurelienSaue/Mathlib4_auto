/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.filter.basic
import Mathlib.data.set.countable
import PostPort

universes u_2 l u_1 

namespace Mathlib

/-!
# Filters with countable intersection property

In this file we define `countable_Inter_filter` to be the class of filters with the following
property: for any countable collection of sets `s ∈ l` their intersection belongs to `l` as well.

Two main examples are the `residual` filter defined in `topology.metric_space.baire` and
the `measure.ae` filter defined in `measure_theory.measure_space`.
-/

/-- A filter `l` has the countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
class countable_Inter_filter {α : Type u_2} (l : filter α) 
where
  countable_sInter_mem_sets' : ∀ {S : set (set α)}, set.countable S → (∀ (s : set α), s ∈ S → s ∈ l) → ⋂₀S ∈ l

theorem countable_sInter_mem_sets {α : Type u_2} {l : filter α} [countable_Inter_filter l] {S : set (set α)} (hSc : set.countable S) : ⋂₀S ∈ l ↔ ∀ (s : set α), s ∈ S → s ∈ l :=
  { mp := fun (hS : ⋂₀S ∈ l) (s : set α) (hs : s ∈ S) => filter.mem_sets_of_superset hS (set.sInter_subset_of_mem hs),
    mpr := countable_Inter_filter.countable_sInter_mem_sets' hSc }

theorem countable_Inter_mem_sets {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] [encodable ι] {s : ι → set α} : (set.Inter fun (i : ι) => s i) ∈ l ↔ ∀ (i : ι), s i ∈ l :=
  set.sInter_range s ▸ iff.trans (countable_sInter_mem_sets (set.countable_range s)) set.forall_range_iff

theorem countable_bInter_mem_sets {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] {S : set ι} (hS : set.countable S) {s : (i : ι) → i ∈ S → set α} : (set.Inter fun (i : ι) => set.Inter fun (H : i ∈ S) => s i H) ∈ l ↔ ∀ (i : ι) (H : i ∈ S), s i H ∈ l := sorry

theorem eventually_countable_forall {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] [encodable ι] {p : α → ι → Prop} : filter.eventually (fun (x : α) => ∀ (i : ι), p x i) l ↔ ∀ (i : ι), filter.eventually (fun (x : α) => p x i) l := sorry

theorem eventually_countable_ball {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] {S : set ι} (hS : set.countable S) {p : α → (i : ι) → i ∈ S → Prop} : filter.eventually (fun (x : α) => ∀ (i : ι) (H : i ∈ S), p x i H) l ↔
  ∀ (i : ι) (H : i ∈ S), filter.eventually (fun (x : α) => p x i H) l := sorry

theorem eventually_le.countable_Union {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] [encodable ι] {s : ι → set α} {t : ι → set α} (h : ∀ (i : ι), filter.eventually_le l (s i) (t i)) : filter.eventually_le l (set.Union fun (i : ι) => s i) (set.Union fun (i : ι) => t i) :=
  filter.eventually.mono (iff.mpr eventually_countable_forall h)
    fun (x : α) (hst : ∀ (i : ι), s i x ≤ t i x) (hs : set.Union (fun (i : ι) => s i) x) =>
      iff.mpr set.mem_Union (Exists.imp hst (iff.mp set.mem_Union hs))

theorem eventually_eq.countable_Union {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] [encodable ι] {s : ι → set α} {t : ι → set α} (h : ∀ (i : ι), filter.eventually_eq l (s i) (t i)) : filter.eventually_eq l (set.Union fun (i : ι) => s i) (set.Union fun (i : ι) => t i) :=
  filter.eventually_le.antisymm (eventually_le.countable_Union fun (i : ι) => filter.eventually_eq.le (h i))
    (eventually_le.countable_Union fun (i : ι) => filter.eventually_eq.le (filter.eventually_eq.symm (h i)))

theorem eventually_le.countable_bUnion {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] {S : set ι} (hS : set.countable S) {s : (i : ι) → i ∈ S → set α} {t : (i : ι) → i ∈ S → set α} (h : ∀ (i : ι) (H : i ∈ S), filter.eventually_le l (s i H) (t i H)) : filter.eventually_le l (set.Union fun (i : ι) => set.Union fun (H : i ∈ S) => s i H)
  (set.Union fun (i : ι) => set.Union fun (H : i ∈ S) => t i H) := sorry

theorem eventually_eq.countable_bUnion {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] {S : set ι} (hS : set.countable S) {s : (i : ι) → i ∈ S → set α} {t : (i : ι) → i ∈ S → set α} (h : ∀ (i : ι) (H : i ∈ S), filter.eventually_eq l (s i H) (t i H)) : filter.eventually_eq l (set.Union fun (i : ι) => set.Union fun (H : i ∈ S) => s i H)
  (set.Union fun (i : ι) => set.Union fun (H : i ∈ S) => t i H) := sorry

theorem eventually_le.countable_Inter {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] [encodable ι] {s : ι → set α} {t : ι → set α} (h : ∀ (i : ι), filter.eventually_le l (s i) (t i)) : filter.eventually_le l (set.Inter fun (i : ι) => s i) (set.Inter fun (i : ι) => t i) :=
  filter.eventually.mono (iff.mpr eventually_countable_forall h)
    fun (x : α) (hst : ∀ (i : ι), s i x ≤ t i x) (hs : set.Inter (fun (i : ι) => s i) x) =>
      iff.mpr set.mem_Inter fun (i : ι) => hst i (iff.mp set.mem_Inter hs i)

theorem eventually_eq.countable_Inter {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] [encodable ι] {s : ι → set α} {t : ι → set α} (h : ∀ (i : ι), filter.eventually_eq l (s i) (t i)) : filter.eventually_eq l (set.Inter fun (i : ι) => s i) (set.Inter fun (i : ι) => t i) :=
  filter.eventually_le.antisymm (eventually_le.countable_Inter fun (i : ι) => filter.eventually_eq.le (h i))
    (eventually_le.countable_Inter fun (i : ι) => filter.eventually_eq.le (filter.eventually_eq.symm (h i)))

theorem eventually_le.countable_bInter {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] {S : set ι} (hS : set.countable S) {s : (i : ι) → i ∈ S → set α} {t : (i : ι) → i ∈ S → set α} (h : ∀ (i : ι) (H : i ∈ S), filter.eventually_le l (s i H) (t i H)) : filter.eventually_le l (set.Inter fun (i : ι) => set.Inter fun (H : i ∈ S) => s i H)
  (set.Inter fun (i : ι) => set.Inter fun (H : i ∈ S) => t i H) := sorry

theorem eventually_eq.countable_bInter {ι : Type u_1} {α : Type u_2} {l : filter α} [countable_Inter_filter l] {S : set ι} (hS : set.countable S) {s : (i : ι) → i ∈ S → set α} {t : (i : ι) → i ∈ S → set α} (h : ∀ (i : ι) (H : i ∈ S), filter.eventually_eq l (s i H) (t i H)) : filter.eventually_eq l (set.Inter fun (i : ι) => set.Inter fun (H : i ∈ S) => s i H)
  (set.Inter fun (i : ι) => set.Inter fun (H : i ∈ S) => t i H) := sorry

protected instance countable_Inter_filter_principal {α : Type u_2} (s : set α) : countable_Inter_filter (filter.principal s) :=
  countable_Inter_filter.mk
    fun (S : set (set α)) (hSc : set.countable S) (hS : ∀ (s_1 : set α), s_1 ∈ S → s_1 ∈ filter.principal s) =>
      set.subset_sInter hS

protected instance countable_Inter_filter_bot {α : Type u_2} : countable_Inter_filter ⊥ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (countable_Inter_filter ⊥)) (Eq.symm filter.principal_empty)))
    (Mathlib.countable_Inter_filter_principal ∅)

protected instance countable_Inter_filter_top {α : Type u_2} : countable_Inter_filter ⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (countable_Inter_filter ⊤)) (Eq.symm filter.principal_univ)))
    (Mathlib.countable_Inter_filter_principal set.univ)

/-- Infimum of two `countable_Inter_filter`s is a `countable_Inter_filter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
protected instance countable_Inter_filter_inf {α : Type u_2} (l₁ : filter α) (l₂ : filter α) [countable_Inter_filter l₁] [countable_Inter_filter l₂] : countable_Inter_filter (l₁ ⊓ l₂) := sorry

/-- Supremum of two `countable_Inter_filter`s is a `countable_Inter_filter`. -/
protected instance countable_Inter_filter_sup {α : Type u_2} (l₁ : filter α) (l₂ : filter α) [countable_Inter_filter l₁] [countable_Inter_filter l₂] : countable_Inter_filter (l₁ ⊔ l₂) :=
  countable_Inter_filter.mk
    fun (S : set (set α)) (hSc : set.countable S) (hS : ∀ (s : set α), s ∈ S → s ∈ l₁ ⊔ l₂) =>
      { left := iff.mpr (countable_sInter_mem_sets hSc) fun (s : set α) (hs : s ∈ S) => and.left (hS s hs),
        right := iff.mpr (countable_sInter_mem_sets hSc) fun (s : set α) (hs : s ∈ S) => and.right (hS s hs) }

