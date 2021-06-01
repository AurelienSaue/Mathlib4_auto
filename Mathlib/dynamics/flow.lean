/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.algebra.group
import Mathlib.logic.function.iterate
import Mathlib.PostPort

universes u_1 u_2 l u_3 

namespace Mathlib

/-!
# Flows and invariant sets

This file defines a flow on a topological space `α` by a topological
monoid `τ` as a continuous monoid-act of `τ` on `α`. Anticipating the
cases where `τ` is one of `ℕ`, `ℤ`, `ℝ⁺`, or `ℝ`, we use additive
notation for the monoids, though the definition does not require
commutativity.

A subset `s` of `α` is invariant under a family of maps `ϕₜ : α → α`
if `ϕₜ s ⊆ s` for all `t`. In many cases `ϕ` will be a flow on
`α`. For the cases where `ϕ` is a flow by an ordered (additive,
commutative) monoid, we additionally define forward invariance, where
`t` ranges over those elements which are nonnegative.

Additionally, we define such constructions as the restriction of a
flow onto an invariant subset, and the time-reveral of a flow by a
group.
-/

/-!
### Invariant sets
-/

/-- A set `s ⊆ α` is invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t` in `τ`. -/
def is_invariant {τ : Type u_1} {α : Type u_2} (ϕ : τ → α → α) (s : set α) :=
  ∀ (t : τ), set.maps_to (ϕ t) s s

theorem is_invariant_iff_image {τ : Type u_1} {α : Type u_2} (ϕ : τ → α → α) (s : set α) : is_invariant ϕ s ↔ ∀ (t : τ), ϕ t '' s ⊆ s := sorry

/-- A set `s ⊆ α` is forward-invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t ≥ 0`. -/
def is_fw_invariant {τ : Type u_1} {α : Type u_2} [preorder τ] [HasZero τ] (ϕ : τ → α → α) (s : set α) :=
  ∀ {t : τ}, 0 ≤ t → set.maps_to (ϕ t) s s

theorem is_invariant.is_fw_invariant {τ : Type u_1} {α : Type u_2} [preorder τ] [HasZero τ] {ϕ : τ → α → α} {s : set α} (h : is_invariant ϕ s) : is_fw_invariant ϕ s :=
  fun (t : τ) (ht : 0 ≤ t) => h t

/-- If `τ` is a `canonically_ordered_add_monoid` (e.g., `ℕ` or `ℝ≥0`), then the notions
`is_fw_invariant` and `is_invariant` are equivalent. -/
theorem is_fw_invariant.is_invariant {τ : Type u_1} {α : Type u_2} [canonically_ordered_add_monoid τ] {ϕ : τ → α → α} {s : set α} (h : is_fw_invariant ϕ s) : is_invariant ϕ s :=
  fun (t : τ) => h (zero_le t)

/-- If `τ` is a `canonically_ordered_add_monoid` (e.g., `ℕ` or `ℝ≥0`), then the notions
`is_fw_invariant` and `is_invariant` are equivalent. -/
theorem is_fw_invariant_iff_is_invariant {τ : Type u_1} {α : Type u_2} [canonically_ordered_add_monoid τ] {ϕ : τ → α → α} {s : set α} : is_fw_invariant ϕ s ↔ is_invariant ϕ s :=
  { mp := is_fw_invariant.is_invariant, mpr := is_invariant.is_fw_invariant }

/-!
### Flows
-/

/-- A flow on a topological space `α` by an a additive topological
    monoid `τ` is a continuous monoid action of `τ` on `α`.-/
structure flow (τ : Type u_1) [topological_space τ] [add_monoid τ] [has_continuous_add τ] (α : Type u_2) [topological_space α] 
where
  to_fun : τ → α → α
  cont' : continuous (function.uncurry to_fun)
  map_add' : ∀ (t₁ t₂ : τ) (x : α), to_fun (t₁ + t₂) x = to_fun t₁ (to_fun t₂ x)
  map_zero' : ∀ (x : α), to_fun 0 x = x

namespace flow


protected instance inhabited {τ : Type u_1} [add_monoid τ] [topological_space τ] [has_continuous_add τ] {α : Type u_2} [topological_space α] : Inhabited (flow τ α) :=
  { default := mk (fun (_x : τ) (x : α) => x) continuous_snd sorry sorry }

protected instance has_coe_to_fun {τ : Type u_1} [add_monoid τ] [topological_space τ] [has_continuous_add τ] {α : Type u_2} [topological_space α] : has_coe_to_fun (flow τ α) :=
  has_coe_to_fun.mk (fun (x : flow τ α) => τ → α → α) to_fun

theorem ext {τ : Type u_1} [add_monoid τ] [topological_space τ] [has_continuous_add τ] {α : Type u_2} [topological_space α] {ϕ₁ : flow τ α} {ϕ₂ : flow τ α} : (∀ (t : τ) (x : α), coe_fn ϕ₁ t x = coe_fn ϕ₂ t x) → ϕ₁ = ϕ₂ := sorry

protected theorem continuous {τ : Type u_1} [add_monoid τ] [topological_space τ] [has_continuous_add τ] {α : Type u_2} [topological_space α] (ϕ : flow τ α) {β : Type u_3} [topological_space β] {t : β → τ} (ht : continuous t) {f : β → α} (hf : continuous f) : continuous fun (x : β) => coe_fn ϕ (t x) (f x) :=
  continuous.comp (cont' ϕ) (continuous.prod_mk ht hf)

theorem Mathlib.continuous.flow {τ : Type u_1} [add_monoid τ] [topological_space τ] [has_continuous_add τ] {α : Type u_2} [topological_space α] (ϕ : flow τ α) {β : Type u_3} [topological_space β] {t : β → τ} (ht : continuous t) {f : β → α} (hf : continuous f) : continuous fun (x : β) => coe_fn ϕ (t x) (f x) :=
  flow.continuous

theorem map_add {τ : Type u_1} [add_monoid τ] [topological_space τ] [has_continuous_add τ] {α : Type u_2} [topological_space α] (ϕ : flow τ α) (t₁ : τ) (t₂ : τ) (x : α) : coe_fn ϕ (t₁ + t₂) x = coe_fn ϕ t₁ (coe_fn ϕ t₂ x) :=
  map_add' ϕ t₁ t₂ x

@[simp] theorem map_zero {τ : Type u_1} [add_monoid τ] [topological_space τ] [has_continuous_add τ] {α : Type u_2} [topological_space α] (ϕ : flow τ α) : coe_fn ϕ 0 = id :=
  funext (map_zero' ϕ)

theorem map_zero_apply {τ : Type u_1} [add_monoid τ] [topological_space τ] [has_continuous_add τ] {α : Type u_2} [topological_space α] (ϕ : flow τ α) (x : α) : coe_fn ϕ 0 x = x :=
  map_zero' ϕ x

/-- Iterations of a continuous function from a topological space `α`
    to itself defines a semiflow by `ℕ` on `α`. -/
def from_iter {α : Type u_2} [topological_space α] {g : α → α} (h : continuous g) : flow ℕ α :=
  mk (fun (n : ℕ) (x : α) => nat.iterate g n x) sorry (function.iterate_add_apply g) sorry

/-- Restriction of a flow onto an invariant set. -/
def restrict {τ : Type u_1} [add_monoid τ] [topological_space τ] [has_continuous_add τ] {α : Type u_2} [topological_space α] (ϕ : flow τ α) {s : set α} (h : is_invariant (⇑ϕ) s) : flow τ ↥s :=
  mk (fun (t : τ) => set.maps_to.restrict (coe_fn ϕ t) s s (h t)) sorry sorry sorry

end flow


namespace flow


theorem is_invariant_iff_image_eq {τ : Type u_1} [add_comm_group τ] [topological_space τ] [topological_add_group τ] {α : Type u_2} [topological_space α] (ϕ : flow τ α) (s : set α) : is_invariant (⇑ϕ) s ↔ ∀ (t : τ), coe_fn ϕ t '' s = s := sorry

/-- The time-reversal of a flow `ϕ` by a (commutative, additive) group
    is defined `ϕ.reverse t x = ϕ (-t) x`. -/
def reverse {τ : Type u_1} [add_comm_group τ] [topological_space τ] [topological_add_group τ] {α : Type u_2} [topological_space α] (ϕ : flow τ α) : flow τ α :=
  mk (fun (t : τ) => coe_fn ϕ (-t)) sorry sorry sorry

/-- The map `ϕ t` as a homeomorphism. -/
def to_homeomorph {τ : Type u_1} [add_comm_group τ] [topological_space τ] [topological_add_group τ] {α : Type u_2} [topological_space α] (ϕ : flow τ α) (t : τ) : α ≃ₜ α :=
  homeomorph.mk (equiv.mk (coe_fn ϕ t) (coe_fn ϕ (-t)) sorry sorry)

theorem image_eq_preimage {τ : Type u_1} [add_comm_group τ] [topological_space τ] [topological_add_group τ] {α : Type u_2} [topological_space α] (ϕ : flow τ α) (t : τ) (s : set α) : coe_fn ϕ t '' s = coe_fn ϕ (-t) ⁻¹' s :=
  equiv.image_eq_preimage (homeomorph.to_equiv (to_homeomorph ϕ t)) s

