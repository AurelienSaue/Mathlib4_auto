/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.dynamics.flow
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# ω-limits

For a function `ϕ : τ → α → β` where `β` is a topological space, we
define the ω-limit under `ϕ` of a set `s` in `α` with respect to
filter `f` on `τ`: an element `y : β` is in the ω-limit of `s` if the
forward images of `s` intersect arbitrarily small neighbourhoods of
`y` frequently "in the direction of `f`".

In practice `ϕ` is often a continuous monoid-act, but the definition
requires only that `ϕ` has a coercion to the appropriate function
type. In the case where `τ` is `ℕ` or `ℝ` and `f` is `at_top`, we
recover the usual definition of the ω-limit set as the set of all `y`
such that there exist sequences `(tₙ)`, `(xₙ)` such that `ϕ tₙ xₙ ⟶ y`
as `n ⟶ ∞`.

## Notations

The `omega_limit` locale provides the localised notation `ω` for
`omega_limit`, as well as `ω⁺` and `ω⁻` for `omega_limit at_top` and
`omega_limit at_bot` respectively for when the acting monoid is
endowed with an order.
-/

/-!
### Definition and notation
-/

/-- The ω-limit of a set `s` under `ϕ` with respect to a filter `f` is
    ⋂ u ∈ f, cl (ϕ u s). -/
def omega_limit {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) : set β :=
  set.Inter fun (u : set τ) => set.Inter fun (H : u ∈ f) => closure (set.image2 ϕ u s)

/-!
### Elementary properties
-/

theorem omega_limit_def {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) : omega_limit f ϕ s = set.Inter fun (u : set τ) => set.Inter fun (H : u ∈ f) => closure (set.image2 ϕ u s) :=
  rfl

theorem omega_limit_subset_of_tendsto {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (ϕ : τ → α → β) (s : set α) {m : τ → τ} {f₁ : filter τ} {f₂ : filter τ} (hf : filter.tendsto m f₁ f₂) : omega_limit f₁ (fun (t : τ) (x : α) => ϕ (m t) x) s ⊆ omega_limit f₂ ϕ s := sorry

theorem omega_limit_mono_left {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (ϕ : τ → α → β) (s : set α) {f₁ : filter τ} {f₂ : filter τ} (hf : f₁ ≤ f₂) : omega_limit f₁ ϕ s ⊆ omega_limit f₂ ϕ s :=
  omega_limit_subset_of_tendsto ϕ s (filter.tendsto_id' hf)

theorem omega_limit_mono_right {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) {s₁ : set α} {s₂ : set α} (hs : s₁ ⊆ s₂) : omega_limit f ϕ s₁ ⊆ omega_limit f ϕ s₂ :=
  set.bInter_subset_bInter_right
    fun (u : set τ) (hu : u ∈ fun (u : set τ) => u ∈ filter.sets f) => closure_mono (set.image2_subset set.subset.rfl hs)

theorem is_closed_omega_limit {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) : is_closed (omega_limit f ϕ s) :=
  is_closed_Inter fun (u : set τ) => is_closed_Inter fun (hu : u ∈ f) => is_closed_closure

theorem maps_to_omega_limit' {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (s : set α) {α' : Type u_4} {β' : Type u_5} [topological_space β'] {f : filter τ} {ϕ : τ → α → β} {ϕ' : τ → α' → β'} {ga : α → α'} {s' : set α'} (hs : set.maps_to ga s s') {gb : β → β'} (hg : filter.eventually (fun (t : τ) => set.eq_on (gb ∘ ϕ t) (ϕ' t ∘ ga) s) f) (hgc : continuous gb) : set.maps_to gb (omega_limit f ϕ s) (omega_limit f ϕ' s') := sorry

theorem maps_to_omega_limit {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (s : set α) {α' : Type u_4} {β' : Type u_5} [topological_space β'] {f : filter τ} {ϕ : τ → α → β} {ϕ' : τ → α' → β'} {ga : α → α'} {s' : set α'} (hs : set.maps_to ga s s') {gb : β → β'} (hg : ∀ (t : τ) (x : α), gb (ϕ t x) = ϕ' t (ga x)) (hgc : continuous gb) : set.maps_to gb (omega_limit f ϕ s) (omega_limit f ϕ' s') :=
  maps_to_omega_limit' s hs (filter.eventually_of_forall fun (t : τ) (x : α) (hx : x ∈ s) => hg t x) hgc

theorem omega_limit_image_eq {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (s : set α) {α' : Type u_4} (ϕ : τ → α' → β) (f : filter τ) (g : α → α') : omega_limit f ϕ (g '' s) = omega_limit f (fun (t : τ) (x : α) => ϕ t (g x)) s := sorry

theorem omega_limit_preimage_subset {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] {α' : Type u_4} (ϕ : τ → α' → β) (s : set α') (f : filter τ) (g : α → α') : omega_limit f (fun (t : τ) (x : α) => ϕ t (g x)) (g ⁻¹' s) ⊆ omega_limit f ϕ s :=
  maps_to_omega_limit (g ⁻¹' s) (set.maps_to_preimage g s) (fun (t : τ) (x : α) => rfl) continuous_id

/-!
### Equivalent definitions of the omega limit

The next few lemmas are various versions of the property
characterising ω-limits:
-/

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    preimages of an arbitrary neighbourhood of `y` frequently
    (w.r.t. `f`) intersects of `s`. -/
theorem mem_omega_limit_iff_frequently {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) (y : β) : y ∈ omega_limit f ϕ s ↔ ∀ (n : set β), n ∈ nhds y → filter.frequently (fun (t : τ) => set.nonempty (s ∩ ϕ t ⁻¹' n)) f := sorry

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    forward images of `s` frequently (w.r.t. `f`) intersect arbitrary
    neighbourhoods of `y`. -/
theorem mem_omega_limit_iff_frequently₂ {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) (y : β) : y ∈ omega_limit f ϕ s ↔ ∀ (n : set β), n ∈ nhds y → filter.frequently (fun (t : τ) => set.nonempty (ϕ t '' s ∩ n)) f := sorry

/-- An element `y` is in the ω-limit of `x` w.r.t. `f` if the forward
    images of `x` frequently (w.r.t. `f`) falls within an arbitrary
    neighbourhood of `y`. -/
theorem mem_omega_limit_singleton_iff_map_cluster_point {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (x : α) (y : β) : y ∈ omega_limit f ϕ (singleton x) ↔ map_cluster_pt y f fun (t : τ) => ϕ t x := sorry

/-!
### Set operations and omega limits
-/

theorem omega_limit_inter {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s₁ : set α) (s₂ : set α) : omega_limit f ϕ (s₁ ∩ s₂) ⊆ omega_limit f ϕ s₁ ∩ omega_limit f ϕ s₂ :=
  set.subset_inter (omega_limit_mono_right f ϕ (set.inter_subset_left s₁ s₂))
    (omega_limit_mono_right f ϕ (set.inter_subset_right s₁ s₂))

theorem omega_limit_Inter {τ : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type u_4} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (p : ι → set α) : omega_limit f ϕ (set.Inter fun (i : ι) => p i) ⊆ set.Inter fun (i : ι) => omega_limit f ϕ (p i) :=
  set.subset_Inter fun (i : ι) => omega_limit_mono_right f ϕ (set.Inter_subset (fun (i : ι) => p i) i)

theorem omega_limit_union {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s₁ : set α) (s₂ : set α) : omega_limit f ϕ (s₁ ∪ s₂) = omega_limit f ϕ s₁ ∪ omega_limit f ϕ s₂ := sorry

theorem omega_limit_Union {τ : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type u_4} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (p : ι → set α) : (set.Union fun (i : ι) => omega_limit f ϕ (p i)) ⊆ omega_limit f ϕ (set.Union fun (i : ι) => p i) := sorry

/-!
Different expressions for omega limits, useful for rewrites. In
particular, one may restrict the intersection to sets in `f` which are
subsets of some set `v` also in `f`.
-/

theorem omega_limit_eq_Inter {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) : omega_limit f ϕ s = set.Inter fun (u : ↥(filter.sets f)) => closure (set.image2 ϕ (↑u) s) :=
  set.bInter_eq_Inter (fun (u : set τ) => u ∈ filter.sets f) fun (u : set τ) (H : u ∈ f) => closure (set.image2 ϕ u s)

theorem omega_limit_eq_bInter_inter {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) {v : set τ} (hv : v ∈ f) : omega_limit f ϕ s = set.Inter fun (u : set τ) => set.Inter fun (H : u ∈ f) => closure (set.image2 ϕ (u ∩ v) s) := sorry

theorem omega_limit_eq_Inter_inter {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) {v : set τ} (hv : v ∈ f) : omega_limit f ϕ s = set.Inter fun (u : ↥(filter.sets f)) => closure (set.image2 ϕ (↑u ∩ v) s) := sorry

theorem omega_limit_subset_closure_fw_image {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) {u : set τ} (hu : u ∈ f) : omega_limit f ϕ s ⊆ closure (set.image2 ϕ u s) := sorry

/-!
### `ω-limits and compactness
-/

/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
theorem eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset' {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) {c : set β} (hc₁ : is_compact c) (hc₂ : ∃ (v : set τ), ∃ (H : v ∈ f), closure (set.image2 ϕ v s) ⊆ c) {n : set β} (hn₁ : is_open n) (hn₂ : omega_limit f ϕ s ⊆ n) : ∃ (u : set τ), ∃ (H : u ∈ f), closure (set.image2 ϕ u s) ⊆ n := sorry

/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
theorem eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) [t2_space β] {c : set β} (hc₁ : is_compact c) (hc₂ : filter.eventually (fun (t : τ) => set.maps_to (ϕ t) s c) f) {n : set β} (hn₁ : is_open n) (hn₂ : omega_limit f ϕ s ⊆ n) : ∃ (u : set τ), ∃ (H : u ∈ f), closure (set.image2 ϕ u s) ⊆ n := sorry

theorem eventually_maps_to_of_is_compact_absorbing_of_is_open_of_omega_limit_subset {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) [t2_space β] {c : set β} (hc₁ : is_compact c) (hc₂ : filter.eventually (fun (t : τ) => set.maps_to (ϕ t) s c) f) {n : set β} (hn₁ : is_open n) (hn₂ : omega_limit f ϕ s ⊆ n) : filter.eventually (fun (t : τ) => set.maps_to (ϕ t) s n) f := sorry

theorem eventually_closure_subset_of_is_open_of_omega_limit_subset {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) [compact_space β] {v : set β} (hv₁ : is_open v) (hv₂ : omega_limit f ϕ s ⊆ v) : ∃ (u : set τ), ∃ (H : u ∈ f), closure (set.image2 ϕ u s) ⊆ v :=
  eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset' f ϕ s compact_univ
    (Exists.intro set.univ (Exists.intro filter.univ_mem_sets (set.subset_univ (closure (set.image2 ϕ set.univ s))))) hv₁
    hv₂

theorem eventually_maps_to_of_is_open_of_omega_limit_subset {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) [compact_space β] {v : set β} (hv₁ : is_open v) (hv₂ : omega_limit f ϕ s ⊆ v) : filter.eventually (fun (t : τ) => set.maps_to (ϕ t) s v) f := sorry

/-- The ω-limit of a nonempty set w.r.t. a nontrivial filter is nonempty. -/
theorem nonempty_omega_limit_of_is_compact_absorbing {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) [filter.ne_bot f] {c : set β} (hc₁ : is_compact c) (hc₂ : ∃ (v : set τ), ∃ (H : v ∈ f), closure (set.image2 ϕ v s) ⊆ c) (hs : set.nonempty s) : set.nonempty (omega_limit f ϕ s) := sorry

theorem nonempty_omega_limit {τ : Type u_1} {α : Type u_2} {β : Type u_3} [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) [compact_space β] [filter.ne_bot f] (hs : set.nonempty s) : set.nonempty (omega_limit f ϕ s) :=
  nonempty_omega_limit_of_is_compact_absorbing f ϕ s compact_univ
    (Exists.intro set.univ (Exists.intro filter.univ_mem_sets (set.subset_univ (closure (set.image2 ϕ set.univ s))))) hs

/-!
### ω-limits of Flows by a Monoid
-/

namespace flow


theorem is_invariant_omega_limit {τ : Type u_1} [topological_space τ] [add_monoid τ] [has_continuous_add τ] {α : Type u_2} [topological_space α] (f : filter τ) (ϕ : flow τ α) (s : set α) (hf : ∀ (t : τ), filter.tendsto (Add.add t) f f) : is_invariant (⇑ϕ) (omega_limit f (⇑ϕ) s) := sorry

theorem omega_limit_image_subset {τ : Type u_1} [topological_space τ] [add_monoid τ] [has_continuous_add τ] {α : Type u_2} [topological_space α] (f : filter τ) (ϕ : flow τ α) (s : set α) (t : τ) (ht : filter.tendsto (fun (_x : τ) => _x + t) f f) : omega_limit f (⇑ϕ) (coe_fn ϕ t '' s) ⊆ omega_limit f (⇑ϕ) s := sorry

end flow


/-!
### ω-limits of Flows by a Group
-/

namespace flow


/-- the ω-limit of a forward image of `s` is the same as the ω-limit of `s`. -/
@[simp] theorem omega_limit_image_eq {τ : Type u_1} [topological_space τ] [add_comm_group τ] [topological_add_group τ] {α : Type u_2} [topological_space α] (f : filter τ) (ϕ : flow τ α) (s : set α) (hf : ∀ (t : τ), filter.tendsto (fun (_x : τ) => _x + t) f f) (t : τ) : omega_limit f (⇑ϕ) (coe_fn ϕ t '' s) = omega_limit f (⇑ϕ) s := sorry

theorem omega_limit_omega_limit {τ : Type u_1} [topological_space τ] [add_comm_group τ] [topological_add_group τ] {α : Type u_2} [topological_space α] (f : filter τ) (ϕ : flow τ α) (s : set α) (hf : ∀ (t : τ), filter.tendsto (Add.add t) f f) : omega_limit f (⇑ϕ) (omega_limit f (⇑ϕ) s) ⊆ omega_limit f (⇑ϕ) s := sorry

