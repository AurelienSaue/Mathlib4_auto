/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.metric_space.lipschitz
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Antilipschitz functions

We say that a map `f : α → β` between two (extended) metric spaces is
`antilipschitz_with K`, `K ≥ 0`, if for all `x, y` we have `edist x y ≤ K * edist (f x) (f y)`.
For a metric space, the latter inequality is equivalent to `dist x y ≤ K * dist (f x) (f y)`.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjuction in the definition and have
coercions both to `ℝ` and `ennreal`. We do not require `0 < K` in the definition, mostly because
we do not have a `posreal` type.
-/

/-- We say that `f : α → β` is `antilipschitz_with K` if for any two points `x`, `y` we have
`K * edist x y ≤ edist (f x) (f y)`. -/
def antilipschitz_with {α : Type u_1} {β : Type u_2} [emetric_space α] [emetric_space β]
    (K : nnreal) (f : α → β) :=
  ∀ (x y : α), edist x y ≤ ↑K * edist (f x) (f y)

theorem antilipschitz_with_iff_le_mul_dist {α : Type u_1} {β : Type u_2} [metric_space α]
    [metric_space β] {K : nnreal} {f : α → β} :
    antilipschitz_with K f ↔ ∀ (x y : α), dist x y ≤ ↑K * dist (f x) (f y) :=
  sorry

theorem antilipschitz_with.of_le_mul_dist {α : Type u_1} {β : Type u_2} [metric_space α]
    [metric_space β] {K : nnreal} {f : α → β} :
    (∀ (x y : α), dist x y ≤ ↑K * dist (f x) (f y)) → antilipschitz_with K f :=
  iff.mpr antilipschitz_with_iff_le_mul_dist

theorem antilipschitz_with.mul_le_dist {α : Type u_1} {β : Type u_2} [metric_space α]
    [metric_space β] {K : nnreal} {f : α → β} (hf : antilipschitz_with K f) (x : α) (y : α) :
    ↑(K⁻¹) * dist x y ≤ dist (f x) (f y) :=
  sorry

namespace antilipschitz_with


/-- Extract the constant from `hf : antilipschitz_with K f`. This is useful, e.g.,
if `K` is given by a long formula, and we want to reuse this value. -/
protected def K {α : Type u_1} {β : Type u_2} [emetric_space α] [emetric_space β] {K : nnreal}
    {f : α → β} (hf : antilipschitz_with K f) : nnreal :=
  K

protected theorem injective {α : Type u_1} {β : Type u_2} [emetric_space α] [emetric_space β]
    {K : nnreal} {f : α → β} (hf : antilipschitz_with K f) : function.injective f :=
  sorry

theorem mul_le_edist {α : Type u_1} {β : Type u_2} [emetric_space α] [emetric_space β] {K : nnreal}
    {f : α → β} (hf : antilipschitz_with K f) (x : α) (y : α) :
    ↑(K⁻¹) * edist x y ≤ edist (f x) (f y) :=
  sorry

protected theorem id {α : Type u_1} [emetric_space α] : antilipschitz_with 1 id := sorry

theorem comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [emetric_space α] [emetric_space β]
    [emetric_space γ] {Kg : nnreal} {g : β → γ} (hg : antilipschitz_with Kg g) {Kf : nnreal}
    {f : α → β} (hf : antilipschitz_with Kf f) : antilipschitz_with (Kf * Kg) (g ∘ f) :=
  sorry

theorem restrict {α : Type u_1} {β : Type u_2} [emetric_space α] [emetric_space β] {K : nnreal}
    {f : α → β} (hf : antilipschitz_with K f) (s : set α) :
    antilipschitz_with K (set.restrict f s) :=
  fun (x y : ↥s) => hf ↑x ↑y

theorem cod_restrict {α : Type u_1} {β : Type u_2} [emetric_space α] [emetric_space β] {K : nnreal}
    {f : α → β} (hf : antilipschitz_with K f) {s : set β} (hs : ∀ (x : α), f x ∈ s) :
    antilipschitz_with K (set.cod_restrict f s hs) :=
  fun (x y : α) => hf x y

theorem to_right_inv_on' {α : Type u_1} {β : Type u_2} [emetric_space α] [emetric_space β]
    {K : nnreal} {f : α → β} {s : set α} (hf : antilipschitz_with K (set.restrict f s)) {g : β → α}
    {t : set β} (g_maps : set.maps_to g t s) (g_inv : set.right_inv_on g f t) :
    lipschitz_with K (set.restrict g t) :=
  sorry

theorem to_right_inv_on {α : Type u_1} {β : Type u_2} [emetric_space α] [emetric_space β]
    {K : nnreal} {f : α → β} (hf : antilipschitz_with K f) {g : β → α} {t : set β}
    (h : set.right_inv_on g f t) : lipschitz_with K (set.restrict g t) :=
  to_right_inv_on' (restrict hf set.univ) (set.maps_to_univ g t) h

theorem to_right_inverse {α : Type u_1} {β : Type u_2} [emetric_space α] [emetric_space β]
    {K : nnreal} {f : α → β} (hf : antilipschitz_with K f) {g : β → α}
    (hg : function.right_inverse g f) : lipschitz_with K g :=
  sorry

theorem uniform_embedding {α : Type u_1} {β : Type u_2} [emetric_space α] [emetric_space β]
    {K : nnreal} {f : α → β} (hf : antilipschitz_with K f) (hfc : uniform_continuous f) :
    uniform_embedding f :=
  sorry

theorem subtype_coe {α : Type u_1} [emetric_space α] (s : set α) : antilipschitz_with 1 coe :=
  restrict antilipschitz_with.id s

theorem of_subsingleton {α : Type u_1} {β : Type u_2} [emetric_space α] [emetric_space β]
    {f : α → β} [subsingleton α] {K : nnreal} : antilipschitz_with K f :=
  sorry

end antilipschitz_with


theorem lipschitz_with.to_right_inverse {α : Type u_1} {β : Type u_2} [emetric_space α]
    [emetric_space β] {K : nnreal} {f : α → β} (hf : lipschitz_with K f) {g : β → α}
    (hg : function.right_inverse g f) : antilipschitz_with K g :=
  sorry

end Mathlib