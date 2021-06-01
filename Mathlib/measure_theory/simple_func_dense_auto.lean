/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.l1_space
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated,
both pointwise and in `L¹` norm, by a sequence of simple functions.

## Main definitions

* `measure_theory.simple_func.nearest_pt (e : ℕ → α) (N : ℕ) : α →ₛ ℕ`: the `simple_func` sending
  each `x : α` to the point `e k` which is the nearest to `x` among `e 0`, ..., `e N`.
* `measure_theory.simple_func.approx_on (f : β → α) (hf : measurable f) (s : set α) (y₀ : α)
  (h₀ : y₀ ∈ s) [separable_space s] (n : ℕ) : β →ₛ α` : a simple function that takes values in `s`
  and approximates `f`. If `f x ∈ s`, then `measure_theory.simple_func.approx_on f hf s y₀ h₀ n x`
  tends to `f x` as `n` tends to `∞`. If `α` is a `normed_group`, `f x - y₀`
  is `measure_theory.integrable`, and `f x ∈ s` for a.e. `x`, then
  `simple_func.approx_on f hf s y₀ h₀ n` tends to `f` in `L₁`. The main use case is `s = univ`,
  `y₀ = 0`.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/

namespace measure_theory


namespace simple_func


/-- `nearest_pt_ind e N x` is the index `k` such that `e k` is the nearest point to `x` among the
points `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then
`nearest_pt_ind e N x` returns the least of their indexes. -/
def nearest_pt_ind {α : Type u_1} [measurable_space α] [emetric_space α] [opens_measurable_space α]
    (e : ℕ → α) : ℕ → simple_func α ℕ :=
  sorry

/-- `nearest_pt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`. If more than
one point are at the same distance from `x`, then `nearest_pt e N x` returns the point with the
least possible index. -/
def nearest_pt {α : Type u_1} [measurable_space α] [emetric_space α] [opens_measurable_space α]
    (e : ℕ → α) (N : ℕ) : simple_func α α :=
  map e (nearest_pt_ind e N)

@[simp] theorem nearest_pt_ind_zero {α : Type u_1} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] (e : ℕ → α) : nearest_pt_ind e 0 = const α 0 :=
  rfl

@[simp] theorem nearest_pt_zero {α : Type u_1} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] (e : ℕ → α) : nearest_pt e 0 = const α (e 0) :=
  rfl

theorem nearest_pt_ind_succ {α : Type u_1} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] (e : ℕ → α) (N : ℕ) (x : α) :
    coe_fn (nearest_pt_ind e (N + 1)) x =
        ite (∀ (k : ℕ), k ≤ N → edist (e (N + 1)) x < edist (e k) x) (N + 1)
          (coe_fn (nearest_pt_ind e N) x) :=
  sorry

theorem nearest_pt_ind_le {α : Type u_1} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] (e : ℕ → α) (N : ℕ) (x : α) : coe_fn (nearest_pt_ind e N) x ≤ N :=
  sorry

theorem edist_nearest_pt_le {α : Type u_1} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] (e : ℕ → α) (x : α) {k : ℕ} {N : ℕ} (hk : k ≤ N) :
    edist (coe_fn (nearest_pt e N) x) x ≤ edist (e k) x :=
  sorry

theorem tendsto_nearest_pt {α : Type u_1} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] {e : ℕ → α} {x : α} (hx : x ∈ closure (set.range e)) :
    filter.tendsto (fun (N : ℕ) => coe_fn (nearest_pt e N) x) filter.at_top (nhds x) :=
  sorry

/-- Approximate a measurable function by a sequence of simple functions `F n` such that
`F n x ∈ s`. -/
def approx_on {α : Type u_1} {β : Type u_2} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] [measurable_space β] (f : β → α) (hf : measurable f) (s : set α)
    (y₀ : α) (h₀ : y₀ ∈ s) [topological_space.separable_space ↥s] (n : ℕ) : simple_func β α :=
  comp (nearest_pt (fun (k : ℕ) => nat.cases_on k y₀ (coe ∘ topological_space.dense_seq ↥s)) n) f hf

@[simp] theorem approx_on_zero {α : Type u_1} {β : Type u_2} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] [measurable_space β] {f : β → α} (hf : measurable f) {s : set α}
    {y₀ : α} (h₀ : y₀ ∈ s) [topological_space.separable_space ↥s] (x : β) :
    coe_fn (approx_on f hf s y₀ h₀ 0) x = y₀ :=
  rfl

theorem approx_on_mem {α : Type u_1} {β : Type u_2} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] [measurable_space β] {f : β → α} (hf : measurable f) {s : set α}
    {y₀ : α} (h₀ : y₀ ∈ s) [topological_space.separable_space ↥s] (n : ℕ) (x : β) :
    coe_fn (approx_on f hf s y₀ h₀ n) x ∈ s :=
  (fun (n_1 : ℕ) =>
      nat.cases_on n_1 h₀ fun (n : ℕ) => subtype.mem (topological_space.dense_seq (↥s) n))
    (coe_fn
      (nearest_pt_ind (fun (k : ℕ) => nat.cases_on k y₀ (coe ∘ topological_space.dense_seq ↥s)) n)
      (f x))

@[simp] theorem approx_on_comp {α : Type u_1} {β : Type u_2} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] [measurable_space β] {γ : Type u_3} [measurable_space γ] {f : β → α}
    (hf : measurable f) {g : γ → β} (hg : measurable g) {s : set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [topological_space.separable_space ↥s] (n : ℕ) :
    approx_on (f ∘ g) (measurable.comp hf hg) s y₀ h₀ n = comp (approx_on f hf s y₀ h₀ n) g hg :=
  rfl

theorem tendsto_approx_on {α : Type u_1} {β : Type u_2} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] [measurable_space β] {f : β → α} (hf : measurable f) {s : set α}
    {y₀ : α} (h₀ : y₀ ∈ s) [topological_space.separable_space ↥s] {x : β} (hx : f x ∈ closure s) :
    filter.tendsto (fun (n : ℕ) => coe_fn (approx_on f hf s y₀ h₀ n) x) filter.at_top
        (nhds (f x)) :=
  sorry

theorem edist_approx_on_le {α : Type u_1} {β : Type u_2} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] [measurable_space β] {f : β → α} (hf : measurable f) {s : set α}
    {y₀ : α} (h₀ : y₀ ∈ s) [topological_space.separable_space ↥s] (x : β) (n : ℕ) :
    edist (coe_fn (approx_on f hf s y₀ h₀ n) x) (f x) ≤ edist y₀ (f x) :=
  id
    (edist_nearest_pt_le (Nat.rec y₀ fun (n : ℕ) (ih : α) => ↑(topological_space.dense_seq (↥s) n))
      (f x) (zero_le n))

theorem edist_approx_on_y0_le {α : Type u_1} {β : Type u_2} [measurable_space α] [emetric_space α]
    [opens_measurable_space α] [measurable_space β] {f : β → α} (hf : measurable f) {s : set α}
    {y₀ : α} (h₀ : y₀ ∈ s) [topological_space.separable_space ↥s] (x : β) (n : ℕ) :
    edist y₀ (coe_fn (approx_on f hf s y₀ h₀ n) x) ≤ edist y₀ (f x) + edist y₀ (f x) :=
  le_trans (edist_triangle_right y₀ (coe_fn (approx_on f hf s y₀ h₀ n) x) (f x))
    (add_le_add_left (edist_approx_on_le hf h₀ x n) (edist y₀ (f x)))

theorem norm_approx_on_zero_le {β : Type u_2} {E : Type u_4} [measurable_space β]
    [measurable_space E] [normed_group E] [opens_measurable_space E] {f : β → E} (hf : measurable f)
    {s : set E} (h₀ : 0 ∈ s) [topological_space.separable_space ↥s] (x : β) (n : ℕ) :
    norm (coe_fn (approx_on f hf s 0 h₀ n) x) ≤ norm (f x) + norm (f x) :=
  sorry

theorem tendsto_approx_on_l1_edist {β : Type u_2} {E : Type u_4} [measurable_space β]
    [measurable_space E] [normed_group E] [opens_measurable_space E] {f : β → E} (hf : measurable f)
    {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [topological_space.separable_space ↥s] {μ : measure β}
    (hμ : filter.eventually (fun (x : β) => f x ∈ closure s) (measure.ae μ))
    (hi : has_finite_integral fun (x : β) => f x - y₀) :
    filter.tendsto
        (fun (n : ℕ) =>
          lintegral μ fun (x : β) => edist (coe_fn (approx_on f hf s y₀ h₀ n) x) (f x))
        filter.at_top (nhds 0) :=
  sorry

theorem integrable_approx_on {β : Type u_2} {E : Type u_4} [measurable_space β] [measurable_space E]
    [normed_group E] [borel_space E] {f : β → E} {μ : measure β} (fmeas : measurable f)
    (hf : integrable f) {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [topological_space.separable_space ↥s]
    (hi₀ : integrable fun (x : β) => y₀) (n : ℕ) : integrable ⇑(approx_on f fmeas s y₀ h₀ n) :=
  sorry

theorem tendsto_approx_on_univ_l1_edist {β : Type u_2} {E : Type u_4} [measurable_space β]
    [measurable_space E] [normed_group E] [opens_measurable_space E]
    [topological_space.second_countable_topology E] {f : β → E} {μ : measure β}
    (fmeas : measurable f) (hf : integrable f) :
    filter.tendsto
        (fun (n : ℕ) =>
          lintegral μ
            fun (x : β) => edist (coe_fn (approx_on f fmeas set.univ 0 trivial n) x) (f x))
        filter.at_top (nhds 0) :=
  sorry

theorem integrable_approx_on_univ {β : Type u_2} {E : Type u_4} [measurable_space β]
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {f : β → E} {μ : measure β}
    (fmeas : measurable f) (hf : integrable f) (n : ℕ) :
    integrable ⇑(approx_on f fmeas set.univ 0 trivial n) :=
  integrable_approx_on fmeas hf trivial (integrable_zero β E μ) n

theorem tendsto_approx_on_univ_l1 {β : Type u_2} {E : Type u_4} [measurable_space β]
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {f : β → E} {μ : measure β}
    (fmeas : measurable f) (hf : integrable f) :
    filter.tendsto
        (fun (n : ℕ) =>
          l1.of_fun (⇑(approx_on f fmeas set.univ 0 trivial n))
            (integrable_approx_on_univ fmeas hf n))
        filter.at_top (nhds (l1.of_fun f hf)) :=
  iff.mpr tendsto_iff_edist_tendsto_0 (tendsto_approx_on_univ_l1_edist fmeas hf)

end Mathlib