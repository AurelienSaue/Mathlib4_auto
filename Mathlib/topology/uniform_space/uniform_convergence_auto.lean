/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.uniform_space.basic
import Mathlib.PostPort

universes u v u_1 w 

namespace Mathlib

/-!
# Uniform convergence

A sequence of functions `Fₙ` (with values in a metric space) converges uniformly on a set `s` to a
function `f` if, for all `ε > 0`, for all large enough `n`, one has for all `y ∈ s` the inequality
`dist (f y, Fₙ y) < ε`. Under uniform convergence, many properties of the `Fₙ` pass to the limit,
most notably continuity. We prove this in the file, defining the notion of uniform convergence
in the more general setting of uniform spaces, and with respect to an arbitrary indexing set
endowed with a filter (instead of just `ℕ` with `at_top`).

## Main results

Let `α` be a topological space, `β` a uniform space, `Fₙ` and `f` be functions from `α`to `β`
(where the index `n` belongs to an indexing type `ι` endowed with a filter `p`).

* `tendsto_uniformly_on F f p s`: the fact that `Fₙ` converges uniformly to `f` on `s`. This means
  that, for any entourage `u` of the diagonal, for large enough `n` (with respect to `p`), one has
  `(f y, Fₙ y) ∈ u` for all `y ∈ s`.
* `tendsto_uniformly F f p`: same notion with `s = univ`.
* `tendsto_uniformly_on.continuous_on`: a uniform limit on a set of functions which are continuous
  on this set is itself continuous on this set.
* `tendsto_uniformly.continuous`: a uniform limit of continuous functions is continuous.
* `tendsto_uniformly_on.tendsto_comp`: If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends
  to `x` within `s`, then `Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s`.
* `tendsto_uniformly.tendsto_comp`: If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then
  `Fₙ gₙ` tends to `f x`.

We also define notions where the convergence is locally uniform, called
`tendsto_locally_uniformly_on F f p s` and `tendsto_locally_uniformly F f p`. The previous theorems
all have corresponding versions under locally uniform convergence.

## Implementation notes

Most results hold under weaker assumptions of locally uniform approximation. In a first section,
we prove the results under these weaker assumptions. Then, we derive the results on uniform
convergence from them.

## Tags

Uniform limit, uniform convergence, tends uniformly to
 -/

/-!
### Different notions of uniform convergence

We define uniform convergence and locally uniform convergence, on a set or in the whole space.
-/

/-- A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting function `f` with
respect to the filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x ∈ s`. -/
def tendsto_uniformly_on {α : Type u} {β : Type v} {ι : Type u_1} [uniform_space β] (F : ι → α → β)
    (f : α → β) (p : filter ι) (s : set α) :=
  ∀ (u : set (β × β)),
    u ∈ uniformity β → filter.eventually (fun (n : ι) => ∀ (x : α), x ∈ s → (f x, F n x) ∈ u) p

/-- A sequence of functions `Fₙ` converges uniformly to a limiting function `f` with respect to a
filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x`. -/
def tendsto_uniformly {α : Type u} {β : Type v} {ι : Type u_1} [uniform_space β] (F : ι → α → β)
    (f : α → β) (p : filter ι) :=
  ∀ (u : set (β × β)),
    u ∈ uniformity β → filter.eventually (fun (n : ι) => ∀ (x : α), (f x, F n x) ∈ u) p

theorem tendsto_uniformly_on_univ {α : Type u} {β : Type v} {ι : Type u_1} [uniform_space β]
    {F : ι → α → β} {f : α → β} {p : filter ι} :
    tendsto_uniformly_on F f p set.univ ↔ tendsto_uniformly F f p :=
  sorry

theorem tendsto_uniformly_on.mono {α : Type u} {β : Type v} {ι : Type u_1} [uniform_space β]
    {F : ι → α → β} {f : α → β} {s : set α} {p : filter ι} {s' : set α}
    (h : tendsto_uniformly_on F f p s) (h' : s' ⊆ s) : tendsto_uniformly_on F f p s' :=
  fun (u : set (β × β)) (hu : u ∈ uniformity β) =>
    filter.eventually.mono (h u hu)
      fun (n : ι) (hn : ∀ (x : α), x ∈ s → (f x, F n x) ∈ u) (x : α) (hx : x ∈ s') => hn x (h' hx)

theorem tendsto_uniformly.tendsto_uniformly_on {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {s : set α} {p : filter ι}
    (h : tendsto_uniformly F f p) : tendsto_uniformly_on F f p s :=
  tendsto_uniformly_on.mono (iff.mpr tendsto_uniformly_on_univ h) (set.subset_univ s)

/-- Composing on the right by a function preserves uniform convergence on a set -/
theorem tendsto_uniformly_on.comp {α : Type u} {β : Type v} {γ : Type w} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {s : set α} {p : filter ι}
    (h : tendsto_uniformly_on F f p s) (g : γ → α) :
    tendsto_uniformly_on (fun (n : ι) => F n ∘ g) (f ∘ g) p (g ⁻¹' s) :=
  sorry

/-- Composing on the right by a function preserves uniform convergence -/
theorem tendsto_uniformly.comp {α : Type u} {β : Type v} {γ : Type w} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {p : filter ι} (h : tendsto_uniformly F f p)
    (g : γ → α) : tendsto_uniformly (fun (n : ι) => F n ∘ g) (f ∘ g) p :=
  id
    fun (u : set (β × β)) (hu : u ∈ uniformity β) =>
      filter.eventually.mono (h u hu)
        fun (n : ι) (hn : ∀ (x : α), (f x, F n x) ∈ u) (x : γ) => hn (g x)

/-- A sequence of functions `Fₙ` converges locally uniformly on a set `s` to a limiting function
`f` with respect to a filter `p` if, for any entourage of the diagonal `u`, for any `x ∈ s`, one
has `p`-eventually `(f x, Fₙ x) ∈ u` for all `y` in a neighborhood of `x` in `s`. -/
def tendsto_locally_uniformly_on {α : Type u} {β : Type v} {ι : Type u_1} [uniform_space β]
    [topological_space α] (F : ι → α → β) (f : α → β) (p : filter ι) (s : set α) :=
  ∀ (u : set (β × β)) (H : u ∈ uniformity β) (x : α) (H : x ∈ s),
    ∃ (t : set α),
      ∃ (H : t ∈ nhds_within x s),
        filter.eventually (fun (n : ι) => ∀ (y : α), y ∈ t → (f y, F n y) ∈ u) p

/-- A sequence of functions `Fₙ` converges locally uniformly to a limiting function `f` with respect
to a filter `p` if, for any entourage of the diagonal `u`, for any `x`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `y` in a neighborhood of `x`. -/
def tendsto_locally_uniformly {α : Type u} {β : Type v} {ι : Type u_1} [uniform_space β]
    [topological_space α] (F : ι → α → β) (f : α → β) (p : filter ι) :=
  ∀ (u : set (β × β)) (H : u ∈ uniformity β) (x : α),
    ∃ (t : set α),
      ∃ (H : t ∈ nhds x), filter.eventually (fun (n : ι) => ∀ (y : α), y ∈ t → (f y, F n y) ∈ u) p

theorem tendsto_uniformly_on.tendsto_locally_uniformly_on {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {s : set α} {p : filter ι} [topological_space α]
    (h : tendsto_uniformly_on F f p s) : tendsto_locally_uniformly_on F f p s :=
  fun (u : set (β × β)) (hu : u ∈ uniformity β) (x : α) (hx : x ∈ s) =>
    Exists.intro s (Exists.intro self_mem_nhds_within (h u hu))

theorem tendsto_uniformly.tendsto_locally_uniformly {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {p : filter ι} [topological_space α]
    (h : tendsto_uniformly F f p) : tendsto_locally_uniformly F f p :=
  sorry

theorem tendsto_locally_uniformly_on.mono {α : Type u} {β : Type v} {ι : Type u_1} [uniform_space β]
    {F : ι → α → β} {f : α → β} {s : set α} {s' : set α} {p : filter ι} [topological_space α]
    (h : tendsto_locally_uniformly_on F f p s) (h' : s' ⊆ s) :
    tendsto_locally_uniformly_on F f p s' :=
  sorry

theorem tendsto_locally_uniformly_on_univ {α : Type u} {β : Type v} {ι : Type u_1} [uniform_space β]
    {F : ι → α → β} {f : α → β} {p : filter ι} [topological_space α] :
    tendsto_locally_uniformly_on F f p set.univ ↔ tendsto_locally_uniformly F f p :=
  sorry

theorem tendsto_locally_uniformly_on.comp {α : Type u} {β : Type v} {γ : Type w} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {s : set α} {p : filter ι} [topological_space α]
    [topological_space γ] {t : set γ} (h : tendsto_locally_uniformly_on F f p s) (g : γ → α)
    (hg : set.maps_to g t s) (cg : continuous_on g t) :
    tendsto_locally_uniformly_on (fun (n : ι) => F n ∘ g) (f ∘ g) p t :=
  sorry

theorem tendsto_locally_uniformly.comp {α : Type u} {β : Type v} {γ : Type w} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {p : filter ι} [topological_space α]
    [topological_space γ] (h : tendsto_locally_uniformly F f p) (g : γ → α) (cg : continuous g) :
    tendsto_locally_uniformly (fun (n : ι) => F n ∘ g) (f ∘ g) p :=
  sorry

/-!
### Uniform approximation

In this section, we give lemmas ensuring that a function is continuous if it can be approximated
uniformly by continuous functions. We give various versions, within a set or the whole space, at
a single point or at all points, with locally uniform approximation or uniform approximation. All
the statements are derived from a statement about locally uniform approximation within a set at
a point, called `continuous_within_at_of_locally_uniform_approx_of_continuous_within_at`. -/

/-- A function which can be locally uniformly approximated by functions which are continuous
within a set at a point is continuous within this set at this point. -/
theorem continuous_within_at_of_locally_uniform_approx_of_continuous_within_at {α : Type u}
    {β : Type v} {ι : Type u_1} [uniform_space β] {F : ι → α → β} {f : α → β} {s : set α} {x : α}
    [topological_space α] (hx : x ∈ s)
    (L :
      ∀ (u : set (β × β)) (H : u ∈ uniformity β),
        ∃ (t : set α), ∃ (H : t ∈ nhds_within x s), ∃ (n : ι), ∀ (y : α), y ∈ t → (f y, F n y) ∈ u)
    (C : ∀ (n : ι), continuous_within_at (F n) s x) : continuous_within_at f s x :=
  sorry

/-- A function which can be locally uniformly approximated by functions which are continuous at
a point is continuous at this point. -/
theorem continuous_at_of_locally_uniform_approx_of_continuous_at {α : Type u} {β : Type v}
    {ι : Type u_1} [uniform_space β] {F : ι → α → β} {f : α → β} {x : α} [topological_space α]
    (L :
      ∀ (u : set (β × β)) (H : u ∈ uniformity β),
        ∃ (t : set α), ∃ (H : t ∈ nhds x), ∃ (n : ι), ∀ (y : α), y ∈ t → (f y, F n y) ∈ u)
    (C : ∀ (n : ι), continuous_at (F n) x) : continuous_at f x :=
  sorry

/-- A function which can be locally uniformly approximated by functions which are continuous
on a set is continuous on this set. -/
theorem continuous_on_of_locally_uniform_approx_of_continuous_on {α : Type u} {β : Type v}
    {ι : Type u_1} [uniform_space β] {F : ι → α → β} {f : α → β} {s : set α} [topological_space α]
    (L :
      ∀ (x : α) (H : x ∈ s) (u : set (β × β)) (H : u ∈ uniformity β),
        ∃ (t : set α), ∃ (H : t ∈ nhds_within x s), ∃ (n : ι), ∀ (y : α), y ∈ t → (f y, F n y) ∈ u)
    (C : ∀ (n : ι), continuous_on (F n) s) : continuous_on f s :=
  fun (x : α) (hx : x ∈ s) =>
    continuous_within_at_of_locally_uniform_approx_of_continuous_within_at hx (L x hx)
      fun (n : ι) => C n x hx

/-- A function which can be uniformly approximated by functions which are continuous on a set
is continuous on this set. -/
theorem continuous_on_of_uniform_approx_of_continuous_on {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {s : set α} [topological_space α]
    (L : ∀ (u : set (β × β)), u ∈ uniformity β → ∃ (n : ι), ∀ (y : α), y ∈ s → (f y, F n y) ∈ u) :
    (∀ (n : ι), continuous_on (F n) s) → continuous_on f s :=
  continuous_on_of_locally_uniform_approx_of_continuous_on
    fun (x : α) (hx : x ∈ s) (u : set (β × β)) (hu : u ∈ uniformity β) =>
      Exists.intro s (Exists.intro self_mem_nhds_within (L u hu))

/-- A function which can be locally uniformly approximated by continuous functions is continuous. -/
theorem continuous_of_locally_uniform_approx_of_continuous {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} [topological_space α]
    (L :
      ∀ (x : α) (u : set (β × β)) (H : u ∈ uniformity β),
        ∃ (t : set α), ∃ (H : t ∈ nhds x), ∃ (n : ι), ∀ (y : α), y ∈ t → (f y, F n y) ∈ u)
    (C : ∀ (n : ι), continuous (F n)) : continuous f :=
  sorry

/-- A function which can be uniformly approximated by continuous functions is continuous. -/
theorem continuous_of_uniform_approx_of_continuous {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} [topological_space α]
    (L : ∀ (u : set (β × β)), u ∈ uniformity β → ∃ (N : ι), ∀ (y : α), (f y, F N y) ∈ u) :
    (∀ (n : ι), continuous (F n)) → continuous f :=
  sorry

/-!
### Uniform limits

From the previous statements on uniform approximation, we deduce continuity results for uniform
limits.
-/

/-- A locally uniform limit on a set of functions which are continuous on this set is itself
continuous on this set. -/
theorem tendsto_locally_uniformly_on.continuous_on {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {s : set α} {p : filter ι} [topological_space α]
    (h : tendsto_locally_uniformly_on F f p s) (hc : ∀ (n : ι), continuous_on (F n) s)
    [filter.ne_bot p] : continuous_on f s :=
  sorry

/-- A uniform limit on a set of functions which are continuous on this set is itself continuous
on this set. -/
theorem tendsto_uniformly_on.continuous_on {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {s : set α} {p : filter ι} [topological_space α]
    (h : tendsto_uniformly_on F f p s) (hc : ∀ (n : ι), continuous_on (F n) s) [filter.ne_bot p] :
    continuous_on f s :=
  tendsto_locally_uniformly_on.continuous_on (tendsto_uniformly_on.tendsto_locally_uniformly_on h)
    hc

/-- A locally uniform limit of continuous functions is continuous. -/
theorem tendsto_locally_uniformly.continuous {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {p : filter ι} [topological_space α]
    (h : tendsto_locally_uniformly F f p) (hc : ∀ (n : ι), continuous (F n)) [filter.ne_bot p] :
    continuous f :=
  sorry

/-- A uniform limit of continuous functions is continuous. -/
theorem tendsto_uniformly.continuous {α : Type u} {β : Type v} {ι : Type u_1} [uniform_space β]
    {F : ι → α → β} {f : α → β} {p : filter ι} [topological_space α] (h : tendsto_uniformly F f p)
    (hc : ∀ (n : ι), continuous (F n)) [filter.ne_bot p] : continuous f :=
  tendsto_locally_uniformly.continuous (tendsto_uniformly.tendsto_locally_uniformly h) hc

/-!
### Composing limits under uniform convergence

In general, if `Fₙ` converges pointwise to a function `f`, and `gₙ` tends to `x`, it is not true
that `Fₙ gₙ` tends to `f x`. It is true however if the convergence of `Fₙ` to `f` is uniform. In
this paragraph, we prove variations around this statement.
-/

/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` within a set `s` to a function `f`
which is continuous at `x` within `s `, and `gₙ` tends to `x` within `s`, then `Fₙ (gₙ)` tends
to `f x`. -/
theorem tendsto_comp_of_locally_uniform_limit_within {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {s : set α} {x : α} {p : filter ι} {g : ι → α}
    [topological_space α] (h : continuous_within_at f s x)
    (hg : filter.tendsto g p (nhds_within x s))
    (hunif :
      ∀ (u : set (β × β)) (H : u ∈ uniformity β),
        ∃ (t : set α),
          ∃ (H : t ∈ nhds_within x s),
            filter.eventually (fun (n : ι) => ∀ (y : α), y ∈ t → (f y, F n y) ∈ u) p) :
    filter.tendsto (fun (n : ι) => F n (g n)) p (nhds (f x)) :=
  sorry

/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` to a function `f` which is
continuous at `x`, and `gₙ` tends to `x`, then `Fₙ (gₙ)` tends to `f x`. -/
theorem tendsto_comp_of_locally_uniform_limit {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {x : α} {p : filter ι} {g : ι → α}
    [topological_space α] (h : continuous_at f x) (hg : filter.tendsto g p (nhds x))
    (hunif :
      ∀ (u : set (β × β)) (H : u ∈ uniformity β),
        ∃ (t : set α),
          ∃ (H : t ∈ nhds x),
            filter.eventually (fun (n : ι) => ∀ (y : α), y ∈ t → (f y, F n y) ∈ u) p) :
    filter.tendsto (fun (n : ι) => F n (g n)) p (nhds (f x)) :=
  sorry

/-- If `Fₙ` tends locally uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then
`Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s` and `x ∈ s`. -/
theorem tendsto_locally_uniformly_on.tendsto_comp {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {s : set α} {x : α} {p : filter ι} {g : ι → α}
    [topological_space α] (h : tendsto_locally_uniformly_on F f p s)
    (hf : continuous_within_at f s x) (hx : x ∈ s) (hg : filter.tendsto g p (nhds_within x s)) :
    filter.tendsto (fun (n : ι) => F n (g n)) p (nhds (f x)) :=
  tendsto_comp_of_locally_uniform_limit_within hf hg
    fun (u : set (β × β)) (hu : u ∈ uniformity β) => h u hu x hx

/-- If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then `Fₙ gₙ` tends
to `f x` if `f` is continuous at `x` within `s`. -/
theorem tendsto_uniformly_on.tendsto_comp {α : Type u} {β : Type v} {ι : Type u_1} [uniform_space β]
    {F : ι → α → β} {f : α → β} {s : set α} {x : α} {p : filter ι} {g : ι → α} [topological_space α]
    (h : tendsto_uniformly_on F f p s) (hf : continuous_within_at f s x)
    (hg : filter.tendsto g p (nhds_within x s)) :
    filter.tendsto (fun (n : ι) => F n (g n)) p (nhds (f x)) :=
  tendsto_comp_of_locally_uniform_limit_within hf hg
    fun (u : set (β × β)) (hu : u ∈ uniformity β) =>
      Exists.intro s (Exists.intro self_mem_nhds_within (h u hu))

/-- If `Fₙ` tends locally uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
theorem tendsto_locally_uniformly.tendsto_comp {α : Type u} {β : Type v} {ι : Type u_1}
    [uniform_space β] {F : ι → α → β} {f : α → β} {x : α} {p : filter ι} {g : ι → α}
    [topological_space α] (h : tendsto_locally_uniformly F f p) (hf : continuous_at f x)
    (hg : filter.tendsto g p (nhds x)) : filter.tendsto (fun (n : ι) => F n (g n)) p (nhds (f x)) :=
  tendsto_comp_of_locally_uniform_limit hf hg
    fun (u : set (β × β)) (hu : u ∈ uniformity β) => h u hu x

/-- If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
theorem tendsto_uniformly.tendsto_comp {α : Type u} {β : Type v} {ι : Type u_1} [uniform_space β]
    {F : ι → α → β} {f : α → β} {x : α} {p : filter ι} {g : ι → α} [topological_space α]
    (h : tendsto_uniformly F f p) (hf : continuous_at f x) (hg : filter.tendsto g p (nhds x)) :
    filter.tendsto (fun (n : ι) => F n (g n)) p (nhds (f x)) :=
  tendsto_locally_uniformly.tendsto_comp (tendsto_uniformly.tendsto_locally_uniformly h) hf hg

end Mathlib