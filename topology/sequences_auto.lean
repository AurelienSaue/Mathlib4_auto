/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.bases
import Mathlib.topology.subset_properties
import Mathlib.topology.metric_space.basic
import PostPort

universes u_1 u_3 l u_2 

namespace Mathlib

/-!
# Sequences in topological spaces

In this file we define sequences in topological spaces and show how they are related to
filters and the topology. In particular, we
* define the sequential closure of a set and prove that it's contained in the closure,
* define a type class "sequential_space" in which closure and sequential closure agree,
* define sequential continuity and show that it coincides with continuity in sequential spaces,
* provide an instance that shows that every first-countable (and in particular metric) space is
  a sequential space.
* define sequential compactness, prove that compactness implies sequential compactness in first
  countable spaces, and prove they are equivalent for uniform spaces having a countable uniformity
  basis (in particular metric spaces).
-/

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/

/-- A sequence converges in the sence of topological spaces iff the associated statement for filter
holds. -/
theorem topological_space.seq_tendsto_iff {α : Type u_1} [topological_space α] {x : ℕ → α} {limit : α} : filter.tendsto x filter.at_top (nhds limit) ↔
  ∀ (U : set α), limit ∈ U → is_open U → ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → x n ∈ U := sorry

/-- The sequential closure of a subset M ⊆ α of a topological space α is
the set of all p ∈ α which arise as limit of sequences in M. -/
def sequential_closure {α : Type u_1} [topological_space α] (M : set α) : set α :=
  set_of fun (p : α) => ∃ (x : ℕ → α), (∀ (n : ℕ), x n ∈ M) ∧ filter.tendsto x filter.at_top (nhds p)

theorem subset_sequential_closure {α : Type u_1} [topological_space α] (M : set α) : M ⊆ sequential_closure M :=
  fun (p : α) (_x : p ∈ M) =>
    (fun (this : p ∈ sequential_closure M) => this)
      (Exists.intro (fun (n : ℕ) => p) { left := fun (n : ℕ) => _x, right := tendsto_const_nhds })

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`,
the limit belongs to `s` as well. -/
def is_seq_closed {α : Type u_1} [topological_space α] (s : set α)  :=
  s = sequential_closure s

/-- A convenience lemma for showing that a set is sequentially closed. -/
theorem is_seq_closed_of_def {α : Type u_1} [topological_space α] {A : set α} (h : ∀ (x : ℕ → α) (p : α), (∀ (n : ℕ), x n ∈ A) → filter.tendsto x filter.at_top (nhds p) → p ∈ A) : is_seq_closed A := sorry

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
theorem sequential_closure_subset_closure {α : Type u_1} [topological_space α] (M : set α) : sequential_closure M ⊆ closure M := sorry

/-- A set is sequentially closed if it is closed. -/
theorem is_seq_closed_of_is_closed {α : Type u_1} [topological_space α] (M : set α) (_x : is_closed M) : is_seq_closed M :=
  (fun (this : sequential_closure M ⊆ M) => set.eq_of_subset_of_subset (subset_sequential_closure M) this)
    (trans_rel_left has_subset.subset (sequential_closure_subset_closure M) (is_closed.closure_eq _x))

/-- The limit of a convergent sequence in a sequentially closed set is in that set.-/
theorem mem_of_is_seq_closed {α : Type u_1} [topological_space α] {A : set α} (_x : is_seq_closed A) {x : ℕ → α} : (∀ (n : ℕ), x n ∈ A) → ∀ {limit : α}, filter.tendsto x filter.at_top (nhds limit) → limit ∈ A := sorry

/-- The limit of a convergent sequence in a closed set is in that set.-/
theorem mem_of_is_closed_sequential {α : Type u_1} [topological_space α] {A : set α} (_x : is_closed A) {x : ℕ → α} : (∀ (n : ℕ), x n ∈ A) → ∀ {limit : α}, filter.tendsto x filter.at_top (nhds limit) → limit ∈ A :=
  fun (_x_1 : ∀ (n : ℕ), x n ∈ A) {limit : α} (_x_2 : filter.tendsto x filter.at_top (nhds limit)) =>
    mem_of_is_seq_closed (is_seq_closed_of_is_closed A _x) _x_1 _x_2

/-- A sequential space is a space in which 'sequences are enough to probe the topology'. This can be
 formalised by demanding that the sequential closure and the closure coincide. The following
 statements show that other topological properties can be deduced from sequences in sequential
 spaces. -/
class sequential_space (α : Type u_3) [topological_space α] 
where
  sequential_closure_eq_closure : ∀ (M : set α), sequential_closure M = closure M

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
theorem is_seq_closed_iff_is_closed {α : Type u_1} [topological_space α] [sequential_space α] {M : set α} : is_seq_closed M ↔ is_closed M := sorry

/-- In a sequential space, a point belongs to the closure of a set iff it is a limit of a sequence
taking values in this set. -/
theorem mem_closure_iff_seq_limit {α : Type u_1} [topological_space α] [sequential_space α] {s : set α} {a : α} : a ∈ closure s ↔ ∃ (x : ℕ → α), (∀ (n : ℕ), x n ∈ s) ∧ filter.tendsto x filter.at_top (nhds a) := sorry

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def sequentially_continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β)  :=
  ∀ (x : ℕ → α) {limit : α},
    filter.tendsto x filter.at_top (nhds limit) → filter.tendsto (f ∘ x) filter.at_top (nhds (f limit))

/- A continuous function is sequentially continuous. -/

theorem continuous.to_sequentially_continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (_x : continuous f) : sequentially_continuous f := sorry

/-- In a sequential space, continuity and sequential continuity coincide. -/
theorem continuous_iff_sequentially_continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} [sequential_space α] : continuous f ↔ sequentially_continuous f := sorry

namespace topological_space


namespace first_countable_topology


/-- Every first-countable space is sequential. -/
protected instance sequential_space {α : Type u_1} [topological_space α] [first_countable_topology α] : sequential_space α :=
  sequential_space.mk
    ((fun (this : ∀ (M : set α), sequential_closure M = closure M) => this)
      fun (M : set α) =>
        (fun (this : closure M ⊆ sequential_closure M) => set.subset.antisymm (sequential_closure_subset_closure M) this)
          fun (p : α) (hp : p ∈ closure M) => sorry)

end first_countable_topology


end topological_space


/-- A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence. -/
def is_seq_compact {α : Type u_1} [topological_space α] (s : set α)  :=
  ∀ {u : ℕ → α},
    (∀ (n : ℕ), u n ∈ s) →
      ∃ (x : α), ∃ (H : x ∈ s), ∃ (φ : ℕ → ℕ), strict_mono φ ∧ filter.tendsto (u ∘ φ) filter.at_top (nhds x)

/-- A space `α` is sequentially compact if every sequence in `α` has a
converging subsequence. -/
class seq_compact_space (α : Type u_3) [topological_space α] 
where
  seq_compact_univ : is_seq_compact set.univ

theorem is_seq_compact.subseq_of_frequently_in {α : Type u_1} [topological_space α] {s : set α} (hs : is_seq_compact s) {u : ℕ → α} (hu : filter.frequently (fun (n : ℕ) => u n ∈ s) filter.at_top) : ∃ (x : α), ∃ (H : x ∈ s), ∃ (φ : ℕ → ℕ), strict_mono φ ∧ filter.tendsto (u ∘ φ) filter.at_top (nhds x) := sorry

theorem seq_compact_space.tendsto_subseq {α : Type u_1} [topological_space α] [seq_compact_space α] (u : ℕ → α) : ∃ (x : α), ∃ (φ : ℕ → ℕ), strict_mono φ ∧ filter.tendsto (u ∘ φ) filter.at_top (nhds x) := sorry

theorem is_compact.is_seq_compact {α : Type u_1} [topological_space α] [topological_space.first_countable_topology α] {s : set α} (hs : is_compact s) : is_seq_compact s := sorry

theorem is_compact.tendsto_subseq' {α : Type u_1} [topological_space α] [topological_space.first_countable_topology α] {s : set α} {u : ℕ → α} (hs : is_compact s) (hu : filter.frequently (fun (n : ℕ) => u n ∈ s) filter.at_top) : ∃ (x : α), ∃ (H : x ∈ s), ∃ (φ : ℕ → ℕ), strict_mono φ ∧ filter.tendsto (u ∘ φ) filter.at_top (nhds x) :=
  is_seq_compact.subseq_of_frequently_in (is_compact.is_seq_compact hs) hu

theorem is_compact.tendsto_subseq {α : Type u_1} [topological_space α] [topological_space.first_countable_topology α] {s : set α} {u : ℕ → α} (hs : is_compact s) (hu : ∀ (n : ℕ), u n ∈ s) : ∃ (x : α), ∃ (H : x ∈ s), ∃ (φ : ℕ → ℕ), strict_mono φ ∧ filter.tendsto (u ∘ φ) filter.at_top (nhds x) :=
  is_compact.is_seq_compact hs hu

protected instance first_countable_topology.seq_compact_of_compact {α : Type u_1} [topological_space α] [topological_space.first_countable_topology α] [compact_space α] : seq_compact_space α :=
  seq_compact_space.mk (is_compact.is_seq_compact compact_univ)

theorem compact_space.tendsto_subseq {α : Type u_1} [topological_space α] [topological_space.first_countable_topology α] [compact_space α] (u : ℕ → α) : ∃ (x : α), ∃ (φ : ℕ → ℕ), strict_mono φ ∧ filter.tendsto (u ∘ φ) filter.at_top (nhds x) :=
  seq_compact_space.tendsto_subseq u

theorem lebesgue_number_lemma_seq {β : Type u_2} [uniform_space β] {s : set β} {ι : Type u_1} {c : ι → set β} (hs : is_seq_compact s) (hc₁ : ∀ (i : ι), is_open (c i)) (hc₂ : s ⊆ set.Union fun (i : ι) => c i) (hU : filter.is_countably_generated (uniformity β)) : ∃ (V : set (β × β)),
  ∃ (H : V ∈ uniformity β), symmetric_rel V ∧ ∀ (x : β), x ∈ s → ∃ (i : ι), uniform_space.ball x V ⊆ c i := sorry

theorem is_seq_compact.totally_bounded {β : Type u_2} [uniform_space β] {s : set β} (h : is_seq_compact s) : totally_bounded s := sorry

protected theorem is_seq_compact.is_compact {β : Type u_2} [uniform_space β] {s : set β} (h : filter.is_countably_generated (uniformity β)) (hs : is_seq_compact s) : is_compact s := sorry

protected theorem uniform_space.compact_iff_seq_compact {β : Type u_2} [uniform_space β] {s : set β} (h : filter.is_countably_generated (uniformity β)) : is_compact s ↔ is_seq_compact s :=
  { mp := fun (H : is_compact s) => is_compact.is_seq_compact H,
    mpr := fun (H : is_seq_compact s) => is_seq_compact.is_compact h H }

theorem uniform_space.compact_space_iff_seq_compact_space {β : Type u_2} [uniform_space β] (H : filter.is_countably_generated (uniformity β)) : compact_space β ↔ seq_compact_space β := sorry

/-- A version of Bolzano-Weistrass: in a metric space, is_compact s ↔ is_seq_compact s -/
theorem metric.compact_iff_seq_compact {β : Type u_2} [metric_space β] {s : set β} : is_compact s ↔ is_seq_compact s :=
  uniform_space.compact_iff_seq_compact emetric.uniformity_has_countable_basis

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
theorem tendsto_subseq_of_frequently_bounded {β : Type u_2} [metric_space β] {s : set β} [proper_space β] (hs : metric.bounded s) {u : ℕ → β} (hu : filter.frequently (fun (n : ℕ) => u n ∈ s) filter.at_top) : ∃ (b : β), ∃ (H : b ∈ closure s), ∃ (φ : ℕ → ℕ), strict_mono φ ∧ filter.tendsto (u ∘ φ) filter.at_top (nhds b) := sorry

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
theorem tendsto_subseq_of_bounded {β : Type u_2} [metric_space β] {s : set β} [proper_space β] (hs : metric.bounded s) {u : ℕ → β} (hu : ∀ (n : ℕ), u n ∈ s) : ∃ (b : β), ∃ (H : b ∈ closure s), ∃ (φ : ℕ → ℕ), strict_mono φ ∧ filter.tendsto (u ∘ φ) filter.at_top (nhds b) :=
  tendsto_subseq_of_frequently_bounded hs (filter.frequently_of_forall hu)

theorem metric.compact_space_iff_seq_compact_space {β : Type u_2} [metric_space β] : compact_space β ↔ seq_compact_space β :=
  uniform_space.compact_space_iff_seq_compact_space emetric.uniformity_has_countable_basis

theorem seq_compact.lebesgue_number_lemma_of_metric {β : Type u_2} [metric_space β] {s : set β} {ι : Type u_1} {c : ι → set β} (hs : is_seq_compact s) (hc₁ : ∀ (i : ι), is_open (c i)) (hc₂ : s ⊆ set.Union fun (i : ι) => c i) : ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ (x : β), x ∈ s → ∃ (i : ι), metric.ball x δ ⊆ c i := sorry

