/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Bases of topologies. Countability axioms.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.continuous_on
import Mathlib.PostPort

universes u l u_1 u_2 

namespace Mathlib

namespace topological_space


/- countability axioms

For our applications we are interested that there exists a countable basis, but we do not need the
concrete basis itself. This allows us to declare these type classes as `Prop` to use them as mixins.
-/

/-- A topological basis is one that satisfies the necessary conditions so that
  it suffices to take unions of the basis sets to get a topology (without taking
  finite intersections as well). -/
def is_topological_basis {α : Type u} [t : topological_space α] (s : set (set α)) :=
  (∀ (t₁ : set α) (H : t₁ ∈ s) (t₂ : set α) (H : t₂ ∈ s) (x : α) (H : x ∈ t₁ ∩ t₂),
      ∃ (t₃ : set α), ∃ (H : t₃ ∈ s), x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂) ∧
    ⋃₀s = set.univ ∧ t = generate_from s

theorem is_topological_basis_of_subbasis {α : Type u} [t : topological_space α] {s : set (set α)}
    (hs : t = generate_from s) :
    is_topological_basis
        ((fun (f : set (set α)) => ⋂₀f) ''
          set_of fun (f : set (set α)) => set.finite f ∧ f ⊆ s ∧ set.nonempty (⋂₀f)) :=
  sorry

theorem is_topological_basis_of_open_of_nhds {α : Type u} [t : topological_space α]
    {s : set (set α)} (h_open : ∀ (u : set α), u ∈ s → is_open u)
    (h_nhds :
      ∀ (a : α) (u : set α), a ∈ u → is_open u → ∃ (v : set α), ∃ (H : v ∈ s), a ∈ v ∧ v ⊆ u) :
    is_topological_basis s :=
  sorry

theorem mem_nhds_of_is_topological_basis {α : Type u} [t : topological_space α] {a : α} {s : set α}
    {b : set (set α)} (hb : is_topological_basis b) :
    s ∈ nhds a ↔ ∃ (t : set α), ∃ (H : t ∈ b), a ∈ t ∧ t ⊆ s :=
  sorry

theorem is_topological_basis.nhds_has_basis {α : Type u} [t : topological_space α] {b : set (set α)}
    (hb : is_topological_basis b) {a : α} :
    filter.has_basis (nhds a) (fun (t : set α) => t ∈ b ∧ a ∈ t) fun (t : set α) => t :=
  sorry

theorem is_open_of_is_topological_basis {α : Type u} [t : topological_space α] {s : set α}
    {b : set (set α)} (hb : is_topological_basis b) (hs : s ∈ b) : is_open s :=
  sorry

theorem mem_basis_subset_of_mem_open {α : Type u} [t : topological_space α] {b : set (set α)}
    (hb : is_topological_basis b) {a : α} {u : set α} (au : a ∈ u) (ou : is_open u) :
    ∃ (v : set α), ∃ (H : v ∈ b), a ∈ v ∧ v ⊆ u :=
  iff.mp (mem_nhds_of_is_topological_basis hb) (mem_nhds_sets ou au)

theorem sUnion_basis_of_is_open {α : Type u} [t : topological_space α] {B : set (set α)}
    (hB : is_topological_basis B) {u : set α} (ou : is_open u) :
    ∃ (S : set (set α)), ∃ (H : S ⊆ B), u = ⋃₀S :=
  sorry

theorem Union_basis_of_is_open {α : Type u} [t : topological_space α] {B : set (set α)}
    (hB : is_topological_basis B) {u : set α} (ou : is_open u) :
    ∃ (β : Type u), ∃ (f : β → set α), (u = set.Union fun (i : β) => f i) ∧ ∀ (i : β), f i ∈ B :=
  sorry

/-- A separable space is one with a countable dense subset, available through
`topological_space.exists_countable_dense`. If `α` is also known to be nonempty, then
`topological_space.dense_seq` provides a sequence `ℕ → α` with dense range, see
`topological_space.dense_range_dense_seq`.

If `α` is a uniform space with countably generated uniformity filter (e.g., an `emetric_space`),
then this condition is equivalent to `topological_space.second_countable_topology α`. In this case
the latter should be used as a typeclass argument in theorems because Lean can automatically deduce
`separable_space` from `second_countable_topology` but it can't deduce `second_countable_topology`
and `emetric_space`. -/
class separable_space (α : Type u) [t : topological_space α] where
  exists_countable_dense : ∃ (s : set α), set.countable s ∧ dense s

theorem exists_countable_dense (α : Type u) [t : topological_space α] [separable_space α] :
    ∃ (s : set α), set.countable s ∧ dense s :=
  separable_space.exists_countable_dense

/-- A nonempty separable space admits a sequence with dense range. Instead of running `cases` on the
conclusion of this lemma, you might want to use `topological_space.dense_seq` and
`topological_space.dense_range_dense_seq`.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
theorem exists_dense_seq (α : Type u) [t : topological_space α] [separable_space α] [Nonempty α] :
    ∃ (u : ℕ → α), dense_range u :=
  sorry

/-- A sequence dense in a non-empty separable topological space.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
def dense_seq (α : Type u) [t : topological_space α] [separable_space α] [Nonempty α] : ℕ → α :=
  classical.some (exists_dense_seq α)

/-- The sequence `dense_seq α` has dense range. -/
@[simp] theorem dense_range_dense_seq (α : Type u) [t : topological_space α] [separable_space α]
    [Nonempty α] : dense_range (dense_seq α) :=
  classical.some_spec (exists_dense_seq α)

end topological_space


/-- If `α` is a separable space and `f : α → β` is a continuous map with dense range, then `β` is
a separable space as well. E.g., the completion of a separable uniform space is separable. -/
protected theorem dense_range.separable_space {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space.separable_space α] [topological_space β] {f : α → β} (h : dense_range f)
    (h' : continuous f) : topological_space.separable_space β :=
  sorry

namespace topological_space


/-- A first-countable space is one in which every point has a
  countable neighborhood basis. -/
class first_countable_topology (α : Type u) [t : topological_space α] where
  nhds_generated_countable : ∀ (a : α), filter.is_countably_generated (nhds a)

namespace first_countable_topology


theorem tendsto_subseq {α : Type u} [t : topological_space α] [first_countable_topology α]
    {u : ℕ → α} {x : α} (hx : map_cluster_pt x filter.at_top u) :
    ∃ (ψ : ℕ → ℕ), strict_mono ψ ∧ filter.tendsto (u ∘ ψ) filter.at_top (nhds x) :=
  filter.is_countably_generated.subseq_tendsto (nhds_generated_countable x) hx

end first_countable_topology


theorem is_countably_generated_nhds {α : Type u} [t : topological_space α]
    [first_countable_topology α] (x : α) : filter.is_countably_generated (nhds x) :=
  first_countable_topology.nhds_generated_countable x

theorem is_countably_generated_nhds_within {α : Type u} [t : topological_space α]
    [first_countable_topology α] (x : α) (s : set α) :
    filter.is_countably_generated (nhds_within x s) :=
  filter.is_countably_generated.inf_principal (is_countably_generated_nhds x) s

/-- A second-countable space is one with a countable basis. -/
class second_countable_topology (α : Type u) [t : topological_space α] where
  is_open_generated_countable : ∃ (b : set (set α)), set.countable b ∧ t = generate_from b

protected instance second_countable_topology.to_first_countable_topology (α : Type u)
    [t : topological_space α] [second_countable_topology α] : first_countable_topology α :=
  sorry

theorem second_countable_topology_induced (α : Type u) (β : Type u_1) [t : topological_space β]
    [second_countable_topology β] (f : α → β) : second_countable_topology α :=
  sorry

protected instance subtype.second_countable_topology (α : Type u) [t : topological_space α]
    (s : set α) [second_countable_topology α] : second_countable_topology ↥s :=
  second_countable_topology_induced (↥s) α coe

theorem is_open_generated_countable_inter (α : Type u) [t : topological_space α]
    [second_countable_topology α] :
    ∃ (b : set (set α)), set.countable b ∧ ¬∅ ∈ b ∧ is_topological_basis b :=
  sorry

/- TODO: more fine grained instances for first_countable_topology, separable_space, t2_space, ... -/

protected instance prod.second_countable_topology (α : Type u) [t : topological_space α]
    {β : Type u_1} [topological_space β] [second_countable_topology α]
    [second_countable_topology β] : second_countable_topology (α × β) :=
  second_countable_topology.mk sorry

protected instance second_countable_topology_fintype {ι : Type u_1} {π : ι → Type u_2} [fintype ι]
    [t : (a : ι) → topological_space (π a)] [sc : ∀ (a : ι), second_countable_topology (π a)] :
    second_countable_topology ((a : ι) → π a) :=
  (fun
      (this :
      ∀ (i : ι), ∃ (b : set (set (π i))), set.countable b ∧ ¬∅ ∈ b ∧ is_topological_basis b) =>
      sorry)
    fun (a : ι) => is_open_generated_countable_inter (π a)

protected instance second_countable_topology.to_separable_space (α : Type u)
    [t : topological_space α] [second_countable_topology α] : separable_space α :=
  sorry

theorem is_open_Union_countable {α : Type u} [t : topological_space α] [second_countable_topology α]
    {ι : Type u_1} (s : ι → set α) (H : ∀ (i : ι), is_open (s i)) :
    ∃ (T : set ι),
        set.countable T ∧
          (set.Union fun (i : ι) => set.Union fun (H : i ∈ T) => s i) =
            set.Union fun (i : ι) => s i :=
  sorry

theorem is_open_sUnion_countable {α : Type u} [t : topological_space α]
    [second_countable_topology α] (S : set (set α)) (H : ∀ (s : set α), s ∈ S → is_open s) :
    ∃ (T : set (set α)), set.countable T ∧ T ⊆ S ∧ ⋃₀T = ⋃₀S :=
  sorry

/-- In a topological space with second countable topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
theorem countable_cover_nhds {α : Type u} [t : topological_space α] [second_countable_topology α]
    {f : α → set α} (hf : ∀ (x : α), f x ∈ nhds x) :
    ∃ (s : set α),
        set.countable s ∧ (set.Union fun (x : α) => set.Union fun (H : x ∈ s) => f x) = set.univ :=
  sorry

end Mathlib