/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.bases
import Mathlib.data.finset.order
import Mathlib.PostPort

universes u v u_1 l u_2 

namespace Mathlib

/-!
# Properties of subsets of topological spaces

In this file we define various properties of subsets of a topological space, and some classes on
topological spaces.

## Main definitions

We define the following properties for sets in a topological space:

* `is_compact`: each open cover has a finite subcover. This is defined in mathlib using filters.
  The main property of a compact set is `is_compact.elim_finite_subcover`.
* `is_clopen`: a set that is both open and closed.
* `is_irreducible`: a nonempty set that has contains no non-trivial pair of disjoint opens.
  See also the section below in the module doc.
* `is_connected`: a nonempty set that has no non-trivial open partition.
  See also the section below in the module doc.
  `connected_component` is the connected component of an element in the space.
* `is_totally_disconnected`: all of its connected components are singletons.
* `is_totally_separated`: any two points can be separated by two disjoint opens that cover the set.

For each of these definitions (except for `is_clopen`), we also have a class stating that the whole
space satisfies that property:
`compact_space`, `irreducible_space`, `connected_space`, `totally_disconnected_space`,
`totally_separated_space`.

Furthermore, we have two more classes:
* `locally_compact_space`: for every point `x`, every open neighborhood of `x` contains a compact
  neighborhood of `x`. The definition is formulated in terms of the neighborhood filter.
* `sigma_compact_space`: a space that is the union of a countably many compact subspaces.

## On the definition of irreducible and connected sets/spaces

In informal mathematics, irreducible and connected spaces are assumed to be nonempty.
We formalise the predicate without that assumption
as `is_preirreducible` and `is_preconnected` respectively.
In other words, the only difference is whether the empty space
counts as irreducible and/or connected.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
-/

/- compact sets -/

/-- A set `s` is compact if for every filter `f` that contains `s`,
    every set of `f` also meets every neighborhood of some `a ∈ s`. -/
def is_compact {α : Type u} [topological_space α] (s : set α)  :=
  ∀ {f : filter α} [_inst_2 : filter.ne_bot f], f ≤ filter.principal s → ∃ (a : α), ∃ (H : a ∈ s), cluster_pt a f

/-- The complement to a compact set belongs to a filter `f` if it belongs to each filter
`𝓝 a ⊓ f`, `a ∈ s`. -/
theorem is_compact.compl_mem_sets {α : Type u} [topological_space α] {s : set α} (hs : is_compact s) {f : filter α} (hf : ∀ (a : α), a ∈ s → sᶜ ∈ nhds a ⊓ f) : sᶜ ∈ f := sorry

/-- The complement to a compact set belongs to a filter `f` if each `a ∈ s` has a neighborhood `t`
within `s` such that `tᶜ` belongs to `f`. -/
theorem is_compact.compl_mem_sets_of_nhds_within {α : Type u} [topological_space α] {s : set α} (hs : is_compact s) {f : filter α} (hf : ∀ (a : α) (H : a ∈ s), ∃ (t : set α), ∃ (H : t ∈ nhds_within a s), tᶜ ∈ f) : sᶜ ∈ f := sorry

/-- If `p : set α → Prop` is stable under restriction and union, and each point `x`
  of a compact set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
theorem is_compact.induction_on {α : Type u} [topological_space α] {s : set α} (hs : is_compact s) {p : set α → Prop} (he : p ∅) (hmono : ∀ {s t : set α}, s ⊆ t → p t → p s) (hunion : ∀ {s t : set α}, p s → p t → p (s ∪ t)) (hnhds : ∀ (x : α) (H : x ∈ s), ∃ (t : set α), ∃ (H : t ∈ nhds_within x s), p t) : p s := sorry

/-- The intersection of a compact set and a closed set is a compact set. -/
theorem is_compact.inter_right {α : Type u} [topological_space α] {s : set α} {t : set α} (hs : is_compact s) (ht : is_closed t) : is_compact (s ∩ t) := sorry

/-- The intersection of a closed set and a compact set is a compact set. -/
theorem is_compact.inter_left {α : Type u} [topological_space α] {s : set α} {t : set α} (ht : is_compact t) (hs : is_closed s) : is_compact (s ∩ t) :=
  set.inter_comm t s ▸ is_compact.inter_right ht hs

/-- The set difference of a compact set and an open set is a compact set. -/
theorem compact_diff {α : Type u} [topological_space α] {s : set α} {t : set α} (hs : is_compact s) (ht : is_open t) : is_compact (s \ t) :=
  is_compact.inter_right hs (iff.mpr is_closed_compl_iff ht)

/-- A closed subset of a compact set is a compact set. -/
theorem compact_of_is_closed_subset {α : Type u} [topological_space α] {s : set α} {t : set α} (hs : is_compact s) (ht : is_closed t) (h : t ⊆ s) : is_compact t :=
  set.inter_eq_self_of_subset_right h ▸ is_compact.inter_right hs ht

theorem is_compact.adherence_nhdset {α : Type u} [topological_space α] {s : set α} {t : set α} {f : filter α} (hs : is_compact s) (hf₂ : f ≤ filter.principal s) (ht₁ : is_open t) (ht₂ : ∀ (a : α), a ∈ s → cluster_pt a f → a ∈ t) : t ∈ f := sorry

theorem compact_iff_ultrafilter_le_nhds {α : Type u} [topological_space α] {s : set α} : is_compact s ↔ ∀ (f : ultrafilter α), ↑f ≤ filter.principal s → ∃ (a : α), ∃ (H : a ∈ s), ↑f ≤ nhds a := sorry

theorem is_compact.ultrafilter_le_nhds {α : Type u} [topological_space α] {s : set α} : is_compact s → ∀ (f : ultrafilter α), ↑f ≤ filter.principal s → ∃ (a : α), ∃ (H : a ∈ s), ↑f ≤ nhds a :=
  iff.mp compact_iff_ultrafilter_le_nhds

/-- For every open cover of a compact set, there exists a finite subcover. -/
theorem is_compact.elim_finite_subcover {α : Type u} [topological_space α] {s : set α} {ι : Type v} (hs : is_compact s) (U : ι → set α) (hUo : ∀ (i : ι), is_open (U i)) (hsU : s ⊆ set.Union fun (i : ι) => U i) : ∃ (t : finset ι), s ⊆ set.Union fun (i : ι) => set.Union fun (H : i ∈ t) => U i := sorry

/-- For every family of closed sets whose intersection avoids a compact set,
there exists a finite subfamily whose intersection avoids this compact set. -/
theorem is_compact.elim_finite_subfamily_closed {α : Type u} [topological_space α] {s : set α} {ι : Type v} (hs : is_compact s) (Z : ι → set α) (hZc : ∀ (i : ι), is_closed (Z i)) (hsZ : (s ∩ set.Inter fun (i : ι) => Z i) = ∅) : ∃ (t : finset ι), (s ∩ set.Inter fun (i : ι) => set.Inter fun (H : i ∈ t) => Z i) = ∅ := sorry

/-- To show that a compact set intersects the intersection of a family of closed sets,
  it is sufficient to show that it intersects every finite subfamily. -/
theorem is_compact.inter_Inter_nonempty {α : Type u} [topological_space α] {s : set α} {ι : Type v} (hs : is_compact s) (Z : ι → set α) (hZc : ∀ (i : ι), is_closed (Z i)) (hsZ : ∀ (t : finset ι), set.nonempty (s ∩ set.Inter fun (i : ι) => set.Inter fun (H : i ∈ t) => Z i)) : set.nonempty (s ∩ set.Inter fun (i : ι) => Z i) := sorry

/-- Cantor's intersection theorem:
the intersection of a directed family of nonempty compact closed sets is nonempty. -/
theorem is_compact.nonempty_Inter_of_directed_nonempty_compact_closed {α : Type u} [topological_space α] {ι : Type v} [hι : Nonempty ι] (Z : ι → set α) (hZd : directed superset Z) (hZn : ∀ (i : ι), set.nonempty (Z i)) (hZc : ∀ (i : ι), is_compact (Z i)) (hZcl : ∀ (i : ι), is_closed (Z i)) : set.nonempty (set.Inter fun (i : ι) => Z i) := sorry

/-- Cantor's intersection theorem for sequences indexed by `ℕ`:
the intersection of a decreasing sequence of nonempty compact closed sets is nonempty. -/
theorem is_compact.nonempty_Inter_of_sequence_nonempty_compact_closed {α : Type u} [topological_space α] (Z : ℕ → set α) (hZd : ∀ (i : ℕ), Z (i + 1) ⊆ Z i) (hZn : ∀ (i : ℕ), set.nonempty (Z i)) (hZ0 : is_compact (Z 0)) (hZcl : ∀ (i : ℕ), is_closed (Z i)) : set.nonempty (set.Inter fun (i : ℕ) => Z i) := sorry

/-- For every open cover of a compact set, there exists a finite subcover. -/
theorem is_compact.elim_finite_subcover_image {α : Type u} {β : Type v} [topological_space α] {s : set α} {b : set β} {c : β → set α} (hs : is_compact s) (hc₁ : ∀ (i : β), i ∈ b → is_open (c i)) (hc₂ : s ⊆ set.Union fun (i : β) => set.Union fun (H : i ∈ b) => c i) : ∃ (b' : set β), ∃ (H : b' ⊆ b), set.finite b' ∧ s ⊆ set.Union fun (i : β) => set.Union fun (H : i ∈ b') => c i := sorry

/-- A set `s` is compact if for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem compact_of_finite_subfamily_closed {α : Type u} [topological_space α] {s : set α} (h : ∀ {ι : Type u} (Z : ι → set α),
  (∀ (i : ι), is_closed (Z i)) →
    (s ∩ set.Inter fun (i : ι) => Z i) = ∅ →
      ∃ (t : finset ι), (s ∩ set.Inter fun (i : ι) => set.Inter fun (H : i ∈ t) => Z i) = ∅) : is_compact s := sorry

/-- A set `s` is compact if for every open cover of `s`, there exists a finite subcover. -/
theorem compact_of_finite_subcover {α : Type u} [topological_space α] {s : set α} (h : ∀ {ι : Type u} (U : ι → set α),
  (∀ (i : ι), is_open (U i)) →
    (s ⊆ set.Union fun (i : ι) => U i) → ∃ (t : finset ι), s ⊆ set.Union fun (i : ι) => set.Union fun (H : i ∈ t) => U i) : is_compact s := sorry

/-- A set `s` is compact if and only if
for every open cover of `s`, there exists a finite subcover. -/
theorem compact_iff_finite_subcover {α : Type u} [topological_space α] {s : set α} : is_compact s ↔
  ∀ {ι : Type u} (U : ι → set α),
    (∀ (i : ι), is_open (U i)) →
      (s ⊆ set.Union fun (i : ι) => U i) →
        ∃ (t : finset ι), s ⊆ set.Union fun (i : ι) => set.Union fun (H : i ∈ t) => U i :=
  { mp := fun (hs : is_compact s) (ι : Type u) => is_compact.elim_finite_subcover hs, mpr := compact_of_finite_subcover }

/-- A set `s` is compact if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem compact_iff_finite_subfamily_closed {α : Type u} [topological_space α] {s : set α} : is_compact s ↔
  ∀ {ι : Type u} (Z : ι → set α),
    (∀ (i : ι), is_closed (Z i)) →
      (s ∩ set.Inter fun (i : ι) => Z i) = ∅ →
        ∃ (t : finset ι), (s ∩ set.Inter fun (i : ι) => set.Inter fun (H : i ∈ t) => Z i) = ∅ :=
  { mp := fun (hs : is_compact s) (ι : Type u) => is_compact.elim_finite_subfamily_closed hs,
    mpr := compact_of_finite_subfamily_closed }

@[simp] theorem compact_empty {α : Type u} [topological_space α] : is_compact ∅ :=
  fun (f : filter α) (hnf : filter.ne_bot f) (hsf : f ≤ filter.principal ∅) =>
    not.elim hnf (iff.mp filter.empty_in_sets_eq_bot (iff.mp filter.le_principal_iff hsf))

@[simp] theorem compact_singleton {α : Type u} [topological_space α] {a : α} : is_compact (singleton a) := sorry

theorem set.subsingleton.is_compact {α : Type u} [topological_space α] {s : set α} (hs : set.subsingleton s) : is_compact s :=
  set.subsingleton.induction_on hs compact_empty fun (x : α) => compact_singleton

theorem set.finite.compact_bUnion {α : Type u} {β : Type v} [topological_space α] {s : set β} {f : β → set α} (hs : set.finite s) (hf : ∀ (i : β), i ∈ s → is_compact (f i)) : is_compact (set.Union fun (i : β) => set.Union fun (H : i ∈ s) => f i) := sorry

theorem compact_Union {α : Type u} {β : Type v} [topological_space α] {f : β → set α} [fintype β] (h : ∀ (i : β), is_compact (f i)) : is_compact (set.Union fun (i : β) => f i) :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (is_compact (set.Union fun (i : β) => f i))) (Eq.symm (set.bUnion_univ fun (i : β) => f i))))
    (set.finite.compact_bUnion set.finite_univ fun (i : β) (_x : i ∈ set.univ) => h i)

theorem set.finite.is_compact {α : Type u} [topological_space α] {s : set α} (hs : set.finite s) : is_compact s :=
  set.bUnion_of_singleton s ▸ set.finite.compact_bUnion hs fun (_x : α) (_x_1 : _x ∈ s) => compact_singleton

theorem is_compact.union {α : Type u} [topological_space α] {s : set α} {t : set α} (hs : is_compact s) (ht : is_compact t) : is_compact (s ∪ t) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_compact (s ∪ t))) set.union_eq_Union))
    (compact_Union fun (b : Bool) => bool.cases_on b ht hs)

theorem is_compact.insert {α : Type u} [topological_space α] {s : set α} (hs : is_compact s) (a : α) : is_compact (insert a s) :=
  is_compact.union compact_singleton hs

/-- `filter.cocompact` is the filter generated by complements to compact sets. -/
def filter.cocompact (α : Type u_1) [topological_space α] : filter α :=
  infi fun (s : set α) => infi fun (hs : is_compact s) => filter.principal (sᶜ)

theorem filter.has_basis_cocompact {α : Type u} [topological_space α] : filter.has_basis (filter.cocompact α) is_compact compl := sorry

theorem filter.mem_cocompact {α : Type u} [topological_space α] {s : set α} : s ∈ filter.cocompact α ↔ ∃ (t : set α), is_compact t ∧ tᶜ ⊆ s :=
  iff.trans (filter.has_basis.mem_iff filter.has_basis_cocompact) (exists_congr fun (t : set α) => exists_prop)

theorem filter.mem_cocompact' {α : Type u} [topological_space α] {s : set α} : s ∈ filter.cocompact α ↔ ∃ (t : set α), is_compact t ∧ sᶜ ⊆ t :=
  iff.trans filter.mem_cocompact
    (exists_congr fun (t : set α) => and_congr_right fun (ht : is_compact t) => set.compl_subset_comm)

theorem is_compact.compl_mem_cocompact {α : Type u} [topological_space α] {s : set α} (hs : is_compact s) : sᶜ ∈ filter.cocompact α :=
  filter.has_basis.mem_of_mem filter.has_basis_cocompact hs

/-- `nhds_contain_boxes s t` means that any open neighborhood of `s × t` in `α × β` includes
a product of an open neighborhood of `s` by an open neighborhood of `t`. -/
def nhds_contain_boxes {α : Type u} {β : Type v} [topological_space α] [topological_space β] (s : set α) (t : set β)  :=
  ∀ (n : set (α × β)),
    is_open n → set.prod s t ⊆ n → ∃ (u : set α), ∃ (v : set β), is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ set.prod u v ⊆ n

theorem nhds_contain_boxes.symm {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} {t : set β} : nhds_contain_boxes s t → nhds_contain_boxes t s := sorry

theorem nhds_contain_boxes.comm {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} {t : set β} : nhds_contain_boxes s t ↔ nhds_contain_boxes t s :=
  { mp := nhds_contain_boxes.symm, mpr := nhds_contain_boxes.symm }

theorem nhds_contain_boxes_of_singleton {α : Type u} {β : Type v} [topological_space α] [topological_space β] {x : α} {y : β} : nhds_contain_boxes (singleton x) (singleton y) := sorry

theorem nhds_contain_boxes_of_compact {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} (hs : is_compact s) (t : set β) (H : ∀ (x : α), x ∈ s → nhds_contain_boxes (singleton x) t) : nhds_contain_boxes s t := sorry

/-- If `s` and `t` are compact sets and `n` is an open neighborhood of `s × t`, then there exist
open neighborhoods `u ⊇ s` and `v ⊇ t` such that `u × v ⊆ n`. -/
theorem generalized_tube_lemma {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} (hs : is_compact s) {t : set β} (ht : is_compact t) {n : set (α × β)} (hn : is_open n) (hp : set.prod s t ⊆ n) : ∃ (u : set α), ∃ (v : set β), is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ set.prod u v ⊆ n := sorry

/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
class compact_space (α : Type u_1) [topological_space α] 
where
  compact_univ : is_compact set.univ

protected instance subsingleton.compact_space {α : Type u} [topological_space α] [subsingleton α] : compact_space α :=
  compact_space.mk (set.subsingleton.is_compact set.subsingleton_univ)

theorem compact_univ {α : Type u} [topological_space α] [h : compact_space α] : is_compact set.univ :=
  compact_space.compact_univ

theorem cluster_point_of_compact {α : Type u} [topological_space α] [compact_space α] (f : filter α) [filter.ne_bot f] : ∃ (x : α), cluster_pt x f := sorry

theorem compact_space_of_finite_subfamily_closed {α : Type u} [topological_space α] (h : ∀ {ι : Type u} (Z : ι → set α),
  (∀ (i : ι), is_closed (Z i)) →
    (set.Inter fun (i : ι) => Z i) = ∅ →
      ∃ (t : finset ι), (set.Inter fun (i : ι) => set.Inter fun (H : i ∈ t) => Z i) = ∅) : compact_space α := sorry

theorem is_closed.compact {α : Type u} [topological_space α] [compact_space α] {s : set α} (h : is_closed s) : is_compact s :=
  compact_of_is_closed_subset compact_univ h (set.subset_univ s)

theorem is_compact.image_of_continuous_on {α : Type u} {β : Type v} [topological_space α] {s : set α} [topological_space β] {f : α → β} (hs : is_compact s) (hf : continuous_on f s) : is_compact (f '' s) := sorry

theorem is_compact.image {α : Type u} {β : Type v} [topological_space α] {s : set α} [topological_space β] {f : α → β} (hs : is_compact s) (hf : continuous f) : is_compact (f '' s) :=
  is_compact.image_of_continuous_on hs (continuous.continuous_on hf)

theorem compact_range {α : Type u} {β : Type v} [topological_space α] [topological_space β] [compact_space α] {f : α → β} (hf : continuous f) : is_compact (set.range f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_compact (set.range f))) (Eq.symm set.image_univ)))
    (is_compact.image compact_univ hf)

/-- If X is is_compact then pr₂ : X × Y → Y is a closed map -/
theorem is_closed_proj_of_compact {X : Type u_1} [topological_space X] [compact_space X] {Y : Type u_2} [topological_space Y] : is_closed_map prod.snd := sorry

theorem embedding.compact_iff_compact_image {α : Type u} {β : Type v} [topological_space α] {s : set α} [topological_space β] {f : α → β} (hf : embedding f) : is_compact s ↔ is_compact (f '' s) := sorry

theorem compact_iff_compact_in_subtype {α : Type u} [topological_space α] {p : α → Prop} {s : set (Subtype fun (a : α) => p a)} : is_compact s ↔ is_compact (coe '' s) :=
  embedding.compact_iff_compact_image embedding_subtype_coe

theorem compact_iff_compact_univ {α : Type u} [topological_space α] {s : set α} : is_compact s ↔ is_compact set.univ := sorry

theorem compact_iff_compact_space {α : Type u} [topological_space α] {s : set α} : is_compact s ↔ compact_space ↥s :=
  iff.trans compact_iff_compact_univ
    { mp := fun (h : is_compact set.univ) => compact_space.mk h, mpr := compact_space.compact_univ }

theorem is_compact.prod {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} {t : set β} (hs : is_compact s) (ht : is_compact t) : is_compact (set.prod s t) := sorry

/-- Finite topological spaces are compact. -/
protected instance fintype.compact_space {α : Type u} [topological_space α] [fintype α] : compact_space α :=
  compact_space.mk (set.finite.is_compact set.finite_univ)

/-- The product of two compact spaces is compact. -/
protected instance prod.compact_space {α : Type u} {β : Type v} [topological_space α] [topological_space β] [compact_space α] [compact_space β] : compact_space (α × β) :=
  compact_space.mk
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_compact set.univ)) (Eq.symm set.univ_prod_univ)))
      (is_compact.prod compact_univ compact_univ))

/-- The disjoint union of two compact spaces is compact. -/
protected instance sum.compact_space {α : Type u} {β : Type v} [topological_space α] [topological_space β] [compact_space α] [compact_space β] : compact_space (α ⊕ β) :=
  compact_space.mk
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_compact set.univ)) (Eq.symm set.range_inl_union_range_inr)))
      (is_compact.union (compact_range continuous_inl) (compact_range continuous_inr)))

/-- Tychonoff's theorem -/
theorem compact_pi_infinite {ι : Type u_1} {π : ι → Type u_2} [(i : ι) → topological_space (π i)] {s : (i : ι) → set (π i)} : (∀ (i : ι), is_compact (s i)) → is_compact (set_of fun (x : (i : ι) → π i) => ∀ (i : ι), x i ∈ s i) := sorry

/-- A version of Tychonoff's theorem that uses `set.pi`. -/
theorem compact_univ_pi {ι : Type u_1} {π : ι → Type u_2} [(i : ι) → topological_space (π i)] {s : (i : ι) → set (π i)} (h : ∀ (i : ι), is_compact (s i)) : is_compact (set.pi set.univ s) := sorry

protected instance pi.compact {ι : Type u_1} {π : ι → Type u_2} [(i : ι) → topological_space (π i)] [∀ (i : ι), compact_space (π i)] : compact_space ((i : ι) → π i) := sorry

protected instance quot.compact_space {α : Type u} [topological_space α] {r : α → α → Prop} [compact_space α] : compact_space (Quot r) :=
  compact_space.mk
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_compact set.univ)) (Eq.symm (set.range_quot_mk r))))
      (compact_range continuous_quot_mk))

protected instance quotient.compact_space {α : Type u} [topological_space α] {s : setoid α} [compact_space α] : compact_space (quotient s) :=
  quot.compact_space

/-- There are various definitions of "locally compact space" in the literature, which agree for
Hausdorff spaces but not in general. This one is the precise condition on X needed for the
evaluation `map C(X, Y) × X → Y` to be continuous for all `Y` when `C(X, Y)` is given the
compact-open topology. -/
class locally_compact_space (α : Type u_1) [topological_space α] 
where
  local_compact_nhds : ∀ (x : α) (n : set α) (H : n ∈ nhds x), ∃ (s : set α), ∃ (H : s ∈ nhds x), s ⊆ n ∧ is_compact s

/-- A reformulation of the definition of locally compact space: In a locally compact space,
  every open set containing `x` has a compact subset containing `x` in its interior. -/
theorem exists_compact_subset {α : Type u} [topological_space α] [locally_compact_space α] {x : α} {U : set α} (hU : is_open U) (hx : x ∈ U) : ∃ (K : set α), is_compact K ∧ x ∈ interior K ∧ K ⊆ U := sorry

/-- In a locally compact space every point has a compact neighborhood. -/
theorem exists_compact_mem_nhds {α : Type u} [topological_space α] [locally_compact_space α] (x : α) : ∃ (K : set α), is_compact K ∧ K ∈ nhds x := sorry

theorem ultrafilter.le_nhds_Lim {α : Type u} [topological_space α] [compact_space α] (F : ultrafilter α) : ↑F ≤ nhds (Lim ↑F) := sorry

/-- A σ-compact space is a space that is the union of a countable collection of compact subspaces.
  Note that a locally compact separable T₂ space need not be σ-compact.
  The sequence can be extracted using `topological_space.compact_covering`. -/
class sigma_compact_space (α : Type u_1) [topological_space α] 
where
  exists_compact_covering : ∃ (K : ℕ → set α), (∀ (n : ℕ), is_compact (K n)) ∧ (set.Union fun (n : ℕ) => K n) = set.univ

protected instance compact_space.sigma_compact {α : Type u} [topological_space α] [compact_space α] : sigma_compact_space α :=
  sigma_compact_space.mk
    (Exists.intro (fun (_x : ℕ) => set.univ) { left := fun (_x : ℕ) => compact_univ, right := set.Union_const set.univ })

theorem sigma_compact_space.of_countable {α : Type u} [topological_space α] (S : set (set α)) (Hc : set.countable S) (Hcomp : ∀ (s : set α), s ∈ S → is_compact s) (HU : ⋃₀S = set.univ) : sigma_compact_space α :=
  sigma_compact_space.mk
    (iff.mpr (set.exists_seq_cover_iff_countable (Exists.intro ∅ compact_empty))
      (Exists.intro S { left := Hc, right := { left := Hcomp, right := HU } }))

theorem sigma_compact_space_of_locally_compact_second_countable {α : Type u} [topological_space α] [locally_compact_space α] [topological_space.second_countable_topology α] : sigma_compact_space α := sorry

/-- An arbitrary compact covering of a σ-compact space. -/
def compact_covering (α : Type u) [topological_space α] [sigma_compact_space α] : ℕ → set α :=
  classical.some sigma_compact_space.exists_compact_covering

theorem is_compact_compact_covering (α : Type u) [topological_space α] [sigma_compact_space α] (n : ℕ) : is_compact (compact_covering α n) :=
  and.left (classical.some_spec sigma_compact_space.exists_compact_covering) n

theorem Union_compact_covering (α : Type u) [topological_space α] [sigma_compact_space α] : (set.Union fun (n : ℕ) => compact_covering α n) = set.univ :=
  and.right (classical.some_spec sigma_compact_space.exists_compact_covering)

/-- A set is clopen if it is both open and closed. -/
def is_clopen {α : Type u} [topological_space α] (s : set α)  :=
  is_open s ∧ is_closed s

theorem is_clopen_union {α : Type u} [topological_space α] {s : set α} {t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s ∪ t) :=
  { left := is_open_union (and.left hs) (and.left ht), right := is_closed_union (and.right hs) (and.right ht) }

theorem is_clopen_inter {α : Type u} [topological_space α] {s : set α} {t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s ∩ t) :=
  { left := is_open_inter (and.left hs) (and.left ht), right := is_closed_inter (and.right hs) (and.right ht) }

@[simp] theorem is_clopen_empty {α : Type u} [topological_space α] : is_clopen ∅ :=
  { left := is_open_empty, right := is_closed_empty }

@[simp] theorem is_clopen_univ {α : Type u} [topological_space α] : is_clopen set.univ :=
  { left := is_open_univ, right := is_closed_univ }

theorem is_clopen_compl {α : Type u} [topological_space α] {s : set α} (hs : is_clopen s) : is_clopen (sᶜ) :=
  { left := and.right hs, right := iff.mpr is_closed_compl_iff (and.left hs) }

@[simp] theorem is_clopen_compl_iff {α : Type u} [topological_space α] {s : set α} : is_clopen (sᶜ) ↔ is_clopen s :=
  { mp := fun (h : is_clopen (sᶜ)) => compl_compl s ▸ is_clopen_compl h, mpr := is_clopen_compl }

theorem is_clopen_diff {α : Type u} [topological_space α] {s : set α} {t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s \ t) :=
  is_clopen_inter hs (is_clopen_compl ht)

theorem is_clopen_Inter {α : Type u} [topological_space α] {β : Type u_1} [fintype β] {s : β → set α} (h : ∀ (i : β), is_clopen (s i)) : is_clopen (set.Inter fun (i : β) => s i) :=
  { left := is_open_Inter (and.left (iff.mp forall_and_distrib h)),
    right := is_closed_Inter (and.right (iff.mp forall_and_distrib h)) }

theorem is_clopen_bInter {α : Type u} [topological_space α] {β : Type u_1} {s : finset β} {f : β → set α} (h : ∀ (i : β), i ∈ s → is_clopen (f i)) : is_clopen (set.Inter fun (i : β) => set.Inter fun (H : i ∈ s) => f i) := sorry

theorem continuous_on.preimage_clopen_of_clopen {α : Type u} [topological_space α] {β : Type u_1} [topological_space β] {f : α → β} {s : set α} {t : set β} (hf : continuous_on f s) (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s ∩ f ⁻¹' t) :=
  { left := continuous_on.preimage_open_of_open hf (and.left hs) (and.left ht),
    right := continuous_on.preimage_closed_of_closed hf (and.right hs) (and.right ht) }

/-- The intersection of a disjoint covering by two open sets of a clopen set will be clopen. -/
theorem is_clopen_inter_of_disjoint_cover_clopen {α : Type u} [topological_space α] {Z : set α} {a : set α} {b : set α} (h : is_clopen Z) (cover : Z ⊆ a ∪ b) (ha : is_open a) (hb : is_open b) (hab : a ∩ b = ∅) : is_clopen (Z ∩ a) := sorry

/-- A preirreducible set `s` is one where there is no non-trivial pair of disjoint opens on `s`. -/
def is_preirreducible {α : Type u} [topological_space α] (s : set α)  :=
  ∀ (u v : set α), is_open u → is_open v → set.nonempty (s ∩ u) → set.nonempty (s ∩ v) → set.nonempty (s ∩ (u ∩ v))

/-- An irreducible set `s` is one that is nonempty and
where there is no non-trivial pair of disjoint opens on `s`. -/
def is_irreducible {α : Type u} [topological_space α] (s : set α)  :=
  set.nonempty s ∧ is_preirreducible s

theorem is_irreducible.nonempty {α : Type u} [topological_space α] {s : set α} (h : is_irreducible s) : set.nonempty s :=
  and.left h

theorem is_irreducible.is_preirreducible {α : Type u} [topological_space α] {s : set α} (h : is_irreducible s) : is_preirreducible s :=
  and.right h

theorem is_preirreducible_empty {α : Type u} [topological_space α] : is_preirreducible ∅ := sorry

theorem is_irreducible_singleton {α : Type u} [topological_space α] {x : α} : is_irreducible (singleton x) := sorry

theorem is_preirreducible.closure {α : Type u} [topological_space α] {s : set α} (H : is_preirreducible s) : is_preirreducible (closure s) := sorry

theorem is_irreducible.closure {α : Type u} [topological_space α] {s : set α} (h : is_irreducible s) : is_irreducible (closure s) :=
  { left := set.nonempty.closure (is_irreducible.nonempty h),
    right := is_preirreducible.closure (is_irreducible.is_preirreducible h) }

theorem exists_preirreducible {α : Type u} [topological_space α] (s : set α) (H : is_preirreducible s) : ∃ (t : set α), is_preirreducible t ∧ s ⊆ t ∧ ∀ (u : set α), is_preirreducible u → t ⊆ u → u = t := sorry

/-- A maximal irreducible set that contains a given point. -/
def irreducible_component {α : Type u} [topological_space α] (x : α) : set α :=
  classical.some sorry

theorem irreducible_component_property {α : Type u} [topological_space α] (x : α) : is_preirreducible (irreducible_component x) ∧
  singleton x ⊆ irreducible_component x ∧
    ∀ (u : set α), is_preirreducible u → irreducible_component x ⊆ u → u = irreducible_component x :=
  classical.some_spec (exists_preirreducible (singleton x) (is_irreducible.is_preirreducible is_irreducible_singleton))

theorem mem_irreducible_component {α : Type u} [topological_space α] {x : α} : x ∈ irreducible_component x :=
  iff.mp set.singleton_subset_iff (and.left (and.right (irreducible_component_property x)))

theorem is_irreducible_irreducible_component {α : Type u} [topological_space α] {x : α} : is_irreducible (irreducible_component x) :=
  { left := Exists.intro x mem_irreducible_component, right := and.left (irreducible_component_property x) }

theorem eq_irreducible_component {α : Type u} [topological_space α] {x : α} {s : set α} : is_preirreducible s → irreducible_component x ⊆ s → s = irreducible_component x :=
  and.right (and.right (irreducible_component_property x))

theorem is_closed_irreducible_component {α : Type u} [topological_space α] {x : α} : is_closed (irreducible_component x) :=
  iff.mp closure_eq_iff_is_closed
    (eq_irreducible_component
      (is_preirreducible.closure (is_irreducible.is_preirreducible is_irreducible_irreducible_component)) subset_closure)

/-- A preirreducible space is one where there is no non-trivial pair of disjoint opens. -/
class preirreducible_space (α : Type u) [topological_space α] 
where
  is_preirreducible_univ : is_preirreducible set.univ

/-- An irreducible space is one that is nonempty
and where there is no non-trivial pair of disjoint opens. -/
class irreducible_space (α : Type u) [topological_space α] 
extends Nonempty α, preirreducible_space α
where
  to_nonempty : Nonempty α

theorem nonempty_preirreducible_inter {α : Type u} [topological_space α] [preirreducible_space α] {s : set α} {t : set α} : is_open s → is_open t → set.nonempty s → set.nonempty t → set.nonempty (s ∩ t) := sorry

theorem is_preirreducible.image {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} (H : is_preirreducible s) (f : α → β) (hf : continuous_on f s) : is_preirreducible (f '' s) := sorry

theorem is_irreducible.image {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} (H : is_irreducible s) (f : α → β) (hf : continuous_on f s) : is_irreducible (f '' s) :=
  { left := iff.mpr set.nonempty_image_iff (is_irreducible.nonempty H),
    right := is_preirreducible.image (is_irreducible.is_preirreducible H) f hf }

theorem subtype.preirreducible_space {α : Type u} [topological_space α] {s : set α} (h : is_preirreducible s) : preirreducible_space ↥s := sorry

theorem subtype.irreducible_space {α : Type u} [topological_space α] {s : set α} (h : is_irreducible s) : irreducible_space ↥s :=
  irreducible_space.mk (set.nonempty.to_subtype (is_irreducible.nonempty h))

/-- A set `s` is irreducible if and only if
for every finite collection of open sets all of whose members intersect `s`,
`s` also intersects the intersection of the entire collection
(i.e., there is an element of `s` contained in every member of the collection). -/
theorem is_irreducible_iff_sInter {α : Type u} [topological_space α] {s : set α} : is_irreducible s ↔
  ∀ (U : finset (set α)),
    (∀ (u : set α), u ∈ U → is_open u) → (∀ (u : set α), u ∈ U → set.nonempty (s ∩ u)) → set.nonempty (s ∩ ⋂₀↑U) := sorry

/-- A set is preirreducible if and only if
for every cover by two closed sets, it is contained in one of the two covering sets. -/
theorem is_preirreducible_iff_closed_union_closed {α : Type u} [topological_space α] {s : set α} : is_preirreducible s ↔ ∀ (z₁ z₂ : set α), is_closed z₁ → is_closed z₂ → s ⊆ z₁ ∪ z₂ → s ⊆ z₁ ∨ s ⊆ z₂ := sorry

/-- A set is irreducible if and only if
for every cover by a finite collection of closed sets,
it is contained in one of the members of the collection. -/
theorem is_irreducible_iff_sUnion_closed {α : Type u} [topological_space α] {s : set α} : is_irreducible s ↔
  ∀ (Z : finset (set α)), (∀ (z : set α), z ∈ Z → is_closed z) → ∀ (H : s ⊆ ⋃₀↑Z), ∃ (z : set α), ∃ (H : z ∈ Z), s ⊆ z := sorry

/-- A preconnected set is one where there is no non-trivial open partition. -/
def is_preconnected {α : Type u} [topological_space α] (s : set α)  :=
  ∀ (u v : set α),
    is_open u → is_open v → s ⊆ u ∪ v → set.nonempty (s ∩ u) → set.nonempty (s ∩ v) → set.nonempty (s ∩ (u ∩ v))

/-- A connected set is one that is nonempty and where there is no non-trivial open partition. -/
def is_connected {α : Type u} [topological_space α] (s : set α)  :=
  set.nonempty s ∧ is_preconnected s

theorem is_connected.nonempty {α : Type u} [topological_space α] {s : set α} (h : is_connected s) : set.nonempty s :=
  and.left h

theorem is_connected.is_preconnected {α : Type u} [topological_space α] {s : set α} (h : is_connected s) : is_preconnected s :=
  and.right h

theorem is_preirreducible.is_preconnected {α : Type u} [topological_space α] {s : set α} (H : is_preirreducible s) : is_preconnected s :=
  fun (_x _x_1 : set α) (hu : is_open _x) (hv : is_open _x_1) (_x_2 : s ⊆ _x ∪ _x_1) => H _x _x_1 hu hv

theorem is_irreducible.is_connected {α : Type u} [topological_space α] {s : set α} (H : is_irreducible s) : is_connected s :=
  { left := is_irreducible.nonempty H, right := is_preirreducible.is_preconnected (is_irreducible.is_preirreducible H) }

theorem is_preconnected_empty {α : Type u} [topological_space α] : is_preconnected ∅ :=
  is_preirreducible.is_preconnected is_preirreducible_empty

theorem is_connected_singleton {α : Type u} [topological_space α] {x : α} : is_connected (singleton x) :=
  is_irreducible.is_connected is_irreducible_singleton

/-- If any point of a set is joined to a fixed point by a preconnected subset,
then the original set is preconnected as well. -/
theorem is_preconnected_of_forall {α : Type u} [topological_space α] {s : set α} (x : α) (H : ∀ (y : α) (H : y ∈ s), ∃ (t : set α), ∃ (H : t ⊆ s), x ∈ t ∧ y ∈ t ∧ is_preconnected t) : is_preconnected s := sorry

/-- If any two points of a set are contained in a preconnected subset,
then the original set is preconnected as well. -/
theorem is_preconnected_of_forall_pair {α : Type u} [topological_space α] {s : set α} (H : ∀ (x y : α) (H : x ∈ s) (H : y ∈ s), ∃ (t : set α), ∃ (H : t ⊆ s), x ∈ t ∧ y ∈ t ∧ is_preconnected t) : is_preconnected s := sorry

/-- A union of a family of preconnected sets with a common point is preconnected as well. -/
theorem is_preconnected_sUnion {α : Type u} [topological_space α] (x : α) (c : set (set α)) (H1 : ∀ (s : set α), s ∈ c → x ∈ s) (H2 : ∀ (s : set α), s ∈ c → is_preconnected s) : is_preconnected (⋃₀c) := sorry

theorem is_preconnected.union {α : Type u} [topological_space α] (x : α) {s : set α} {t : set α} (H1 : x ∈ s) (H2 : x ∈ t) (H3 : is_preconnected s) (H4 : is_preconnected t) : is_preconnected (s ∪ t) := sorry

theorem is_connected.union {α : Type u} [topological_space α] {s : set α} {t : set α} (H : set.nonempty (s ∩ t)) (Hs : is_connected s) (Ht : is_connected t) : is_connected (s ∪ t) := sorry

theorem is_preconnected.closure {α : Type u} [topological_space α] {s : set α} (H : is_preconnected s) : is_preconnected (closure s) := sorry

theorem is_connected.closure {α : Type u} [topological_space α] {s : set α} (H : is_connected s) : is_connected (closure s) :=
  { left := set.nonempty.closure (is_connected.nonempty H),
    right := is_preconnected.closure (is_connected.is_preconnected H) }

theorem is_preconnected.image {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} (H : is_preconnected s) (f : α → β) (hf : continuous_on f s) : is_preconnected (f '' s) := sorry

theorem is_connected.image {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} (H : is_connected s) (f : α → β) (hf : continuous_on f s) : is_connected (f '' s) :=
  { left := iff.mpr set.nonempty_image_iff (is_connected.nonempty H),
    right := is_preconnected.image (is_connected.is_preconnected H) f hf }

theorem is_preconnected_closed_iff {α : Type u} [topological_space α] {s : set α} : is_preconnected s ↔
  ∀ (t t' : set α),
    is_closed t → is_closed t' → s ⊆ t ∪ t' → set.nonempty (s ∩ t) → set.nonempty (s ∩ t') → set.nonempty (s ∩ (t ∩ t')) := sorry

/-- The connected component of a point is the maximal connected set
that contains this point. -/
def connected_component {α : Type u} [topological_space α] (x : α) : set α :=
  ⋃₀set_of fun (s : set α) => is_preconnected s ∧ x ∈ s

/-- The connected component of a point inside a set. -/
def connected_component_in {α : Type u} [topological_space α] (F : set α) (x : ↥F) : set α :=
  coe '' connected_component x

theorem mem_connected_component {α : Type u} [topological_space α] {x : α} : x ∈ connected_component x :=
  set.mem_sUnion_of_mem (set.mem_singleton x)
    { left := is_connected.is_preconnected is_connected_singleton, right := set.mem_singleton x }

theorem is_connected_connected_component {α : Type u} [topological_space α] {x : α} : is_connected (connected_component x) := sorry

theorem subset_connected_component {α : Type u} [topological_space α] {x : α} {s : set α} (H1 : is_preconnected s) (H2 : x ∈ s) : s ⊆ connected_component x :=
  fun (z : α) (hz : z ∈ s) => set.mem_sUnion_of_mem hz { left := H1, right := H2 }

theorem is_closed_connected_component {α : Type u} [topological_space α] {x : α} : is_closed (connected_component x) := sorry

theorem irreducible_component_subset_connected_component {α : Type u} [topological_space α] {x : α} : irreducible_component x ⊆ connected_component x :=
  subset_connected_component
    (is_connected.is_preconnected (is_irreducible.is_connected is_irreducible_irreducible_component))
    mem_irreducible_component

/-- A preconnected space is one where there is no non-trivial open partition. -/
class preconnected_space (α : Type u) [topological_space α] 
where
  is_preconnected_univ : is_preconnected set.univ

/-- A connected space is a nonempty one where there is no non-trivial open partition. -/
class connected_space (α : Type u) [topological_space α] 
extends preconnected_space α, Nonempty α
where
  to_nonempty : Nonempty α

theorem is_connected_range {α : Type u} {β : Type v} [topological_space α] [topological_space β] [connected_space α] {f : α → β} (h : continuous f) : is_connected (set.range f) := sorry

theorem connected_space_iff_connected_component {α : Type u} [topological_space α] : connected_space α ↔ ∃ (x : α), connected_component x = set.univ := sorry

protected instance preirreducible_space.preconnected_space (α : Type u) [topological_space α] [preirreducible_space α] : preconnected_space α :=
  preconnected_space.mk (is_preirreducible.is_preconnected (preirreducible_space.is_preirreducible_univ α))

protected instance irreducible_space.connected_space (α : Type u) [topological_space α] [irreducible_space α] : connected_space α :=
  connected_space.mk (irreducible_space.to_nonempty α)

theorem nonempty_inter {α : Type u} [topological_space α] [preconnected_space α] {s : set α} {t : set α} : is_open s → is_open t → s ∪ t = set.univ → set.nonempty s → set.nonempty t → set.nonempty (s ∩ t) := sorry

theorem is_clopen_iff {α : Type u} [topological_space α] [preconnected_space α] {s : set α} : is_clopen s ↔ s = ∅ ∨ s = set.univ := sorry

theorem eq_univ_of_nonempty_clopen {α : Type u} [topological_space α] [preconnected_space α] {s : set α} (h : set.nonempty s) (h' : is_clopen s) : s = set.univ := sorry

theorem subtype.preconnected_space {α : Type u} [topological_space α] {s : set α} (h : is_preconnected s) : preconnected_space ↥s := sorry

theorem subtype.connected_space {α : Type u} [topological_space α] {s : set α} (h : is_connected s) : connected_space ↥s :=
  connected_space.mk (set.nonempty.to_subtype (is_connected.nonempty h))

theorem is_preconnected_iff_preconnected_space {α : Type u} [topological_space α] {s : set α} : is_preconnected s ↔ preconnected_space ↥s := sorry

theorem is_connected_iff_connected_space {α : Type u} [topological_space α] {s : set α} : is_connected s ↔ connected_space ↥s := sorry

/-- A set `s` is preconnected if and only if
for every cover by two open sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_disjoint {α : Type u} [topological_space α] {s : set α} : is_preconnected s ↔ ∀ (u v : set α), is_open u → is_open v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := sorry

/-- A set `s` is connected if and only if
for every cover by a finite collection of open sets that are pairwise disjoint on `s`,
it is contained in one of the members of the collection. -/
theorem is_connected_iff_sUnion_disjoint_open {α : Type u} [topological_space α] {s : set α} : is_connected s ↔
  ∀ (U : finset (set α)) (H : ∀ (u v : set α), u ∈ U → v ∈ U → set.nonempty (s ∩ (u ∩ v)) → u = v),
    (∀ (u : set α), u ∈ U → is_open u) → s ⊆ ⋃₀↑U → ∃ (u : set α), ∃ (H : u ∈ U), s ⊆ u := sorry

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem subset_or_disjoint_of_clopen {α : Type u_1} [topological_space α] {s : set α} {t : set α} (h : is_preconnected t) (h1 : is_clopen s) : s ∩ t = ∅ ∨ t ⊆ s := sorry

/-- A set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_disjoint_closed {α : Type u_1} {s : set α} [topological_space α] : is_preconnected s ↔ ∀ (u v : set α), is_closed u → is_closed v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := sorry

/-- A closed set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_fully_disjoint_closed {α : Type u} [topological_space α] {s : set α} (hs : is_closed s) : is_preconnected s ↔ ∀ (u v : set α), is_closed u → is_closed v → s ⊆ u ∪ v → u ∩ v = ∅ → s ⊆ u ∨ s ⊆ v := sorry

/-- The connected component of a point is always a subset of the intersection of all its clopen
neighbourhoods. -/
theorem connected_component_subset_Inter_clopen {α : Type u} [topological_space α] {x : α} : connected_component x ⊆ set.Inter fun (Z : Subtype fun (Z : set α) => is_clopen Z ∧ x ∈ Z) => ↑Z := sorry

/-- A set is called totally disconnected if all of its connected components are singletons. -/
def is_totally_disconnected {α : Type u} [topological_space α] (s : set α)  :=
  ∀ (t : set α), t ⊆ s → is_preconnected t → subsingleton ↥t

theorem is_totally_disconnected_empty {α : Type u} [topological_space α] : is_totally_disconnected ∅ := sorry

theorem is_totally_disconnected_singleton {α : Type u} [topological_space α] {x : α} : is_totally_disconnected (singleton x) := sorry

/-- A space is totally disconnected if all of its connected components are singletons. -/
class totally_disconnected_space (α : Type u) [topological_space α] 
where
  is_totally_disconnected_univ : is_totally_disconnected set.univ

protected instance pi.totally_disconnected_space {α : Type u_1} {β : α → Type u_2} [t₂ : (a : α) → topological_space (β a)] [∀ (a : α), totally_disconnected_space (β a)] : totally_disconnected_space ((a : α) → β a) := sorry

protected instance subtype.totally_disconnected_space {α : Type u_1} {p : α → Prop} [topological_space α] [totally_disconnected_space α] : totally_disconnected_space (Subtype p) :=
  totally_disconnected_space.mk
    fun (s : set (Subtype p)) (h1 : s ⊆ set.univ) (h2 : is_preconnected s) =>
      set.subsingleton_of_image subtype.val_injective s
        (totally_disconnected_space.is_totally_disconnected_univ (subtype.val '' s) (set.subset_univ (subtype.val '' s))
          (is_preconnected.image h2 subtype.val (continuous.continuous_on continuous_subtype_val)))

/-- A set `s` is called totally separated if any two points of this set can be separated
by two disjoint open sets covering `s`. -/
def is_totally_separated {α : Type u} [topological_space α] (s : set α)  :=
  ∀ (x : α),
    x ∈ s →
      ∀ (y : α),
        y ∈ s → x ≠ y → ∃ (u : set α), ∃ (v : set α), is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ s ⊆ u ∪ v ∧ u ∩ v = ∅

theorem is_totally_separated_empty {α : Type u} [topological_space α] : is_totally_separated ∅ :=
  fun (x : α) => false.elim

theorem is_totally_separated_singleton {α : Type u} [topological_space α] {x : α} : is_totally_separated (singleton x) :=
  fun (p : α) (hp : p ∈ singleton x) (q : α) (hq : q ∈ singleton x) (hpq : p ≠ q) =>
    false.elim (hpq (Eq.symm (set.eq_of_mem_singleton hp) ▸ Eq.symm (set.eq_of_mem_singleton hq)))

theorem is_totally_disconnected_of_is_totally_separated {α : Type u} [topological_space α] {s : set α} (H : is_totally_separated s) : is_totally_disconnected s := sorry

/-- A space is totally separated if any two points can be separated by two disjoint open sets
covering the whole space. -/
class totally_separated_space (α : Type u) [topological_space α] 
where
  is_totally_separated_univ : is_totally_separated set.univ

protected instance totally_separated_space.totally_disconnected_space (α : Type u) [topological_space α] [totally_separated_space α] : totally_disconnected_space α :=
  totally_disconnected_space.mk
    (is_totally_disconnected_of_is_totally_separated (totally_separated_space.is_totally_separated_univ α))

protected instance totally_separated_space.of_discrete (α : Type u_1) [topological_space α] [discrete_topology α] : totally_separated_space α := sorry

