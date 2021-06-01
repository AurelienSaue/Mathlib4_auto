/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Separation properties of topological spaces.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.subset_properties
import Mathlib.PostPort

universes u l u_1 u_2 v 

namespace Mathlib

/--
`separated` is a predicate on pairs of sub`set`s of a topological space.  It holds if the two
sub`set`s are contained in disjoint open sets.
-/
def separated {α : Type u} [topological_space α] : set α → set α → Prop :=
  fun (s t : set α) =>
    ∃ (U : set α), ∃ (V : set α), is_open U ∧ is_open V ∧ s ⊆ U ∧ t ⊆ V ∧ disjoint U V

namespace separated


theorem symm {α : Type u} [topological_space α] {s : set α} {t : set α} :
    separated s t → separated t s :=
  sorry

theorem comm {α : Type u} [topological_space α] (s : set α) (t : set α) :
    separated s t ↔ separated t s :=
  { mp := symm, mpr := symm }

theorem empty_right {α : Type u} [topological_space α] (a : set α) : separated a ∅ := sorry

theorem empty_left {α : Type u} [topological_space α] (a : set α) : separated ∅ a :=
  symm (empty_right a)

theorem union_left {α : Type u} [topological_space α] {a : set α} {b : set α} {c : set α} :
    separated a c → separated b c → separated (a ∪ b) c :=
  sorry

theorem union_right {α : Type u} [topological_space α] {a : set α} {b : set α} {c : set α}
    (ab : separated a b) (ac : separated a c) : separated a (b ∪ c) :=
  symm (union_left (symm ab) (symm ac))

end separated


/-- A T₀ space, also known as a Kolmogorov space, is a topological space
  where for every pair `x ≠ y`, there is an open set containing one but not the other. -/
class t0_space (α : Type u) [topological_space α] where
  t0 : ∀ (x y : α), x ≠ y → ∃ (U : set α), is_open U ∧ xor (x ∈ U) (y ∈ U)

theorem exists_open_singleton_of_open_finset {α : Type u} [topological_space α] [t0_space α]
    (s : finset α) (sne : finset.nonempty s) (hso : is_open ↑s) :
    ∃ (x : α), ∃ (H : x ∈ s), is_open (singleton x) :=
  sorry

theorem exists_open_singleton_of_fintype {α : Type u} [topological_space α] [t0_space α]
    [f : fintype α] [ha : Nonempty α] : ∃ (x : α), is_open (singleton x) :=
  sorry

protected instance subtype.t0_space {α : Type u} [topological_space α] [t0_space α] {p : α → Prop} :
    t0_space (Subtype p) :=
  t0_space.mk fun (x y : Subtype p) (hxy : x ≠ y) => sorry

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
class t1_space (α : Type u) [topological_space α] where
  t1 : ∀ (x : α), is_closed (singleton x)

theorem is_closed_singleton {α : Type u} [topological_space α] [t1_space α] {x : α} :
    is_closed (singleton x) :=
  t1_space.t1 x

theorem is_open_compl_singleton {α : Type u} [topological_space α] [t1_space α] {x : α} :
    is_open (singleton xᶜ) :=
  is_closed_singleton

theorem is_open_ne {α : Type u} [topological_space α] [t1_space α] {x : α} :
    is_open (set_of fun (y : α) => y ≠ x) :=
  is_open_compl_singleton

protected instance subtype.t1_space {α : Type u} [topological_space α] [t1_space α] {p : α → Prop} :
    t1_space (Subtype p) :=
  t1_space.mk fun (_x : Subtype p) => sorry

protected instance t1_space.t0_space {α : Type u} [topological_space α] [t1_space α] : t0_space α :=
  t0_space.mk
    fun (x y : α) (h : x ≠ y) =>
      Exists.intro (set_of fun (z : α) => z ≠ y)
        { left := is_open_ne, right := Or.inl { left := h, right := not_not_intro rfl } }

theorem compl_singleton_mem_nhds {α : Type u} [topological_space α] [t1_space α] {x : α} {y : α}
    (h : y ≠ x) : singleton xᶜ ∈ nhds y :=
  mem_nhds_sets is_closed_singleton
    (eq.mpr (id (Eq._oldrec (Eq.refl (y ∈ (singleton xᶜ))) (set.mem_compl_eq (singleton x) y)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (¬y ∈ singleton x)) (propext set.mem_singleton_iff))) h))

@[simp] theorem closure_singleton {α : Type u} [topological_space α] [t1_space α] {a : α} :
    closure (singleton a) = singleton a :=
  is_closed.closure_eq is_closed_singleton

theorem is_closed_map_const {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [t1_space β] {y : β} : is_closed_map (function.const α y) :=
  sorry

theorem discrete_of_t1_of_finite {X : Type u_1} [topological_space X] [t1_space X] [fintype X] :
    discrete_topology X :=
  sorry

theorem singleton_mem_nhds_within_of_mem_discrete {α : Type u} [topological_space α] {s : set α}
    [discrete_topology ↥s] {x : α} (hx : x ∈ s) : singleton x ∈ nhds_within x s :=
  sorry

theorem nhds_within_of_mem_discrete {α : Type u} [topological_space α] {s : set α}
    [discrete_topology ↥s] {x : α} (hx : x ∈ s) : nhds_within x s = pure x :=
  le_antisymm (iff.mpr filter.le_pure_iff (singleton_mem_nhds_within_of_mem_discrete hx))
    (pure_le_nhds_within hx)

theorem filter.has_basis.exists_inter_eq_singleton_of_mem_discrete {α : Type u}
    [topological_space α] {ι : Type u_1} {p : ι → Prop} {t : ι → set α} {s : set α}
    [discrete_topology ↥s] {x : α} (hb : filter.has_basis (nhds x) p t) (hx : x ∈ s) :
    ∃ (i : ι), ∃ (hi : p i), t i ∩ s = singleton x :=
  sorry

/-- A point `x` in a discrete subset `s` of a topological space admits a neighbourhood
that only meets `s` at `x`.  -/
theorem nhds_inter_eq_singleton_of_mem_discrete {α : Type u} [topological_space α] {s : set α}
    [discrete_topology ↥s] {x : α} (hx : x ∈ s) :
    ∃ (U : set α), ∃ (H : U ∈ nhds x), U ∩ s = singleton x :=
  sorry

/-- For point `x` in a discrete subset `s` of a topological space, there is a set `U`
such that
1. `U` is a punctured neighborhood of `x` (ie. `U ∪ {x}` is a neighbourhood of `x`),
2. `U` is disjoint from `s`.
-/
theorem disjoint_nhds_within_of_mem_discrete {α : Type u} [topological_space α] {s : set α}
    [discrete_topology ↥s] {x : α} (hx : x ∈ s) :
    ∃ (U : set α), ∃ (H : U ∈ nhds_within x (singleton xᶜ)), disjoint U s :=
  sorry

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
class t2_space (α : Type u) [topological_space α] where
  t2 :
    ∀ (x y : α),
      x ≠ y → ∃ (u : set α), ∃ (v : set α), is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅

theorem t2_separation {α : Type u} [topological_space α] [t2_space α] {x : α} {y : α} (h : x ≠ y) :
    ∃ (u : set α), ∃ (v : set α), is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
  t2_space.t2 x y h

protected instance t2_space.t1_space {α : Type u} [topological_space α] [t2_space α] : t1_space α :=
  t1_space.mk
    fun (x : α) =>
      iff.mpr is_open_iff_forall_mem_open fun (y : α) (hxy : y ∈ (singleton xᶜ)) => sorry

theorem eq_of_nhds_ne_bot {α : Type u} [topological_space α] [ht : t2_space α] {x : α} {y : α}
    (h : filter.ne_bot (nhds x ⊓ nhds y)) : x = y :=
  sorry

theorem t2_iff_nhds {α : Type u} [topological_space α] :
    t2_space α ↔ ∀ {x y : α}, filter.ne_bot (nhds x ⊓ nhds y) → x = y :=
  sorry

theorem t2_iff_ultrafilter {α : Type u} [topological_space α] :
    t2_space α ↔ ∀ {x y : α} (f : ultrafilter α), ↑f ≤ nhds x → ↑f ≤ nhds y → x = y :=
  sorry

theorem is_closed_diagonal {α : Type u} [topological_space α] [t2_space α] :
    is_closed (set.diagonal α) :=
  sorry

theorem t2_iff_is_closed_diagonal {α : Type u} [topological_space α] :
    t2_space α ↔ is_closed (set.diagonal α) :=
  sorry

theorem finset_disjoint_finset_opens_of_t2 {α : Type u} [topological_space α] [t2_space α]
    (s : finset α) (t : finset α) : disjoint s t → separated ↑s ↑t :=
  sorry

theorem point_disjoint_finset_opens_of_t2 {α : Type u} [topological_space α] [t2_space α] {x : α}
    {s : finset α} (h : ¬x ∈ s) : separated (singleton x) ↑s :=
  sorry

@[simp] theorem nhds_eq_nhds_iff {α : Type u} [topological_space α] {a : α} {b : α} [t2_space α] :
    nhds a = nhds b ↔ a = b :=
  sorry

@[simp] theorem nhds_le_nhds_iff {α : Type u} [topological_space α] {a : α} {b : α} [t2_space α] :
    nhds a ≤ nhds b ↔ a = b :=
  sorry

theorem tendsto_nhds_unique {α : Type u} {β : Type v} [topological_space α] [t2_space α] {f : β → α}
    {l : filter β} {a : α} {b : α} [filter.ne_bot l] (ha : filter.tendsto f l (nhds a))
    (hb : filter.tendsto f l (nhds b)) : a = b :=
  eq_of_nhds_ne_bot (filter.ne_bot_of_le (le_inf ha hb))

theorem tendsto_nhds_unique' {α : Type u} {β : Type v} [topological_space α] [t2_space α]
    {f : β → α} {l : filter β} {a : α} {b : α} (hl : filter.ne_bot l)
    (ha : filter.tendsto f l (nhds a)) (hb : filter.tendsto f l (nhds b)) : a = b :=
  eq_of_nhds_ne_bot (filter.ne_bot_of_le (le_inf ha hb))

/-!
### Properties of `Lim` and `lim`

In this section we use explicit `nonempty α` instances for `Lim` and `lim`. This way the lemmas
are useful without a `nonempty α` instance.
-/

theorem Lim_eq {α : Type u} [topological_space α] [t2_space α] {f : filter α} {a : α}
    [filter.ne_bot f] (h : f ≤ nhds a) : Lim f = a :=
  tendsto_nhds_unique (le_nhds_Lim (Exists.intro a h)) h

theorem Lim_eq_iff {α : Type u} [topological_space α] [t2_space α] {f : filter α} [filter.ne_bot f]
    (h : ∃ (a : α), f ≤ nhds a) {a : α} : Lim f = a ↔ f ≤ nhds a :=
  { mp := fun (c : Lim f = a) => c ▸ le_nhds_Lim h, mpr := Lim_eq }

theorem ultrafilter.Lim_eq_iff_le_nhds {α : Type u} [topological_space α] [t2_space α]
    [compact_space α] {x : α} {F : ultrafilter α} : ultrafilter.Lim F = x ↔ ↑F ≤ nhds x :=
  { mp := fun (h : ultrafilter.Lim F = x) => h ▸ ultrafilter.le_nhds_Lim F, mpr := Lim_eq }

theorem is_open_iff_ultrafilter' {α : Type u} [topological_space α] [t2_space α] [compact_space α]
    (U : set α) :
    is_open U ↔ ∀ (F : ultrafilter α), ultrafilter.Lim F ∈ U → U ∈ ultrafilter.to_filter F :=
  sorry

theorem filter.tendsto.lim_eq {α : Type u} {β : Type v} [topological_space α] [t2_space α] {a : α}
    {f : filter β} [filter.ne_bot f] {g : β → α} (h : filter.tendsto g f (nhds a)) : lim f g = a :=
  Lim_eq h

theorem filter.lim_eq_iff {α : Type u} {β : Type v} [topological_space α] [t2_space α]
    {f : filter β} [filter.ne_bot f] {g : β → α} (h : ∃ (a : α), filter.tendsto g f (nhds a))
    {a : α} : lim f g = a ↔ filter.tendsto g f (nhds a) :=
  { mp := fun (c : lim f g = a) => c ▸ tendsto_nhds_lim h, mpr := filter.tendsto.lim_eq }

theorem continuous.lim_eq {α : Type u} {β : Type v} [topological_space α] [t2_space α]
    [topological_space β] {f : β → α} (h : continuous f) (a : β) : lim (nhds a) f = f a :=
  filter.tendsto.lim_eq (continuous.tendsto h a)

@[simp] theorem Lim_nhds {α : Type u} [topological_space α] [t2_space α] (a : α) :
    Lim (nhds a) = a :=
  Lim_eq (le_refl (nhds a))

@[simp] theorem lim_nhds_id {α : Type u} [topological_space α] [t2_space α] (a : α) :
    lim (nhds a) id = a :=
  Lim_nhds a

@[simp] theorem Lim_nhds_within {α : Type u} [topological_space α] [t2_space α] {a : α} {s : set α}
    (h : a ∈ closure s) : Lim (nhds_within a s) = a :=
  Lim_eq inf_le_left

@[simp] theorem lim_nhds_within_id {α : Type u} [topological_space α] [t2_space α] {a : α}
    {s : set α} (h : a ∈ closure s) : lim (nhds_within a s) id = a :=
  Lim_nhds_within h

/-!
### Instances of `t2_space` typeclass

We use two lemmas to prove that various standard constructions generate Hausdorff spaces from
Hausdorff spaces:

* `separated_by_continuous` says that two points `x y : α` can be separated by open neighborhoods
  provided that there exists a continuous map `f`: α → β` with a Hausdorff codomain such that
  `f x ≠ f y`. We use this lemma to prove that topological spaces defined using `induced` are
  Hausdorff spaces.

* `separated_by_open_embedding` says that for an open embedding `f : α → β` of a Hausdorff space
  `α`, the images of two distinct points `x y : α`, `x ≠ y` can be separated by open neighborhoods.
  We use this lemma to prove that topological spaces defined using `coinduced` are Hausdorff spaces.
-/

protected instance t2_space_discrete {α : Type u_1} [topological_space α] [discrete_topology α] :
    t2_space α :=
  sorry

theorem separated_by_continuous {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [t2_space β] {f : α → β} (hf : continuous f) {x : α} {y : α}
    (h : f x ≠ f y) :
    ∃ (u : set α), ∃ (v : set α), is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
  sorry

theorem separated_by_open_embedding {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [t2_space α] {f : α → β} (hf : open_embedding f) {x : α} {y : α}
    (h : x ≠ y) :
    ∃ (u : set β), ∃ (v : set β), is_open u ∧ is_open v ∧ f x ∈ u ∧ f y ∈ v ∧ u ∩ v = ∅ :=
  sorry

protected instance subtype.t2_space {α : Type u_1} {p : α → Prop} [t : topological_space α]
    [t2_space α] : t2_space (Subtype p) :=
  t2_space.mk
    fun (x y : Subtype p) (h : x ≠ y) =>
      separated_by_continuous continuous_subtype_val (mt subtype.eq h)

protected instance prod.t2_space {α : Type u_1} {β : Type u_2} [t₁ : topological_space α]
    [t2_space α] [t₂ : topological_space β] [t2_space β] : t2_space (α × β) :=
  t2_space.mk fun (_x : α × β) => sorry

protected instance sum.t2_space {α : Type u_1} {β : Type u_2} [t₁ : topological_space α]
    [t2_space α] [t₂ : topological_space β] [t2_space β] : t2_space (α ⊕ β) :=
  sorry

protected instance Pi.t2_space {α : Type u_1} {β : α → Type v}
    [t₂ : (a : α) → topological_space (β a)] [∀ (a : α), t2_space (β a)] :
    t2_space ((a : α) → β a) :=
  t2_space.mk fun (x y : (a : α) → β a) (h : x ≠ y) => sorry

protected instance sigma.t2_space {ι : Type u_1} {α : ι → Type u_2}
    [(i : ι) → topological_space (α i)] [∀ (a : ι), t2_space (α a)] :
    t2_space (sigma fun (i : ι) => α i) :=
  sorry

theorem is_closed_eq {α : Type u} {β : Type v} [topological_space α] [topological_space β]
    [t2_space α] {f : β → α} {g : β → α} (hf : continuous f) (hg : continuous g) :
    is_closed (set_of fun (x : β) => f x = g x) :=
  iff.mp continuous_iff_is_closed (continuous.prod_mk hf hg) (set.diagonal α) is_closed_diagonal

/-- If two continuous maps are equal on `s`, then they are equal on the closure of `s`. -/
theorem set.eq_on.closure {α : Type u} {β : Type v} [topological_space α] [topological_space β]
    [t2_space α] {s : set β} {f : β → α} {g : β → α} (h : set.eq_on f g s) (hf : continuous f)
    (hg : continuous g) : set.eq_on f g (closure s) :=
  closure_minimal h (is_closed_eq hf hg)

/-- If two continuous functions are equal on a dense set, then they are equal. -/
theorem continuous.ext_on {α : Type u} {β : Type v} [topological_space α] [topological_space β]
    [t2_space α] {s : set β} (hs : dense s) {f : β → α} {g : β → α} (hf : continuous f)
    (hg : continuous g) (h : set.eq_on f g s) : f = g :=
  funext fun (x : β) => set.eq_on.closure h hf hg (hs x)

theorem diagonal_eq_range_diagonal_map {α : Type u_1} :
    (set_of fun (p : α × α) => prod.fst p = prod.snd p) = set.range fun (x : α) => (x, x) :=
  sorry

theorem prod_subset_compl_diagonal_iff_disjoint {α : Type u_1} {s : set α} {t : set α} :
    set.prod s t ⊆ ((set_of fun (p : α × α) => prod.fst p = prod.snd p)ᶜ) ↔ s ∩ t = ∅ :=
  sorry

theorem compact_compact_separated {α : Type u} [topological_space α] [t2_space α] {s : set α}
    {t : set α} (hs : is_compact s) (ht : is_compact t) (hst : s ∩ t = ∅) :
    ∃ (u : set α), ∃ (v : set α), is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ u ∩ v = ∅ :=
  sorry

/-- In a `t2_space`, every compact set is closed. -/
theorem is_compact.is_closed {α : Type u} [topological_space α] [t2_space α] {s : set α}
    (hs : is_compact s) : is_closed s :=
  sorry

theorem is_compact.inter {α : Type u} [topological_space α] [t2_space α] {s : set α} {t : set α}
    (hs : is_compact s) (ht : is_compact t) : is_compact (s ∩ t) :=
  is_compact.inter_right hs (is_compact.is_closed ht)

/-- If a compact set is covered by two open sets, then we can cover it by two compact subsets. -/
theorem is_compact.binary_compact_cover {α : Type u} [topological_space α] [t2_space α] {K : set α}
    {U : set α} {V : set α} (hK : is_compact K) (hU : is_open U) (hV : is_open V)
    (h2K : K ⊆ U ∪ V) :
    ∃ (K₁ : set α), ∃ (K₂ : set α), is_compact K₁ ∧ is_compact K₂ ∧ K₁ ⊆ U ∧ K₂ ⊆ V ∧ K = K₁ ∪ K₂ :=
  sorry

/-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
theorem is_compact.finite_compact_cover {α : Type u} [topological_space α] [t2_space α] {s : set α}
    (hs : is_compact s) {ι : Type u_1} (t : finset ι) (U : ι → set α)
    (hU : ∀ (i : ι), i ∈ t → is_open (U i))
    (hsC : s ⊆ set.Union fun (i : ι) => set.Union fun (H : i ∈ t) => U i) :
    ∃ (K : ι → set α),
        (∀ (i : ι), is_compact (K i)) ∧
          (∀ (i : ι), K i ⊆ U i) ∧ s = set.Union fun (i : ι) => set.Union fun (H : i ∈ t) => K i :=
  sorry

theorem locally_compact_of_compact_nhds {α : Type u} [topological_space α] [t2_space α]
    (h : ∀ (x : α), ∃ (s : set α), s ∈ nhds x ∧ is_compact s) : locally_compact_space α :=
  sorry

protected instance locally_compact_of_compact {α : Type u} [topological_space α] [t2_space α]
    [compact_space α] : locally_compact_space α :=
  locally_compact_of_compact_nhds
    fun (x : α) =>
      Exists.intro set.univ { left := mem_nhds_sets is_open_univ trivial, right := compact_univ }

/-- In a locally compact T₂ space, every point has an open neighborhood with compact closure -/
theorem exists_open_with_compact_closure {α : Type u} [topological_space α]
    [locally_compact_space α] [t2_space α] (x : α) :
    ∃ (U : set α), is_open U ∧ x ∈ U ∧ is_compact (closure U) :=
  sorry

/-- In a locally compact T₂ space, every compact set is contained in the interior of a compact
  set. -/
theorem exists_compact_superset {α : Type u} [topological_space α] [locally_compact_space α]
    [t2_space α] {K : set α} (hK : is_compact K) :
    ∃ (K' : set α), is_compact K' ∧ K ⊆ interior K' :=
  sorry

/-- A T₃ space, also known as a regular space (although this condition sometimes
  omits T₂), is one in which for every closed `C` and `x ∉ C`, there exist
  disjoint open sets containing `x` and `C` respectively. -/
class regular_space (α : Type u) [topological_space α] extends t1_space α where
  regular :
    ∀ {s : set α} {a : α},
      is_closed s → ¬a ∈ s → ∃ (t : set α), is_open t ∧ s ⊆ t ∧ nhds_within a t = ⊥

theorem nhds_is_closed {α : Type u} [topological_space α] [regular_space α] {a : α} {s : set α}
    (h : s ∈ nhds a) : ∃ (t : set α), ∃ (H : t ∈ nhds a), t ⊆ s ∧ is_closed t :=
  sorry

theorem closed_nhds_basis {α : Type u} [topological_space α] [regular_space α] (a : α) :
    filter.has_basis (nhds a) (fun (s : set α) => s ∈ nhds a ∧ is_closed s) id :=
  sorry

protected instance subtype.regular_space {α : Type u} [topological_space α] [regular_space α]
    {p : α → Prop} : regular_space (Subtype p) :=
  sorry

protected instance regular_space.t2_space (α : Type u) [topological_space α] [regular_space α] :
    t2_space α :=
  t2_space.mk fun (x y : α) (hxy : x ≠ y) => sorry

theorem disjoint_nested_nhds {α : Type u} [topological_space α] [regular_space α] {x : α} {y : α}
    (h : x ≠ y) :
    ∃ (U₁ : set α),
        ∃ (V₁ : set α),
          ∃ (H : U₁ ∈ nhds x),
            ∃ (H : V₁ ∈ nhds x),
              ∃ (U₂ : set α),
                ∃ (V₂ : set α),
                  ∃ (H : U₂ ∈ nhds y),
                    ∃ (H : V₂ ∈ nhds y),
                      is_closed V₁ ∧
                        is_closed V₂ ∧ is_open U₁ ∧ is_open U₂ ∧ V₁ ⊆ U₁ ∧ V₂ ⊆ U₂ ∧ U₁ ∩ U₂ = ∅ :=
  sorry

/-- A T₄ space, also known as a normal space (although this condition sometimes
  omits T₂), is one in which for every pair of disjoint closed sets `C` and `D`,
  there exist disjoint open sets containing `C` and `D` respectively. -/
class normal_space (α : Type u) [topological_space α] extends t1_space α where
  normal :
    ∀ (s t : set α),
      is_closed s →
        is_closed t →
          disjoint s t →
            ∃ (u : set α), ∃ (v : set α), is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v

theorem normal_separation {α : Type u} [topological_space α] [normal_space α] (s : set α)
    (t : set α) (H1 : is_closed s) (H2 : is_closed t) (H3 : disjoint s t) :
    ∃ (u : set α), ∃ (v : set α), is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v :=
  normal_space.normal s t H1 H2 H3

protected instance normal_space.regular_space {α : Type u} [topological_space α] [normal_space α] :
    regular_space α :=
  regular_space.mk fun (s : set α) (x : α) (hs : is_closed s) (hxs : ¬x ∈ s) => sorry

-- We can't make this an instance because it could cause an instance loop.

theorem normal_of_compact_t2 {α : Type u} [topological_space α] [compact_space α] [t2_space α] :
    normal_space α :=
  sorry

/-- In a compact t2 space, the connected component of a point equals the intersection of all
its clopen neighbourhoods. -/
theorem connected_component_eq_Inter_clopen {α : Type u} [topological_space α] [t2_space α]
    [compact_space α] {x : α} :
    connected_component x =
        set.Inter fun (Z : Subtype fun (Z : set α) => is_clopen Z ∧ x ∈ Z) => ↑Z :=
  sorry

end Mathlib