/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.maps
import PostPort

universes u v w x u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Constructions of new topological spaces from old ones

This file constructs products, sums, subtypes and quotients of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, sum, disjoint union, subspace, quotient space

-/

protected instance subtype.topological_space {α : Type u} {p : α → Prop} [t : topological_space α] : topological_space (Subtype p) :=
  topological_space.induced coe t

protected instance quot.topological_space {α : Type u} {r : α → α → Prop} [t : topological_space α] : topological_space (Quot r) :=
  topological_space.coinduced (Quot.mk r) t

protected instance quotient.topological_space {α : Type u} {s : setoid α} [t : topological_space α] : topological_space (quotient s) :=
  topological_space.coinduced quotient.mk t

protected instance prod.topological_space {α : Type u} {β : Type v} [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α × β) :=
  topological_space.induced prod.fst t₁ ⊓ topological_space.induced prod.snd t₂

protected instance sum.topological_space {α : Type u} {β : Type v} [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α ⊕ β) :=
  topological_space.coinduced sum.inl t₁ ⊔ topological_space.coinduced sum.inr t₂

protected instance sigma.topological_space {α : Type u} {β : α → Type v} [t₂ : (a : α) → topological_space (β a)] : topological_space (sigma β) :=
  supr fun (a : α) => topological_space.coinduced (sigma.mk a) (t₂ a)

protected instance Pi.topological_space {α : Type u} {β : α → Type v} [t₂ : (a : α) → topological_space (β a)] : topological_space ((a : α) → β a) :=
  infi fun (a : α) => topological_space.induced (fun (f : (a : α) → β a) => f a) (t₂ a)

protected instance ulift.topological_space {α : Type u} [t : topological_space α] : topological_space (ulift α) :=
  topological_space.induced ulift.down t

/-- The image of a dense set under `quotient.mk` is a dense set. -/
theorem dense.quotient {α : Type u} [setoid α] [topological_space α] {s : set α} (H : dense s) : dense (quotient.mk '' s) :=
  dense_range.dense_image (function.surjective.dense_range (surjective_quotient_mk α)) continuous_coinduced_rng H

/-- The composition of `quotient.mk` and a function with dense range has dense range. -/
theorem dense_range.quotient {α : Type u} {β : Type v} [setoid α] [topological_space α] {f : β → α} (hf : dense_range f) : dense_range (quotient.mk ∘ f) :=
  dense_range.comp (function.surjective.dense_range (surjective_quotient_mk α)) hf continuous_coinduced_rng

protected instance subtype.discrete_topology {α : Type u} {p : α → Prop} [topological_space α] [discrete_topology α] : discrete_topology (Subtype p) :=
  discrete_topology.mk
    (bot_unique
      fun (s : set (Subtype p)) (hs : topological_space.is_open ⊥ s) =>
        Exists.intro (coe '' s)
          { left := is_open_discrete (coe '' s), right := set.preimage_image_eq s subtype.coe_injective })

protected instance sum.discrete_topology {α : Type u} {β : Type v} [topological_space α] [topological_space β] [hα : discrete_topology α] [hβ : discrete_topology β] : discrete_topology (α ⊕ β) := sorry

protected instance sigma.discrete_topology {α : Type u} {β : α → Type v} [(a : α) → topological_space (β a)] [h : ∀ (a : α), discrete_topology (β a)] : discrete_topology (sigma β) := sorry

/-
The 𝓝 filter and the subspace topology.
-/

theorem mem_nhds_subtype {α : Type u} [topological_space α] (s : set α) (a : Subtype fun (x : α) => x ∈ s) (t : set (Subtype fun (x : α) => x ∈ s)) : t ∈ nhds a ↔ ∃ (u : set α), ∃ (H : u ∈ nhds ↑a), coe ⁻¹' u ⊆ t :=
  mem_nhds_induced coe a t

theorem nhds_subtype {α : Type u} [topological_space α] (s : set α) (a : Subtype fun (x : α) => x ∈ s) : nhds a = filter.comap coe (nhds ↑a) :=
  nhds_induced coe a

theorem continuous_fst {α : Type u} {β : Type v} [topological_space α] [topological_space β] : continuous prod.fst :=
  continuous_inf_dom_left continuous_induced_dom

theorem continuous_at_fst {α : Type u} {β : Type v} [topological_space α] [topological_space β] {p : α × β} : continuous_at prod.fst p :=
  continuous.continuous_at continuous_fst

theorem continuous_snd {α : Type u} {β : Type v} [topological_space α] [topological_space β] : continuous prod.snd :=
  continuous_inf_dom_right continuous_induced_dom

theorem continuous_at_snd {α : Type u} {β : Type v} [topological_space α] [topological_space β] {p : α × β} : continuous_at prod.snd p :=
  continuous.continuous_at continuous_snd

theorem continuous.prod_mk {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [topological_space β] [topological_space γ] {f : γ → α} {g : γ → β} (hf : continuous f) (hg : continuous g) : continuous fun (x : γ) => (f x, g x) :=
  continuous_inf_rng (continuous_induced_rng hf) (continuous_induced_rng hg)

theorem continuous.prod_map {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] {f : γ → α} {g : δ → β} (hf : continuous f) (hg : continuous g) : continuous fun (x : γ × δ) => (f (prod.fst x), g (prod.snd x)) :=
  continuous.prod_mk (continuous.comp hf continuous_fst) (continuous.comp hg continuous_snd)

theorem filter.eventually.prod_inl_nhds {α : Type u} {β : Type v} [topological_space α] [topological_space β] {p : α → Prop} {a : α} (h : filter.eventually (fun (x : α) => p x) (nhds a)) (b : β) : filter.eventually (fun (x : α × β) => p (prod.fst x)) (nhds (a, b)) :=
  continuous_at_fst h

theorem filter.eventually.prod_inr_nhds {α : Type u} {β : Type v} [topological_space α] [topological_space β] {p : β → Prop} {b : β} (h : filter.eventually (fun (x : β) => p x) (nhds b)) (a : α) : filter.eventually (fun (x : α × β) => p (prod.snd x)) (nhds (a, b)) :=
  continuous_at_snd h

theorem filter.eventually.prod_mk_nhds {α : Type u} {β : Type v} [topological_space α] [topological_space β] {pa : α → Prop} {a : α} (ha : filter.eventually (fun (x : α) => pa x) (nhds a)) {pb : β → Prop} {b : β} (hb : filter.eventually (fun (y : β) => pb y) (nhds b)) : filter.eventually (fun (p : α × β) => pa (prod.fst p) ∧ pb (prod.snd p)) (nhds (a, b)) :=
  filter.eventually.and (filter.eventually.prod_inl_nhds ha b) (filter.eventually.prod_inr_nhds hb a)

theorem continuous_swap {α : Type u} {β : Type v} [topological_space α] [topological_space β] : continuous prod.swap :=
  continuous.prod_mk continuous_snd continuous_fst

theorem continuous_uncurry_left {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [topological_space β] [topological_space γ] {f : α → β → γ} (a : α) (h : continuous (function.uncurry f)) : continuous (f a) :=
  (fun (this : continuous (function.uncurry f ∘ fun (b : β) => (a, b))) => this)
    (continuous.comp h (continuous.prod_mk continuous_const continuous_id'))

theorem continuous_uncurry_right {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [topological_space β] [topological_space γ] {f : α → β → γ} (b : β) (h : continuous (function.uncurry f)) : continuous fun (a : α) => f a b :=
  (fun (this : continuous (function.uncurry f ∘ fun (a : α) => (a, b))) => this)
    (continuous.comp h (continuous.prod_mk continuous_id' continuous_const))

theorem continuous_curry {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [topological_space β] [topological_space γ] {g : α × β → γ} (a : α) (h : continuous g) : continuous (function.curry g a) :=
  (fun (this : continuous (g ∘ fun (b : β) => (a, b))) => this)
    (continuous.comp h (continuous.prod_mk continuous_const continuous_id'))

theorem is_open.prod {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} {t : set β} (hs : is_open s) (ht : is_open t) : is_open (set.prod s t) :=
  is_open_inter (is_open.preimage continuous_fst hs) (is_open.preimage continuous_snd ht)

theorem nhds_prod_eq {α : Type u} {β : Type v} [topological_space α] [topological_space β] {a : α} {b : β} : nhds (a, b) = filter.prod (nhds a) (nhds b) := sorry

theorem mem_nhds_prod_iff {α : Type u} {β : Type v} [topological_space α] [topological_space β] {a : α} {b : β} {s : set (α × β)} : s ∈ nhds (a, b) ↔ ∃ (u : set α), ∃ (H : u ∈ nhds a), ∃ (v : set β), ∃ (H : v ∈ nhds b), set.prod u v ⊆ s := sorry

theorem filter.has_basis.prod_nhds {α : Type u} {β : Type v} [topological_space α] [topological_space β] {ιa : Type u_1} {ιb : Type u_2} {pa : ιa → Prop} {pb : ιb → Prop} {sa : ιa → set α} {sb : ιb → set β} {a : α} {b : β} (ha : filter.has_basis (nhds a) pa sa) (hb : filter.has_basis (nhds b) pb sb) : filter.has_basis (nhds (a, b)) (fun (i : ιa × ιb) => pa (prod.fst i) ∧ pb (prod.snd i))
  fun (i : ιa × ιb) => set.prod (sa (prod.fst i)) (sb (prod.snd i)) := sorry

protected instance prod.discrete_topology {α : Type u} {β : Type v} [topological_space α] [topological_space β] [discrete_topology α] [discrete_topology β] : discrete_topology (α × β) :=
  discrete_topology.mk (eq_of_nhds_eq_nhds fun (_x : α × β) => sorry)

theorem prod_mem_nhds_sets {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} {t : set β} {a : α} {b : β} (ha : s ∈ nhds a) (hb : t ∈ nhds b) : set.prod s t ∈ nhds (a, b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (set.prod s t ∈ nhds (a, b))) nhds_prod_eq)) (filter.prod_mem_prod ha hb)

theorem nhds_swap {α : Type u} {β : Type v} [topological_space α] [topological_space β] (a : α) (b : β) : nhds (a, b) = filter.map prod.swap (nhds (b, a)) := sorry

theorem filter.tendsto.prod_mk_nhds {α : Type u} {β : Type v} [topological_space α] [topological_space β] {γ : Type u_1} {a : α} {b : β} {f : filter γ} {ma : γ → α} {mb : γ → β} (ha : filter.tendsto ma f (nhds a)) (hb : filter.tendsto mb f (nhds b)) : filter.tendsto (fun (c : γ) => (ma c, mb c)) f (nhds (a, b)) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (filter.tendsto (fun (c : γ) => (ma c, mb c)) f (nhds (a, b)))) nhds_prod_eq))
    (filter.tendsto.prod_mk ha hb)

theorem filter.eventually.curry_nhds {α : Type u} {β : Type v} [topological_space α] [topological_space β] {p : α × β → Prop} {x : α} {y : β} (h : filter.eventually (fun (x : α × β) => p x) (nhds (x, y))) : filter.eventually (fun (x' : α) => filter.eventually (fun (y' : β) => p (x', y')) (nhds y)) (nhds x) :=
  filter.eventually.curry
    (eq.mp (Eq._oldrec (Eq.refl (filter.eventually (fun (x : α × β) => p x) (nhds (x, y)))) nhds_prod_eq) h)

theorem continuous_at.prod {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {g : α → γ} {x : α} (hf : continuous_at f x) (hg : continuous_at g x) : continuous_at (fun (x : α) => (f x, g x)) x :=
  filter.tendsto.prod_mk_nhds hf hg

theorem continuous_at.prod_map {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] {f : α → γ} {g : β → δ} {p : α × β} (hf : continuous_at f (prod.fst p)) (hg : continuous_at g (prod.snd p)) : continuous_at (fun (p : α × β) => (f (prod.fst p), g (prod.snd p))) p :=
  continuous_at.prod (continuous_at.comp hf (continuous.continuous_at continuous_fst))
    (continuous_at.comp hg (continuous.continuous_at continuous_snd))

theorem continuous_at.prod_map' {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] {f : α → γ} {g : β → δ} {x : α} {y : β} (hf : continuous_at f x) (hg : continuous_at g y) : continuous_at (fun (p : α × β) => (f (prod.fst p), g (prod.snd p))) (x, y) :=
  (fun (hf : continuous_at f (prod.fst (x, y))) =>
      (fun (hg : continuous_at g (prod.snd (x, y))) => continuous_at.prod_map hf hg) hg)
    hf

theorem prod_generate_from_generate_from_eq {α : Type u_1} {β : Type u_2} {s : set (set α)} {t : set (set β)} (hs : ⋃₀s = set.univ) (ht : ⋃₀t = set.univ) : prod.topological_space =
  topological_space.generate_from
    (set_of fun (g : set (α × β)) => ∃ (u : set α), ∃ (H : u ∈ s), ∃ (v : set β), ∃ (H : v ∈ t), g = set.prod u v) := sorry

theorem prod_eq_generate_from {α : Type u} {β : Type v} [topological_space α] [topological_space β] : prod.topological_space =
  topological_space.generate_from
    (set_of fun (g : set (α × β)) => ∃ (s : set α), ∃ (t : set β), is_open s ∧ is_open t ∧ g = set.prod s t) := sorry

theorem is_open_prod_iff {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set (α × β)} : is_open s ↔
  ∀ (a : α) (b : β), (a, b) ∈ s → ∃ (u : set α), ∃ (v : set β), is_open u ∧ is_open v ∧ a ∈ u ∧ b ∈ v ∧ set.prod u v ⊆ s := sorry

theorem continuous_uncurry_of_discrete_topology_left {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [topological_space β] [topological_space γ] [discrete_topology α] {f : α → β → γ} (h : ∀ (a : α), continuous (f a)) : continuous (function.uncurry f) := sorry

/-- Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
theorem exists_nhds_square {α : Type u} [topological_space α] {s : set (α × α)} {x : α} (hx : s ∈ nhds (x, x)) : ∃ (U : set α), is_open U ∧ x ∈ U ∧ set.prod U U ⊆ s := sorry

/-- The first projection in a product of topological spaces sends open sets to open sets. -/
theorem is_open_map_fst {α : Type u} {β : Type v} [topological_space α] [topological_space β] : is_open_map prod.fst := sorry

/-- The second projection in a product of topological spaces sends open sets to open sets. -/
theorem is_open_map_snd {α : Type u} {β : Type v} [topological_space α] [topological_space β] : is_open_map prod.snd := sorry

/-- A product set is open in a product space if and only if each factor is open, or one of them is
empty -/
theorem is_open_prod_iff' {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} {t : set β} : is_open (set.prod s t) ↔ is_open s ∧ is_open t ∨ s = ∅ ∨ t = ∅ := sorry

theorem closure_prod_eq {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} {t : set β} : closure (set.prod s t) = set.prod (closure s) (closure t) := sorry

theorem map_mem_closure2 {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [topological_space β] [topological_space γ] {s : set α} {t : set β} {u : set γ} {f : α → β → γ} {a : α} {b : β} (hf : continuous fun (p : α × β) => f (prod.fst p) (prod.snd p)) (ha : a ∈ closure s) (hb : b ∈ closure t) (hu : ∀ (a : α) (b : β), a ∈ s → b ∈ t → f a b ∈ u) : f a b ∈ closure u := sorry

theorem is_closed.prod {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s₁ : set α} {s₂ : set β} (h₁ : is_closed s₁) (h₂ : is_closed s₂) : is_closed (set.prod s₁ s₂) := sorry

/-- The product of two dense sets is a dense set. -/
theorem dense.prod {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set α} {t : set β} (hs : dense s) (ht : dense t) : dense (set.prod s t) :=
  fun (x : α × β) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (x ∈ closure (set.prod s t))) closure_prod_eq))
      { left := hs (prod.fst x), right := ht (prod.snd x) }

/-- If `f` and `g` are maps with dense range, then `prod.map f g` has dense range. -/
theorem dense_range.prod_map {β : Type v} {γ : Type w} [topological_space β] [topological_space γ] {ι : Type u_1} {κ : Type u_2} {f : ι → β} {g : κ → γ} (hf : dense_range f) (hg : dense_range g) : dense_range (prod.map f g) := sorry

theorem inducing.prod_mk {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] {f : α → β} {g : γ → δ} (hf : inducing f) (hg : inducing g) : inducing fun (x : α × γ) => (f (prod.fst x), g (prod.snd x)) := sorry

theorem embedding.prod_mk {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] {f : α → β} {g : γ → δ} (hf : embedding f) (hg : embedding g) : embedding fun (x : α × γ) => (f (prod.fst x), g (prod.snd x)) := sorry

protected theorem is_open_map.prod {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] {f : α → β} {g : γ → δ} (hf : is_open_map f) (hg : is_open_map g) : is_open_map fun (p : α × γ) => (f (prod.fst p), g (prod.snd p)) := sorry

protected theorem open_embedding.prod {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] {f : α → β} {g : γ → δ} (hf : open_embedding f) (hg : open_embedding g) : open_embedding fun (x : α × γ) => (f (prod.fst x), g (prod.snd x)) :=
  open_embedding_of_embedding_open (embedding.prod_mk (open_embedding.to_embedding hf) (open_embedding.to_embedding hg))
    (is_open_map.prod (open_embedding.is_open_map hf) (open_embedding.is_open_map hg))

theorem embedding_graph {α : Type u} {β : Type v} [topological_space α] [topological_space β] {f : α → β} (hf : continuous f) : embedding fun (x : α) => (x, f x) :=
  embedding_of_embedding_compose (continuous.prod_mk continuous_id hf) continuous_fst embedding_id

theorem continuous_inl {α : Type u} {β : Type v} [topological_space α] [topological_space β] : continuous sum.inl :=
  continuous_sup_rng_left continuous_coinduced_rng

theorem continuous_inr {α : Type u} {β : Type v} [topological_space α] [topological_space β] : continuous sum.inr :=
  continuous_sup_rng_right continuous_coinduced_rng

theorem continuous_sum_rec {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [topological_space β] [topological_space γ] {f : α → γ} {g : β → γ} (hf : continuous f) (hg : continuous g) : continuous (sum.rec f g) := sorry

theorem is_open_sum_iff {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : set (α ⊕ β)} : is_open s ↔ is_open (sum.inl ⁻¹' s) ∧ is_open (sum.inr ⁻¹' s) :=
  iff.rfl

theorem is_open_map_sum {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [topological_space β] [topological_space γ] {f : α ⊕ β → γ} (h₁ : is_open_map fun (a : α) => f (sum.inl a)) (h₂ : is_open_map fun (b : β) => f (sum.inr b)) : is_open_map f := sorry

theorem embedding_inl {α : Type u} {β : Type v} [topological_space α] [topological_space β] : embedding sum.inl := sorry

theorem embedding_inr {α : Type u} {β : Type v} [topological_space α] [topological_space β] : embedding sum.inr := sorry

theorem is_open_range_inl {α : Type u} {β : Type v} [topological_space α] [topological_space β] : is_open (set.range sum.inl) := sorry

theorem is_open_range_inr {α : Type u} {β : Type v} [topological_space α] [topological_space β] : is_open (set.range sum.inr) := sorry

theorem open_embedding_inl {α : Type u} {β : Type v} [topological_space α] [topological_space β] : open_embedding sum.inl :=
  open_embedding.mk (embedding.mk (embedding.to_inducing embedding_inl) (embedding.inj embedding_inl)) is_open_range_inl

theorem open_embedding_inr {α : Type u} {β : Type v} [topological_space α] [topological_space β] : open_embedding sum.inr :=
  open_embedding.mk (embedding.mk (embedding.to_inducing embedding_inr) (embedding.inj embedding_inr)) is_open_range_inr

theorem embedding_subtype_coe {α : Type u} [topological_space α] {p : α → Prop} : embedding coe :=
  embedding.mk (inducing.mk rfl) subtype.coe_injective

theorem continuous_subtype_val {α : Type u} [topological_space α] {p : α → Prop} : continuous subtype.val :=
  continuous_induced_dom

theorem continuous_subtype_coe {α : Type u} [topological_space α] {p : α → Prop} : continuous coe :=
  continuous_subtype_val

theorem is_open.open_embedding_subtype_coe {α : Type u} [topological_space α] {s : set α} (hs : is_open s) : open_embedding coe :=
  open_embedding.mk (embedding.mk (inducing.mk rfl) subtype.coe_injective) (Eq.symm subtype.range_coe ▸ hs)

theorem is_open.is_open_map_subtype_coe {α : Type u} [topological_space α] {s : set α} (hs : is_open s) : is_open_map coe :=
  open_embedding.is_open_map (is_open.open_embedding_subtype_coe hs)

theorem is_open_map.restrict {α : Type u} {β : Type v} [topological_space α] [topological_space β] {f : α → β} (hf : is_open_map f) {s : set α} (hs : is_open s) : is_open_map (set.restrict f s) :=
  is_open_map.comp hf (is_open.is_open_map_subtype_coe hs)

theorem is_closed.closed_embedding_subtype_coe {α : Type u} [topological_space α] {s : set α} (hs : is_closed s) : closed_embedding coe :=
  closed_embedding.mk (embedding.mk (inducing.mk rfl) subtype.coe_injective) (Eq.symm subtype.range_coe ▸ hs)

theorem continuous_subtype_mk {α : Type u} {β : Type v} [topological_space α] [topological_space β] {p : α → Prop} {f : β → α} (hp : ∀ (x : β), p (f x)) (h : continuous f) : continuous fun (x : β) => { val := f x, property := hp x } :=
  continuous_induced_rng h

theorem continuous_inclusion {α : Type u} [topological_space α] {s : set α} {t : set α} (h : s ⊆ t) : continuous (set.inclusion h) :=
  continuous_subtype_mk (fun (x : ↥s) => set.inclusion._proof_1 h x) continuous_subtype_coe

theorem continuous_at_subtype_coe {α : Type u} [topological_space α] {p : α → Prop} {a : Subtype p} : continuous_at coe a :=
  iff.mp continuous_iff_continuous_at continuous_subtype_coe a

theorem map_nhds_subtype_coe_eq {α : Type u} [topological_space α] {p : α → Prop} {a : α} (ha : p a) (h : (set_of fun (a : α) => p a) ∈ nhds a) : filter.map coe (nhds { val := a, property := ha }) = nhds a := sorry

theorem nhds_subtype_eq_comap {α : Type u} [topological_space α] {p : α → Prop} {a : α} {h : p a} : nhds { val := a, property := h } = filter.comap coe (nhds a) :=
  nhds_induced coe { val := a, property := h }

theorem tendsto_subtype_rng {α : Type u} [topological_space α] {β : Type u_1} {p : α → Prop} {b : filter β} {f : β → Subtype p} {a : Subtype p} : filter.tendsto f b (nhds a) ↔ filter.tendsto (fun (x : β) => ↑(f x)) b (nhds ↑a) := sorry

theorem continuous_subtype_nhds_cover {α : Type u} {β : Type v} [topological_space α] [topological_space β] {ι : Sort u_1} {f : α → β} {c : ι → α → Prop} (c_cover : ∀ (x : α), ∃ (i : ι), (set_of fun (x : α) => c i x) ∈ nhds x) (f_cont : ∀ (i : ι), continuous fun (x : Subtype (c i)) => f ↑x) : continuous f := sorry

theorem continuous_subtype_is_closed_cover {α : Type u} {β : Type v} [topological_space α] [topological_space β] {ι : Type u_1} {f : α → β} (c : ι → α → Prop) (h_lf : locally_finite fun (i : ι) => set_of fun (x : α) => c i x) (h_is_closed : ∀ (i : ι), is_closed (set_of fun (x : α) => c i x)) (h_cover : ∀ (x : α), ∃ (i : ι), c i x) (f_cont : ∀ (i : ι), continuous fun (x : Subtype (c i)) => f ↑x) : continuous f := sorry

theorem closure_subtype {α : Type u} [topological_space α] {p : α → Prop} {x : Subtype fun (a : α) => p a} {s : set (Subtype fun (a : α) => p a)} : x ∈ closure s ↔ ↑x ∈ closure (coe '' s) :=
  closure_induced fun (x y : Subtype fun (a : α) => p a) => subtype.eq

theorem quotient_map_quot_mk {α : Type u} [topological_space α] {r : α → α → Prop} : quotient_map (Quot.mk r) :=
  { left := quot.exists_rep, right := rfl }

theorem continuous_quot_mk {α : Type u} [topological_space α] {r : α → α → Prop} : continuous (Quot.mk r) :=
  continuous_coinduced_rng

theorem continuous_quot_lift {α : Type u} {β : Type v} [topological_space α] [topological_space β] {r : α → α → Prop} {f : α → β} (hr : ∀ (a b : α), r a b → f a = f b) (h : continuous f) : continuous (Quot.lift f hr) :=
  continuous_coinduced_dom h

theorem quotient_map_quotient_mk {α : Type u} [topological_space α] {s : setoid α} : quotient_map quotient.mk :=
  quotient_map_quot_mk

theorem continuous_quotient_mk {α : Type u} [topological_space α] {s : setoid α} : continuous quotient.mk :=
  continuous_coinduced_rng

theorem continuous_quotient_lift {α : Type u} {β : Type v} [topological_space α] [topological_space β] {s : setoid α} {f : α → β} (hs : ∀ (a b : α), a ≈ b → f a = f b) (h : continuous f) : continuous (quotient.lift f hs) :=
  continuous_coinduced_dom h

theorem continuous_pi {α : Type u} {ι : Type u_1} {π : ι → Type u_2} [topological_space α] [(i : ι) → topological_space (π i)] {f : α → (i : ι) → π i} (h : ∀ (i : ι), continuous fun (a : α) => f a i) : continuous f :=
  continuous_infi_rng fun (i : ι) => continuous_induced_rng (h i)

theorem continuous_apply {ι : Type u_1} {π : ι → Type u_2} [(i : ι) → topological_space (π i)] (i : ι) : continuous fun (p : (i : ι) → π i) => p i :=
  continuous_infi_dom continuous_induced_dom

/-- Embedding a factor into a product space (by fixing arbitrarily all the other coordinates) is
continuous. -/
theorem continuous_update {ι : Type u_1} {π : ι → Type u_2} [DecidableEq ι] [(i : ι) → topological_space (π i)] {i : ι} {f : (i : ι) → π i} : continuous fun (x : π i) => function.update f i x := sorry

theorem nhds_pi {ι : Type u_1} {π : ι → Type u_2} [t : (i : ι) → topological_space (π i)] {a : (i : ι) → π i} : nhds a = infi fun (i : ι) => filter.comap (fun (x : (i : ι) → π i) => x i) (nhds (a i)) := sorry

theorem tendsto_pi {α : Type u} {ι : Type u_1} {π : ι → Type u_2} [t : (i : ι) → topological_space (π i)] {f : α → (i : ι) → π i} {g : (i : ι) → π i} {u : filter α} : filter.tendsto f u (nhds g) ↔ ∀ (x : ι), filter.tendsto (fun (i : α) => f i x) u (nhds (g x)) := sorry

theorem is_open_set_pi {ι : Type u_1} {π : ι → Type u_2} [(a : ι) → topological_space (π a)] {i : set ι} {s : (a : ι) → set (π a)} (hi : set.finite i) (hs : ∀ (a : ι), a ∈ i → is_open (s a)) : is_open (set.pi i s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_open (set.pi i s))) (set.pi_def i s)))
    (is_open_bInter hi fun (a : ι) (ha : a ∈ i) => is_open.preimage (continuous_apply a) (hs a ha))

theorem set_pi_mem_nhds {ι : Type u_1} {π : ι → Type u_2} [(a : ι) → topological_space (π a)] {i : set ι} {s : (a : ι) → set (π a)} {x : (a : ι) → π a} (hi : set.finite i) (hs : ∀ (a : ι), a ∈ i → s a ∈ nhds (x a)) : set.pi i s ∈ nhds x := sorry

theorem pi_eq_generate_from {ι : Type u_1} {π : ι → Type u_2} [(a : ι) → topological_space (π a)] : Pi.topological_space =
  topological_space.generate_from
    (set_of
      fun (g : set ((a : ι) → π a)) =>
        ∃ (s : (a : ι) → set (π a)), ∃ (i : finset ι), (∀ (a : ι), a ∈ i → is_open (s a)) ∧ g = set.pi (↑i) s) := sorry

theorem pi_generate_from_eq {ι : Type u_1} {π : ι → Type u_2} {g : (a : ι) → set (set (π a))} : Pi.topological_space =
  topological_space.generate_from
    (set_of
      fun (t : set ((a : ι) → π a)) =>
        ∃ (s : (a : ι) → set (π a)), ∃ (i : finset ι), (∀ (a : ι), a ∈ i → s a ∈ g a) ∧ t = set.pi (↑i) s) := sorry

theorem pi_generate_from_eq_fintype {ι : Type u_1} {π : ι → Type u_2} {g : (a : ι) → set (set (π a))} [fintype ι] (hg : ∀ (a : ι), ⋃₀g a = set.univ) : Pi.topological_space =
  topological_space.generate_from
    (set_of
      fun (t : set ((a : ι) → π a)) => ∃ (s : (a : ι) → set (π a)), (∀ (a : ι), s a ∈ g a) ∧ t = set.pi set.univ s) := sorry

theorem continuous_sigma_mk {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {i : ι} : continuous (sigma.mk i) :=
  continuous_supr_rng continuous_coinduced_rng

theorem is_open_sigma_iff {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {s : set (sigma σ)} : is_open s ↔ ∀ (i : ι), is_open (sigma.mk i ⁻¹' s) := sorry

theorem is_closed_sigma_iff {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {s : set (sigma σ)} : is_closed s ↔ ∀ (i : ι), is_closed (sigma.mk i ⁻¹' s) :=
  is_open_sigma_iff

theorem is_open_map_sigma_mk {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {i : ι} : is_open_map (sigma.mk i) := sorry

theorem is_open_range_sigma_mk {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {i : ι} : is_open (set.range (sigma.mk i)) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_open (set.range (sigma.mk i)))) (Eq.symm set.image_univ)))
    (is_open_map_sigma_mk set.univ is_open_univ)

theorem is_closed_map_sigma_mk {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {i : ι} : is_closed_map (sigma.mk i) := sorry

theorem is_closed_sigma_mk {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {i : ι} : is_closed (set.range (sigma.mk i)) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_closed (set.range (sigma.mk i)))) (Eq.symm set.image_univ)))
    (is_closed_map_sigma_mk set.univ is_closed_univ)

theorem open_embedding_sigma_mk {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {i : ι} : open_embedding (sigma.mk i) :=
  open_embedding_of_continuous_injective_open continuous_sigma_mk sigma_mk_injective is_open_map_sigma_mk

theorem closed_embedding_sigma_mk {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {i : ι} : closed_embedding (sigma.mk i) :=
  closed_embedding_of_continuous_injective_closed continuous_sigma_mk sigma_mk_injective is_closed_map_sigma_mk

theorem embedding_sigma_mk {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {i : ι} : embedding (sigma.mk i) :=
  closed_embedding.to_embedding closed_embedding_sigma_mk

/-- A map out of a sum type is continuous if its restriction to each summand is. -/
theorem continuous_sigma {β : Type v} {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] [topological_space β] {f : sigma σ → β} (h : ∀ (i : ι), continuous fun (a : σ i) => f (sigma.mk i a)) : continuous f :=
  continuous_supr_dom fun (i : ι) => continuous_coinduced_dom (h i)

theorem continuous_sigma_map {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {κ : Type u_3} {τ : κ → Type u_4} [(k : κ) → topological_space (τ k)] {f₁ : ι → κ} {f₂ : (i : ι) → σ i → τ (f₁ i)} (hf : ∀ (i : ι), continuous (f₂ i)) : continuous (sigma.map f₁ f₂) := sorry

theorem is_open_map_sigma {β : Type v} {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] [topological_space β] {f : sigma σ → β} (h : ∀ (i : ι), is_open_map fun (a : σ i) => f (sigma.mk i a)) : is_open_map f := sorry

/-- The sum of embeddings is an embedding. -/
theorem embedding_sigma_map {ι : Type u_1} {σ : ι → Type u_2} [(i : ι) → topological_space (σ i)] {τ : ι → Type u_3} [(i : ι) → topological_space (τ i)] {f : (i : ι) → σ i → τ i} (hf : ∀ (i : ι), embedding (f i)) : embedding (sigma.map id f) := sorry

theorem continuous_ulift_down {α : Type u} [topological_space α] : continuous ulift.down :=
  continuous_induced_dom

theorem continuous_ulift_up {α : Type u} [topological_space α] : continuous ulift.up :=
  continuous_induced_rng continuous_id

theorem mem_closure_of_continuous {α : Type u} {β : Type v} [topological_space α] [topological_space β] {f : α → β} {a : α} {s : set α} {t : set β} (hf : continuous f) (ha : a ∈ closure s) (h : set.maps_to f s (closure t)) : f a ∈ closure t :=
  set.mem_of_mem_of_subset (set.mem_of_mem_of_subset (set.mem_image_of_mem f ha) (image_closure_subset_closure_image hf))
    (closure_minimal (set.maps_to.image_subset h) is_closed_closure)

theorem mem_closure_of_continuous2 {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [topological_space β] [topological_space γ] {f : α → β → γ} {a : α} {b : β} {s : set α} {t : set β} {u : set γ} (hf : continuous fun (p : α × β) => f (prod.fst p) (prod.snd p)) (ha : a ∈ closure s) (hb : b ∈ closure t) (h : ∀ (a : α), a ∈ s → ∀ (b : β), b ∈ t → f a b ∈ closure u) : f a b ∈ closure u := sorry

