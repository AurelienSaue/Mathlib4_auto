/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.uniform_space.abstract_completion
import PostPort

universes u v u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Hausdorff completions of uniform spaces

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `completion α` and a morphism
(ie. uniformly continuous map) `coe : α → completion α` which solves the universal
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`.
It means any uniformly continuous `f : α → β` gives rise to a unique morphism
`completion.extension f : completion α → β` such that `f = completion.extension f ∘ coe`.
Actually `completion.extension f` is defined for all maps from `α` to `β` but it has the desired
properties only if `f` is uniformly continuous.

Beware that `coe` is not injective if `α` is not Hausdorff. But its image is always
dense. The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, it turns `f : α → β` into a morphism
  `completion.map f : completion α → completion β`
such that
  `coe ∘ f = (completion.map f) ∘ coe`
provided `f` is uniformly continuous. This construction is compatible with composition.

In this file we introduce the following concepts:

* `Cauchy α` the uniform completion of the uniform space `α` (using Cauchy filters). These are not
  minimal filters.

* `completion α := quotient (separation_setoid (Cauchy α))` the Hausdorff completion.

## References

This formalization is mostly based on
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
From a slightly different perspective in order to reuse material in topology.uniform_space.basic.
-/

/-- Space of Cauchy filters

This is essentially the completion of a uniform space. The embeddings are the neighbourhood filters.
This space is not minimal, the separated uniform space (i.e. quotiented on the intersection of all
entourages) is necessary for this.
-/
def Cauchy (α : Type u) [uniform_space α]  :=
  Subtype fun (f : filter α) => cauchy f

namespace Cauchy


def gen {α : Type u} [uniform_space α] (s : set (α × α)) : set (Cauchy α × Cauchy α) :=
  set_of fun (p : Cauchy α × Cauchy α) => s ∈ filter.prod (subtype.val (prod.fst p)) (subtype.val (prod.snd p))

theorem monotone_gen {α : Type u} [uniform_space α] : monotone gen :=
  set.monotone_set_of fun (p : Cauchy α × Cauchy α) => filter.monotone_mem_sets

protected instance uniform_space {α : Type u} [uniform_space α] : uniform_space (Cauchy α) :=
  uniform_space.of_core (uniform_space.core.mk (filter.lift' (uniformity α) gen) sorry symm_gen comp_gen)

theorem mem_uniformity {α : Type u} [uniform_space α] {s : set (Cauchy α × Cauchy α)} : s ∈ uniformity (Cauchy α) ↔ ∃ (t : set (α × α)), ∃ (H : t ∈ uniformity α), gen t ⊆ s :=
  filter.mem_lift'_sets monotone_gen

theorem mem_uniformity' {α : Type u} [uniform_space α] {s : set (Cauchy α × Cauchy α)} : s ∈ uniformity (Cauchy α) ↔
  ∃ (t : set (α × α)),
    ∃ (H : t ∈ uniformity α), ∀ (f g : Cauchy α), t ∈ filter.prod (subtype.val f) (subtype.val g) → (f, g) ∈ s :=
  iff.trans mem_uniformity (bex_congr fun (t : set (α × α)) (h : t ∈ uniformity α) => prod.forall)

/-- Embedding of `α` into its completion `Cauchy α` -/
def pure_cauchy {α : Type u} [uniform_space α] (a : α) : Cauchy α :=
  { val := pure a, property := cauchy_pure }

theorem uniform_inducing_pure_cauchy {α : Type u} [uniform_space α] : uniform_inducing pure_cauchy := sorry

theorem uniform_embedding_pure_cauchy {α : Type u} [uniform_space α] : uniform_embedding pure_cauchy :=
  uniform_embedding.mk (uniform_inducing.mk (uniform_inducing.comap_uniformity uniform_inducing_pure_cauchy))
    fun (a₁ a₂ : α) (h : pure_cauchy a₁ = pure_cauchy a₂) => filter.pure_injective (iff.mp subtype.ext_iff_val h)

theorem dense_range_pure_cauchy {α : Type u} [uniform_space α] : dense_range pure_cauchy := sorry

theorem dense_inducing_pure_cauchy {α : Type u} [uniform_space α] : dense_inducing pure_cauchy :=
  uniform_inducing.dense_inducing uniform_inducing_pure_cauchy dense_range_pure_cauchy

theorem dense_embedding_pure_cauchy {α : Type u} [uniform_space α] : dense_embedding pure_cauchy :=
  uniform_embedding.dense_embedding uniform_embedding_pure_cauchy dense_range_pure_cauchy

theorem nonempty_Cauchy_iff {α : Type u} [uniform_space α] : Nonempty (Cauchy α) ↔ Nonempty α := sorry

protected instance complete_space {α : Type u} [uniform_space α] : complete_space (Cauchy α) :=
  complete_space_extension uniform_inducing_pure_cauchy dense_range_pure_cauchy
    fun (f : filter α) (hf : cauchy f) =>
      let f' : Cauchy α := { val := f, property := hf };
      (fun (this : filter.map pure_cauchy f ≤ filter.lift' (uniformity (Cauchy α)) (set.preimage (Prod.mk f'))) =>
          Exists.intro f'
            (eq.mpr
              (id
                ((fun (ᾰ ᾰ_1 : filter (Cauchy α)) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : filter (Cauchy α)) (e_3 : ᾰ_2 = ᾰ_3) =>
                    congr (congr_arg LessEq e_2) e_3)
                  (filter.map pure_cauchy f) (filter.map pure_cauchy f) (Eq.refl (filter.map pure_cauchy f)) (nhds f')
                  (filter.lift' (uniformity (Cauchy α)) (uniform_space.ball f')) nhds_eq_uniformity))
              this))
        (filter.le_lift' fun (s : set (Cauchy α × Cauchy α)) (hs : s ∈ uniformity (Cauchy α)) => sorry)

protected instance inhabited {α : Type u} [uniform_space α] [Inhabited α] : Inhabited (Cauchy α) :=
  { default := pure_cauchy Inhabited.default }

protected instance nonempty {α : Type u} [uniform_space α] [h : Nonempty α] : Nonempty (Cauchy α) :=
  nonempty.rec_on h fun (a : α) => Nonempty.intro (pure_cauchy a)

def extend {α : Type u} [uniform_space α] {β : Type v} [uniform_space β] (f : α → β) : Cauchy α → β :=
  ite (uniform_continuous f) (dense_inducing.extend dense_inducing_pure_cauchy f)
    fun (x : Cauchy α) => f Inhabited.default

theorem extend_pure_cauchy {α : Type u} [uniform_space α] {β : Type v} [uniform_space β] [separated_space β] {f : α → β} (hf : uniform_continuous f) (a : α) : extend f (pure_cauchy a) = f a := sorry

theorem uniform_continuous_extend {α : Type u} [uniform_space α] {β : Type v} [uniform_space β] [separated_space β] [complete_space β] {f : α → β} : uniform_continuous (extend f) := sorry

theorem Cauchy_eq {α : Type u_1} [Inhabited α] [uniform_space α] [complete_space α] [separated_space α] {f : Cauchy α} {g : Cauchy α} : Lim (subtype.val f) = Lim (subtype.val g) ↔ (f, g) ∈ Mathlib.separation_rel (Cauchy α) := sorry

theorem separated_pure_cauchy_injective {α : Type u_1} [uniform_space α] [s : separated_space α] : function.injective fun (a : α) => quotient.mk (pure_cauchy a) := sorry

end Cauchy


namespace uniform_space


protected instance complete_space_separation (α : Type u_1) [uniform_space α] [h : complete_space α] : complete_space (quotient (separation_setoid α)) :=
  complete_space.mk
    fun (f : filter (quotient (separation_setoid α))) (hf : cauchy f) =>
      (fun (this : cauchy (filter.comap (fun (x : α) => quotient.mk x) f)) => sorry)
        (cauchy.comap' hf comap_quotient_le_uniformity
          (filter.ne_bot.comap_of_surj (and.left hf) fun (b : quotient (separation_setoid α)) => quotient.exists_rep b))

/-- Hausdorff completion of `α` -/
def completion (α : Type u_1) [uniform_space α]  :=
  quotient (separation_setoid (Cauchy α))

namespace completion


protected instance inhabited (α : Type u_1) [uniform_space α] [Inhabited α] : Inhabited (completion α) :=
  eq.mpr sorry quotient.inhabited

protected instance uniform_space (α : Type u_1) [uniform_space α] : uniform_space (completion α) :=
  id separation_setoid.uniform_space

protected instance complete_space (α : Type u_1) [uniform_space α] : complete_space (completion α) :=
  id (uniform_space.complete_space_separation (Cauchy α))

protected instance separated_space (α : Type u_1) [uniform_space α] : separated_space (completion α) :=
  id uniform_space.separated_separation

protected instance regular_space (α : Type u_1) [uniform_space α] : regular_space (completion α) :=
  Mathlib.separated_regular

/-- Automatic coercion from `α` to its completion. Not always injective. -/
protected instance has_coe_t (α : Type u_1) [uniform_space α] : has_coe_t α (completion α) :=
  has_coe_t.mk (quotient.mk ∘ Cauchy.pure_cauchy)

protected theorem coe_eq (α : Type u_1) [uniform_space α] : coe = quotient.mk ∘ Cauchy.pure_cauchy :=
  rfl

theorem comap_coe_eq_uniformity (α : Type u_1) [uniform_space α] : filter.comap (fun (p : α × α) => (↑(prod.fst p), ↑(prod.snd p))) (uniformity (completion α)) = uniformity α := sorry

theorem uniform_inducing_coe (α : Type u_1) [uniform_space α] : uniform_inducing coe :=
  uniform_inducing.mk (comap_coe_eq_uniformity α)

theorem dense_range_coe {α : Type u_1} [uniform_space α] : dense_range coe :=
  dense_range.quotient Cauchy.dense_range_pure_cauchy

def cpkg {α : Type u_1} [uniform_space α] : abstract_completion α :=
  abstract_completion.mk (completion α) coe (completion.uniform_space α) (completion.complete_space α)
    (completion.separated_space α) (uniform_inducing_coe α) dense_range_coe

protected instance abstract_completion.inhabited (α : Type u_1) [uniform_space α] : Inhabited (abstract_completion α) :=
  { default := cpkg }

theorem nonempty_completion_iff (α : Type u_1) [uniform_space α] : Nonempty (completion α) ↔ Nonempty α :=
  iff.symm (dense_range.nonempty_iff (abstract_completion.dense cpkg))

theorem uniform_continuous_coe (α : Type u_1) [uniform_space α] : uniform_continuous coe :=
  abstract_completion.uniform_continuous_coe cpkg

theorem continuous_coe (α : Type u_1) [uniform_space α] : continuous coe :=
  abstract_completion.continuous_coe cpkg

theorem uniform_embedding_coe (α : Type u_1) [uniform_space α] [separated_space α] : uniform_embedding coe :=
  uniform_embedding.mk (uniform_inducing.mk (comap_coe_eq_uniformity α)) Cauchy.separated_pure_cauchy_injective

theorem dense_inducing_coe {α : Type u_1} [uniform_space α] : dense_inducing coe :=
  dense_inducing.mk (inducing.mk (inducing.induced (uniform_inducing.inducing (uniform_inducing_coe α)))) dense_range_coe

protected instance separable_space_completion {α : Type u_1} [uniform_space α] [topological_space.separable_space α] : topological_space.separable_space (completion α) :=
  dense_inducing.separable_space dense_inducing_coe

theorem dense_embedding_coe {α : Type u_1} [uniform_space α] [separated_space α] : dense_embedding coe :=
  dense_embedding.mk
    (dense_inducing.mk (dense_inducing.to_inducing dense_inducing_coe) (dense_inducing.dense dense_inducing_coe))
    Cauchy.separated_pure_cauchy_injective

theorem dense_range_coe₂ {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] : dense_range fun (x : α × β) => (↑(prod.fst x), ↑(prod.snd x)) :=
  dense_range.prod_map dense_range_coe dense_range_coe

theorem dense_range_coe₃ {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {γ : Type u_3} [uniform_space γ] : dense_range fun (x : α × β × γ) => (↑(prod.fst x), ↑(prod.fst (prod.snd x)), ↑(prod.snd (prod.snd x))) :=
  dense_range.prod_map dense_range_coe dense_range_coe₂

theorem induction_on {α : Type u_1} [uniform_space α] {p : completion α → Prop} (a : completion α) (hp : is_closed (set_of fun (a : completion α) => p a)) (ih : ∀ (a : α), p ↑a) : p a :=
  is_closed_property dense_range_coe hp ih a

theorem induction_on₂ {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {p : completion α → completion β → Prop} (a : completion α) (b : completion β) (hp : is_closed (set_of fun (x : completion α × completion β) => p (prod.fst x) (prod.snd x))) (ih : ∀ (a : α) (b : β), p ↑a ↑b) : p a b := sorry

theorem induction_on₃ {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {γ : Type u_3} [uniform_space γ] {p : completion α → completion β → completion γ → Prop} (a : completion α) (b : completion β) (c : completion γ) (hp : is_closed
  (set_of
    fun (x : completion α × completion β × completion γ) =>
      p (prod.fst x) (prod.fst (prod.snd x)) (prod.snd (prod.snd x)))) (ih : ∀ (a : α) (b : β) (c : γ), p ↑a ↑b ↑c) : p a b c := sorry

theorem ext {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] [t2_space β] {f : completion α → β} {g : completion α → β} (hf : continuous f) (hg : continuous g) (h : ∀ (a : α), f ↑a = g ↑a) : f = g :=
  abstract_completion.funext cpkg hf hg h

/-- "Extension" to the completion. It is defined for any map `f` but
returns an arbitrary constant value if `f` is not uniformly continuous -/
protected def extension {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] (f : α → β) : completion α → β :=
  abstract_completion.extend cpkg f

@[simp] theorem extension_coe {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {f : α → β} [separated_space β] (hf : uniform_continuous f) (a : α) : completion.extension f ↑a = f a :=
  abstract_completion.extend_coe cpkg hf a

theorem uniform_continuous_extension {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {f : α → β} [separated_space β] [complete_space β] : uniform_continuous (completion.extension f) :=
  abstract_completion.uniform_continuous_extend cpkg

theorem continuous_extension {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {f : α → β} [separated_space β] [complete_space β] : continuous (completion.extension f) :=
  abstract_completion.continuous_extend cpkg

theorem extension_unique {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {f : α → β} [separated_space β] [complete_space β] (hf : uniform_continuous f) {g : completion α → β} (hg : uniform_continuous g) (h : ∀ (a : α), f a = g ↑a) : completion.extension f = g :=
  abstract_completion.extend_unique cpkg hf hg h

@[simp] theorem extension_comp_coe {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] [separated_space β] [complete_space β] {f : completion α → β} (hf : uniform_continuous f) : completion.extension (f ∘ coe) = f :=
  abstract_completion.extend_comp_coe cpkg hf

/-- Completion functor acting on morphisms -/
protected def map {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] (f : α → β) : completion α → completion β :=
  abstract_completion.map cpkg cpkg f

theorem uniform_continuous_map {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {f : α → β} : uniform_continuous (completion.map f) :=
  abstract_completion.uniform_continuous_map cpkg cpkg f

theorem continuous_map {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {f : α → β} : continuous (completion.map f) :=
  abstract_completion.continuous_map cpkg cpkg f

@[simp] theorem map_coe {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {f : α → β} (hf : uniform_continuous f) (a : α) : completion.map f ↑a = ↑(f a) :=
  abstract_completion.map_coe cpkg cpkg hf a

theorem map_unique {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {f : α → β} {g : completion α → completion β} (hg : uniform_continuous g) (h : ∀ (a : α), ↑(f a) = g ↑a) : completion.map f = g :=
  abstract_completion.map_unique cpkg cpkg hg h

@[simp] theorem map_id {α : Type u_1} [uniform_space α] : completion.map id = id :=
  abstract_completion.map_id cpkg

theorem extension_map {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {γ : Type u_3} [uniform_space γ] [complete_space γ] [separated_space γ] {f : β → γ} {g : α → β} (hf : uniform_continuous f) (hg : uniform_continuous g) : completion.extension f ∘ completion.map g = completion.extension (f ∘ g) := sorry

theorem map_comp {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {γ : Type u_3} [uniform_space γ] {g : β → γ} {f : α → β} (hg : uniform_continuous g) (hf : uniform_continuous f) : completion.map g ∘ completion.map f = completion.map (g ∘ f) :=
  extension_map (uniform_continuous.comp (uniform_continuous_coe γ) hg) hf

/- In this section we construct isomorphisms between the completion of a uniform space and the
completion of its separation quotient -/

def completion_separation_quotient_equiv (α : Type u) [uniform_space α] : completion (separation_quotient α) ≃ completion α :=
  equiv.mk (completion.extension (separation_quotient.lift coe)) (completion.map quotient.mk) sorry sorry

theorem uniform_continuous_completion_separation_quotient_equiv {α : Type u_1} [uniform_space α] : uniform_continuous ⇑(completion_separation_quotient_equiv α) :=
  uniform_continuous_extension

theorem uniform_continuous_completion_separation_quotient_equiv_symm {α : Type u_1} [uniform_space α] : uniform_continuous ⇑(equiv.symm (completion_separation_quotient_equiv α)) :=
  uniform_continuous_map

protected def extension₂ {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {γ : Type u_3} [uniform_space γ] (f : α → β → γ) : completion α → completion β → γ :=
  abstract_completion.extend₂ cpkg cpkg f

@[simp] theorem extension₂_coe_coe {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {γ : Type u_3} [uniform_space γ] {f : α → β → γ} [separated_space γ] (hf : uniform_continuous₂ f) (a : α) (b : β) : completion.extension₂ f ↑a ↑b = f a b :=
  abstract_completion.extension₂_coe_coe cpkg cpkg hf a b

theorem uniform_continuous_extension₂ {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {γ : Type u_3} [uniform_space γ] (f : α → β → γ) [separated_space γ] [complete_space γ] : uniform_continuous₂ (completion.extension₂ f) :=
  abstract_completion.uniform_continuous_extension₂ cpkg cpkg f

protected def map₂ {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {γ : Type u_3} [uniform_space γ] (f : α → β → γ) : completion α → completion β → completion γ :=
  abstract_completion.map₂ cpkg cpkg cpkg f

theorem uniform_continuous_map₂ {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {γ : Type u_3} [uniform_space γ] (f : α → β → γ) : uniform_continuous₂ (completion.map₂ f) :=
  abstract_completion.uniform_continuous_map₂ cpkg cpkg cpkg f

theorem continuous_map₂ {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {γ : Type u_3} [uniform_space γ] {δ : Type u_4} [topological_space δ] {f : α → β → γ} {a : δ → completion α} {b : δ → completion β} (ha : continuous a) (hb : continuous b) : continuous fun (d : δ) => completion.map₂ f (a d) (b d) :=
  abstract_completion.continuous_map₂ cpkg cpkg cpkg ha hb

theorem map₂_coe_coe {α : Type u_1} [uniform_space α] {β : Type u_2} [uniform_space β] {γ : Type u_3} [uniform_space γ] (a : α) (b : β) (f : α → β → γ) (hf : uniform_continuous₂ f) : completion.map₂ f ↑a ↑b = ↑(f a b) :=
  abstract_completion.map₂_coe_coe cpkg cpkg cpkg a b f hf

