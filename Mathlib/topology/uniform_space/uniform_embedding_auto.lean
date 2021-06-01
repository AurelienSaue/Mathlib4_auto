/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.uniform_space.cauchy
import Mathlib.topology.uniform_space.separation
import Mathlib.topology.dense_embedding
import Mathlib.PostPort

universes u_1 u_2 l u_3 u_4 

namespace Mathlib

/-!
# Uniform embeddings of uniform spaces.

Extension of uniform continuous functions.
-/

structure uniform_inducing {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    (f : α → β)
    where
  comap_uniformity :
    filter.comap (fun (x : α × α) => (f (prod.fst x), f (prod.snd x))) (uniformity β) = uniformity α

theorem uniform_inducing.mk' {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    {f : α → β}
    (h :
      ∀ (s : set (α × α)),
        s ∈ uniformity α ↔
          ∃ (t : set (β × β)), ∃ (H : t ∈ uniformity β), ∀ (x y : α), (f x, f y) ∈ t → (x, y) ∈ s) :
    uniform_inducing f :=
  sorry

theorem uniform_inducing.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α]
    [uniform_space β] [uniform_space γ] {g : β → γ} (hg : uniform_inducing g) {f : α → β}
    (hf : uniform_inducing f) : uniform_inducing (g ∘ f) :=
  sorry

structure uniform_embedding {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    (f : α → β)
    extends uniform_inducing f where
  inj : function.injective f

theorem uniform_embedding_subtype_val {α : Type u_1} [uniform_space α] {p : α → Prop} :
    uniform_embedding subtype.val :=
  uniform_embedding.mk (uniform_inducing.mk rfl) subtype.val_injective

theorem uniform_embedding_subtype_coe {α : Type u_1} [uniform_space α] {p : α → Prop} :
    uniform_embedding coe :=
  uniform_embedding_subtype_val

theorem uniform_embedding_set_inclusion {α : Type u_1} [uniform_space α] {s : set α} {t : set α}
    (hst : s ⊆ t) : uniform_embedding (set.inclusion hst) :=
  sorry

theorem uniform_embedding.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α]
    [uniform_space β] [uniform_space γ] {g : β → γ} (hg : uniform_embedding g) {f : α → β}
    (hf : uniform_embedding f) : uniform_embedding (g ∘ f) :=
  sorry

theorem uniform_embedding_def {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    {f : α → β} :
    uniform_embedding f ↔
        function.injective f ∧
          ∀ (s : set (α × α)),
            s ∈ uniformity α ↔
              ∃ (t : set (β × β)),
                ∃ (H : t ∈ uniformity β), ∀ (x y : α), (f x, f y) ∈ t → (x, y) ∈ s :=
  sorry

theorem uniform_embedding_def' {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    {f : α → β} :
    uniform_embedding f ↔
        function.injective f ∧
          uniform_continuous f ∧
            ∀ (s : set (α × α)),
              s ∈ uniformity α →
                ∃ (t : set (β × β)),
                  ∃ (H : t ∈ uniformity β), ∀ (x y : α), (f x, f y) ∈ t → (x, y) ∈ s :=
  sorry

theorem uniform_inducing.uniform_continuous {α : Type u_1} {β : Type u_2} [uniform_space α]
    [uniform_space β] {f : α → β} (hf : uniform_inducing f) : uniform_continuous f :=
  sorry

theorem uniform_inducing.uniform_continuous_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    [uniform_space α] [uniform_space β] [uniform_space γ] {f : α → β} {g : β → γ}
    (hg : uniform_inducing g) : uniform_continuous f ↔ uniform_continuous (g ∘ f) :=
  sorry

theorem uniform_inducing.inducing {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    {f : α → β} (h : uniform_inducing f) : inducing f :=
  sorry

theorem uniform_inducing.prod {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    {α' : Type u_3} {β' : Type u_4} [uniform_space α'] [uniform_space β'] {e₁ : α → α'}
    {e₂ : β → β'} (h₁ : uniform_inducing e₁) (h₂ : uniform_inducing e₂) :
    uniform_inducing fun (p : α × β) => (e₁ (prod.fst p), e₂ (prod.snd p)) :=
  sorry

theorem uniform_inducing.dense_inducing {α : Type u_1} {β : Type u_2} [uniform_space α]
    [uniform_space β] {f : α → β} (h : uniform_inducing f) (hd : dense_range f) :
    dense_inducing f :=
  dense_inducing.mk (inducing.mk (inducing.induced (uniform_inducing.inducing h))) hd

theorem uniform_embedding.embedding {α : Type u_1} {β : Type u_2} [uniform_space α]
    [uniform_space β] {f : α → β} (h : uniform_embedding f) : embedding f :=
  embedding.mk
    (inducing.mk
      (inducing.induced (uniform_inducing.inducing (uniform_embedding.to_uniform_inducing h))))
    (uniform_embedding.inj h)

theorem uniform_embedding.dense_embedding {α : Type u_1} {β : Type u_2} [uniform_space α]
    [uniform_space β] {f : α → β} (h : uniform_embedding f) (hd : dense_range f) :
    dense_embedding f :=
  dense_embedding.mk
    (dense_inducing.mk
      (inducing.mk (inducing.induced (embedding.to_inducing (uniform_embedding.embedding h)))) hd)
    (uniform_embedding.inj h)

theorem closure_image_mem_nhds_of_uniform_inducing {α : Type u_1} {β : Type u_2} [uniform_space α]
    [uniform_space β] {s : set (α × α)} {e : α → β} (b : β) (he₁ : uniform_inducing e)
    (he₂ : dense_inducing e) (hs : s ∈ uniformity α) :
    ∃ (a : α), closure (e '' set_of fun (a' : α) => (a, a') ∈ s) ∈ nhds b :=
  sorry

theorem uniform_embedding_subtype_emb {α : Type u_1} {β : Type u_2} [uniform_space α]
    [uniform_space β] (p : α → Prop) {e : α → β} (ue : uniform_embedding e)
    (de : dense_embedding e) : uniform_embedding (dense_embedding.subtype_emb p e) :=
  sorry

theorem uniform_embedding.prod {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    {α' : Type u_3} {β' : Type u_4} [uniform_space α'] [uniform_space β'] {e₁ : α → α'}
    {e₂ : β → β'} (h₁ : uniform_embedding e₁) (h₂ : uniform_embedding e₂) :
    uniform_embedding fun (p : α × β) => (e₁ (prod.fst p), e₂ (prod.snd p)) :=
  sorry

theorem is_complete_of_complete_image {α : Type u_1} {β : Type u_2} [uniform_space α]
    [uniform_space β] {m : α → β} {s : set α} (hm : uniform_inducing m)
    (hs : is_complete (m '' s)) : is_complete s :=
  sorry

/-- A set is complete iff its image under a uniform embedding is complete. -/
theorem is_complete_image_iff {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    {m : α → β} {s : set α} (hm : uniform_embedding m) : is_complete (m '' s) ↔ is_complete s :=
  sorry

theorem complete_space_iff_is_complete_range {α : Type u_1} {β : Type u_2} [uniform_space α]
    [uniform_space β] {f : α → β} (hf : uniform_embedding f) :
    complete_space α ↔ is_complete (set.range f) :=
  sorry

theorem complete_space_congr {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    {e : α ≃ β} (he : uniform_embedding ⇑e) : complete_space α ↔ complete_space β :=
  sorry

theorem complete_space_coe_iff_is_complete {α : Type u_1} [uniform_space α] {s : set α} :
    complete_space ↥s ↔ is_complete s :=
  iff.trans (complete_space_iff_is_complete_range uniform_embedding_subtype_coe)
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (is_complete (set.range coe) ↔ is_complete s)) subtype.range_coe))
      (iff.refl (is_complete s)))

theorem is_complete.complete_space_coe {α : Type u_1} [uniform_space α] {s : set α}
    (hs : is_complete s) : complete_space ↥s :=
  iff.mpr complete_space_coe_iff_is_complete hs

theorem is_closed.complete_space_coe {α : Type u_1} [uniform_space α] [complete_space α] {s : set α}
    (hs : is_closed s) : complete_space ↥s :=
  is_complete.complete_space_coe (is_closed.is_complete hs)

theorem complete_space_extension {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    {m : β → α} (hm : uniform_inducing m) (dense : dense_range m)
    (h : ∀ (f : filter β), cauchy f → ∃ (x : α), filter.map m f ≤ nhds x) : complete_space α :=
  sorry

theorem totally_bounded_preimage {α : Type u_1} {β : Type u_2} [uniform_space α] [uniform_space β]
    {f : α → β} {s : set β} (hf : uniform_embedding f) (hs : totally_bounded s) :
    totally_bounded (f ⁻¹' s) :=
  sorry

theorem uniform_embedding_comap {α : Type u_1} {β : Type u_2} {f : α → β} [u : uniform_space β]
    (hf : function.injective f) : uniform_embedding f :=
  uniform_embedding.mk (uniform_inducing.mk rfl) hf

theorem uniformly_extend_exists {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α]
    [uniform_space β] [uniform_space γ] {e : β → α} (h_e : uniform_inducing e)
    (h_dense : dense_range e) {f : β → γ} (h_f : uniform_continuous f) [complete_space γ] (a : α) :
    ∃ (c : γ), filter.tendsto f (filter.comap e (nhds a)) (nhds c) :=
  sorry

theorem uniform_extend_subtype {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α]
    [uniform_space β] [uniform_space γ] [complete_space γ] {p : α → Prop} {e : α → β} {f : α → γ}
    {b : β} {s : set α} (hf : uniform_continuous fun (x : Subtype p) => f (subtype.val x))
    (he : uniform_embedding e) (hd : ∀ (x : β), x ∈ closure (set.range e))
    (hb : closure (e '' s) ∈ nhds b) (hs : is_closed s) (hp : ∀ (x : α), x ∈ s → p x) :
    ∃ (c : γ), filter.tendsto f (filter.comap e (nhds b)) (nhds c) :=
  sorry

theorem uniformly_extend_of_ind {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α]
    [uniform_space β] [uniform_space γ] {e : β → α} (h_e : uniform_inducing e)
    (h_dense : dense_range e) {f : β → γ} (h_f : uniform_continuous f) [separated_space γ] (b : β) :
    dense_inducing.extend (uniform_inducing.dense_inducing h_e h_dense) f (e b) = f b :=
  dense_inducing.extend_eq_at (uniform_inducing.dense_inducing h_e h_dense) b
    (continuous.continuous_at (uniform_continuous.continuous h_f))

theorem uniformly_extend_unique {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α]
    [uniform_space β] [uniform_space γ] {e : β → α} (h_e : uniform_inducing e)
    (h_dense : dense_range e) {f : β → γ} [separated_space γ] {g : α → γ}
    (hg : ∀ (b : β), g (e b) = f b) (hc : continuous g) :
    dense_inducing.extend (uniform_inducing.dense_inducing h_e h_dense) f = g :=
  dense_inducing.extend_unique (uniform_inducing.dense_inducing h_e h_dense) hg hc

theorem uniformly_extend_spec {α : Type u_1} {β : Type u_2} {γ : Type u_3} [uniform_space α]
    [uniform_space β] [uniform_space γ] {e : β → α} (h_e : uniform_inducing e)
    (h_dense : dense_range e) {f : β → γ} (h_f : uniform_continuous f) [separated_space γ]
    [complete_space γ] (a : α) :
    filter.tendsto f (filter.comap e (nhds a))
        (nhds (dense_inducing.extend (uniform_inducing.dense_inducing h_e h_dense) f a)) :=
  sorry

theorem uniform_continuous_uniformly_extend {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    [uniform_space α] [uniform_space β] [uniform_space γ] {e : β → α} (h_e : uniform_inducing e)
    (h_dense : dense_range e) {f : β → γ} (h_f : uniform_continuous f) [separated_space γ]
    [cγ : complete_space γ] :
    uniform_continuous (dense_inducing.extend (uniform_inducing.dense_inducing h_e h_dense) f) :=
  sorry

end Mathlib