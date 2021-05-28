/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.separation
import Mathlib.topology.bases
import Mathlib.PostPort

universes u_1 u_2 l u_3 u_4 

namespace Mathlib

/-!
# Dense embeddings

This file defines three properties of functions:

* `dense_range f`      means `f` has dense image;
* `dense_inducing i`   means `i` is also `inducing`;
* `dense_embedding e`  means `e` is also an `embedding`.

The main theorem `continuous_extend` gives a criterion for a function
`f : X → Z` to a regular (T₃) space Z to extend along a dense embedding
`i : X → Y` to a continuous function `g : Y → Z`. Actually `i` only
has to be `dense_inducing` (not necessarily injective).

-/

/-- `i : α → β` is "dense inducing" if it has dense range and the topology on `α`
  is the one induced by `i` from the topology on `β`. -/
structure dense_inducing {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (i : α → β) 
extends inducing i
where
  dense : dense_range i

namespace dense_inducing


theorem nhds_eq_comap {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {i : α → β} (di : dense_inducing i) (a : α) : nhds a = filter.comap i (nhds (i a)) :=
  inducing.nhds_eq_comap (to_inducing di)

protected theorem continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {i : α → β} (di : dense_inducing i) : continuous i :=
  inducing.continuous (to_inducing di)

theorem closure_range {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {i : α → β} (di : dense_inducing i) : closure (set.range i) = set.univ :=
  dense_range.closure_range (dense di)

theorem self_sub_closure_image_preimage_of_open {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {i : α → β} {s : set β} (di : dense_inducing i) : is_open s → s ⊆ closure (i '' (i ⁻¹' s)) := sorry

theorem closure_image_nhds_of_nhds {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {i : α → β} {s : set α} {a : α} (di : dense_inducing i) : s ∈ nhds a → closure (i '' s) ∈ nhds (i a) := sorry

/-- The product of two dense inducings is a dense inducing -/
protected theorem prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] {e₁ : α → β} {e₂ : γ → δ} (de₁ : dense_inducing e₁) (de₂ : dense_inducing e₂) : dense_inducing fun (p : α × γ) => (e₁ (prod.fst p), e₂ (prod.snd p)) :=
  mk (inducing.mk (inducing.induced (inducing.prod_mk (to_inducing de₁) (to_inducing de₂))))
    (dense_range.prod_map (dense de₁) (dense de₂))

/-- If the domain of a `dense_inducing` map is a separable space, then so is the codomain. -/
protected theorem separable_space {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {i : α → β} (di : dense_inducing i) [topological_space.separable_space α] : topological_space.separable_space β :=
  dense_range.separable_space (dense di) (dense_inducing.continuous di)

/--
 γ -f→ α
g↓     ↓e
 δ -h→ β
-/
theorem tendsto_comap_nhds_nhds {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [topological_space α] [topological_space β] {i : α → β} [topological_space δ] {f : γ → α} {g : γ → δ} {h : δ → β} {d : δ} {a : α} (di : dense_inducing i) (H : filter.tendsto h (nhds d) (nhds (i a))) (comm : h ∘ g = i ∘ f) : filter.tendsto f (filter.comap g (nhds d)) (nhds a) := sorry

protected theorem nhds_within_ne_bot {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {i : α → β} (di : dense_inducing i) (b : β) : filter.ne_bot (nhds_within b (set.range i)) :=
  dense_range.nhds_within_ne_bot (dense di) b

theorem comap_nhds_ne_bot {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {i : α → β} (di : dense_inducing i) (b : β) : filter.ne_bot (filter.comap i (nhds b)) := sorry

/-- If `i : α → β` is a dense inducing, then any function `f : α → γ` "extends"
  to a function `g = extend di f : β → γ`. If `γ` is Hausdorff and `f` has a
  continuous extension, then `g` is the unique such extension. In general,
  `g` might not be continuous or even extend `f`. -/
def extend {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] {i : α → β} [topological_space γ] (di : dense_inducing i) (f : α → γ) (b : β) : γ :=
  lim (filter.comap i (nhds b)) f

theorem extend_eq_of_tendsto {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] {i : α → β} (di : dense_inducing i) [topological_space γ] [t2_space γ] {b : β} {c : γ} {f : α → γ} (hf : filter.tendsto f (filter.comap i (nhds b)) (nhds c)) : extend di f b = c :=
  filter.tendsto.lim_eq hf

theorem extend_eq_at {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] {i : α → β} (di : dense_inducing i) [topological_space γ] [t2_space γ] {f : α → γ} (a : α) (hf : continuous_at f a) : extend di f (i a) = f a :=
  extend_eq_of_tendsto di (nhds_eq_comap di a ▸ hf)

theorem extend_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] {i : α → β} (di : dense_inducing i) [topological_space γ] [t2_space γ] {f : α → γ} (hf : continuous f) (a : α) : extend di f (i a) = f a :=
  extend_eq_at di a (continuous.continuous_at hf)

theorem extend_unique_at {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] {i : α → β} [topological_space γ] [t2_space γ] {b : β} {f : α → γ} {g : β → γ} (di : dense_inducing i) (hf : filter.eventually (fun (x : α) => g (i x) = f x) (filter.comap i (nhds b))) (hg : continuous_at g b) : extend di f b = g b := sorry

theorem extend_unique {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] {i : α → β} [topological_space γ] [t2_space γ] {f : α → γ} {g : β → γ} (di : dense_inducing i) (hf : ∀ (x : α), g (i x) = f x) (hg : continuous g) : extend di f = g :=
  funext fun (b : β) => extend_unique_at di (filter.eventually_of_forall hf) (continuous.continuous_at hg)

theorem continuous_at_extend {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] {i : α → β} [topological_space γ] [regular_space γ] {b : β} {f : α → γ} (di : dense_inducing i) (hf : filter.eventually (fun (x : β) => ∃ (c : γ), filter.tendsto f (filter.comap i (nhds x)) (nhds c)) (nhds b)) : continuous_at (extend di f) b := sorry

theorem continuous_extend {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] {i : α → β} [topological_space γ] [regular_space γ] {f : α → γ} (di : dense_inducing i) (hf : ∀ (b : β), ∃ (c : γ), filter.tendsto f (filter.comap i (nhds b)) (nhds c)) : continuous (extend di f) :=
  iff.mpr continuous_iff_continuous_at fun (b : β) => continuous_at_extend di (filter.univ_mem_sets' hf)

theorem mk' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (i : α → β) (c : continuous i) (dense : ∀ (x : β), x ∈ closure (set.range i)) (H : ∀ (a : α) (s : set α) (H : s ∈ nhds a), ∃ (t : set β), ∃ (H : t ∈ nhds (i a)), ∀ (b : α), i b ∈ t → b ∈ s) : dense_inducing i := sorry

end dense_inducing


/-- A dense embedding is an embedding with dense image. -/
structure dense_embedding {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (e : α → β) 
extends dense_inducing e
where
  inj : function.injective e

theorem dense_embedding.mk' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (e : α → β) (c : continuous e) (dense : dense_range e) (inj : function.injective e) (H : ∀ (a : α) (s : set α) (H : s ∈ nhds a), ∃ (t : set β), ∃ (H : t ∈ nhds (e a)), ∀ (b : α), e b ∈ t → b ∈ s) : dense_embedding e := sorry

namespace dense_embedding


theorem inj_iff {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {e : α → β} (de : dense_embedding e) {x : α} {y : α} : e x = e y ↔ x = y :=
  function.injective.eq_iff (inj de)

theorem to_embedding {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {e : α → β} (de : dense_embedding e) : embedding e :=
  embedding.mk (inducing.mk (inducing.induced (dense_inducing.to_inducing (to_dense_inducing de)))) (inj de)

/-- If the domain of a `dense_embedding` is a separable space, then so is its codomain. -/
protected theorem separable_space {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {e : α → β} (de : dense_embedding e) [topological_space.separable_space α] : topological_space.separable_space β :=
  dense_inducing.separable_space (to_dense_inducing de)

/-- The product of two dense embeddings is a dense embedding. -/
protected theorem prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] {e₁ : α → β} {e₂ : γ → δ} (de₁ : dense_embedding e₁) (de₂ : dense_embedding e₂) : dense_embedding fun (p : α × γ) => (e₁ (prod.fst p), e₂ (prod.snd p)) := sorry

/-- The dense embedding of a subtype inside its closure. -/
def subtype_emb {β : Type u_2} [topological_space β] {α : Type u_1} (p : α → Prop) (e : α → β) (x : Subtype fun (x : α) => p x) : Subtype fun (x : β) => x ∈ closure (e '' set_of fun (x : α) => p x) :=
  { val := e ↑x, property := sorry }

protected theorem subtype {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {e : α → β} (de : dense_embedding e) (p : α → Prop) : dense_embedding (subtype_emb p e) := sorry

end dense_embedding


theorem is_closed_property {α : Type u_1} {β : Type u_2} [topological_space β] {e : α → β} {p : β → Prop} (he : dense_range e) (hp : is_closed (set_of fun (x : β) => p x)) (h : ∀ (a : α), p (e a)) (b : β) : p b := sorry

theorem is_closed_property2 {α : Type u_1} {β : Type u_2} [topological_space β] {e : α → β} {p : β → β → Prop} (he : dense_range e) (hp : is_closed (set_of fun (q : β × β) => p (prod.fst q) (prod.snd q))) (h : ∀ (a₁ a₂ : α), p (e a₁) (e a₂)) (b₁ : β) (b₂ : β) : p b₁ b₂ :=
  (fun (this : ∀ (q : β × β), p (prod.fst q) (prod.snd q)) (b₁ b₂ : β) => this (b₁, b₂))
    (is_closed_property (dense_range.prod_map he he) hp fun (_x : α × α) => h (prod.fst _x) (prod.snd _x))

theorem is_closed_property3 {α : Type u_1} {β : Type u_2} [topological_space β] {e : α → β} {p : β → β → β → Prop} (he : dense_range e) (hp : is_closed (set_of fun (q : β × β × β) => p (prod.fst q) (prod.fst (prod.snd q)) (prod.snd (prod.snd q)))) (h : ∀ (a₁ a₂ a₃ : α), p (e a₁) (e a₂) (e a₃)) (b₁ : β) (b₂ : β) (b₃ : β) : p b₁ b₂ b₃ := sorry

theorem dense_range.induction_on {α : Type u_1} {β : Type u_2} [topological_space β] {e : α → β} (he : dense_range e) {p : β → Prop} (b₀ : β) (hp : is_closed (set_of fun (b : β) => p b)) (ih : ∀ (a : α), p (e a)) : p b₀ :=
  is_closed_property he hp ih b₀

theorem dense_range.induction_on₂ {α : Type u_1} {β : Type u_2} [topological_space β] {e : α → β} {p : β → β → Prop} (he : dense_range e) (hp : is_closed (set_of fun (q : β × β) => p (prod.fst q) (prod.snd q))) (h : ∀ (a₁ a₂ : α), p (e a₁) (e a₂)) (b₁ : β) (b₂ : β) : p b₁ b₂ :=
  is_closed_property2 he hp h b₁ b₂

theorem dense_range.induction_on₃ {α : Type u_1} {β : Type u_2} [topological_space β] {e : α → β} {p : β → β → β → Prop} (he : dense_range e) (hp : is_closed (set_of fun (q : β × β × β) => p (prod.fst q) (prod.fst (prod.snd q)) (prod.snd (prod.snd q)))) (h : ∀ (a₁ a₂ a₃ : α), p (e a₁) (e a₂) (e a₃)) (b₁ : β) (b₂ : β) (b₃ : β) : p b₁ b₂ b₃ :=
  is_closed_property3 he hp h b₁ b₂ b₃

/-- Two continuous functions to a t2-space that agree on the dense range of a function are equal. -/
theorem dense_range.equalizer {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space β] [topological_space γ] [t2_space γ] {f : α → β} (hfd : dense_range f) {g : β → γ} {h : β → γ} (hg : continuous g) (hh : continuous h) (H : g ∘ f = h ∘ f) : g = h :=
  funext fun (y : β) => dense_range.induction_on hfd y (is_closed_eq hg hh) (congr_fun H)

