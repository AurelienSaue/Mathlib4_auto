/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.order
import Mathlib.PostPort

universes u_1 u_2 l u_3 

namespace Mathlib

/-!
# Specific classes of maps between topological spaces

This file introduces the following properties of a map `f : X → Y` between topological spaces:

* `is_open_map f` means the image of an open set under `f` is open.
* `is_closed_map f` means the image of a closed set under `f` is closed.

(Open and closed maps need not be continuous.)

* `inducing f` means the topology on `X` is the one induced via `f` from the topology on `Y`.
  These behave like embeddings except they need not be injective. Instead, points of `X` which
  are identified by `f` are also indistinguishable in the topology on `X`.
* `embedding f` means `f` is inducing and also injective. Equivalently, `f` identifies `X` with
  a subspace of `Y`.
* `open_embedding f` means `f` is an embedding with open image, so it identifies `X` with an
  open subspace of `Y`. Equivalently, `f` is an embedding and an open map.
* `closed_embedding f` similarly means `f` is an embedding with closed image, so it identifies
  `X` with a closed subspace of `Y`. Equivalently, `f` is an embedding and a closed map.

* `quotient_map f` is the dual condition to `embedding f`: `f` is surjective and the topology
  on `Y` is the one coinduced via `f` from the topology on `X`. Equivalently, `f` identifies
  `Y` with a quotient of `X`. Quotient maps are also sometimes known as identification maps.

## References

* <https://en.wikipedia.org/wiki/Open_and_closed_maps>
* <https://en.wikipedia.org/wiki/Embedding#General_topology>
* <https://en.wikipedia.org/wiki/Quotient_space_(topology)#Quotient_map>

## Tags

open map, closed map, embedding, quotient map, identification map

-/

structure inducing {α : Type u_1} {β : Type u_2} [tα : topological_space α] [tβ : topological_space β] (f : α → β) 
where
  induced : tα = topological_space.induced f tβ

theorem inducing_id {α : Type u_1} [topological_space α] : inducing id :=
  inducing.mk (Eq.symm induced_id)

protected theorem inducing.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} (hg : inducing g) (hf : inducing f) : inducing (g ∘ f) := sorry

theorem inducing_of_inducing_compose {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g) (hgf : inducing (g ∘ f)) : inducing f := sorry

theorem inducing_open {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} (hf : inducing f) (h : is_open (set.range f)) (hs : is_open s) : is_open (f '' s) := sorry

theorem inducing_is_closed {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} (hf : inducing f) (h : is_closed (set.range f)) (hs : is_closed s) : is_closed (f '' s) := sorry

theorem inducing.nhds_eq_comap {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : inducing f) (a : α) : nhds a = filter.comap f (nhds (f a)) :=
  iff.mp (induced_iff_nhds_eq f) (inducing.induced hf)

theorem inducing.map_nhds_eq {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : inducing f) (a : α) (h : set.range f ∈ nhds (f a)) : filter.map f (nhds a) = nhds (f a) :=
  Eq.symm (inducing.induced hf) ▸ map_nhds_induced_eq h

theorem inducing.tendsto_nhds_iff {β : Type u_2} {γ : Type u_3} [topological_space β] [topological_space γ] {ι : Type u_1} {f : ι → β} {g : β → γ} {a : filter ι} {b : β} (hg : inducing g) : filter.tendsto f a (nhds b) ↔ filter.tendsto (g ∘ f) a (nhds (g b)) := sorry

theorem inducing.continuous_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {g : β → γ} (hg : inducing g) : continuous f ↔ continuous (g ∘ f) := sorry

theorem inducing.continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : inducing f) : continuous f :=
  iff.mp (inducing.continuous_iff hf) continuous_id

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : set α`, `s` is open iff it is the preimage of an open set. -/
structure embedding {α : Type u_1} {β : Type u_2} [tα : topological_space α] [tβ : topological_space β] (f : α → β) 
extends inducing f
where
  inj : function.injective f

theorem embedding.mk' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β) (inj : function.injective f) (induced : ∀ (a : α), filter.comap f (nhds (f a)) = nhds a) : embedding f :=
  embedding.mk (inducing.mk (iff.mpr (induced_iff_nhds_eq f) fun (a : α) => Eq.symm (induced a))) inj

theorem embedding_id {α : Type u_1} [topological_space α] : embedding id :=
  embedding.mk inducing_id fun (a₁ a₂ : α) (h : id a₁ = id a₂) => h

theorem embedding.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} (hg : embedding g) (hf : embedding f) : embedding (g ∘ f) :=
  embedding.mk (inducing.mk (inducing.induced (inducing.comp (embedding.to_inducing hg) (embedding.to_inducing hf))))
    fun (a₁ a₂ : α) (h : function.comp g f a₁ = function.comp g f a₂) => embedding.inj hf (embedding.inj hg h)

theorem embedding_of_embedding_compose {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g) (hgf : embedding (g ∘ f)) : embedding f := sorry

theorem embedding_open {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} (hf : embedding f) (h : is_open (set.range f)) (hs : is_open s) : is_open (f '' s) :=
  inducing_open (embedding.to_inducing hf) h hs

theorem embedding_is_closed {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} (hf : embedding f) (h : is_closed (set.range f)) (hs : is_closed s) : is_closed (f '' s) :=
  inducing_is_closed (embedding.to_inducing hf) h hs

theorem embedding.map_nhds_eq {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : embedding f) (a : α) (h : set.range f ∈ nhds (f a)) : filter.map f (nhds a) = nhds (f a) :=
  inducing.map_nhds_eq (embedding.to_inducing hf) a h

theorem embedding.tendsto_nhds_iff {β : Type u_2} {γ : Type u_3} [topological_space β] [topological_space γ] {ι : Type u_1} {f : ι → β} {g : β → γ} {a : filter ι} {b : β} (hg : embedding g) : filter.tendsto f a (nhds b) ↔ filter.tendsto (g ∘ f) a (nhds (g b)) := sorry

theorem embedding.continuous_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {g : β → γ} (hg : embedding g) : continuous f ↔ continuous (g ∘ f) :=
  inducing.continuous_iff (embedding.to_inducing hg)

theorem embedding.continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : embedding f) : continuous f :=
  inducing.continuous (embedding.to_inducing hf)

theorem embedding.closure_eq_preimage_closure_image {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {e : α → β} (he : embedding e) (s : set α) : closure s = e ⁻¹' closure (e '' s) := sorry

/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : set β`, `s` is open iff its preimage is an open set. -/
def quotient_map {α : Type u_1} {β : Type u_2} [tα : topological_space α] [tβ : topological_space β] (f : α → β) :=
  function.surjective f ∧ tβ = topological_space.coinduced f tα

theorem quotient_map_iff {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} : quotient_map f ↔ function.surjective f ∧ ∀ (s : set β), is_open s ↔ is_open (f ⁻¹' s) :=
  and_congr iff.rfl topological_space_eq_iff

namespace quotient_map


protected theorem id {α : Type u_1} [topological_space α] : quotient_map id :=
  { left := fun (a : α) => Exists.intro a rfl, right := Eq.symm coinduced_id }

protected theorem comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} (hg : quotient_map g) (hf : quotient_map f) : quotient_map (g ∘ f) := sorry

protected theorem of_quotient_map_compose {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g) (hgf : quotient_map (g ∘ f)) : quotient_map g := sorry

protected theorem continuous_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {g : β → γ} (hf : quotient_map f) : continuous g ↔ continuous (g ∘ f) := sorry

protected theorem continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : quotient_map f) : continuous f :=
  iff.mp (quotient_map.continuous_iff hf) continuous_id

protected theorem surjective {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : quotient_map f) : function.surjective f :=
  and.left hf

protected theorem is_open_preimage {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : quotient_map f) {s : set β} : is_open (f ⁻¹' s) ↔ is_open s :=
  iff.symm (and.right (iff.mp quotient_map_iff hf) s)

end quotient_map


/-- A map `f : α → β` is said to be an *open map*, if the image of any open `U : set α`
is open in `β`. -/
def is_open_map {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β) :=
  ∀ (U : set α), is_open U → is_open (f '' U)

namespace is_open_map


protected theorem id {α : Type u_1} [topological_space α] : is_open_map id :=
  fun (s : set α) (hs : is_open s) => eq.mpr (id (Eq._oldrec (Eq.refl (is_open (id '' s))) (set.image_id s))) hs

protected theorem comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} (hg : is_open_map g) (hf : is_open_map f) : is_open_map (g ∘ f) :=
  id
    fun (s : set α) (hs : is_open s) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (is_open (g ∘ f '' s))) (set.image_comp g f s))) (hg (f '' s) (hf s hs))

theorem is_open_range {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : is_open_map f) : is_open (set.range f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_open (set.range f))) (Eq.symm set.image_univ))) (hf set.univ is_open_univ)

theorem image_mem_nhds {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : is_open_map f) {x : α} {s : set α} (hx : s ∈ nhds x) : f '' s ∈ nhds (f x) := sorry

theorem nhds_le {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : is_open_map f) (a : α) : nhds (f a) ≤ filter.map f (nhds a) :=
  filter.le_map fun (s : set α) => image_mem_nhds hf

theorem of_nhds_le {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : ∀ (a : α), nhds (f a) ≤ filter.map f (nhds a)) : is_open_map f := sorry

theorem of_inverse {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {f' : β → α} (h : continuous f') (l_inv : function.left_inverse f f') (r_inv : function.right_inverse f f') : is_open_map f := sorry

theorem to_quotient_map {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (open_map : is_open_map f) (cont : continuous f) (surj : function.surjective f) : quotient_map f := sorry

end is_open_map


theorem is_open_map_iff_nhds_le {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} : is_open_map f ↔ ∀ (a : α), nhds (f a) ≤ filter.map f (nhds a) :=
  { mp := fun (hf : is_open_map f) => is_open_map.nhds_le hf, mpr := is_open_map.of_nhds_le }

/-- A map `f : α → β` is said to be a *closed map*, if the image of any closed `U : set α`
is closed in `β`. -/
def is_closed_map {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β) :=
  ∀ (U : set α), is_closed U → is_closed (f '' U)

namespace is_closed_map


protected theorem id {α : Type u_1} [topological_space α] : is_closed_map id :=
  fun (s : set α) (hs : is_closed s) => eq.mpr (id (Eq._oldrec (Eq.refl (is_closed (id '' s))) (set.image_id s))) hs

protected theorem comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} (hg : is_closed_map g) (hf : is_closed_map f) : is_closed_map (g ∘ f) :=
  id
    fun (s : set α) (hs : is_closed s) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (is_closed (g ∘ f '' s))) (set.image_comp g f s))) (hg (f '' s) (hf s hs))

theorem of_inverse {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {f' : β → α} (h : continuous f') (l_inv : function.left_inverse f f') (r_inv : function.right_inverse f f') : is_closed_map f := sorry

theorem of_nonempty {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (h : ∀ (s : set α), is_closed s → set.nonempty s → is_closed (f '' s)) : is_closed_map f := sorry

end is_closed_map


/-- An open embedding is an embedding with open image. -/
structure open_embedding {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β) 
extends embedding f
where
  open_range : is_open (set.range f)

theorem open_embedding.open_iff_image_open {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : open_embedding f) {s : set α} : is_open s ↔ is_open (f '' s) := sorry

theorem open_embedding.is_open_map {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : open_embedding f) : is_open_map f :=
  fun (s : set α) => iff.mp (open_embedding.open_iff_image_open hf)

theorem open_embedding.continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : open_embedding f) : continuous f :=
  embedding.continuous (open_embedding.to_embedding hf)

theorem open_embedding.open_iff_preimage_open {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : open_embedding f) {s : set β} (hs : s ⊆ set.range f) : is_open s ↔ is_open (f ⁻¹' s) := sorry

theorem open_embedding_of_embedding_open {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (h₁ : embedding f) (h₂ : is_open_map f) : open_embedding f := sorry

theorem open_embedding_of_continuous_injective_open {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (h₁ : continuous f) (h₂ : function.injective f) (h₃ : is_open_map f) : open_embedding f := sorry

theorem open_embedding_id {α : Type u_1} [topological_space α] : open_embedding id :=
  open_embedding.mk embedding_id
    (eq.mpr ((fun (s s_1 : set α) (e_2 : s = s_1) => congr_arg is_open e_2) (set.range id) set.univ set.range_id)
      is_open_univ)

theorem open_embedding.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} (hg : open_embedding g) (hf : open_embedding f) : open_embedding (g ∘ f) := sorry

/-- A closed embedding is an embedding with closed image. -/
structure closed_embedding {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β) 
extends embedding f
where
  closed_range : is_closed (set.range f)

theorem closed_embedding.continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : closed_embedding f) : continuous f :=
  embedding.continuous (closed_embedding.to_embedding hf)

theorem closed_embedding.closed_iff_image_closed {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : closed_embedding f) {s : set α} : is_closed s ↔ is_closed (f '' s) := sorry

theorem closed_embedding.is_closed_map {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : closed_embedding f) : is_closed_map f :=
  fun (s : set α) => iff.mp (closed_embedding.closed_iff_image_closed hf)

theorem closed_embedding.closed_iff_preimage_closed {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : closed_embedding f) {s : set β} (hs : s ⊆ set.range f) : is_closed s ↔ is_closed (f ⁻¹' s) := sorry

theorem closed_embedding_of_embedding_closed {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (h₁ : embedding f) (h₂ : is_closed_map f) : closed_embedding f := sorry

theorem closed_embedding_of_continuous_injective_closed {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (h₁ : continuous f) (h₂ : function.injective f) (h₃ : is_closed_map f) : closed_embedding f := sorry

theorem closed_embedding_id {α : Type u_1} [topological_space α] : closed_embedding id :=
  closed_embedding.mk embedding_id
    (eq.mpr ((fun (s s_1 : set α) (e_2 : s = s_1) => congr_arg is_closed e_2) (set.range id) set.univ set.range_id)
      is_closed_univ)

theorem closed_embedding.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} (hg : closed_embedding g) (hf : closed_embedding f) : closed_embedding (g ∘ f) := sorry

