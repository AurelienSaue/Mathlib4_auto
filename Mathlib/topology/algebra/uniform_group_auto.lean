/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.uniform_space.uniform_embedding
import Mathlib.topology.uniform_space.complete_separated
import Mathlib.topology.algebra.group
import Mathlib.tactic.abel
import Mathlib.PostPort

universes u_3 l u_1 u_2 u u_4 u_5 

namespace Mathlib

/-!
# Uniform structure on topological groups

* `topological_add_group.to_uniform_space` and `topological_add_group_is_uniform` can be used to
  construct a canonical uniformity for a topological add group.

* extension of ℤ-bilinear maps to complete groups (useful for ring completions)

* `add_group_with_zero_nhd`: construct the topological structure from a group with a neighbourhood
  around zero. Then with `topological_add_group.to_uniform_space` one can derive a `uniform_space`.
-/

/-- A uniform (additive) group is a group in which the addition and negation are
  uniformly continuous. -/
class uniform_add_group (α : Type u_3) [uniform_space α] [add_group α] where
  uniform_continuous_sub : uniform_continuous fun (p : α × α) => prod.fst p - prod.snd p

theorem uniform_add_group.mk' {α : Type u_1} [uniform_space α] [add_group α]
    (h₁ : uniform_continuous fun (p : α × α) => prod.fst p + prod.snd p)
    (h₂ : uniform_continuous fun (p : α) => -p) : uniform_add_group α :=
  sorry

theorem uniform_continuous_sub {α : Type u_1} [uniform_space α] [add_group α]
    [uniform_add_group α] : uniform_continuous fun (p : α × α) => prod.fst p - prod.snd p :=
  uniform_add_group.uniform_continuous_sub

theorem uniform_continuous.sub {α : Type u_1} {β : Type u_2} [uniform_space α] [add_group α]
    [uniform_add_group α] [uniform_space β] {f : β → α} {g : β → α} (hf : uniform_continuous f)
    (hg : uniform_continuous g) : uniform_continuous fun (x : β) => f x - g x :=
  uniform_continuous.comp uniform_continuous_sub (uniform_continuous.prod_mk hf hg)

theorem uniform_continuous.neg {α : Type u_1} {β : Type u_2} [uniform_space α] [add_group α]
    [uniform_add_group α] [uniform_space β] {f : β → α} (hf : uniform_continuous f) :
    uniform_continuous fun (x : β) => -f x :=
  sorry

theorem uniform_continuous_neg {α : Type u_1} [uniform_space α] [add_group α]
    [uniform_add_group α] : uniform_continuous fun (x : α) => -x :=
  uniform_continuous.neg uniform_continuous_id

theorem uniform_continuous.add {α : Type u_1} {β : Type u_2} [uniform_space α] [add_group α]
    [uniform_add_group α] [uniform_space β] {f : β → α} {g : β → α} (hf : uniform_continuous f)
    (hg : uniform_continuous g) : uniform_continuous fun (x : β) => f x + g x :=
  sorry

theorem uniform_continuous_add {α : Type u_1} [uniform_space α] [add_group α]
    [uniform_add_group α] : uniform_continuous fun (p : α × α) => prod.fst p + prod.snd p :=
  uniform_continuous.add uniform_continuous_fst uniform_continuous_snd

protected instance uniform_add_group.to_topological_add_group {α : Type u_1} [uniform_space α]
    [add_group α] [uniform_add_group α] : topological_add_group α :=
  topological_add_group.mk (uniform_continuous.continuous uniform_continuous_neg)

protected instance prod.uniform_add_group {α : Type u_1} {β : Type u_2} [uniform_space α]
    [add_group α] [uniform_add_group α] [uniform_space β] [add_group β] [uniform_add_group β] :
    uniform_add_group (α × β) :=
  uniform_add_group.mk
    (uniform_continuous.prod_mk
      (uniform_continuous.sub
        (uniform_continuous.comp uniform_continuous_fst uniform_continuous_fst)
        (uniform_continuous.comp uniform_continuous_fst uniform_continuous_snd))
      (uniform_continuous.sub
        (uniform_continuous.comp uniform_continuous_snd uniform_continuous_fst)
        (uniform_continuous.comp uniform_continuous_snd uniform_continuous_snd)))

theorem uniformity_translate {α : Type u_1} [uniform_space α] [add_group α] [uniform_add_group α]
    (a : α) :
    filter.map (fun (x : α × α) => (prod.fst x + a, prod.snd x + a)) (uniformity α) =
        uniformity α :=
  sorry

theorem uniform_embedding_translate {α : Type u_1} [uniform_space α] [add_group α]
    [uniform_add_group α] (a : α) : uniform_embedding fun (x : α) => x + a :=
  sorry

theorem uniformity_eq_comap_nhds_zero (α : Type u_1) [uniform_space α] [add_group α]
    [uniform_add_group α] :
    uniformity α = filter.comap (fun (x : α × α) => prod.snd x - prod.fst x) (nhds 0) :=
  sorry

theorem group_separation_rel {α : Type u_1} [uniform_space α] [add_group α] [uniform_add_group α]
    (x : α) (y : α) : (x, y) ∈ Mathlib.separation_rel α ↔ x - y ∈ closure (singleton 0) :=
  sorry

theorem uniform_continuous_of_tendsto_zero {α : Type u_1} {β : Type u_2} [uniform_space α]
    [add_group α] [uniform_add_group α] [uniform_space β] [add_group β] [uniform_add_group β]
    {f : α → β} [is_add_group_hom f] (h : filter.tendsto f (nhds 0) (nhds 0)) :
    uniform_continuous f :=
  sorry

theorem uniform_continuous_of_continuous {α : Type u_1} {β : Type u_2} [uniform_space α]
    [add_group α] [uniform_add_group α] [uniform_space β] [add_group β] [uniform_add_group β]
    {f : α → β} [is_add_group_hom f] (h : continuous f) : uniform_continuous f :=
  sorry

/-- The right uniformity on a topological group. -/
def topological_add_group.to_uniform_space (G : Type u) [add_comm_group G] [topological_space G]
    [topological_add_group G] : uniform_space G :=
  uniform_space.mk
    (uniform_space.core.mk (filter.comap (fun (p : G × G) => prod.snd p - prod.fst p) (nhds 0))
      sorry sorry sorry)
    sorry

theorem uniformity_eq_comap_nhds_zero' (G : Type u) [add_comm_group G] [topological_space G]
    [topological_add_group G] :
    uniformity G = filter.comap (fun (p : G × G) => prod.snd p - prod.fst p) (nhds 0) :=
  rfl

theorem topological_add_group_is_uniform {G : Type u} [add_comm_group G] [topological_space G]
    [topological_add_group G] : uniform_add_group G :=
  sorry

theorem to_uniform_space_eq {G : Type u} [u : uniform_space G] [add_comm_group G]
    [uniform_add_group G] : topological_add_group.to_uniform_space G = u :=
  sorry

namespace add_comm_group


/- TODO: when modules are changed to have more explicit base ring, then change replace `is_Z_bilin`
by using `is_bilinear_map ℤ` from `tensor_product`. -/

/-- `ℤ`-bilinearity for maps between additive commutative groups. -/
class is_Z_bilin {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α] [add_comm_group β]
    [add_comm_group γ] (f : α × β → γ)
    where
  add_left : ∀ (a a' : α) (b : β), f (a + a', b) = f (a, b) + f (a', b)
  add_right : ∀ (a : α) (b b' : β), f (a, b + b') = f (a, b) + f (a, b')

theorem is_Z_bilin.comp_hom {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    [add_comm_group α] [add_comm_group β] [add_comm_group γ] (f : α × β → γ) [is_Z_bilin f]
    {g : γ → δ} [add_comm_group δ] [is_add_group_hom g] : is_Z_bilin (g ∘ f) :=
  sorry

protected instance is_Z_bilin.comp_swap {α : Type u_1} {β : Type u_2} {γ : Type u_3}
    [add_comm_group α] [add_comm_group β] [add_comm_group γ] (f : α × β → γ) [is_Z_bilin f] :
    is_Z_bilin (f ∘ prod.swap) :=
  is_Z_bilin.mk (fun (a a' : β) (b : α) => is_Z_bilin.add_right f b a a')
    fun (a : β) (b b' : α) => is_Z_bilin.add_left f b b' a

theorem is_Z_bilin.zero_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α]
    [add_comm_group β] [add_comm_group γ] (f : α × β → γ) [is_Z_bilin f] (b : β) : f (0, b) = 0 :=
  sorry

theorem is_Z_bilin.zero_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α]
    [add_comm_group β] [add_comm_group γ] (f : α × β → γ) [is_Z_bilin f] (a : α) : f (a, 0) = 0 :=
  is_Z_bilin.zero_left (f ∘ prod.swap)

theorem is_Z_bilin.zero {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α]
    [add_comm_group β] [add_comm_group γ] (f : α × β → γ) [is_Z_bilin f] : f (0, 0) = 0 :=
  is_Z_bilin.zero_left f 0

theorem is_Z_bilin.neg_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α]
    [add_comm_group β] [add_comm_group γ] (f : α × β → γ) [is_Z_bilin f] (a : α) (b : β) :
    f (-a, b) = -f (a, b) :=
  sorry

theorem is_Z_bilin.neg_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α]
    [add_comm_group β] [add_comm_group γ] (f : α × β → γ) [is_Z_bilin f] (a : α) (b : β) :
    f (a, -b) = -f (a, b) :=
  is_Z_bilin.neg_left (f ∘ prod.swap) b a

theorem is_Z_bilin.sub_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α]
    [add_comm_group β] [add_comm_group γ] (f : α × β → γ) [is_Z_bilin f] (a : α) (a' : α) (b : β) :
    f (a - a', b) = f (a, b) - f (a', b) :=
  sorry

theorem is_Z_bilin.sub_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α]
    [add_comm_group β] [add_comm_group γ] (f : α × β → γ) [is_Z_bilin f] (a : α) (b : β) (b' : β) :
    f (a, b - b') = f (a, b) - f (a, b') :=
  is_Z_bilin.sub_left (f ∘ prod.swap) b b' a

end add_comm_group


-- α, β and G are abelian topological groups, G is a uniform space

theorem is_Z_bilin.tendsto_zero_left {α : Type u_1} {β : Type u_2} [topological_space α]
    [add_comm_group α] [topological_space β] [add_comm_group β] {G : Type u_5} [uniform_space G]
    [add_comm_group G] {ψ : α × β → G} (hψ : continuous ψ) [ψbilin : add_comm_group.is_Z_bilin ψ]
    (x₁ : α) : filter.tendsto ψ (nhds (x₁, 0)) (nhds 0) :=
  sorry

theorem is_Z_bilin.tendsto_zero_right {α : Type u_1} {β : Type u_2} [topological_space α]
    [add_comm_group α] [topological_space β] [add_comm_group β] {G : Type u_5} [uniform_space G]
    [add_comm_group G] {ψ : α × β → G} (hψ : continuous ψ) [ψbilin : add_comm_group.is_Z_bilin ψ]
    (y₁ : β) : filter.tendsto ψ (nhds (0, y₁)) (nhds 0) :=
  eq.mp
    (Eq._oldrec (Eq.refl (filter.tendsto ψ (nhds (0, y₁)) (nhds (ψ (0, y₁)))))
      (add_comm_group.is_Z_bilin.zero_left ψ y₁))
    (continuous.tendsto hψ (0, y₁))

-- β is a dense subgroup of α, inclusion is denoted by e

theorem tendsto_sub_comap_self {α : Type u_1} {β : Type u_2} [topological_space α]
    [add_comm_group α] [topological_add_group α] [topological_space β] [add_comm_group β]
    {e : β → α} [is_add_group_hom e] (de : dense_inducing e) (x₀ : α) :
    filter.tendsto (fun (t : β × β) => prod.snd t - prod.fst t)
        (filter.comap (fun (p : β × β) => (e (prod.fst p), e (prod.snd p))) (nhds (x₀, x₀)))
        (nhds 0) :=
  sorry

namespace dense_inducing


-- β is a dense subgroup of α, inclusion is denoted by e

-- δ is a dense subgroup of γ, inclusion is denoted by f

/-- Bourbaki GT III.6.5 Theorem I:
ℤ-bilinear continuous maps from dense images into a complete Hausdorff group extend by continuity.
Note: Bourbaki assumes that α and β are also complete Hausdorff, but this is not necessary. -/
theorem extend_Z_bilin {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {G : Type u_5}
    [topological_space α] [add_comm_group α] [topological_add_group α] [topological_space β]
    [add_comm_group β] [topological_add_group β] [topological_space γ] [add_comm_group γ]
    [topological_add_group γ] [topological_space δ] [add_comm_group δ] [topological_add_group δ]
    [uniform_space G] [add_comm_group G] [uniform_add_group G] [separated_space G]
    [complete_space G] {e : β → α} [is_add_group_hom e] (de : dense_inducing e) {f : δ → γ}
    [is_add_group_hom f] (df : dense_inducing f) {φ : β × δ → G} (hφ : continuous φ)
    [bilin : add_comm_group.is_Z_bilin φ] : continuous (extend (dense_inducing.prod de df) φ) :=
  sorry

end Mathlib