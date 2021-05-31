/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.constructions
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Neighborhoods and continuity relative to a subset

This file defines relative versions

* `nhds_within`           of `nhds`
* `continuous_on`         of `continuous`
* `continuous_within_at`  of `continuous_at`

and proves their basic properties, including the relationships between
these restricted notions and the corresponding notions for the subtype
equipped with the subspace topology.

## Notation

* `𝓝 x`: the filter of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhds_within x s` of neighborhoods of a point `x` within a set `s`.

-/

/-- The "neighborhood within" filter. Elements of `𝓝[s] a` are sets containing the
intersection of `s` and a neighborhood of `a`. -/
def nhds_within {α : Type u_1} [topological_space α] (a : α) (s : set α) : filter α :=
  nhds a ⊓ filter.principal s

@[simp] theorem nhds_bind_nhds_within {α : Type u_1} [topological_space α] {a : α} {s : set α} : (filter.bind (nhds a) fun (x : α) => nhds_within x s) = nhds_within a s :=
  Eq.trans filter.bind_inf_principal (congr_arg2 has_inf.inf nhds_bind_nhds rfl)

@[simp] theorem eventually_nhds_nhds_within {α : Type u_1} [topological_space α] {a : α} {s : set α} {p : α → Prop} : filter.eventually (fun (y : α) => filter.eventually (fun (x : α) => p x) (nhds_within y s)) (nhds a) ↔
  filter.eventually (fun (x : α) => p x) (nhds_within a s) :=
  iff.mp filter.ext_iff nhds_bind_nhds_within (set_of fun (x : α) => p x)

theorem eventually_nhds_within_iff {α : Type u_1} [topological_space α] {a : α} {s : set α} {p : α → Prop} : filter.eventually (fun (x : α) => p x) (nhds_within a s) ↔ filter.eventually (fun (x : α) => x ∈ s → p x) (nhds a) :=
  filter.eventually_inf_principal

@[simp] theorem eventually_nhds_within_nhds_within {α : Type u_1} [topological_space α] {a : α} {s : set α} {p : α → Prop} : filter.eventually (fun (y : α) => filter.eventually (fun (x : α) => p x) (nhds_within y s)) (nhds_within a s) ↔
  filter.eventually (fun (x : α) => p x) (nhds_within a s) := sorry

theorem nhds_within_eq {α : Type u_1} [topological_space α] (a : α) (s : set α) : nhds_within a s =
  infi fun (t : set α) => infi fun (H : t ∈ set_of fun (t : set α) => a ∈ t ∧ is_open t) => filter.principal (t ∩ s) :=
  filter.has_basis.eq_binfi (filter.has_basis.inf_principal (nhds_basis_opens a) s)

theorem nhds_within_univ {α : Type u_1} [topological_space α] (a : α) : nhds_within a set.univ = nhds a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nhds_within a set.univ = nhds a)) (nhds_within.equations._eqn_1 a set.univ)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nhds a ⊓ filter.principal set.univ = nhds a)) filter.principal_univ))
      (eq.mpr (id (Eq._oldrec (Eq.refl (nhds a ⊓ ⊤ = nhds a)) inf_top_eq)) (Eq.refl (nhds a))))

theorem nhds_within_has_basis {α : Type u_1} {β : Type u_2} [topological_space α] {p : β → Prop} {s : β → set α} {a : α} (h : filter.has_basis (nhds a) p s) (t : set α) : filter.has_basis (nhds_within a t) p fun (i : β) => s i ∩ t :=
  filter.has_basis.inf_principal h t

theorem nhds_within_basis_open {α : Type u_1} [topological_space α] (a : α) (t : set α) : filter.has_basis (nhds_within a t) (fun (u : set α) => a ∈ u ∧ is_open u) fun (u : set α) => u ∩ t :=
  nhds_within_has_basis (nhds_basis_opens a) t

theorem mem_nhds_within {α : Type u_1} [topological_space α] {t : set α} {a : α} {s : set α} : t ∈ nhds_within a s ↔ ∃ (u : set α), is_open u ∧ a ∈ u ∧ u ∩ s ⊆ t := sorry

theorem mem_nhds_within_iff_exists_mem_nhds_inter {α : Type u_1} [topological_space α] {t : set α} {a : α} {s : set α} : t ∈ nhds_within a s ↔ ∃ (u : set α), ∃ (H : u ∈ nhds a), u ∩ s ⊆ t :=
  filter.has_basis.mem_iff (nhds_within_has_basis (filter.basis_sets (nhds a)) s)

theorem diff_mem_nhds_within_compl {X : Type u_1} [topological_space X] {x : X} {s : set X} (hs : s ∈ nhds x) (t : set X) : s \ t ∈ nhds_within x (tᶜ) :=
  filter.diff_mem_inf_principal_compl hs t

theorem nhds_of_nhds_within_of_nhds {α : Type u_1} [topological_space α] {s : set α} {t : set α} {a : α} (h1 : s ∈ nhds a) (h2 : t ∈ nhds_within a s) : t ∈ nhds a := sorry

theorem mem_nhds_within_of_mem_nhds {α : Type u_1} [topological_space α] {s : set α} {t : set α} {a : α} (h : s ∈ nhds a) : s ∈ nhds_within a t :=
  filter.mem_inf_sets_of_left h

theorem self_mem_nhds_within {α : Type u_1} [topological_space α] {a : α} {s : set α} : s ∈ nhds_within a s :=
  filter.mem_inf_sets_of_right (filter.mem_principal_self s)

theorem inter_mem_nhds_within {α : Type u_1} [topological_space α] (s : set α) {t : set α} {a : α} (h : t ∈ nhds a) : s ∩ t ∈ nhds_within a s :=
  filter.inter_mem_sets (filter.mem_inf_sets_of_right (filter.mem_principal_self s)) (filter.mem_inf_sets_of_left h)

theorem nhds_within_mono {α : Type u_1} [topological_space α] (a : α) {s : set α} {t : set α} (h : s ⊆ t) : nhds_within a s ≤ nhds_within a t :=
  inf_le_inf_left (nhds a) (iff.mpr filter.principal_mono h)

theorem pure_le_nhds_within {α : Type u_1} [topological_space α] {a : α} {s : set α} (ha : a ∈ s) : pure a ≤ nhds_within a s :=
  le_inf (pure_le_nhds a) (iff.mpr filter.le_principal_iff ha)

theorem mem_of_mem_nhds_within {α : Type u_1} [topological_space α] {a : α} {s : set α} {t : set α} (ha : a ∈ s) (ht : t ∈ nhds_within a s) : a ∈ t :=
  pure_le_nhds_within ha ht

theorem filter.eventually.self_of_nhds_within {α : Type u_1} [topological_space α] {p : α → Prop} {s : set α} {x : α} (h : filter.eventually (fun (y : α) => p y) (nhds_within x s)) (hx : x ∈ s) : p x :=
  mem_of_mem_nhds_within hx h

theorem tendsto_const_nhds_within {α : Type u_1} {β : Type u_2} [topological_space α] {l : filter β} {s : set α} {a : α} (ha : a ∈ s) : filter.tendsto (fun (x : β) => a) l (nhds_within a s) :=
  filter.tendsto.mono_right filter.tendsto_const_pure (pure_le_nhds_within ha)

theorem nhds_within_restrict'' {α : Type u_1} [topological_space α] {a : α} (s : set α) {t : set α} (h : t ∈ nhds_within a s) : nhds_within a s = nhds_within a (s ∩ t) :=
  le_antisymm (le_inf inf_le_left (iff.mpr filter.le_principal_iff (filter.inter_mem_sets self_mem_nhds_within h)))
    (inf_le_inf_left (nhds a) (iff.mpr filter.principal_mono (set.inter_subset_left s t)))

theorem nhds_within_restrict' {α : Type u_1} [topological_space α] {a : α} (s : set α) {t : set α} (h : t ∈ nhds a) : nhds_within a s = nhds_within a (s ∩ t) :=
  nhds_within_restrict'' s (filter.mem_inf_sets_of_left h)

theorem nhds_within_restrict {α : Type u_1} [topological_space α] {a : α} (s : set α) {t : set α} (h₀ : a ∈ t) (h₁ : is_open t) : nhds_within a s = nhds_within a (s ∩ t) :=
  nhds_within_restrict' s (mem_nhds_sets h₁ h₀)

theorem nhds_within_le_of_mem {α : Type u_1} [topological_space α] {a : α} {s : set α} {t : set α} (h : s ∈ nhds_within a t) : nhds_within a t ≤ nhds_within a s := sorry

theorem nhds_within_eq_nhds_within {α : Type u_1} [topological_space α] {a : α} {s : set α} {t : set α} {u : set α} (h₀ : a ∈ s) (h₁ : is_open s) (h₂ : t ∩ s = u ∩ s) : nhds_within a t = nhds_within a u := sorry

theorem nhds_within_eq_of_open {α : Type u_1} [topological_space α] {a : α} {s : set α} (h₀ : a ∈ s) (h₁ : is_open s) : nhds_within a s = nhds a :=
  iff.mpr inf_eq_left (iff.mpr filter.le_principal_iff (mem_nhds_sets h₁ h₀))

@[simp] theorem nhds_within_empty {α : Type u_1} [topological_space α] (a : α) : nhds_within a ∅ = ⊥ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nhds_within a ∅ = ⊥)) (nhds_within.equations._eqn_1 a ∅)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nhds a ⊓ filter.principal ∅ = ⊥)) filter.principal_empty))
      (eq.mpr (id (Eq._oldrec (Eq.refl (nhds a ⊓ ⊥ = ⊥)) inf_bot_eq)) (Eq.refl ⊥)))

theorem nhds_within_union {α : Type u_1} [topological_space α] (a : α) (s : set α) (t : set α) : nhds_within a (s ∪ t) = nhds_within a s ⊔ nhds_within a t := sorry

theorem nhds_within_inter {α : Type u_1} [topological_space α] (a : α) (s : set α) (t : set α) : nhds_within a (s ∩ t) = nhds_within a s ⊓ nhds_within a t := sorry

theorem nhds_within_inter' {α : Type u_1} [topological_space α] (a : α) (s : set α) (t : set α) : nhds_within a (s ∩ t) = nhds_within a s ⊓ filter.principal t := sorry

@[simp] theorem nhds_within_singleton {α : Type u_1} [topological_space α] (a : α) : nhds_within a (singleton a) = pure a := sorry

@[simp] theorem nhds_within_insert {α : Type u_1} [topological_space α] (a : α) (s : set α) : nhds_within a (insert a s) = pure a ⊔ nhds_within a s := sorry

theorem mem_nhds_within_insert {α : Type u_1} [topological_space α] {a : α} {s : set α} {t : set α} : t ∈ nhds_within a (insert a s) ↔ a ∈ t ∧ t ∈ nhds_within a s := sorry

theorem insert_mem_nhds_within_insert {α : Type u_1} [topological_space α] {a : α} {s : set α} {t : set α} (h : t ∈ nhds_within a s) : insert a t ∈ nhds_within a (insert a s) := sorry

theorem nhds_within_prod_eq {α : Type u_1} [topological_space α] {β : Type u_2} [topological_space β] (a : α) (b : β) (s : set α) (t : set β) : nhds_within (a, b) (set.prod s t) = filter.prod (nhds_within a s) (nhds_within b t) := sorry

theorem nhds_within_prod {α : Type u_1} [topological_space α] {β : Type u_2} [topological_space β] {s : set α} {u : set α} {t : set β} {v : set β} {a : α} {b : β} (hu : u ∈ nhds_within a s) (hv : v ∈ nhds_within b t) : set.prod u v ∈ nhds_within (a, b) (set.prod s t) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (set.prod u v ∈ nhds_within (a, b) (set.prod s t))) (nhds_within_prod_eq a b s t)))
    (filter.prod_mem_prod hu hv)

theorem tendsto_if_nhds_within {α : Type u_1} {β : Type u_2} [topological_space α] {f : α → β} {g : α → β} {p : α → Prop} [decidable_pred p] {a : α} {s : set α} {l : filter β} (h₀ : filter.tendsto f (nhds_within a (s ∩ p)) l) (h₁ : filter.tendsto g (nhds_within a (s ∩ set_of fun (x : α) => ¬p x)) l) : filter.tendsto (fun (x : α) => ite (p x) (f x) (g x)) (nhds_within a s) l := sorry

theorem map_nhds_within {α : Type u_1} {β : Type u_2} [topological_space α] (f : α → β) (a : α) (s : set α) : filter.map f (nhds_within a s) =
  infi
    fun (t : set α) => infi fun (H : t ∈ set_of fun (t : set α) => a ∈ t ∧ is_open t) => filter.principal (f '' (t ∩ s)) :=
  filter.has_basis.eq_binfi (filter.has_basis.map f (nhds_within_basis_open a s))

theorem tendsto_nhds_within_mono_left {α : Type u_1} {β : Type u_2} [topological_space α] {f : α → β} {a : α} {s : set α} {t : set α} {l : filter β} (hst : s ⊆ t) (h : filter.tendsto f (nhds_within a t) l) : filter.tendsto f (nhds_within a s) l :=
  filter.tendsto.mono_left h (nhds_within_mono a hst)

theorem tendsto_nhds_within_mono_right {α : Type u_1} {β : Type u_2} [topological_space α] {f : β → α} {l : filter β} {a : α} {s : set α} {t : set α} (hst : s ⊆ t) (h : filter.tendsto f l (nhds_within a s)) : filter.tendsto f l (nhds_within a t) :=
  filter.tendsto.mono_right h (nhds_within_mono a hst)

theorem tendsto_nhds_within_of_tendsto_nhds {α : Type u_1} {β : Type u_2} [topological_space α] {f : α → β} {a : α} {s : set α} {l : filter β} (h : filter.tendsto f (nhds a) l) : filter.tendsto f (nhds_within a s) l :=
  filter.tendsto.mono_left h inf_le_left

theorem principal_subtype {α : Type u_1} (s : set α) (t : set (Subtype fun (x : α) => x ∈ s)) : filter.principal t = filter.comap coe (filter.principal (coe '' t)) := sorry

theorem mem_closure_iff_nhds_within_ne_bot {α : Type u_1} [topological_space α] {s : set α} {x : α} : x ∈ closure s ↔ filter.ne_bot (nhds_within x s) :=
  mem_closure_iff_cluster_pt

theorem nhds_within_ne_bot_of_mem {α : Type u_1} [topological_space α] {s : set α} {x : α} (hx : x ∈ s) : filter.ne_bot (nhds_within x s) :=
  iff.mp mem_closure_iff_nhds_within_ne_bot (subset_closure hx)

theorem is_closed.mem_of_nhds_within_ne_bot {α : Type u_1} [topological_space α] {s : set α} (hs : is_closed s) {x : α} (hx : filter.ne_bot (nhds_within x s)) : x ∈ s := sorry

theorem dense_range.nhds_within_ne_bot {α : Type u_1} [topological_space α] {ι : Type u_2} {f : ι → α} (h : dense_range f) (x : α) : filter.ne_bot (nhds_within x (set.range f)) :=
  iff.mp mem_closure_iff_cluster_pt (h x)

theorem eventually_eq_nhds_within_iff {α : Type u_1} {β : Type u_2} [topological_space α] {f : α → β} {g : α → β} {s : set α} {a : α} : filter.eventually_eq (nhds_within a s) f g ↔ filter.eventually (fun (x : α) => x ∈ s → f x = g x) (nhds a) :=
  filter.mem_inf_principal

theorem eventually_eq_nhds_within_of_eq_on {α : Type u_1} {β : Type u_2} [topological_space α] {f : α → β} {g : α → β} {s : set α} {a : α} (h : set.eq_on f g s) : filter.eventually_eq (nhds_within a s) f g :=
  filter.mem_inf_sets_of_right h

theorem set.eq_on.eventually_eq_nhds_within {α : Type u_1} {β : Type u_2} [topological_space α] {f : α → β} {g : α → β} {s : set α} {a : α} (h : set.eq_on f g s) : filter.eventually_eq (nhds_within a s) f g :=
  eventually_eq_nhds_within_of_eq_on h

theorem tendsto_nhds_within_congr {α : Type u_1} {β : Type u_2} [topological_space α] {f : α → β} {g : α → β} {s : set α} {a : α} {l : filter β} (hfg : ∀ (x : α), x ∈ s → f x = g x) (hf : filter.tendsto f (nhds_within a s) l) : filter.tendsto g (nhds_within a s) l :=
  iff.mp (filter.tendsto_congr' (eventually_eq_nhds_within_of_eq_on hfg)) hf

theorem eventually_nhds_with_of_forall {α : Type u_1} [topological_space α] {s : set α} {a : α} {p : α → Prop} (h : ∀ (x : α), x ∈ s → p x) : filter.eventually (fun (x : α) => p x) (nhds_within a s) :=
  filter.mem_inf_sets_of_right h

theorem tendsto_nhds_within_of_tendsto_nhds_of_eventually_within {α : Type u_1} [topological_space α] {β : Type u_2} {a : α} {l : filter β} {s : set α} (f : β → α) (h1 : filter.tendsto f l (nhds a)) (h2 : filter.eventually (fun (x : β) => f x ∈ s) l) : filter.tendsto f l (nhds_within a s) :=
  iff.mpr filter.tendsto_inf { left := h1, right := iff.mpr filter.tendsto_principal h2 }

theorem filter.eventually_eq.eq_of_nhds_within {α : Type u_1} {β : Type u_2} [topological_space α] {s : set α} {f : α → β} {g : α → β} {a : α} (h : filter.eventually_eq (nhds_within a s) f g) (hmem : a ∈ s) : f a = g a :=
  filter.eventually.self_of_nhds_within h hmem

theorem eventually_nhds_within_of_eventually_nhds {α : Type u_1} [topological_space α] {s : set α} {a : α} {p : α → Prop} (h : filter.eventually (fun (x : α) => p x) (nhds a)) : filter.eventually (fun (x : α) => p x) (nhds_within a s) :=
  mem_nhds_within_of_mem_nhds h

/-!
### `nhds_within` and subtypes
-/

theorem mem_nhds_within_subtype {α : Type u_1} [topological_space α] {s : set α} {a : Subtype fun (x : α) => x ∈ s} {t : set (Subtype fun (x : α) => x ∈ s)} {u : set (Subtype fun (x : α) => x ∈ s)} : t ∈ nhds_within a u ↔ t ∈ filter.comap coe (nhds_within (↑a) (coe '' u)) := sorry

theorem nhds_within_subtype {α : Type u_1} [topological_space α] (s : set α) (a : Subtype fun (x : α) => x ∈ s) (t : set (Subtype fun (x : α) => x ∈ s)) : nhds_within a t = filter.comap coe (nhds_within (↑a) (coe '' t)) :=
  filter.ext fun (u : set (Subtype fun (x : α) => x ∈ s)) => mem_nhds_within_subtype

theorem nhds_within_eq_map_subtype_coe {α : Type u_1} [topological_space α] {s : set α} {a : α} (h : a ∈ s) : nhds_within a s = filter.map coe (nhds { val := a, property := h }) := sorry

theorem tendsto_nhds_within_iff_subtype {α : Type u_1} {β : Type u_2} [topological_space α] {s : set α} {a : α} (h : a ∈ s) (f : α → β) (l : filter β) : filter.tendsto f (nhds_within a s) l ↔ filter.tendsto (set.restrict f s) (nhds { val := a, property := h }) l := sorry

/-- A function between topological spaces is continuous at a point `x₀` within a subset `s`
if `f x` tends to `f x₀` when `x` tends to `x₀` while staying within `s`. -/
def continuous_within_at {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β) (s : set α) (x : α) :=
  filter.tendsto f (nhds_within x s) (nhds (f x))

/-- If a function is continuous within `s` at `x`, then it tends to `f x` within `s` by definition.
We register this fact for use with the dot notation, especially to use `tendsto.comp` as
`continuous_within_at.comp` will have a different meaning. -/
theorem continuous_within_at.tendsto {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {x : α} (h : continuous_within_at f s x) : filter.tendsto f (nhds_within x s) (nhds (f x)) :=
  h

/-- A function between topological spaces is continuous on a subset `s`
when it's continuous at every point of `s` within `s`. -/
def continuous_on {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β) (s : set α) :=
  ∀ (x : α), x ∈ s → continuous_within_at f s x

theorem continuous_on.continuous_within_at {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {x : α} (hf : continuous_on f s) (hx : x ∈ s) : continuous_within_at f s x :=
  hf x hx

theorem continuous_within_at_univ {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β) (x : α) : continuous_within_at f set.univ x ↔ continuous_at f x := sorry

theorem continuous_within_at_iff_continuous_at_restrict {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β) {x : α} {s : set α} (h : x ∈ s) : continuous_within_at f s x ↔ continuous_at (set.restrict f s) { val := x, property := h } :=
  tendsto_nhds_within_iff_subtype h f (nhds (f x))

theorem continuous_within_at.tendsto_nhds_within {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {x : α} {s : set α} {t : set β} (h : continuous_within_at f s x) (ht : set.maps_to f s t) : filter.tendsto f (nhds_within x s) (nhds_within (f x) t) :=
  iff.mpr filter.tendsto_inf
    { left := h,
      right := iff.mpr filter.tendsto_principal (filter.mem_inf_sets_of_right (iff.mpr filter.mem_principal_sets ht)) }

theorem continuous_within_at.tendsto_nhds_within_image {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {x : α} {s : set α} (h : continuous_within_at f s x) : filter.tendsto f (nhds_within x s) (nhds_within (f x) (f '' s)) :=
  continuous_within_at.tendsto_nhds_within h (set.maps_to_image f s)

theorem continuous_within_at.prod_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] {f : α → γ} {g : β → δ} {s : set α} {t : set β} {x : α} {y : β} (hf : continuous_within_at f s x) (hg : continuous_within_at g t y) : continuous_within_at (prod.map f g) (set.prod s t) (x, y) := sorry

theorem continuous_on_iff {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} : continuous_on f s ↔
  ∀ (x : α), x ∈ s → ∀ (t : set β), is_open t → f x ∈ t → ∃ (u : set α), is_open u ∧ x ∈ u ∧ u ∩ s ⊆ f ⁻¹' t := sorry

theorem continuous_on_iff_continuous_restrict {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} : continuous_on f s ↔ continuous (set.restrict f s) := sorry

theorem continuous_on_iff' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} : continuous_on f s ↔ ∀ (t : set β), is_open t → ∃ (u : set α), is_open u ∧ f ⁻¹' t ∩ s = u ∩ s := sorry

theorem continuous_on_iff_is_closed {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} : continuous_on f s ↔ ∀ (t : set β), is_closed t → ∃ (u : set α), is_closed u ∧ f ⁻¹' t ∩ s = u ∩ s := sorry

theorem continuous_on.prod_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [topological_space α] [topological_space β] [topological_space γ] [topological_space δ] {f : α → γ} {g : β → δ} {s : set α} {t : set β} (hf : continuous_on f s) (hg : continuous_on g t) : continuous_on (prod.map f g) (set.prod s t) := sorry

theorem continuous_on_empty {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β) : continuous_on f ∅ :=
  fun (x : α) => false.elim

theorem nhds_within_le_comap {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {x : α} {s : set α} {f : α → β} (ctsf : continuous_within_at f s x) : nhds_within x s ≤ filter.comap f (nhds_within (f x) (f '' s)) :=
  iff.mp filter.map_le_iff_le_comap (continuous_within_at.tendsto_nhds_within_image ctsf)

theorem continuous_within_at_iff_ptendsto_res {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : α → β) {x : α} {s : set α} : continuous_within_at f s x ↔ filter.ptendsto (pfun.res f s) (nhds x) (nhds (f x)) :=
  filter.tendsto_iff_ptendsto (nhds x) (nhds (f x)) s f

theorem continuous_iff_continuous_on_univ {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} : continuous f ↔ continuous_on f set.univ := sorry

theorem continuous_within_at.mono {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {t : set α} {x : α} (h : continuous_within_at f t x) (hs : s ⊆ t) : continuous_within_at f s x :=
  filter.tendsto.mono_left h (nhds_within_mono x hs)

theorem continuous_within_at.mono_of_mem {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {t : set α} {x : α} (h : continuous_within_at f t x) (hs : t ∈ nhds_within x s) : continuous_within_at f s x :=
  filter.tendsto.mono_left h (nhds_within_le_of_mem hs)

theorem continuous_within_at_inter' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {t : set α} {x : α} (h : t ∈ nhds_within x s) : continuous_within_at f (s ∩ t) x ↔ continuous_within_at f s x := sorry

theorem continuous_within_at_inter {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {t : set α} {x : α} (h : t ∈ nhds x) : continuous_within_at f (s ∩ t) x ↔ continuous_within_at f s x := sorry

theorem continuous_within_at_union {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {t : set α} {x : α} : continuous_within_at f (s ∪ t) x ↔ continuous_within_at f s x ∧ continuous_within_at f t x := sorry

theorem continuous_within_at.union {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {t : set α} {x : α} (hs : continuous_within_at f s x) (ht : continuous_within_at f t x) : continuous_within_at f (s ∪ t) x :=
  iff.mpr continuous_within_at_union { left := hs, right := ht }

theorem continuous_within_at.mem_closure_image {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {x : α} (h : continuous_within_at f s x) (hx : x ∈ closure s) : f x ∈ closure (f '' s) :=
  mem_closure_of_tendsto h (filter.mem_sets_of_superset self_mem_nhds_within (set.subset_preimage_image f s))

theorem continuous_within_at.mem_closure {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {x : α} {A : set β} (h : continuous_within_at f s x) (hx : x ∈ closure s) (hA : s ⊆ f ⁻¹' A) : f x ∈ closure A :=
  closure_mono (iff.mpr set.image_subset_iff hA) (continuous_within_at.mem_closure_image h hx)

theorem continuous_within_at.image_closure {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} (hf : ∀ (x : α), x ∈ closure s → continuous_within_at f s x) : f '' closure s ⊆ closure (f '' s) := sorry

@[simp] theorem continuous_within_at_singleton {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {x : α} : continuous_within_at f (singleton x) x := sorry

@[simp] theorem continuous_within_at_insert_self {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {x : α} {s : set α} : continuous_within_at f (insert x s) x ↔ continuous_within_at f s x := sorry

theorem continuous_within_at.insert_self {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {x : α} {s : set α} : continuous_within_at f s x → continuous_within_at f (insert x s) x :=
  iff.mpr continuous_within_at_insert_self

theorem continuous_within_at.diff_iff {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {t : set α} {x : α} (ht : continuous_within_at f t x) : continuous_within_at f (s \ t) x ↔ continuous_within_at f s x := sorry

@[simp] theorem continuous_within_at_diff_self {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {x : α} : continuous_within_at f (s \ singleton x) x ↔ continuous_within_at f s x :=
  continuous_within_at.diff_iff continuous_within_at_singleton

theorem is_open_map.continuous_on_image_of_left_inv_on {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} (h : is_open_map (set.restrict f s)) {finv : β → α} (hleft : set.left_inv_on finv f s) : continuous_on finv (f '' s) := sorry

theorem is_open_map.continuous_on_range_of_left_inverse {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} (hf : is_open_map f) {finv : β → α} (hleft : function.left_inverse finv f) : continuous_on finv (set.range f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (continuous_on finv (set.range f))) (Eq.symm set.image_univ)))
    (is_open_map.continuous_on_image_of_left_inv_on (is_open_map.restrict hf is_open_univ)
      fun (x : α) (_x : x ∈ set.univ) => hleft x)

theorem continuous_on.congr_mono {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {g : α → β} {s : set α} {s₁ : set α} (h : continuous_on f s) (h' : set.eq_on g f s₁) (h₁ : s₁ ⊆ s) : continuous_on g s₁ := sorry

theorem continuous_on.congr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {g : α → β} {s : set α} (h : continuous_on f s) (h' : set.eq_on g f s) : continuous_on g s :=
  continuous_on.congr_mono h h' (set.subset.refl s)

theorem continuous_on_congr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {g : α → β} {s : set α} (h' : set.eq_on g f s) : continuous_on g s ↔ continuous_on f s :=
  { mp := fun (h : continuous_on g s) => continuous_on.congr h (set.eq_on.symm h'),
    mpr := fun (h : continuous_on f s) => continuous_on.congr h h' }

theorem continuous_at.continuous_within_at {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {x : α} (h : continuous_at f x) : continuous_within_at f s x :=
  continuous_within_at.mono (iff.mpr (continuous_within_at_univ f x) h) (set.subset_univ s)

theorem continuous_within_at.continuous_at {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {x : α} (h : continuous_within_at f s x) (hs : s ∈ nhds x) : continuous_at f x := sorry

theorem continuous_on.continuous_at {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {x : α} (h : continuous_on f s) (hx : s ∈ nhds x) : continuous_at f x :=
  continuous_within_at.continuous_at (h x (mem_of_nhds hx)) hx

theorem continuous_within_at.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} {s : set α} {t : set β} {x : α} (hg : continuous_within_at g t (f x)) (hf : continuous_within_at f s x) (h : s ⊆ f ⁻¹' t) : continuous_within_at (g ∘ f) s x := sorry

theorem continuous_within_at.comp' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} {s : set α} {t : set β} {x : α} (hg : continuous_within_at g t (f x)) (hf : continuous_within_at f s x) : continuous_within_at (g ∘ f) (s ∩ f ⁻¹' t) x :=
  continuous_within_at.comp hg (continuous_within_at.mono hf (set.inter_subset_left s (f ⁻¹' t)))
    (set.inter_subset_right s (f ⁻¹' t))

theorem continuous_on.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} {s : set α} {t : set β} (hg : continuous_on g t) (hf : continuous_on f s) (h : s ⊆ f ⁻¹' t) : continuous_on (g ∘ f) s :=
  fun (x : α) (hx : x ∈ s) => continuous_within_at.comp (hg (f x) (h hx)) (hf x hx) h

theorem continuous_on.mono {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {t : set α} (hf : continuous_on f s) (h : t ⊆ s) : continuous_on f t :=
  fun (x : α) (hx : x ∈ t) => filter.tendsto.mono_left (hf x (h hx)) (nhds_within_mono x h)

theorem continuous_on.comp' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} {s : set α} {t : set β} (hg : continuous_on g t) (hf : continuous_on f s) : continuous_on (g ∘ f) (s ∩ f ⁻¹' t) :=
  continuous_on.comp hg (continuous_on.mono hf (set.inter_subset_left s (f ⁻¹' t))) (set.inter_subset_right s (f ⁻¹' t))

theorem continuous.continuous_on {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} (h : continuous f) : continuous_on f s :=
  continuous_on.mono (eq.mp (Eq._oldrec (Eq.refl (continuous f)) (propext continuous_iff_continuous_on_univ)) h)
    (set.subset_univ s)

theorem continuous.continuous_within_at {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {x : α} (h : continuous f) : continuous_within_at f s x :=
  continuous_at.continuous_within_at (continuous.continuous_at h)

theorem continuous.comp_continuous_on {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} {s : set α} (hg : continuous g) (hf : continuous_on f s) : continuous_on (g ∘ f) s :=
  continuous_on.comp (continuous.continuous_on hg) hf set.subset_preimage_univ

theorem continuous_on.comp_continuous {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} {s : set β} (hg : continuous_on g s) (hf : continuous f) (hs : ∀ (x : α), f x ∈ s) : continuous (g ∘ f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (continuous (g ∘ f))) (propext continuous_iff_continuous_on_univ)))
    (continuous_on.comp hg (eq.mp (Eq._oldrec (Eq.refl (continuous f)) (propext continuous_iff_continuous_on_univ)) hf)
      fun (x : α) (_x : x ∈ set.univ) => hs x)

theorem continuous_within_at.preimage_mem_nhds_within {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {x : α} {s : set α} {t : set β} (h : continuous_within_at f s x) (ht : t ∈ nhds (f x)) : f ⁻¹' t ∈ nhds_within x s :=
  h ht

theorem continuous_within_at.preimage_mem_nhds_within' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {x : α} {s : set α} {t : set β} (h : continuous_within_at f s x) (ht : t ∈ nhds_within (f x) (f '' s)) : f ⁻¹' t ∈ nhds_within x s := sorry

theorem continuous_within_at.congr_of_eventually_eq {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {f₁ : α → β} {s : set α} {x : α} (h : continuous_within_at f s x) (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) : continuous_within_at f₁ s x := sorry

theorem continuous_within_at.congr {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {f₁ : α → β} {s : set α} {x : α} (h : continuous_within_at f s x) (h₁ : ∀ (y : α), y ∈ s → f₁ y = f y) (hx : f₁ x = f x) : continuous_within_at f₁ s x :=
  continuous_within_at.congr_of_eventually_eq h (filter.mem_sets_of_superset self_mem_nhds_within h₁) hx

theorem continuous_within_at.congr_mono {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {g : α → β} {s : set α} {s₁ : set α} {x : α} (h : continuous_within_at f s x) (h' : set.eq_on g f s₁) (h₁ : s₁ ⊆ s) (hx : g x = f x) : continuous_within_at g s₁ x :=
  continuous_within_at.congr (continuous_within_at.mono h h₁) h' hx

theorem continuous_on_const {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {s : set α} {c : β} : continuous_on (fun (x : α) => c) s :=
  continuous.continuous_on continuous_const

theorem continuous_within_at_const {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {b : β} {s : set α} {x : α} : continuous_within_at (fun (_x : α) => b) s x :=
  continuous.continuous_within_at continuous_const

theorem continuous_on_id {α : Type u_1} [topological_space α] {s : set α} : continuous_on id s :=
  continuous.continuous_on continuous_id

theorem continuous_within_at_id {α : Type u_1} [topological_space α] {s : set α} {x : α} : continuous_within_at id s x :=
  continuous.continuous_within_at continuous_id

theorem continuous_on_open_iff {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} (hs : is_open s) : continuous_on f s ↔ ∀ (t : set β), is_open t → is_open (s ∩ f ⁻¹' t) := sorry

theorem continuous_on.preimage_open_of_open {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {t : set β} (hf : continuous_on f s) (hs : is_open s) (ht : is_open t) : is_open (s ∩ f ⁻¹' t) :=
  iff.mp (continuous_on_open_iff hs) hf t ht

theorem continuous_on.preimage_closed_of_closed {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {t : set β} (hf : continuous_on f s) (hs : is_closed s) (ht : is_closed t) : is_closed (s ∩ f ⁻¹' t) := sorry

theorem continuous_on.preimage_interior_subset_interior_preimage {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {t : set β} (hf : continuous_on f s) (hs : is_open s) : s ∩ f ⁻¹' interior t ⊆ s ∩ interior (f ⁻¹' t) := sorry

theorem continuous_on_of_locally_continuous_on {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} (h : ∀ (x : α), x ∈ s → ∃ (t : set α), is_open t ∧ x ∈ t ∧ continuous_on f (s ∩ t)) : continuous_on f s := sorry

theorem continuous_on_open_of_generate_from {α : Type u_1} [topological_space α] {β : Type u_2} {s : set α} {T : set (set β)} {f : α → β} (hs : is_open s) (h : ∀ (t : set β), t ∈ T → is_open (s ∩ f ⁻¹' t)) : continuous_on f s := sorry

theorem continuous_within_at.prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {g : α → γ} {s : set α} {x : α} (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) : continuous_within_at (fun (x : α) => (f x, g x)) s x :=
  filter.tendsto.prod_mk_nhds hf hg

theorem continuous_on.prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {g : α → γ} {s : set α} (hf : continuous_on f s) (hg : continuous_on g s) : continuous_on (fun (x : α) => (f x, g x)) s :=
  fun (x : α) (hx : x ∈ s) => continuous_within_at.prod (hf x hx) (hg x hx)

theorem inducing.continuous_on_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {g : β → γ} (hg : inducing g) {s : set α} : continuous_on f s ↔ continuous_on (g ∘ f) s := sorry

theorem embedding.continuous_on_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {g : β → γ} (hg : embedding g) {s : set α} : continuous_on f s ↔ continuous_on (g ∘ f) s :=
  inducing.continuous_on_iff (embedding.to_inducing hg)

theorem continuous_within_at_of_not_mem_closure {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : α → β} {s : set α} {x : α} : ¬x ∈ closure s → continuous_within_at f s x := sorry

theorem continuous_on_if' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {s : set α} {p : α → Prop} {f : α → β} {g : α → β} {h : (a : α) → Decidable (p a)} (hpf : ∀ (a : α),
  a ∈ s ∩ frontier (set_of fun (a : α) => p a) →
    filter.tendsto f (nhds_within a (s ∩ set_of fun (a : α) => p a)) (nhds (ite (p a) (f a) (g a)))) (hpg : ∀ (a : α),
  a ∈ s ∩ frontier (set_of fun (a : α) => p a) →
    filter.tendsto g (nhds_within a (s ∩ set_of fun (a : α) => ¬p a)) (nhds (ite (p a) (f a) (g a)))) (hf : continuous_on f (s ∩ set_of fun (a : α) => p a)) (hg : continuous_on g (s ∩ set_of fun (a : α) => ¬p a)) : continuous_on (fun (a : α) => ite (p a) (f a) (g a)) s := sorry

theorem continuous_on_if {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {p : α → Prop} {h : (a : α) → Decidable (p a)} {s : set α} {f : α → β} {g : α → β} (hp : ∀ (a : α), a ∈ s ∩ frontier (set_of fun (a : α) => p a) → f a = g a) (hf : continuous_on f (s ∩ closure (set_of fun (a : α) => p a))) (hg : continuous_on g (s ∩ closure (set_of fun (a : α) => ¬p a))) : continuous_on (fun (a : α) => ite (p a) (f a) (g a)) s := sorry

theorem continuous_if' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {p : α → Prop} {f : α → β} {g : α → β} {h : (a : α) → Decidable (p a)} (hpf : ∀ (a : α),
  a ∈ frontier (set_of fun (x : α) => p x) →
    filter.tendsto f (nhds_within a (set_of fun (x : α) => p x)) (nhds (ite (p a) (f a) (g a)))) (hpg : ∀ (a : α),
  a ∈ frontier (set_of fun (x : α) => p x) →
    filter.tendsto g (nhds_within a (set_of fun (x : α) => ¬p x)) (nhds (ite (p a) (f a) (g a)))) (hf : continuous_on f (set_of fun (x : α) => p x)) (hg : continuous_on g (set_of fun (x : α) => ¬p x)) : continuous fun (a : α) => ite (p a) (f a) (g a) := sorry

theorem continuous_on_fst {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {s : set (α × β)} : continuous_on prod.fst s :=
  continuous.continuous_on continuous_fst

theorem continuous_within_at_fst {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {s : set (α × β)} {p : α × β} : continuous_within_at prod.fst s p :=
  continuous.continuous_within_at continuous_fst

theorem continuous_on_snd {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {s : set (α × β)} : continuous_on prod.snd s :=
  continuous.continuous_on continuous_snd

theorem continuous_within_at_snd {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {s : set (α × β)} {p : α × β} : continuous_within_at prod.snd s p :=
  continuous.continuous_within_at continuous_snd

