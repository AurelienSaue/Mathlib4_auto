/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.filter.ultrafilter
import Mathlib.order.filter.partial
import Mathlib.PostPort

universes u l w v u_1 u_2 u_3 u_5 

namespace Mathlib

/-!
# Basic theory of topological spaces.

The main definition is the type class `topological space α` which endows a type `α` with a topology.
Then `set α` gets predicates `is_open`, `is_closed` and functions `interior`, `closure` and
`frontier`. Each point `x` of `α` gets a neighborhood filter `𝓝 x`. A filter `F` on `α` has
`x` as a cluster point if `cluster_pt x F : 𝓝 x ⊓ F ≠ ⊥`. A map `f : ι → α` clusters at `x`
along `F : filter ι` if `map_cluster_pt x F f : cluster_pt x (map f F)`. In particular
the notion of cluster point of a sequence `u` is `map_cluster_pt x at_top u`.

This file also defines locally finite families of subsets of `α`.

For topological spaces `α` and `β`, a function `f : α → β` and a point `a : α`,
`continuous_at f a` means `f` is continuous at `a`, and global continuity is
`continuous f`. There is also a version of continuity `pcontinuous` for
partially defined functions.

## Notation

* `𝓝 x`: the filter of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;

## Implementation notes

Topology in mathlib heavily uses filters (even more than in Bourbaki). See explanations in
<https://leanprover-community.github.io/theories/topology.html>.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]
*  [I. M. James, *Topologies and Uniformities*][james1999]

## Tags

topological space, interior, closure, frontier, neighborhood, continuity, continuous function
-/

/-!
### Topological spaces
-/

/-- A topology on `α`. -/
class topological_space (α : Type u) where
  is_open : set α → Prop
  is_open_univ : is_open set.univ
  is_open_inter : ∀ (s t : set α), is_open s → is_open t → is_open (s ∩ t)
  is_open_sUnion : ∀ (s : set (set α)), (∀ (t : set α), t ∈ s → is_open t) → is_open (⋃₀s)

/-- A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions. -/
def topological_space.of_closed {α : Type u} (T : set (set α)) (empty_mem : ∅ ∈ T)
    (sInter_mem : ∀ (A : set (set α)), A ⊆ T → ⋂₀A ∈ T)
    (union_mem : ∀ (A B : set α), A ∈ T → B ∈ T → A ∪ B ∈ T) : topological_space α :=
  topological_space.mk (fun (X : set α) => Xᶜ ∈ T) sorry sorry sorry

theorem topological_space_eq {α : Type u} {f : topological_space α} {g : topological_space α} :
    topological_space.is_open f = topological_space.is_open g → f = g :=
  sorry

/-- `is_open s` means that `s` is open in the ambient topological space on `α` -/
def is_open {α : Type u} [t : topological_space α] (s : set α) := topological_space.is_open t s

@[simp] theorem is_open_univ {α : Type u} [t : topological_space α] : is_open set.univ :=
  topological_space.is_open_univ t

theorem is_open_inter {α : Type u} {s₁ : set α} {s₂ : set α} [t : topological_space α]
    (h₁ : is_open s₁) (h₂ : is_open s₂) : is_open (s₁ ∩ s₂) :=
  topological_space.is_open_inter t s₁ s₂ h₁ h₂

theorem is_open_sUnion {α : Type u} [t : topological_space α] {s : set (set α)}
    (h : ∀ (t_1 : set α), t_1 ∈ s → is_open t_1) : is_open (⋃₀s) :=
  topological_space.is_open_sUnion t s h

theorem topological_space_eq_iff {α : Type u} {t : topological_space α} {t' : topological_space α} :
    t = t' ↔ ∀ (s : set α), is_open s ↔ is_open s :=
  { mp := fun (h : t = t') (s : set α) => h ▸ iff.rfl,
    mpr :=
      fun (h : ∀ (s : set α), is_open s ↔ is_open s) =>
        topological_space_eq (funext fun (x : set α) => propext (h x)) }

theorem is_open_fold {α : Type u} {s : set α} {t : topological_space α} :
    topological_space.is_open t s = is_open s :=
  rfl

theorem is_open_Union {α : Type u} {ι : Sort w} [topological_space α] {f : ι → set α}
    (h : ∀ (i : ι), is_open (f i)) : is_open (set.Union fun (i : ι) => f i) :=
  is_open_sUnion
    fun (t : set α) (H : t ∈ set.range fun (i : ι) => f i) =>
      Exists.dcases_on H fun (i : ι) (H_h : (fun (i : ι) => f i) i = t) => Eq._oldrec (h i) H_h

theorem is_open_bUnion {α : Type u} {β : Type v} [topological_space α] {s : set β} {f : β → set α}
    (h : ∀ (i : β), i ∈ s → is_open (f i)) :
    is_open (set.Union fun (i : β) => set.Union fun (H : i ∈ s) => f i) :=
  is_open_Union fun (i : β) => is_open_Union fun (hi : i ∈ s) => h i hi

theorem is_open_union {α : Type u} {s₁ : set α} {s₂ : set α} [topological_space α] (h₁ : is_open s₁)
    (h₂ : is_open s₂) : is_open (s₁ ∪ s₂) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_open (s₁ ∪ s₂))) set.union_eq_Union))
    (is_open_Union (iff.mpr bool.forall_bool { left := h₂, right := h₁ }))

@[simp] theorem is_open_empty {α : Type u} [topological_space α] : is_open ∅ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_open ∅)) (Eq.symm set.sUnion_empty)))
    (is_open_sUnion fun (a : set α) => false.elim)

theorem is_open_sInter {α : Type u} [topological_space α] {s : set (set α)} (hs : set.finite s) :
    (∀ (t : set α), t ∈ s → is_open t) → is_open (⋂₀s) :=
  sorry

theorem is_open_bInter {α : Type u} {β : Type v} [topological_space α] {s : set β} {f : β → set α}
    (hs : set.finite s) :
    (∀ (i : β), i ∈ s → is_open (f i)) →
        is_open (set.Inter fun (i : β) => set.Inter fun (H : i ∈ s) => f i) :=
  sorry

theorem is_open_Inter {α : Type u} {β : Type v} [topological_space α] [fintype β] {s : β → set α}
    (h : ∀ (i : β), is_open (s i)) : is_open (set.Inter fun (i : β) => s i) :=
  sorry

theorem is_open_Inter_prop {α : Type u} [topological_space α] {p : Prop} {s : p → set α}
    (h : ∀ (h : p), is_open (s h)) : is_open (set.Inter s) :=
  sorry

theorem is_open_const {α : Type u} [topological_space α] {p : Prop} :
    is_open (set_of fun (a : α) => p) :=
  sorry

theorem is_open_and {α : Type u} {p₁ : α → Prop} {p₂ : α → Prop} [topological_space α] :
    is_open (set_of fun (a : α) => p₁ a) →
        is_open (set_of fun (a : α) => p₂ a) → is_open (set_of fun (a : α) => p₁ a ∧ p₂ a) :=
  is_open_inter

/-- A set is closed if its complement is open -/
def is_closed {α : Type u} [topological_space α] (s : set α) := is_open (sᶜ)

@[simp] theorem is_closed_empty {α : Type u} [topological_space α] : is_closed ∅ :=
  eq.mpr (id (is_closed.equations._eqn_1 ∅))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_open (∅ᶜ))) set.compl_empty)) is_open_univ)

@[simp] theorem is_closed_univ {α : Type u} [topological_space α] : is_closed set.univ :=
  eq.mpr (id (is_closed.equations._eqn_1 set.univ))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_open (set.univᶜ))) set.compl_univ)) is_open_empty)

theorem is_closed_union {α : Type u} {s₁ : set α} {s₂ : set α} [topological_space α] :
    is_closed s₁ → is_closed s₂ → is_closed (s₁ ∪ s₂) :=
  fun (h₁ : is_closed s₁) (h₂ : is_closed s₂) =>
    eq.mpr (id (is_closed.equations._eqn_1 (s₁ ∪ s₂)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (is_open (s₁ ∪ s₂ᶜ))) (set.compl_union s₁ s₂)))
        (is_open_inter h₁ h₂))

theorem is_closed_sInter {α : Type u} [topological_space α] {s : set (set α)} :
    (∀ (t : set α), t ∈ s → is_closed t) → is_closed (⋂₀s) :=
  sorry

theorem is_closed_Inter {α : Type u} {ι : Sort w} [topological_space α] {f : ι → set α}
    (h : ∀ (i : ι), is_closed (f i)) : is_closed (set.Inter fun (i : ι) => f i) :=
  sorry

@[simp] theorem is_open_compl_iff {α : Type u} [topological_space α] {s : set α} :
    is_open (sᶜ) ↔ is_closed s :=
  iff.rfl

@[simp] theorem is_closed_compl_iff {α : Type u} [topological_space α] {s : set α} :
    is_closed (sᶜ) ↔ is_open s :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (is_closed (sᶜ) ↔ is_open s)) (Eq.symm (propext is_open_compl_iff))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_open (sᶜᶜ) ↔ is_open s)) (compl_compl s)))
      (iff.refl (is_open s)))

theorem is_open_diff {α : Type u} [topological_space α] {s : set α} {t : set α} (h₁ : is_open s)
    (h₂ : is_closed t) : is_open (s \ t) :=
  is_open_inter h₁ (iff.mpr is_open_compl_iff h₂)

theorem is_closed_inter {α : Type u} {s₁ : set α} {s₂ : set α} [topological_space α]
    (h₁ : is_closed s₁) (h₂ : is_closed s₂) : is_closed (s₁ ∩ s₂) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_closed (s₁ ∩ s₂))) (is_closed.equations._eqn_1 (s₁ ∩ s₂))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_open (s₁ ∩ s₂ᶜ))) (set.compl_inter s₁ s₂)))
      (is_open_union h₁ h₂))

theorem is_closed_bUnion {α : Type u} {β : Type v} [topological_space α] {s : set β} {f : β → set α}
    (hs : set.finite s) :
    (∀ (i : β), i ∈ s → is_closed (f i)) →
        is_closed (set.Union fun (i : β) => set.Union fun (H : i ∈ s) => f i) :=
  sorry

theorem is_closed_Union {α : Type u} {β : Type v} [topological_space α] [fintype β] {s : β → set α}
    (h : ∀ (i : β), is_closed (s i)) : is_closed (set.Union s) :=
  sorry

theorem is_closed_Union_prop {α : Type u} [topological_space α] {p : Prop} {s : p → set α}
    (h : ∀ (h : p), is_closed (s h)) : is_closed (set.Union s) :=
  sorry

theorem is_closed_imp {α : Type u} [topological_space α] {p : α → Prop} {q : α → Prop}
    (hp : is_open (set_of fun (x : α) => p x)) (hq : is_closed (set_of fun (x : α) => q x)) :
    is_closed (set_of fun (x : α) => p x → q x) :=
  sorry

theorem is_open_neg {α : Type u} {p : α → Prop} [topological_space α] :
    is_closed (set_of fun (a : α) => p a) → is_open (set_of fun (a : α) => ¬p a) :=
  iff.mpr is_open_compl_iff

/-!
### Interior of a set
-/

/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior {α : Type u} [topological_space α] (s : set α) : set α :=
  ⋃₀set_of fun (t : set α) => is_open t ∧ t ⊆ s

theorem mem_interior {α : Type u} [topological_space α] {s : set α} {x : α} :
    x ∈ interior s ↔ ∃ (t : set α), ∃ (H : t ⊆ s), is_open t ∧ x ∈ t :=
  sorry

@[simp] theorem is_open_interior {α : Type u} [topological_space α] {s : set α} :
    is_open (interior s) :=
  sorry

theorem interior_subset {α : Type u} [topological_space α] {s : set α} : interior s ⊆ s := sorry

theorem interior_maximal {α : Type u} [topological_space α] {s : set α} {t : set α} (h₁ : t ⊆ s)
    (h₂ : is_open t) : t ⊆ interior s :=
  set.subset_sUnion_of_mem { left := h₂, right := h₁ }

theorem is_open.interior_eq {α : Type u} [topological_space α] {s : set α} (h : is_open s) :
    interior s = s :=
  set.subset.antisymm interior_subset (interior_maximal (set.subset.refl s) h)

theorem interior_eq_iff_open {α : Type u} [topological_space α] {s : set α} :
    interior s = s ↔ is_open s :=
  { mp := fun (h : interior s = s) => h ▸ is_open_interior, mpr := is_open.interior_eq }

theorem subset_interior_iff_open {α : Type u} [topological_space α] {s : set α} :
    s ⊆ interior s ↔ is_open s :=
  sorry

theorem subset_interior_iff_subset_of_open {α : Type u} [topological_space α] {s : set α}
    {t : set α} (h₁ : is_open s) : s ⊆ interior t ↔ s ⊆ t :=
  { mp := fun (h : s ⊆ interior t) => set.subset.trans h interior_subset,
    mpr := fun (h₂ : s ⊆ t) => interior_maximal h₂ h₁ }

theorem interior_mono {α : Type u} [topological_space α] {s : set α} {t : set α} (h : s ⊆ t) :
    interior s ⊆ interior t :=
  interior_maximal (set.subset.trans interior_subset h) is_open_interior

@[simp] theorem interior_empty {α : Type u} [topological_space α] : interior ∅ = ∅ :=
  is_open.interior_eq is_open_empty

@[simp] theorem interior_univ {α : Type u} [topological_space α] : interior set.univ = set.univ :=
  is_open.interior_eq is_open_univ

@[simp] theorem interior_interior {α : Type u} [topological_space α] {s : set α} :
    interior (interior s) = interior s :=
  is_open.interior_eq is_open_interior

@[simp] theorem interior_inter {α : Type u} [topological_space α] {s : set α} {t : set α} :
    interior (s ∩ t) = interior s ∩ interior t :=
  sorry

theorem interior_union_is_closed_of_interior_empty {α : Type u} [topological_space α] {s : set α}
    {t : set α} (h₁ : is_closed s) (h₂ : interior t = ∅) : interior (s ∪ t) = interior s :=
  sorry

theorem is_open_iff_forall_mem_open {α : Type u} {s : set α} [topological_space α] :
    is_open s ↔ ∀ (x : α) (H : x ∈ s), ∃ (t : set α), ∃ (H : t ⊆ s), is_open t ∧ x ∈ t :=
  sorry

/-!
### Closure of a set
-/

/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure {α : Type u} [topological_space α] (s : set α) : set α :=
  ⋂₀set_of fun (t : set α) => is_closed t ∧ s ⊆ t

@[simp] theorem is_closed_closure {α : Type u} [topological_space α] {s : set α} :
    is_closed (closure s) :=
  sorry

theorem subset_closure {α : Type u} [topological_space α] {s : set α} : s ⊆ closure s := sorry

theorem closure_minimal {α : Type u} [topological_space α] {s : set α} {t : set α} (h₁ : s ⊆ t)
    (h₂ : is_closed t) : closure s ⊆ t :=
  set.sInter_subset_of_mem { left := h₂, right := h₁ }

theorem is_closed.closure_eq {α : Type u} [topological_space α] {s : set α} (h : is_closed s) :
    closure s = s :=
  set.subset.antisymm (closure_minimal (set.subset.refl s) h) subset_closure

theorem is_closed.closure_subset {α : Type u} [topological_space α] {s : set α} (hs : is_closed s) :
    closure s ⊆ s :=
  closure_minimal (set.subset.refl s) hs

theorem is_closed.closure_subset_iff {α : Type u} [topological_space α] {s : set α} {t : set α}
    (h₁ : is_closed t) : closure s ⊆ t ↔ s ⊆ t :=
  { mp := set.subset.trans subset_closure, mpr := fun (h : s ⊆ t) => closure_minimal h h₁ }

theorem closure_mono {α : Type u} [topological_space α] {s : set α} {t : set α} (h : s ⊆ t) :
    closure s ⊆ closure t :=
  closure_minimal (set.subset.trans h subset_closure) is_closed_closure

theorem monotone_closure (α : Type u_1) [topological_space α] : monotone closure :=
  fun (_x _x_1 : set α) => closure_mono

theorem closure_inter_subset_inter_closure {α : Type u} [topological_space α] (s : set α)
    (t : set α) : closure (s ∩ t) ⊆ closure s ∩ closure t :=
  monotone.map_inf_le (monotone_closure α) s t

theorem is_closed_of_closure_subset {α : Type u} [topological_space α] {s : set α}
    (h : closure s ⊆ s) : is_closed s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_closed s)) (set.subset.antisymm subset_closure h)))
    is_closed_closure

theorem closure_eq_iff_is_closed {α : Type u} [topological_space α] {s : set α} :
    closure s = s ↔ is_closed s :=
  { mp := fun (h : closure s = s) => h ▸ is_closed_closure, mpr := is_closed.closure_eq }

theorem closure_subset_iff_is_closed {α : Type u} [topological_space α] {s : set α} :
    closure s ⊆ s ↔ is_closed s :=
  { mp := is_closed_of_closure_subset, mpr := is_closed.closure_subset }

@[simp] theorem closure_empty {α : Type u} [topological_space α] : closure ∅ = ∅ :=
  is_closed.closure_eq is_closed_empty

@[simp] theorem closure_empty_iff {α : Type u} [topological_space α] (s : set α) :
    closure s = ∅ ↔ s = ∅ :=
  { mp := set.subset_eq_empty subset_closure, mpr := fun (h : s = ∅) => Eq.symm h ▸ closure_empty }

theorem set.nonempty.closure {α : Type u} [topological_space α] {s : set α} (h : set.nonempty s) :
    set.nonempty (closure s) :=
  sorry

@[simp] theorem closure_univ {α : Type u} [topological_space α] : closure set.univ = set.univ :=
  is_closed.closure_eq is_closed_univ

@[simp] theorem closure_closure {α : Type u} [topological_space α] {s : set α} :
    closure (closure s) = closure s :=
  is_closed.closure_eq is_closed_closure

@[simp] theorem closure_union {α : Type u} [topological_space α] {s : set α} {t : set α} :
    closure (s ∪ t) = closure s ∪ closure t :=
  sorry

theorem interior_subset_closure {α : Type u} [topological_space α] {s : set α} :
    interior s ⊆ closure s :=
  set.subset.trans interior_subset subset_closure

theorem closure_eq_compl_interior_compl {α : Type u} [topological_space α] {s : set α} :
    closure s = (interior (sᶜ)ᶜ) :=
  sorry

@[simp] theorem interior_compl {α : Type u} [topological_space α] {s : set α} :
    interior (sᶜ) = (closure sᶜ) :=
  sorry

@[simp] theorem closure_compl {α : Type u} [topological_space α] {s : set α} :
    closure (sᶜ) = (interior sᶜ) :=
  sorry

theorem mem_closure_iff {α : Type u} [topological_space α] {s : set α} {a : α} :
    a ∈ closure s ↔ ∀ (o : set α), is_open o → a ∈ o → set.nonempty (o ∩ s) :=
  sorry

/-- A set is dense in a topological space if every point belongs to its closure. -/
def dense {α : Type u} [topological_space α] (s : set α) := ∀ (x : α), x ∈ closure s

theorem dense_iff_closure_eq {α : Type u} [topological_space α] {s : set α} :
    dense s ↔ closure s = set.univ :=
  iff.symm set.eq_univ_iff_forall

theorem dense.closure_eq {α : Type u} [topological_space α] {s : set α} (h : dense s) :
    closure s = set.univ :=
  iff.mp dense_iff_closure_eq h

/-- The closure of a set `s` is dense if and only if `s` is dense. -/
@[simp] theorem dense_closure {α : Type u} [topological_space α] {s : set α} :
    dense (closure s) ↔ dense s :=
  sorry

theorem dense.of_closure {α : Type u} [topological_space α] {s : set α} :
    dense (closure s) → dense s :=
  iff.mp dense_closure

@[simp] theorem dense_univ {α : Type u} [topological_space α] : dense set.univ :=
  fun (x : α) => subset_closure trivial

/-- A set is dense if and only if it has a nonempty intersection with each nonempty open set. -/
theorem dense_iff_inter_open {α : Type u} [topological_space α] {s : set α} :
    dense s ↔ ∀ (U : set α), is_open U → set.nonempty U → set.nonempty (U ∩ s) :=
  sorry

theorem dense.inter_open_nonempty {α : Type u} [topological_space α] {s : set α} :
    dense s → ∀ (U : set α), is_open U → set.nonempty U → set.nonempty (U ∩ s) :=
  iff.mp dense_iff_inter_open

theorem dense.nonempty_iff {α : Type u} [topological_space α] {s : set α} (hs : dense s) :
    set.nonempty s ↔ Nonempty α :=
  sorry

theorem dense.nonempty {α : Type u} [topological_space α] [h : Nonempty α] {s : set α}
    (hs : dense s) : set.nonempty s :=
  iff.mpr (dense.nonempty_iff hs) h

theorem dense.mono {α : Type u} [topological_space α] {s₁ : set α} {s₂ : set α} (h : s₁ ⊆ s₂)
    (hd : dense s₁) : dense s₂ :=
  fun (x : α) => closure_mono h (hd x)

/-!
### Frontier of a set
-/

/-- The frontier of a set is the set of points between the closure and interior. -/
def frontier {α : Type u} [topological_space α] (s : set α) : set α := closure s \ interior s

theorem frontier_eq_closure_inter_closure {α : Type u} [topological_space α] {s : set α} :
    frontier s = closure s ∩ closure (sᶜ) :=
  sorry

/-- The complement of a set has the same frontier as the original set. -/
@[simp] theorem frontier_compl {α : Type u} [topological_space α] (s : set α) :
    frontier (sᶜ) = frontier s :=
  sorry

theorem frontier_inter_subset {α : Type u} [topological_space α] (s : set α) (t : set α) :
    frontier (s ∩ t) ⊆ frontier s ∩ closure t ∪ closure s ∩ frontier t :=
  sorry

theorem frontier_union_subset {α : Type u} [topological_space α] (s : set α) (t : set α) :
    frontier (s ∪ t) ⊆ frontier s ∩ closure (tᶜ) ∪ closure (sᶜ) ∩ frontier t :=
  sorry

theorem is_closed.frontier_eq {α : Type u} [topological_space α] {s : set α} (hs : is_closed s) :
    frontier s = s \ interior s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (frontier s = s \ interior s)) (frontier.equations._eqn_1 s)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (closure s \ interior s = s \ interior s)) (is_closed.closure_eq hs)))
      (Eq.refl (s \ interior s)))

theorem is_open.frontier_eq {α : Type u} [topological_space α] {s : set α} (hs : is_open s) :
    frontier s = closure s \ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (frontier s = closure s \ s)) (frontier.equations._eqn_1 s)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (closure s \ interior s = closure s \ s)) (is_open.interior_eq hs)))
      (Eq.refl (closure s \ s)))

/-- The frontier of a set is closed. -/
theorem is_closed_frontier {α : Type u} [topological_space α] {s : set α} :
    is_closed (frontier s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_closed (frontier s))) frontier_eq_closure_inter_closure))
    (is_closed_inter is_closed_closure is_closed_closure)

/-- The frontier of a closed set has no interior point. -/
theorem interior_frontier {α : Type u} [topological_space α] {s : set α} (h : is_closed s) :
    interior (frontier s) = ∅ :=
  sorry

theorem closure_eq_interior_union_frontier {α : Type u} [topological_space α] (s : set α) :
    closure s = interior s ∪ frontier s :=
  Eq.symm (set.union_diff_cancel interior_subset_closure)

theorem closure_eq_self_union_frontier {α : Type u} [topological_space α] (s : set α) :
    closure s = s ∪ frontier s :=
  Eq.symm (set.union_diff_cancel' interior_subset subset_closure)

/-!
### Neighborhoods
-/

/-- A set is called a neighborhood of `a` if it contains an open set around `a`. The set of all
neighborhoods of `a` forms a filter, the neighborhood filter at `a`, is here defined as the
infimum over the principal filters of all open sets containing `a`. -/
def nhds {α : Type u} [topological_space α] (a : α) : filter α :=
  infi
    fun (s : set α) =>
      infi fun (H : s ∈ set_of fun (s : set α) => a ∈ s ∧ is_open s) => filter.principal s

theorem nhds_def {α : Type u} [topological_space α] (a : α) :
    nhds a =
        infi
          fun (s : set α) =>
            infi fun (H : s ∈ set_of fun (s : set α) => a ∈ s ∧ is_open s) => filter.principal s :=
  rfl

/-- The open sets containing `a` are a basis for the neighborhood filter. See `nhds_basis_opens'`
for a variant using open neighborhoods instead. -/
theorem nhds_basis_opens {α : Type u} [topological_space α] (a : α) :
    filter.has_basis (nhds a) (fun (s : set α) => a ∈ s ∧ is_open s) fun (x : set α) => x :=
  sorry

/-- A filter lies below the neighborhood filter at `a` iff it contains every open set around `a`. -/
theorem le_nhds_iff {α : Type u} [topological_space α] {f : filter α} {a : α} :
    f ≤ nhds a ↔ ∀ (s : set α), a ∈ s → is_open s → s ∈ f :=
  sorry

/-- To show a filter is above the neighborhood filter at `a`, it suffices to show that it is above
the principal filter of some open set `s` containing `a`. -/
theorem nhds_le_of_le {α : Type u} [topological_space α] {f : filter α} {a : α} {s : set α}
    (h : a ∈ s) (o : is_open s) (sf : filter.principal s ≤ f) : nhds a ≤ f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nhds a ≤ f)) (nhds_def a)))
    (infi_le_of_le s (infi_le_of_le { left := h, right := o } sf))

theorem mem_nhds_sets_iff {α : Type u} [topological_space α] {a : α} {s : set α} :
    s ∈ nhds a ↔ ∃ (t : set α), ∃ (H : t ⊆ s), is_open t ∧ a ∈ t :=
  sorry

/-- A predicate is true in a neighborhood of `a` iff it is true for all the points in an open set
containing `a`. -/
theorem eventually_nhds_iff {α : Type u} [topological_space α] {a : α} {p : α → Prop} :
    filter.eventually (fun (x : α) => p x) (nhds a) ↔
        ∃ (t : set α), (∀ (x : α), x ∈ t → p x) ∧ is_open t ∧ a ∈ t :=
  sorry

theorem map_nhds {α : Type u} {β : Type v} [topological_space α] {a : α} {f : α → β} :
    filter.map f (nhds a) =
        infi
          fun (s : set α) =>
            infi
              fun (H : s ∈ set_of fun (s : set α) => a ∈ s ∧ is_open s) =>
                filter.principal (f '' s) :=
  filter.has_basis.eq_binfi (filter.has_basis.map f (nhds_basis_opens a))

theorem mem_of_nhds {α : Type u} [topological_space α] {a : α} {s : set α} : s ∈ nhds a → a ∈ s :=
  sorry

/-- If a predicate is true in a neighborhood of `a`, then it is true for `a`. -/
theorem filter.eventually.self_of_nhds {α : Type u} [topological_space α] {p : α → Prop} {a : α}
    (h : filter.eventually (fun (y : α) => p y) (nhds a)) : p a :=
  mem_of_nhds h

theorem mem_nhds_sets {α : Type u} [topological_space α] {a : α} {s : set α} (hs : is_open s)
    (ha : a ∈ s) : s ∈ nhds a :=
  iff.mpr mem_nhds_sets_iff
    (Exists.intro s (Exists.intro (set.subset.refl s) { left := hs, right := ha }))

theorem is_open.eventually_mem {α : Type u} [topological_space α] {a : α} {s : set α}
    (hs : is_open s) (ha : a ∈ s) : filter.eventually (fun (x : α) => x ∈ s) (nhds a) :=
  mem_nhds_sets hs ha

/-- The open neighborhoods of `a` are a basis for the neighborhood filter. See `nhds_basis_opens`
for a variant using open sets around `a` instead. -/
theorem nhds_basis_opens' {α : Type u} [topological_space α] (a : α) :
    filter.has_basis (nhds a) (fun (s : set α) => s ∈ nhds a ∧ is_open s) fun (x : set α) => x :=
  sorry

/-- If a predicate is true in a neighbourhood of `a`, then for `y` sufficiently close
to `a` this predicate is true in a neighbourhood of `y`. -/
theorem filter.eventually.eventually_nhds {α : Type u} [topological_space α] {p : α → Prop} {a : α}
    (h : filter.eventually (fun (y : α) => p y) (nhds a)) :
    filter.eventually (fun (y : α) => filter.eventually (fun (y : α) => p y) (nhds y)) (nhds a) :=
  sorry

@[simp] theorem eventually_eventually_nhds {α : Type u} [topological_space α] {p : α → Prop}
    {a : α} :
    filter.eventually (fun (y : α) => filter.eventually (fun (x : α) => p x) (nhds y)) (nhds a) ↔
        filter.eventually (fun (x : α) => p x) (nhds a) :=
  sorry

@[simp] theorem nhds_bind_nhds {α : Type u} {a : α} [topological_space α] :
    filter.bind (nhds a) nhds = nhds a :=
  filter.ext fun (s : set α) => eventually_eventually_nhds

@[simp] theorem eventually_eventually_eq_nhds {α : Type u} {β : Type v} [topological_space α]
    {f : α → β} {g : α → β} {a : α} :
    filter.eventually (fun (y : α) => filter.eventually_eq (nhds y) f g) (nhds a) ↔
        filter.eventually_eq (nhds a) f g :=
  eventually_eventually_nhds

theorem filter.eventually_eq.eq_of_nhds {α : Type u} {β : Type v} [topological_space α] {f : α → β}
    {g : α → β} {a : α} (h : filter.eventually_eq (nhds a) f g) : f a = g a :=
  filter.eventually.self_of_nhds h

@[simp] theorem eventually_eventually_le_nhds {α : Type u} {β : Type v} [topological_space α]
    [HasLessEq β] {f : α → β} {g : α → β} {a : α} :
    filter.eventually (fun (y : α) => filter.eventually_le (nhds y) f g) (nhds a) ↔
        filter.eventually_le (nhds a) f g :=
  eventually_eventually_nhds

/-- If two functions are equal in a neighbourhood of `a`, then for `y` sufficiently close
to `a` these functions are equal in a neighbourhood of `y`. -/
theorem filter.eventually_eq.eventually_eq_nhds {α : Type u} {β : Type v} [topological_space α]
    {f : α → β} {g : α → β} {a : α} (h : filter.eventually_eq (nhds a) f g) :
    filter.eventually (fun (y : α) => filter.eventually_eq (nhds y) f g) (nhds a) :=
  filter.eventually.eventually_nhds h

/-- If `f x ≤ g x` in a neighbourhood of `a`, then for `y` sufficiently close to `a` we have
`f x ≤ g x` in a neighbourhood of `y`. -/
theorem filter.eventually_le.eventually_le_nhds {α : Type u} {β : Type v} [topological_space α]
    [HasLessEq β] {f : α → β} {g : α → β} {a : α} (h : filter.eventually_le (nhds a) f g) :
    filter.eventually (fun (y : α) => filter.eventually_le (nhds y) f g) (nhds a) :=
  filter.eventually.eventually_nhds h

theorem all_mem_nhds {α : Type u} [topological_space α] (x : α) (P : set α → Prop)
    (hP : ∀ (s t : set α), s ⊆ t → P s → P t) :
    (∀ (s : set α), s ∈ nhds x → P s) ↔ ∀ (s : set α), is_open s → x ∈ s → P s :=
  sorry

theorem all_mem_nhds_filter {α : Type u} {β : Type v} [topological_space α] (x : α)
    (f : set α → set β) (hf : ∀ (s t : set α), s ⊆ t → f s ⊆ f t) (l : filter β) :
    (∀ (s : set α), s ∈ nhds x → f s ∈ l) ↔ ∀ (s : set α), is_open s → x ∈ s → f s ∈ l :=
  all_mem_nhds x (fun (s : set α) => f s ∈ l)
    fun (s t : set α) (ssubt : s ⊆ t) (h : f s ∈ l) => filter.mem_sets_of_superset h (hf s t ssubt)

theorem rtendsto_nhds {α : Type u} {β : Type v} [topological_space α] {r : rel β α} {l : filter β}
    {a : α} : filter.rtendsto r l (nhds a) ↔ ∀ (s : set α), is_open s → a ∈ s → rel.core r s ∈ l :=
  all_mem_nhds_filter a (fun (U : set α) => U) (fun (s t : set α) => id) (filter.rmap r l)

theorem rtendsto'_nhds {α : Type u} {β : Type v} [topological_space α] {r : rel β α} {l : filter β}
    {a : α} :
    filter.rtendsto' r l (nhds a) ↔ ∀ (s : set α), is_open s → a ∈ s → rel.preimage r s ∈ l :=
  sorry

theorem ptendsto_nhds {α : Type u} {β : Type v} [topological_space α] {f : β →. α} {l : filter β}
    {a : α} : filter.ptendsto f l (nhds a) ↔ ∀ (s : set α), is_open s → a ∈ s → pfun.core f s ∈ l :=
  rtendsto_nhds

theorem ptendsto'_nhds {α : Type u} {β : Type v} [topological_space α] {f : β →. α} {l : filter β}
    {a : α} :
    filter.ptendsto' f l (nhds a) ↔ ∀ (s : set α), is_open s → a ∈ s → pfun.preimage f s ∈ l :=
  rtendsto'_nhds

theorem tendsto_nhds {α : Type u} {β : Type v} [topological_space α] {f : β → α} {l : filter β}
    {a : α} : filter.tendsto f l (nhds a) ↔ ∀ (s : set α), is_open s → a ∈ s → f ⁻¹' s ∈ l :=
  all_mem_nhds_filter a (fun (U : set α) => U)
    (fun (s t : set α) (h : s ⊆ t) => set.preimage_mono h) (filter.map f l)

theorem tendsto_const_nhds {α : Type u} {β : Type v} [topological_space α] {a : α} {f : filter β} :
    filter.tendsto (fun (b : β) => a) f (nhds a) :=
  iff.mpr tendsto_nhds
    fun (s : set α) (hs : is_open s) (ha : a ∈ s) => filter.univ_mem_sets' fun (_x : β) => ha

theorem pure_le_nhds {α : Type u} [topological_space α] : pure ≤ nhds :=
  fun (a : α) (s : set α) (hs : s ∈ nhds a) => iff.mpr filter.mem_pure_sets (mem_of_nhds hs)

theorem tendsto_pure_nhds {β : Type v} {α : Type u_1} [topological_space β] (f : α → β) (a : α) :
    filter.tendsto f (pure a) (nhds (f a)) :=
  filter.tendsto.mono_right (filter.tendsto_pure_pure f a) (pure_le_nhds (f a))

theorem order_top.tendsto_at_top_nhds {β : Type v} {α : Type u_1} [order_top α]
    [topological_space β] (f : α → β) : filter.tendsto f filter.at_top (nhds (f ⊤)) :=
  filter.tendsto.mono_right (filter.tendsto_at_top_pure f) (pure_le_nhds (f ⊤))

@[simp] protected instance nhds_ne_bot {α : Type u} [topological_space α] {a : α} :
    filter.ne_bot (nhds a) :=
  filter.ne_bot_of_le (pure_le_nhds a)

/-!
### Cluster points

In this section we define [cluster points](https://en.wikipedia.org/wiki/Limit_point)
(also known as limit points and accumulation points) of a filter and of a sequence.
-/

/-- A point `x` is a cluster point of a filter `F` if 𝓝 x ⊓ F ≠ ⊥. Also known as
an accumulation point or a limit point. -/
def cluster_pt {α : Type u} [topological_space α] (x : α) (F : filter α) :=
  filter.ne_bot (nhds x ⊓ F)

theorem cluster_pt.ne_bot {α : Type u} [topological_space α] {x : α} {F : filter α}
    (h : cluster_pt x F) : filter.ne_bot (nhds x ⊓ F) :=
  h

theorem cluster_pt_iff {α : Type u} [topological_space α] {x : α} {F : filter α} :
    cluster_pt x F ↔ ∀ {U : set α}, U ∈ nhds x → ∀ {V : set α}, V ∈ F → set.nonempty (U ∩ V) :=
  filter.inf_ne_bot_iff

/-- `x` is a cluster point of a set `s` if every neighbourhood of `x` meets `s` on a nonempty
set. -/
theorem cluster_pt_principal_iff {α : Type u} [topological_space α] {x : α} {s : set α} :
    cluster_pt x (filter.principal s) ↔ ∀ (U : set α), U ∈ nhds x → set.nonempty (U ∩ s) :=
  filter.inf_principal_ne_bot_iff

theorem cluster_pt_principal_iff_frequently {α : Type u} [topological_space α] {x : α} {s : set α} :
    cluster_pt x (filter.principal s) ↔ filter.frequently (fun (y : α) => y ∈ s) (nhds x) :=
  sorry

theorem cluster_pt.of_le_nhds {α : Type u} [topological_space α] {x : α} {f : filter α}
    (H : f ≤ nhds x) [filter.ne_bot f] : cluster_pt x f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (cluster_pt x f)) (cluster_pt.equations._eqn_1 x f)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (filter.ne_bot (nhds x ⊓ f))) (iff.mpr inf_eq_right H)))
      _inst_2)

theorem cluster_pt.of_le_nhds' {α : Type u} [topological_space α] {x : α} {f : filter α}
    (H : f ≤ nhds x) (hf : filter.ne_bot f) : cluster_pt x f :=
  cluster_pt.of_le_nhds H

theorem cluster_pt.of_nhds_le {α : Type u} [topological_space α] {x : α} {f : filter α}
    (H : nhds x ≤ f) : cluster_pt x f :=
  sorry

theorem cluster_pt.mono {α : Type u} [topological_space α] {x : α} {f : filter α} {g : filter α}
    (H : cluster_pt x f) (h : f ≤ g) : cluster_pt x g :=
  ne_bot_of_le_ne_bot H (inf_le_inf_left (nhds x) h)

theorem cluster_pt.of_inf_left {α : Type u} [topological_space α] {x : α} {f : filter α}
    {g : filter α} (H : cluster_pt x (f ⊓ g)) : cluster_pt x f :=
  cluster_pt.mono H inf_le_left

theorem cluster_pt.of_inf_right {α : Type u} [topological_space α] {x : α} {f : filter α}
    {g : filter α} (H : cluster_pt x (f ⊓ g)) : cluster_pt x g :=
  cluster_pt.mono H inf_le_right

theorem ultrafilter.cluster_pt_iff {α : Type u} [topological_space α] {x : α} {f : ultrafilter α} :
    cluster_pt x ↑f ↔ ↑f ≤ nhds x :=
  { mp := ultrafilter.le_of_inf_ne_bot' f, mpr := fun (h : ↑f ≤ nhds x) => cluster_pt.of_le_nhds h }

/-- A point `x` is a cluster point of a sequence `u` along a filter `F` if it is a cluster point
of `map u F`. -/
def map_cluster_pt {α : Type u} [topological_space α] {ι : Type u_1} (x : α) (F : filter ι)
    (u : ι → α) :=
  cluster_pt x (filter.map u F)

theorem map_cluster_pt_iff {α : Type u} [topological_space α] {ι : Type u_1} (x : α) (F : filter ι)
    (u : ι → α) :
    map_cluster_pt x F u ↔
        ∀ (s : set α), s ∈ nhds x → filter.frequently (fun (a : ι) => u a ∈ s) F :=
  sorry

theorem map_cluster_pt_of_comp {α : Type u} [topological_space α] {ι : Type u_1} {δ : Type u_2}
    {F : filter ι} {φ : δ → ι} {p : filter δ} {x : α} {u : ι → α} [filter.ne_bot p]
    (h : filter.tendsto φ p F) (H : filter.tendsto (u ∘ φ) p (nhds x)) : map_cluster_pt x F u :=
  filter.ne_bot_of_le (le_inf H (trans_rel_right LessEq filter.map_map (filter.map_mono h)))

/-!
### Interior, closure and frontier in terms of neighborhoods
-/

theorem interior_eq_nhds' {α : Type u} [topological_space α] {s : set α} :
    interior s = set_of fun (a : α) => s ∈ nhds a :=
  sorry

theorem interior_eq_nhds {α : Type u} [topological_space α] {s : set α} :
    interior s = set_of fun (a : α) => nhds a ≤ filter.principal s :=
  sorry

theorem mem_interior_iff_mem_nhds {α : Type u} [topological_space α] {s : set α} {a : α} :
    a ∈ interior s ↔ s ∈ nhds a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ interior s ↔ s ∈ nhds a)) interior_eq_nhds'))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl ((a ∈ set_of fun (a : α) => s ∈ nhds a) ↔ s ∈ nhds a))
          set.mem_set_of_eq))
      (iff.refl (s ∈ nhds a)))

theorem interior_set_of_eq {α : Type u} [topological_space α] {p : α → Prop} :
    interior (set_of fun (x : α) => p x) =
        set_of fun (x : α) => filter.eventually (fun (x : α) => p x) (nhds x) :=
  interior_eq_nhds'

theorem is_open_set_of_eventually_nhds {α : Type u} [topological_space α] {p : α → Prop} :
    is_open (set_of fun (x : α) => filter.eventually (fun (y : α) => p y) (nhds x)) :=
  sorry

theorem subset_interior_iff_nhds {α : Type u} [topological_space α] {s : set α} {V : set α} :
    s ⊆ interior V ↔ ∀ (x : α), x ∈ s → V ∈ nhds x :=
  sorry

theorem is_open_iff_nhds {α : Type u} [topological_space α] {s : set α} :
    is_open s ↔ ∀ (a : α), a ∈ s → nhds a ≤ filter.principal s :=
  iff.trans (iff.symm subset_interior_iff_open)
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (s ⊆ interior s ↔ ∀ (a : α), a ∈ s → nhds a ≤ filter.principal s))
          interior_eq_nhds))
      (iff.refl (s ⊆ set_of fun (a : α) => nhds a ≤ filter.principal s)))

theorem is_open_iff_mem_nhds {α : Type u} [topological_space α] {s : set α} :
    is_open s ↔ ∀ (a : α), a ∈ s → s ∈ nhds a :=
  iff.trans is_open_iff_nhds
    (forall_congr fun (_x : α) => imp_congr_right fun (_x_1 : _x ∈ s) => filter.le_principal_iff)

theorem is_open_iff_ultrafilter {α : Type u} [topological_space α] {s : set α} :
    is_open s ↔ ∀ (x : α), x ∈ s → ∀ (l : ultrafilter α), ↑l ≤ nhds x → s ∈ l :=
  sorry

theorem mem_closure_iff_frequently {α : Type u} [topological_space α] {s : set α} {a : α} :
    a ∈ closure s ↔ filter.frequently (fun (x : α) => x ∈ s) (nhds a) :=
  sorry

theorem filter.frequently.mem_closure {α : Type u} [topological_space α] {s : set α} {a : α} :
    filter.frequently (fun (x : α) => x ∈ s) (nhds a) → a ∈ closure s :=
  iff.mpr mem_closure_iff_frequently

/-- The set of cluster points of a filter is closed. In particular, the set of limit points
of a sequence is closed. -/
theorem is_closed_set_of_cluster_pt {α : Type u} [topological_space α] {f : filter α} :
    is_closed (set_of fun (x : α) => cluster_pt x f) :=
  sorry

theorem mem_closure_iff_cluster_pt {α : Type u} [topological_space α] {s : set α} {a : α} :
    a ∈ closure s ↔ cluster_pt a (filter.principal s) :=
  iff.trans mem_closure_iff_frequently (iff.symm cluster_pt_principal_iff_frequently)

theorem closure_eq_cluster_pts {α : Type u} [topological_space α] {s : set α} :
    closure s = set_of fun (a : α) => cluster_pt a (filter.principal s) :=
  set.ext fun (x : α) => mem_closure_iff_cluster_pt

theorem mem_closure_iff_nhds {α : Type u} [topological_space α] {s : set α} {a : α} :
    a ∈ closure s ↔ ∀ (t : set α), t ∈ nhds a → set.nonempty (t ∩ s) :=
  iff.trans mem_closure_iff_cluster_pt cluster_pt_principal_iff

theorem mem_closure_iff_nhds' {α : Type u} [topological_space α] {s : set α} {a : α} :
    a ∈ closure s ↔ ∀ (t : set α), t ∈ nhds a → ∃ (y : ↥s), ↑y ∈ t :=
  sorry

theorem mem_closure_iff_comap_ne_bot {α : Type u} [topological_space α] {A : set α} {x : α} :
    x ∈ closure A ↔ filter.ne_bot (filter.comap coe (nhds x)) :=
  sorry

theorem mem_closure_iff_nhds_basis {α : Type u} {β : Type v} [topological_space α] {a : α}
    {p : β → Prop} {s : β → set α} (h : filter.has_basis (nhds a) p s) {t : set α} :
    a ∈ closure t ↔ ∀ (i : β), p i → ∃ (y : α), ∃ (H : y ∈ t), y ∈ s i :=
  sorry

/-- `x` belongs to the closure of `s` if and only if some ultrafilter
  supported on `s` converges to `x`. -/
theorem mem_closure_iff_ultrafilter {α : Type u} [topological_space α] {s : set α} {x : α} :
    x ∈ closure s ↔ ∃ (u : ultrafilter α), s ∈ u ∧ ↑u ≤ nhds x :=
  sorry

theorem is_closed_iff_cluster_pt {α : Type u} [topological_space α] {s : set α} :
    is_closed s ↔ ∀ (a : α), cluster_pt a (filter.principal s) → a ∈ s :=
  sorry

theorem is_closed_iff_nhds {α : Type u} [topological_space α] {s : set α} :
    is_closed s ↔ ∀ (x : α), (∀ (U : set α), U ∈ nhds x → set.nonempty (U ∩ s)) → x ∈ s :=
  sorry

theorem closure_inter_open {α : Type u} [topological_space α] {s : set α} {t : set α}
    (h : is_open s) : s ∩ closure t ⊆ closure (s ∩ t) :=
  sorry

/-- The intersection of an open dense set with a dense set is a dense set. -/
theorem dense.inter_of_open_left {α : Type u} [topological_space α] {s : set α} {t : set α}
    (hs : dense s) (ht : dense t) (hso : is_open s) : dense (s ∩ t) :=
  sorry

/-- The intersection of a dense set with an open dense set is a dense set. -/
theorem dense.inter_of_open_right {α : Type u} [topological_space α] {s : set α} {t : set α}
    (hs : dense s) (ht : dense t) (hto : is_open t) : dense (s ∩ t) :=
  set.inter_comm t s ▸ dense.inter_of_open_left ht hs hto

theorem dense.inter_nhds_nonempty {α : Type u} [topological_space α] {s : set α} {t : set α}
    (hs : dense s) {x : α} (ht : t ∈ nhds x) : set.nonempty (s ∩ t) :=
  sorry

theorem closure_diff {α : Type u} [topological_space α] {s : set α} {t : set α} :
    closure s \ closure t ⊆ closure (s \ t) :=
  sorry

theorem filter.frequently.mem_of_closed {α : Type u} [topological_space α] {a : α} {s : set α}
    (h : filter.frequently (fun (x : α) => x ∈ s) (nhds a)) (hs : is_closed s) : a ∈ s :=
  is_closed.closure_subset hs (filter.frequently.mem_closure h)

theorem is_closed.mem_of_frequently_of_tendsto {α : Type u} {β : Type v} [topological_space α]
    {f : β → α} {b : filter β} {a : α} {s : set α} (hs : is_closed s)
    (h : filter.frequently (fun (x : β) => f x ∈ s) b) (hf : filter.tendsto f b (nhds a)) : a ∈ s :=
  sorry

theorem is_closed.mem_of_tendsto {α : Type u} {β : Type v} [topological_space α] {f : β → α}
    {b : filter β} {a : α} {s : set α} [filter.ne_bot b] (hs : is_closed s)
    (hf : filter.tendsto f b (nhds a)) (h : filter.eventually (fun (x : β) => f x ∈ s) b) : a ∈ s :=
  is_closed.mem_of_frequently_of_tendsto hs (filter.eventually.frequently h) hf

theorem mem_closure_of_tendsto {α : Type u} {β : Type v} [topological_space α] {f : β → α}
    {b : filter β} {a : α} {s : set α} [filter.ne_bot b] (hf : filter.tendsto f b (nhds a))
    (h : filter.eventually (fun (x : β) => f x ∈ s) b) : a ∈ closure s :=
  is_closed.mem_of_tendsto is_closed_closure hf
    (filter.eventually.mono h (set.preimage_mono subset_closure))

/-- Suppose that `f` sends the complement to `s` to a single point `a`, and `l` is some filter.
Then `f` tends to `a` along `l` restricted to `s` if and only if it tends to `a` along `l`. -/
theorem tendsto_inf_principal_nhds_iff_of_forall_eq {α : Type u} {β : Type v} [topological_space α]
    {f : β → α} {l : filter β} {s : set β} {a : α} (h : ∀ (x : β), ¬x ∈ s → f x = a) :
    filter.tendsto f (l ⊓ filter.principal s) (nhds a) ↔ filter.tendsto f l (nhds a) :=
  sorry

/-!
### Limits of filters in topological spaces
-/

/-- If `f` is a filter, then `Lim f` is a limit of the filter, if it exists. -/
def Lim {α : Type u} [topological_space α] [Nonempty α] (f : filter α) : α :=
  classical.epsilon fun (a : α) => f ≤ nhds a

/--
If `f` is a filter satisfying `ne_bot f`, then `Lim' f` is a limit of the filter, if it exists.
-/
def Lim' {α : Type u} [topological_space α] (f : filter α) [filter.ne_bot f] : α := Lim f

/--
If `F` is an ultrafilter, then `filter.ultrafilter.Lim F` is a limit of the filter, if it exists.
Note that dot notation `F.Lim` can be used for `F : ultrafilter α`.
-/
def ultrafilter.Lim {α : Type u} [topological_space α] : ultrafilter α → α :=
  fun (F : ultrafilter α) => Lim' ↑F

/-- If `f` is a filter in `β` and `g : β → α` is a function, then `lim f` is a limit of `g` at `f`,
if it exists. -/
def lim {α : Type u} {β : Type v} [topological_space α] [Nonempty α] (f : filter β) (g : β → α) :
    α :=
  Lim (filter.map g f)

/-- If a filter `f` is majorated by some `𝓝 a`, then it is majorated by `𝓝 (Lim f)`. We formulate
this lemma with a `[nonempty α]` argument of `Lim` derived from `h` to make it useful for types
without a `[nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
theorem le_nhds_Lim {α : Type u} [topological_space α] {f : filter α} (h : ∃ (a : α), f ≤ nhds a) :
    f ≤ nhds (Lim f) :=
  classical.epsilon_spec h

/-- If `g` tends to some `𝓝 a` along `f`, then it tends to `𝓝 (lim f g)`. We formulate
this lemma with a `[nonempty α]` argument of `lim` derived from `h` to make it useful for types
without a `[nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
theorem tendsto_nhds_lim {α : Type u} {β : Type v} [topological_space α] {f : filter β} {g : β → α}
    (h : ∃ (a : α), filter.tendsto g f (nhds a)) : filter.tendsto g f (nhds (lim f g)) :=
  le_nhds_Lim h

/-!
### Locally finite families
-/

/- locally finite family [General Topology (Bourbaki, 1995)] -/

/-- A family of sets in `set α` is locally finite if at every point `x:α`,
  there is a neighborhood of `x` which meets only finitely many sets in the family -/
def locally_finite {α : Type u} {β : Type v} [topological_space α] (f : β → set α) :=
  ∀ (x : α),
    ∃ (t : set α), ∃ (H : t ∈ nhds x), set.finite (set_of fun (i : β) => set.nonempty (f i ∩ t))

theorem locally_finite_of_finite {α : Type u} {β : Type v} [topological_space α] {f : β → set α}
    (h : set.finite set.univ) : locally_finite f :=
  sorry

theorem locally_finite_subset {α : Type u} {β : Type v} [topological_space α] {f₁ : β → set α}
    {f₂ : β → set α} (hf₂ : locally_finite f₂) (hf : ∀ (b : β), f₁ b ⊆ f₂ b) : locally_finite f₁ :=
  sorry

theorem is_closed_Union_of_locally_finite {α : Type u} {β : Type v} [topological_space α]
    {f : β → set α} (h₁ : locally_finite f) (h₂ : ∀ (i : β), is_closed (f i)) :
    is_closed (set.Union fun (i : β) => f i) :=
  sorry

/-!
### Continuity
-/

/-- A function between topological spaces is continuous if the preimage
  of every open set is open. Registered as a structure to make sure it is not unfolded by Lean. -/
structure continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (f : α → β)
    where
  is_open_preimage : ∀ (s : set β), is_open s → is_open (f ⁻¹' s)

theorem continuous_def {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {f : α → β} : continuous f ↔ ∀ (s : set β), is_open s → is_open (f ⁻¹' s) :=
  { mp :=
      fun (hf : continuous f) (s : set β) (hs : is_open s) => continuous.is_open_preimage hf s hs,
    mpr := fun (h : ∀ (s : set β), is_open s → is_open (f ⁻¹' s)) => continuous.mk h }

theorem is_open.preimage {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {f : α → β} (hf : continuous f) {s : set β} (h : is_open s) : is_open (f ⁻¹' s) :=
  continuous.is_open_preimage hf s h

/-- A function between topological spaces is continuous at a point `x₀`
if `f x` tends to `f x₀` when `x` tends to `x₀`. -/
def continuous_at {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (f : α → β) (x : α) :=
  filter.tendsto f (nhds x) (nhds (f x))

theorem continuous_at.tendsto {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α → β} {x : α} (h : continuous_at f x) :
    filter.tendsto f (nhds x) (nhds (f x)) :=
  h

theorem continuous_at.preimage_mem_nhds {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α → β} {x : α} {t : set β} (h : continuous_at f x)
    (ht : t ∈ nhds (f x)) : f ⁻¹' t ∈ nhds x :=
  h ht

theorem cluster_pt.map {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {x : α} {la : filter α} {lb : filter β} (H : cluster_pt x la) {f : α → β}
    (hfc : continuous_at f x) (hf : filter.tendsto f la lb) : cluster_pt (f x) lb :=
  ne_bot_of_le_ne_bot (iff.mpr (filter.map_ne_bot_iff f) H)
    (filter.tendsto.inf (continuous_at.tendsto hfc) hf)

theorem preimage_interior_subset_interior_preimage {α : Type u_1} {β : Type u_2}
    [topological_space α] [topological_space β] {f : α → β} {s : set β} (hf : continuous f) :
    f ⁻¹' interior s ⊆ interior (f ⁻¹' s) :=
  interior_maximal (set.preimage_mono interior_subset) (is_open.preimage hf is_open_interior)

theorem continuous_id {α : Type u_1} [topological_space α] : continuous id :=
  iff.mpr continuous_def fun (s : set α) (h : is_open s) => h

theorem continuous.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} (hg : continuous g)
    (hf : continuous f) : continuous (g ∘ f) :=
  iff.mpr continuous_def
    fun (s : set γ) (h : is_open s) => is_open.preimage hf (is_open.preimage hg h)

theorem continuous.iterate {α : Type u_1} [topological_space α] {f : α → α} (h : continuous f)
    (n : ℕ) : continuous (nat.iterate f n) :=
  nat.rec_on n continuous_id
    fun (n : ℕ) (ihn : continuous (nat.iterate f n)) => continuous.comp ihn h

theorem continuous_at.comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] {g : β → γ} {f : α → β} {x : α}
    (hg : continuous_at g (f x)) (hf : continuous_at f x) : continuous_at (g ∘ f) x :=
  filter.tendsto.comp hg hf

theorem continuous.tendsto {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {f : α → β} (hf : continuous f) (x : α) : filter.tendsto f (nhds x) (nhds (f x)) :=
  sorry

/-- A version of `continuous.tendsto` that allows one to specify a simpler form of the limit.
E.g., one can write `continuous_exp.tendsto' 0 1 exp_zero`. -/
theorem continuous.tendsto' {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α → β} (hf : continuous f) (x : α) (y : β) (h : f x = y) :
    filter.tendsto f (nhds x) (nhds y) :=
  h ▸ continuous.tendsto hf x

theorem continuous.continuous_at {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α → β} {x : α} (h : continuous f) : continuous_at f x :=
  continuous.tendsto h x

theorem continuous_iff_continuous_at {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α → β} : continuous f ↔ ∀ (x : α), continuous_at f x :=
  sorry

theorem continuous_at_const {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {x : α} {b : β} : continuous_at (fun (a : α) => b) x :=
  tendsto_const_nhds

theorem continuous_const {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {b : β} : continuous fun (a : α) => b :=
  iff.mpr continuous_iff_continuous_at fun (a : α) => continuous_at_const

theorem continuous_at_id {α : Type u_1} [topological_space α] {x : α} : continuous_at id x :=
  continuous.continuous_at continuous_id

theorem continuous_at.iterate {α : Type u_1} [topological_space α] {f : α → α} {x : α}
    (hf : continuous_at f x) (hx : f x = x) (n : ℕ) : continuous_at (nat.iterate f n) x :=
  nat.rec_on n continuous_at_id
    fun (n : ℕ) (ihn : continuous_at (nat.iterate f n) x) =>
      (fun (this : continuous_at (nat.iterate f n ∘ f) x) => this)
        (continuous_at.comp (Eq.symm hx ▸ ihn) hf)

theorem continuous_iff_is_closed {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α → β} :
    continuous f ↔ ∀ (s : set β), is_closed s → is_closed (f ⁻¹' s) :=
  sorry

theorem is_closed.preimage {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {f : α → β} (hf : continuous f) {s : set β} (h : is_closed s) : is_closed (f ⁻¹' s) :=
  iff.mp continuous_iff_is_closed hf s h

theorem continuous_at_iff_ultrafilter {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α → β} {x : α} :
    continuous_at f x ↔ ∀ (g : ultrafilter α), ↑g ≤ nhds x → filter.tendsto f (↑g) (nhds (f x)) :=
  filter.tendsto_iff_ultrafilter f (nhds x) (nhds (f x))

theorem continuous_iff_ultrafilter {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α → β} :
    continuous f ↔
        ∀ (x : α) (g : ultrafilter α), ↑g ≤ nhds x → filter.tendsto f (↑g) (nhds (f x)) :=
  sorry

/-- A piecewise defined function `if p then f else g` is continuous, if both `f` and `g`
are continuous, and they coincide on the frontier (boundary) of the set `{a | p a}`. -/
theorem continuous_if {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {p : α → Prop} {f : α → β} {g : α → β} {h : (a : α) → Decidable (p a)}
    (hp : ∀ (a : α), a ∈ frontier (set_of fun (a : α) => p a) → f a = g a) (hf : continuous f)
    (hg : continuous g) : continuous fun (a : α) => ite (p a) (f a) (g a) :=
  sorry

/-! ### Continuity and partial functions -/

/-- Continuity of a partial function -/
def pcontinuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (f : α →. β) :=
  ∀ (s : set β), is_open s → is_open (pfun.preimage f s)

theorem open_dom_of_pcontinuous {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α →. β} (h : pcontinuous f) : is_open (pfun.dom f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_open (pfun.dom f))) (Eq.symm (pfun.preimage_univ f))))
    (h set.univ is_open_univ)

theorem pcontinuous_iff' {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {f : α →. β} :
    pcontinuous f ↔ ∀ {x : α} {y : β}, y ∈ f x → filter.ptendsto' f (nhds x) (nhds y) :=
  sorry

/-- If a continuous map `f` maps `s` to `t`, then it maps `closure s` to `closure t`. -/
theorem set.maps_to.closure {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {s : set α} {t : set β} {f : α → β} (h : set.maps_to f s t)
    (hc : continuous f) : set.maps_to f (closure s) (closure t) :=
  sorry

theorem image_closure_subset_closure_image {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α → β} {s : set α} (h : continuous f) :
    f '' closure s ⊆ closure (f '' s) :=
  set.maps_to.image_subset (set.maps_to.closure (set.maps_to_image f s) h)

theorem map_mem_closure {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    {s : set α} {t : set β} {f : α → β} {a : α} (hf : continuous f) (ha : a ∈ closure s)
    (ht : ∀ (a : α), a ∈ s → f a ∈ t) : f a ∈ closure t :=
  set.maps_to.closure ht hf ha

/-!
### Function with dense range
-/

/-- `f : ι → β` has dense range if its range (image) is a dense subset of β. -/
def dense_range {β : Type u_2} [topological_space β] {κ : Type u_5} (f : κ → β) :=
  dense (set.range f)

/-- A surjective map has dense range. -/
theorem function.surjective.dense_range {β : Type u_2} [topological_space β] {κ : Type u_5}
    {f : κ → β} (hf : function.surjective f) : dense_range f :=
  sorry

theorem dense_range_iff_closure_range {β : Type u_2} [topological_space β] {κ : Type u_5}
    {f : κ → β} : dense_range f ↔ closure (set.range f) = set.univ :=
  dense_iff_closure_eq

theorem dense_range.closure_range {β : Type u_2} [topological_space β] {κ : Type u_5} {f : κ → β}
    (h : dense_range f) : closure (set.range f) = set.univ :=
  dense.closure_eq h

theorem continuous.range_subset_closure_image_dense {α : Type u_1} {β : Type u_2}
    [topological_space α] [topological_space β] {f : α → β} (hf : continuous f) {s : set α}
    (hs : dense s) : set.range f ⊆ closure (f '' s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (set.range f ⊆ closure (f '' s))) (Eq.symm set.image_univ)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (f '' set.univ ⊆ closure (f '' s))) (Eq.symm (dense.closure_eq hs))))
      (image_closure_subset_closure_image hf))

/-- The image of a dense set under a continuous map with dense range is a dense set. -/
theorem dense_range.dense_image {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α → β} (hf' : dense_range f) (hf : continuous f) {s : set α}
    (hs : dense s) : dense (f '' s) :=
  dense.of_closure (dense.mono (continuous.range_subset_closure_image_dense hf hs) hf')

/-- If a continuous map with dense range maps a dense set to a subset of `t`, then `t` is a dense
set. -/
theorem dense_range.dense_of_maps_to {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {f : α → β} (hf' : dense_range f) (hf : continuous f) {s : set α}
    (hs : dense s) {t : set β} (ht : set.maps_to f s t) : dense t :=
  dense.mono (set.maps_to.image_subset ht) (dense_range.dense_image hf' hf hs)

/-- Composition of a continuous map with dense range and a function with dense range has dense
range. -/
theorem dense_range.comp {β : Type u_2} {γ : Type u_3} [topological_space β] [topological_space γ]
    {κ : Type u_5} {g : β → γ} {f : κ → β} (hg : dense_range g) (hf : dense_range f)
    (cg : continuous g) : dense_range (g ∘ f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dense_range (g ∘ f))) (dense_range.equations._eqn_1 (g ∘ f))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (dense (set.range (g ∘ f)))) (set.range_comp g f)))
      (dense_range.dense_image hg cg hf))

theorem dense_range.nonempty_iff {β : Type u_2} [topological_space β] {κ : Type u_5} {f : κ → β}
    (hf : dense_range f) : Nonempty κ ↔ Nonempty β :=
  iff.trans (iff.symm set.range_nonempty_iff_nonempty) (dense.nonempty_iff hf)

theorem dense_range.nonempty {β : Type u_2} [topological_space β] {κ : Type u_5} {f : κ → β}
    [h : Nonempty β] (hf : dense_range f) : Nonempty κ :=
  iff.mpr (dense_range.nonempty_iff hf) h

/-- Given a function `f : α → β` with dense range and `b : β`, returns some `a : α`. -/
def dense_range.some {β : Type u_2} [topological_space β] {κ : Type u_5} {f : κ → β}
    (hf : dense_range f) (b : β) : κ :=
  Classical.choice sorry

end Mathlib