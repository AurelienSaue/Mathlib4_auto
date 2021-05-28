/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.tactic
import Mathlib.PostPort

universes u u_1 l v u_2 w u_3 

namespace Mathlib

/-!
# Ordering on topologies and (co)induced topologies

Topologies on a fixed type `α` are ordered, by reverse inclusion.
That is, for topologies `t₁` and `t₂` on `α`, we write `t₁ ≤ t₂`
if every set open in `t₂` is also open in `t₁`.
(One also calls `t₁` finer than `t₂`, and `t₂` coarser than `t₁`.)

Any function `f : α → β` induces
       `induced f : topological_space β → topological_space α`
and  `coinduced f : topological_space α → topological_space β`.
Continuity, the ordering on topologies and (co)induced topologies are
related as follows:
* The identity map (α, t₁) → (α, t₂) is continuous iff t₁ ≤ t₂.
* A map f : (α, t) → (β, u) is continuous
    iff             t ≤ induced f u   (`continuous_iff_le_induced`)
    iff coinduced f t ≤ u             (`continuous_iff_coinduced_le`).

Topologies on α form a complete lattice, with ⊥ the discrete topology
and ⊤ the indiscrete topology.

For a function f : α → β, (coinduced f, induced f) is a Galois connection
between topologies on α and topologies on β.

## Implementation notes

There is a Galois insertion between topologies on α (with the inclusion ordering)
and all collections of sets in α. The complete lattice structure on topologies
on α is defined as the reverse of the one obtained via this Galois insertion.

## Tags

finer, coarser, induced topology, coinduced topology

-/

namespace topological_space


/-- The open sets of the least topology containing a collection of basic sets. -/
inductive generate_open {α : Type u} (g : set (set α)) : set α → Prop
where
| basic : ∀ (s : set α), s ∈ g → generate_open g s
| univ : generate_open g set.univ
| inter : ∀ (s t : set α), generate_open g s → generate_open g t → generate_open g (s ∩ t)
| sUnion : ∀ (k : set (set α)), (∀ (s : set α), s ∈ k → generate_open g s) → generate_open g (⋃₀k)

/-- The smallest topological space containing the collection `g` of basic sets -/
def generate_from {α : Type u} (g : set (set α)) : topological_space α :=
  mk (generate_open g) generate_open.univ generate_open.inter generate_open.sUnion

theorem nhds_generate_from {α : Type u} {g : set (set α)} {a : α} : nhds a = infi fun (s : set α) => infi fun (H : s ∈ set_of fun (s : set α) => a ∈ s ∧ s ∈ g) => filter.principal s := sorry

theorem tendsto_nhds_generate_from {α : Type u} {β : Type u_1} {m : α → β} {f : filter α} {g : set (set β)} {b : β} (h : ∀ (s : set β), s ∈ g → b ∈ s → m ⁻¹' s ∈ f) : filter.tendsto m f (nhds b) := sorry

/-- Construct a topology on α given the filter of neighborhoods of each point of α. -/
protected def mk_of_nhds {α : Type u} (n : α → filter α) : topological_space α :=
  mk (fun (s : set α) => ∀ (a : α), a ∈ s → s ∈ n a) sorry sorry sorry

theorem nhds_mk_of_nhds {α : Type u} (n : α → filter α) (a : α) (h₀ : pure ≤ n) (h₁ : ∀ {a : α} {s : set α}, s ∈ n a → ∃ (t : set α), ∃ (H : t ∈ n a), t ⊆ s ∧ ∀ (a' : α), a' ∈ t → s ∈ n a') : nhds a = n a := sorry

end topological_space


/-- The inclusion ordering on topologies on α. We use it to get a complete
   lattice instance via the Galois insertion method, but the partial order
   that we will eventually impose on `topological_space α` is the reverse one. -/
def tmp_order {α : Type u} : partial_order (topological_space α) :=
  partial_order.mk (fun (t s : topological_space α) => topological_space.is_open t ≤ topological_space.is_open s)
    (preorder.lt._default fun (t s : topological_space α) => topological_space.is_open t ≤ topological_space.is_open s)
    sorry sorry sorry

/- We'll later restate this lemma in terms of the correct order on `topological_space α`. -/

/-- If `s` equals the collection of open sets in the topology it generates,
  then `s` defines a topology. -/
protected def mk_of_closure {α : Type u} (s : set (set α)) (hs : (set_of fun (u : set α) => topological_space.is_open (topological_space.generate_from s) u) = s) : topological_space α :=
  topological_space.mk (fun (u : set α) => u ∈ s) sorry sorry sorry

theorem mk_of_closure_sets {α : Type u} {s : set (set α)} {hs : (set_of fun (u : set α) => topological_space.is_open (topological_space.generate_from s) u) = s} : Mathlib.mk_of_closure s hs = topological_space.generate_from s :=
  topological_space_eq (Eq.symm hs)

/-- The Galois insertion between `set (set α)` and `topological_space α` whose lower part
  sends a collection of subsets of α to the topology they generate, and whose upper part
  sends a topology to its collection of open subsets. -/
def gi_generate_from (α : Type u_1) : galois_insertion topological_space.generate_from
  fun (t : topological_space α) => set_of fun (s : set α) => topological_space.is_open t s :=
  galois_insertion.mk
    (fun (g : set (set α))
      (hg : (set_of fun (s : set α) => topological_space.is_open (topological_space.generate_from g) s) ≤ g) =>
      Mathlib.mk_of_closure g sorry)
    sorry sorry sorry

theorem generate_from_mono {α : Type u_1} {g₁ : set (set α)} {g₂ : set (set α)} (h : g₁ ⊆ g₂) : topological_space.generate_from g₁ ≤ topological_space.generate_from g₂ :=
  galois_connection.monotone_l (galois_insertion.gc (gi_generate_from α)) h

/-- The complete lattice of topological spaces, but built on the inclusion ordering. -/
def tmp_complete_lattice {α : Type u} : complete_lattice (topological_space α) :=
  galois_insertion.lift_complete_lattice (gi_generate_from α)

/-- The ordering on topologies on the type `α`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
protected instance topological_space.partial_order {α : Type u} : partial_order (topological_space α) :=
  partial_order.mk (fun (t s : topological_space α) => topological_space.is_open s ≤ topological_space.is_open t)
    (preorder.lt._default fun (t s : topological_space α) => topological_space.is_open s ≤ topological_space.is_open t)
    sorry sorry sorry

theorem le_generate_from_iff_subset_is_open {α : Type u} {g : set (set α)} {t : topological_space α} : t ≤ topological_space.generate_from g ↔ g ⊆ set_of fun (s : set α) => topological_space.is_open t s :=
  generate_from_le_iff_subset_is_open

/-- Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremem is the
  topology whose open sets are those sets open in every member of the collection. -/
protected instance topological_space.complete_lattice {α : Type u} : complete_lattice (topological_space α) :=
  order_dual.complete_lattice (topological_space α)

/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class discrete_topology (α : Type u_1) [t : topological_space α] 
where
  eq_bot : t = ⊥

@[simp] theorem is_open_discrete {α : Type u} [topological_space α] [discrete_topology α] (s : set α) : is_open s :=
  Eq.symm (discrete_topology.eq_bot α) ▸ trivial

@[simp] theorem is_closed_discrete {α : Type u} [topological_space α] [discrete_topology α] (s : set α) : is_closed s :=
  Eq.symm (discrete_topology.eq_bot α) ▸ trivial

theorem continuous_of_discrete_topology {α : Type u} {β : Type v} [topological_space α] [discrete_topology α] [topological_space β] {f : α → β} : continuous f :=
  iff.mpr continuous_def fun (s : set β) (hs : is_open s) => is_open_discrete (f ⁻¹' s)

theorem nhds_bot (α : Type u_1) : nhds = pure :=
  le_antisymm (id fun (a : α) => id fun (s : set α) (hs : s ∈ pure a) => mem_nhds_sets trivial hs) pure_le_nhds

theorem nhds_discrete (α : Type u_1) [topological_space α] [discrete_topology α] : nhds = pure :=
  Eq.symm (discrete_topology.eq_bot α) ▸ nhds_bot α

theorem le_of_nhds_le_nhds {α : Type u} {t₁ : topological_space α} {t₂ : topological_space α} (h : ∀ (x : α), nhds x ≤ nhds x) : t₁ ≤ t₂ := sorry

theorem eq_of_nhds_eq_nhds {α : Type u} {t₁ : topological_space α} {t₂ : topological_space α} (h : ∀ (x : α), nhds x = nhds x) : t₁ = t₂ :=
  le_antisymm (le_of_nhds_le_nhds fun (x : α) => le_of_eq (h x))
    (le_of_nhds_le_nhds fun (x : α) => le_of_eq (Eq.symm (h x)))

theorem eq_bot_of_singletons_open {α : Type u} {t : topological_space α} (h : ∀ (x : α), topological_space.is_open t (singleton x)) : t = ⊥ :=
  bot_unique
    fun (s : set α) (hs : topological_space.is_open ⊥ s) =>
      set.bUnion_of_singleton s ▸ is_open_bUnion fun (x : α) (_x : x ∈ s) => h x

theorem forall_open_iff_discrete {X : Type u_1} [topological_space X] : (∀ (s : set X), is_open s) ↔ discrete_topology X := sorry

theorem singletons_open_iff_discrete {X : Type u_1} [topological_space X] : (∀ (a : X), is_open (singleton a)) ↔ discrete_topology X :=
  { mp := fun (h : ∀ (a : X), is_open (singleton a)) => discrete_topology.mk (eq_bot_of_singletons_open h),
    mpr := fun (a : discrete_topology X) (_x : X) => is_open_discrete (singleton _x) }

/-- Given `f : α → β` and a topology on `β`, the induced topology on `α` is the collection of
  sets that are preimages of some open set in `β`. This is the coarsest topology that
  makes `f` continuous. -/
def topological_space.induced {α : Type u} {β : Type v} (f : α → β) (t : topological_space β) : topological_space α :=
  topological_space.mk (fun (s : set α) => ∃ (s' : set β), topological_space.is_open t s' ∧ f ⁻¹' s' = s) sorry sorry
    sorry

theorem is_open_induced_iff {α : Type u_1} {β : Type u_2} [t : topological_space β] {s : set α} {f : α → β} : is_open s ↔ ∃ (t_1 : set β), is_open t_1 ∧ f ⁻¹' t_1 = s :=
  iff.rfl

theorem is_closed_induced_iff {α : Type u_1} {β : Type u_2} [t : topological_space β] {s : set α} {f : α → β} : is_closed s ↔ ∃ (t_1 : set β), is_closed t_1 ∧ s = f ⁻¹' t_1 := sorry

/-- Given `f : α → β` and a topology on `α`, the coinduced topology on `β` is defined
  such that `s:set β` is open if the preimage of `s` is open. This is the finest topology that
  makes `f` continuous. -/
def topological_space.coinduced {α : Type u} {β : Type v} (f : α → β) (t : topological_space α) : topological_space β :=
  topological_space.mk (fun (s : set β) => topological_space.is_open t (f ⁻¹' s)) sorry sorry sorry

theorem is_open_coinduced {α : Type u_1} {β : Type u_2} {t : topological_space α} {s : set β} {f : α → β} : is_open s ↔ is_open (f ⁻¹' s) :=
  iff.rfl

theorem continuous.coinduced_le {α : Type u_1} {β : Type u_2} {t : topological_space α} {t' : topological_space β} {f : α → β} (h : continuous f) : topological_space.coinduced f t ≤ t' :=
  fun (s : set β) (hs : topological_space.is_open t' s) => iff.mp continuous_def h s hs

theorem coinduced_le_iff_le_induced {α : Type u_1} {β : Type u_2} {f : α → β} {tα : topological_space α} {tβ : topological_space β} : topological_space.coinduced f tα ≤ tβ ↔ tα ≤ topological_space.induced f tβ := sorry

theorem continuous.le_induced {α : Type u_1} {β : Type u_2} {t : topological_space α} {t' : topological_space β} {f : α → β} (h : continuous f) : t ≤ topological_space.induced f t' :=
  iff.mp coinduced_le_iff_le_induced (continuous.coinduced_le h)

theorem gc_coinduced_induced {α : Type u_1} {β : Type u_2} (f : α → β) : galois_connection (topological_space.coinduced f) (topological_space.induced f) :=
  fun (f_1 : topological_space α) (g : topological_space β) => coinduced_le_iff_le_induced

theorem induced_mono {α : Type u_1} {β : Type u_2} {t₁ : topological_space α} {t₂ : topological_space α} {g : β → α} (h : t₁ ≤ t₂) : topological_space.induced g t₁ ≤ topological_space.induced g t₂ :=
  galois_connection.monotone_u (gc_coinduced_induced g) h

theorem coinduced_mono {α : Type u_1} {β : Type u_2} {t₁ : topological_space α} {t₂ : topological_space α} {f : α → β} (h : t₁ ≤ t₂) : topological_space.coinduced f t₁ ≤ topological_space.coinduced f t₂ :=
  galois_connection.monotone_l (gc_coinduced_induced f) h

@[simp] theorem induced_top {α : Type u_1} {β : Type u_2} {g : β → α} : topological_space.induced g ⊤ = ⊤ :=
  galois_connection.u_top (gc_coinduced_induced g)

@[simp] theorem induced_inf {α : Type u_1} {β : Type u_2} {t₁ : topological_space α} {t₂ : topological_space α} {g : β → α} : topological_space.induced g (t₁ ⊓ t₂) = topological_space.induced g t₁ ⊓ topological_space.induced g t₂ :=
  galois_connection.u_inf (gc_coinduced_induced g)

@[simp] theorem induced_infi {α : Type u_1} {β : Type u_2} {g : β → α} {ι : Sort w} {t : ι → topological_space α} : topological_space.induced g (infi fun (i : ι) => t i) = infi fun (i : ι) => topological_space.induced g (t i) :=
  galois_connection.u_infi (gc_coinduced_induced g)

@[simp] theorem coinduced_bot {α : Type u_1} {β : Type u_2} {f : α → β} : topological_space.coinduced f ⊥ = ⊥ :=
  galois_connection.l_bot (gc_coinduced_induced f)

@[simp] theorem coinduced_sup {α : Type u_1} {β : Type u_2} {t₁ : topological_space α} {t₂ : topological_space α} {f : α → β} : topological_space.coinduced f (t₁ ⊔ t₂) = topological_space.coinduced f t₁ ⊔ topological_space.coinduced f t₂ :=
  galois_connection.l_sup (gc_coinduced_induced f)

@[simp] theorem coinduced_supr {α : Type u_1} {β : Type u_2} {f : α → β} {ι : Sort w} {t : ι → topological_space α} : topological_space.coinduced f (supr fun (i : ι) => t i) = supr fun (i : ι) => topological_space.coinduced f (t i) :=
  galois_connection.l_supr (gc_coinduced_induced f)

theorem induced_id {α : Type u_1} [t : topological_space α] : topological_space.induced id t = t := sorry

theorem induced_compose {α : Type u_1} {β : Type u_2} {γ : Type u_3} [tγ : topological_space γ] {f : α → β} {g : β → γ} : topological_space.induced f (topological_space.induced g tγ) = topological_space.induced (g ∘ f) tγ := sorry

theorem coinduced_id {α : Type u_1} [t : topological_space α] : topological_space.coinduced id t = t :=
  topological_space_eq rfl

theorem coinduced_compose {α : Type u_1} {β : Type u_2} {γ : Type u_3} [tα : topological_space α] {f : α → β} {g : β → γ} : topological_space.coinduced g (topological_space.coinduced f tα) = topological_space.coinduced (g ∘ f) tα :=
  topological_space_eq rfl

/- constructions using the complete lattice structure -/

protected instance inhabited_topological_space {α : Type u} : Inhabited (topological_space α) :=
  { default := ⊤ }

protected instance subsingleton.unique_topological_space {α : Type u} [subsingleton α] : unique (topological_space α) :=
  unique.mk { default := ⊥ } sorry

protected instance subsingleton.discrete_topology {α : Type u} [t : topological_space α] [subsingleton α] : discrete_topology α :=
  discrete_topology.mk (unique.eq_default t)

protected instance empty.topological_space : topological_space empty :=
  ⊥

protected instance empty.discrete_topology : discrete_topology empty :=
  discrete_topology.mk rfl

protected instance pempty.topological_space : topological_space pempty :=
  ⊥

protected instance pempty.discrete_topology : discrete_topology pempty :=
  discrete_topology.mk rfl

protected instance unit.topological_space : topological_space Unit :=
  ⊥

protected instance unit.discrete_topology : discrete_topology Unit :=
  discrete_topology.mk rfl

protected instance bool.topological_space : topological_space Bool :=
  ⊥

protected instance bool.discrete_topology : discrete_topology Bool :=
  discrete_topology.mk rfl

protected instance nat.topological_space : topological_space ℕ :=
  ⊥

protected instance nat.discrete_topology : discrete_topology ℕ :=
  discrete_topology.mk rfl

protected instance int.topological_space : topological_space ℤ :=
  ⊥

protected instance int.discrete_topology : discrete_topology ℤ :=
  discrete_topology.mk rfl

protected instance sierpinski_space : topological_space Prop :=
  topological_space.generate_from (singleton (singleton True))

theorem le_generate_from {α : Type u} {t : topological_space α} {g : set (set α)} (h : ∀ (s : set α), s ∈ g → is_open s) : t ≤ topological_space.generate_from g :=
  iff.mpr le_generate_from_iff_subset_is_open h

theorem induced_generate_from_eq {α : Type u_1} {β : Type u_2} {b : set (set β)} {f : α → β} : topological_space.induced f (topological_space.generate_from b) = topological_space.generate_from (set.preimage f '' b) := sorry

/-- This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`. -/
protected def topological_space.nhds_adjoint {α : Type u} (a : α) (f : filter α) : topological_space α :=
  topological_space.mk (fun (s : set α) => a ∈ s → s ∈ f) sorry sorry sorry

theorem gc_nhds {α : Type u} (a : α) : galois_connection (topological_space.nhds_adjoint a) fun (t : topological_space α) => nhds a := sorry

theorem nhds_mono {α : Type u} {t₁ : topological_space α} {t₂ : topological_space α} {a : α} (h : t₁ ≤ t₂) : nhds a ≤ nhds a :=
  galois_connection.monotone_u (gc_nhds a) h

theorem nhds_infi {α : Type u} {ι : Sort u_1} {t : ι → topological_space α} {a : α} : nhds a = infi fun (i : ι) => nhds a :=
  galois_connection.u_infi (gc_nhds a)

theorem nhds_Inf {α : Type u} {s : set (topological_space α)} {a : α} : nhds a = infi fun (t : topological_space α) => infi fun (H : t ∈ s) => nhds a :=
  galois_connection.u_Inf (gc_nhds a)

theorem nhds_inf {α : Type u} {t₁ : topological_space α} {t₂ : topological_space α} {a : α} : nhds a = nhds a ⊓ nhds a :=
  galois_connection.u_inf (gc_nhds a)

theorem nhds_top {α : Type u} {a : α} : nhds a = ⊤ :=
  galois_connection.u_top (gc_nhds a)

theorem continuous_iff_coinduced_le {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₂ : topological_space β} : continuous f ↔ topological_space.coinduced f t₁ ≤ t₂ :=
  iff.trans continuous_def iff.rfl

theorem continuous_iff_le_induced {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₂ : topological_space β} : continuous f ↔ t₁ ≤ topological_space.induced f t₂ :=
  iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f t₁ t₂)

theorem continuous_generated_from {α : Type u} {β : Type v} {f : α → β} {t : topological_space α} {b : set (set β)} (h : ∀ (s : set β), s ∈ b → is_open (f ⁻¹' s)) : continuous f :=
  iff.mpr continuous_iff_coinduced_le (le_generate_from h)

theorem continuous_induced_dom {α : Type u} {β : Type v} {f : α → β} {t : topological_space β} : continuous f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (continuous f)) (propext continuous_def)))
    fun (s : set β) (h : is_open s) => Exists.intro s { left := h, right := rfl }

theorem continuous_induced_rng {α : Type u} {β : Type v} {γ : Type u_1} {f : α → β} {g : γ → α} {t₂ : topological_space β} {t₁ : topological_space γ} (h : continuous (f ∘ g)) : continuous g := sorry

theorem continuous_induced_rng' {α : Type u} {β : Type v} {γ : Type u_1} [topological_space α] [topological_space β] [topological_space γ] {g : γ → α} (f : α → β) (H : _inst_1 = topological_space.induced f _inst_2) (h : continuous (f ∘ g)) : continuous g :=
  Eq.symm H ▸ continuous_induced_rng h

theorem continuous_coinduced_rng {α : Type u} {β : Type v} {f : α → β} {t : topological_space α} : continuous f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (continuous f)) (propext continuous_def))) fun (s : set β) (h : is_open s) => h

theorem continuous_coinduced_dom {α : Type u} {β : Type v} {γ : Type u_1} {f : α → β} {g : β → γ} {t₁ : topological_space α} {t₂ : topological_space γ} (h : continuous (g ∘ f)) : continuous g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (continuous g)) (propext continuous_def)))
    fun (s : set γ) (hs : is_open s) => eq.mp (Eq._oldrec (Eq.refl (continuous (g ∘ f))) (propext continuous_def)) h s hs

theorem continuous_le_dom {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₂ : topological_space α} {t₃ : topological_space β} (h₁ : t₂ ≤ t₁) (h₂ : continuous f) : continuous f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (continuous f)) (propext continuous_def)))
    fun (s : set β) (h : is_open s) =>
      h₁ (f ⁻¹' s) (eq.mp (Eq._oldrec (Eq.refl (continuous f)) (propext continuous_def)) h₂ s h)

theorem continuous_le_rng {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₂ : topological_space β} {t₃ : topological_space β} (h₁ : t₂ ≤ t₃) (h₂ : continuous f) : continuous f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (continuous f)) (propext continuous_def)))
    fun (s : set β) (h : is_open s) => eq.mp (Eq._oldrec (Eq.refl (continuous f)) (propext continuous_def)) h₂ s (h₁ s h)

theorem continuous_sup_dom {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₂ : topological_space α} {t₃ : topological_space β} (h₁ : continuous f) (h₂ : continuous f) : continuous f := sorry

theorem continuous_sup_rng_left {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₃ : topological_space β} {t₂ : topological_space β} : continuous f → continuous f :=
  continuous_le_rng le_sup_left

theorem continuous_sup_rng_right {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₃ : topological_space β} {t₂ : topological_space β} : continuous f → continuous f :=
  continuous_le_rng le_sup_right

theorem continuous_Sup_dom {α : Type u} {β : Type v} {f : α → β} {t₁ : set (topological_space α)} {t₂ : topological_space β} (h : ∀ (t : topological_space α), t ∈ t₁ → continuous f) : continuous f :=
  iff.mpr continuous_iff_le_induced
    (Sup_le fun (t : topological_space α) (ht : t ∈ t₁) => iff.mp continuous_iff_le_induced (h t ht))

theorem continuous_Sup_rng {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₂ : set (topological_space β)} {t : topological_space β} (h₁ : t ∈ t₂) (hf : continuous f) : continuous f :=
  iff.mpr continuous_iff_coinduced_le (le_Sup_of_le h₁ (iff.mp continuous_iff_coinduced_le hf))

theorem continuous_supr_dom {α : Type u} {β : Type v} {f : α → β} {ι : Sort u_2} {t₁ : ι → topological_space α} {t₂ : topological_space β} (h : ι → continuous f) : continuous f := sorry

theorem continuous_supr_rng {α : Type u} {β : Type v} {f : α → β} {ι : Sort u_2} {t₁ : topological_space α} {t₂ : ι → topological_space β} {i : ι} (h : continuous f) : continuous f :=
  continuous_Sup_rng (Exists.intro i rfl) h

theorem continuous_inf_rng {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₂ : topological_space β} {t₃ : topological_space β} (h₁ : continuous f) (h₂ : continuous f) : continuous f :=
  iff.mpr continuous_iff_coinduced_le
    (le_inf (iff.mp continuous_iff_coinduced_le h₁) (iff.mp continuous_iff_coinduced_le h₂))

theorem continuous_inf_dom_left {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₂ : topological_space α} {t₃ : topological_space β} : continuous f → continuous f :=
  continuous_le_dom inf_le_left

theorem continuous_inf_dom_right {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₂ : topological_space α} {t₃ : topological_space β} : continuous f → continuous f :=
  continuous_le_dom inf_le_right

theorem continuous_Inf_dom {α : Type u} {β : Type v} {f : α → β} {t₁ : set (topological_space α)} {t₂ : topological_space β} {t : topological_space α} (h₁ : t ∈ t₁) : continuous f → continuous f :=
  continuous_le_dom (Inf_le h₁)

theorem continuous_Inf_rng {α : Type u} {β : Type v} {f : α → β} {t₁ : topological_space α} {t₂ : set (topological_space β)} (h : ∀ (t : topological_space β), t ∈ t₂ → continuous f) : continuous f :=
  iff.mpr continuous_iff_coinduced_le
    (le_Inf fun (b : topological_space β) (hb : b ∈ t₂) => iff.mp continuous_iff_coinduced_le (h b hb))

theorem continuous_infi_dom {α : Type u} {β : Type v} {f : α → β} {ι : Sort u_2} {t₁ : ι → topological_space α} {t₂ : topological_space β} {i : ι} : continuous f → continuous f :=
  continuous_le_dom (infi_le t₁ i)

theorem continuous_infi_rng {α : Type u} {β : Type v} {f : α → β} {ι : Sort u_2} {t₁ : topological_space α} {t₂ : ι → topological_space β} (h : ι → continuous f) : continuous f :=
  iff.mpr continuous_iff_coinduced_le (le_infi fun (i : ι) => iff.mp continuous_iff_coinduced_le (h i))

theorem continuous_bot {α : Type u} {β : Type v} {f : α → β} {t : topological_space β} : continuous f :=
  iff.mpr continuous_iff_le_induced bot_le

theorem continuous_top {α : Type u} {β : Type v} {f : α → β} {t : topological_space α} : continuous f :=
  iff.mpr continuous_iff_coinduced_le le_top

/- 𝓝 in the induced topology -/

theorem mem_nhds_induced {α : Type u} {β : Type v} [T : topological_space α] (f : β → α) (a : β) (s : set β) : s ∈ nhds a ↔ ∃ (u : set α), ∃ (H : u ∈ nhds (f a)), f ⁻¹' u ⊆ s := sorry

theorem nhds_induced {α : Type u} {β : Type v} [T : topological_space α] (f : β → α) (a : β) : nhds a = filter.comap f (nhds (f a)) := sorry

theorem induced_iff_nhds_eq {α : Type u} {β : Type v} [tα : topological_space α] [tβ : topological_space β] (f : β → α) : tβ = topological_space.induced f tα ↔ ∀ (b : β), nhds b = filter.comap f (nhds (f b)) := sorry

theorem map_nhds_induced_of_surjective {α : Type u} {β : Type v} [T : topological_space α] {f : β → α} (hf : function.surjective f) (a : β) : filter.map f (nhds a) = nhds (f a) := sorry

theorem is_open_induced_eq {α : Type u_1} {β : Type u_2} [t : topological_space β] {f : α → β} {s : set α} : is_open s ↔ s ∈ set.preimage f '' set_of fun (s : set β) => is_open s :=
  iff.rfl

theorem is_open_induced {α : Type u_1} {β : Type u_2} [t : topological_space β] {f : α → β} {s : set β} (h : is_open s) : topological_space.is_open (topological_space.induced f t) (f ⁻¹' s) :=
  Exists.intro s { left := h, right := rfl }

theorem map_nhds_induced_eq {α : Type u_1} {β : Type u_2} [t : topological_space β] {f : α → β} {a : α} (h : set.range f ∈ nhds (f a)) : filter.map f (nhds a) = nhds (f a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (filter.map f (nhds a) = nhds (f a))) (nhds_induced f a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (filter.map f (filter.comap f (nhds (f a))) = nhds (f a))) (filter.map_comap h)))
      (Eq.refl (nhds (f a))))

theorem closure_induced {α : Type u_1} {β : Type u_2} [t : topological_space β] {f : α → β} {a : α} {s : set α} (hf : ∀ (x y : α), f x = f y → x = y) : a ∈ closure s ↔ f a ∈ closure (f '' s) := sorry

@[simp] theorem is_open_singleton_true : is_open (singleton True) :=
  topological_space.generate_open.basic (singleton True)
    (eq.mpr (id (propext ((fun {α : Type} (a : α) => iff_true_intro (set.mem_singleton a)) (singleton True)))) trivial)

theorem continuous_Prop {α : Type u_1} [topological_space α] {p : α → Prop} : continuous p ↔ is_open (set_of fun (x : α) => p x) := sorry

theorem is_open_supr_iff {α : Type u} {ι : Type v} {t : ι → topological_space α} {s : set α} : is_open s ↔ ι → is_open s := sorry

theorem is_closed_infi_iff {α : Type u} {ι : Type v} {t : ι → topological_space α} {s : set α} : is_closed s ↔ ι → is_closed s :=
  is_open_supr_iff

