/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.zorn
import Mathlib.order.copy
import Mathlib.data.set.finite
import Mathlib.tactic.monotonicity.default
import PostPort

universes u_1 l u v x w u_2 u_3 u_4 

namespace Mathlib

/-!
# Theory of filters on sets

## Main definitions

* `filter` : filters on a set;
* `at_top`, `at_bot`, `cofinite`, `principal` : specific filters;
* `map`, `comap`, `prod` : operations on filters;
* `tendsto` : limit with respect to filters;
* `eventually` : `f.eventually p` means `{x | p x} ∈ f`;
* `frequently` : `f.frequently p` means `{x | ¬p x} ∉ f`;
* `filter_upwards [h₁, ..., hₙ]` : takes a list of proofs `hᵢ : sᵢ ∈ f`, and replaces a goal `s ∈ f`
  with `∀ x, x ∈ s₁ → ... → x ∈ sₙ → x ∈ s`;
* `ne_bot f` : an utility class stating that `f` is a non-trivial filter.

Filters on a type `X` are sets of sets of `X` satisfying three conditions. They are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

In this file, we define the type `filter X` of filters on `X`, and endow it with a complete lattice
structure. This structure is lifted from the lattice structure on `set (set X)` using the Galois
insertion which maps a filter to its elements in one direction, and an arbitrary set of sets to
the smallest filter containing it in the other direction.
We also prove `filter` is a monadic functor, with a push-forward operation
`filter.map` and a pull-back operation `filter.comap` that form a Galois connections for the
order on filters.
Finally we describe a product operation `filter X → filter Y → filter (X × Y)`.

The examples of filters appearing in the description of the two motivating ideas are:
* `(at_top : filter ℕ)` : made of sets of `ℕ` containing `{n | n ≥ N}` for some `N`
* `𝓝 x` : made of neighborhoods of `x` in a topological space (defined in topology.basic)
* `𝓤 X` : made of entourages of a uniform space (those space are generalizations of metric spaces
  defined in topology.uniform_space.basic)
* `μ.ae` : made of sets whose complement has zero measure with respect to `μ` (defined in
  `measure_theory.measure_space`)

The general notion of limit of a map with respect to filters on the source and target types
is `filter.tendsto`. It is defined in terms of the order and the push-forward operation.
The predicate "happening eventually" is `filter.eventually`, and "happening often" is
`filter.frequently`, whose definitions are immediate after `filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).

For instance, anticipating on topology.basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `tendsto u at_top (𝓝 x) → (∀ᶠ n in at_top, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from topology.basic.

## Notations

* `∀ᶠ x in f, p x` : `f.eventually p`;
* `∃ᶠ x in f, p x` : `f.frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `f ×ᶠ g` : `filter.prod f g`, localized in `filter`;
* `𝓟 s` : `principal s`, localized in `filter`.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`, which
we do *not* require. This gives `filter X` better formal properties, in particular a bottom element
`⊥` for its lattice structure, at the cost of including the assumption
`[ne_bot f]` in a number of lemmas and definitions.
-/

/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
structure filter (α : Type u_1) 
where
  sets : set (set α)
  univ_sets : set.univ ∈ sets
  sets_of_superset : ∀ {x y : set α}, x ∈ sets → x ⊆ y → y ∈ sets
  inter_sets : ∀ {x y : set α}, x ∈ sets → y ∈ sets → x ∩ y ∈ sets

/-- If `F` is a filter on `α`, and `U` a subset of `α` then we can write `U ∈ F` as on paper. -/
protected instance filter.has_mem {α : Type u_1} : has_mem (set α) (filter α) :=
  has_mem.mk fun (U : set α) (F : filter α) => U ∈ filter.sets F

namespace filter


@[simp] protected theorem mem_mk {α : Type u} {s : set α} {t : set (set α)} {h₁ : set.univ ∈ t} {h₂ : ∀ {x y : set α}, x ∈ t → x ⊆ y → y ∈ t} {h₃ : ∀ {x y : set α}, x ∈ t → y ∈ t → x ∩ y ∈ t} : s ∈ mk t h₁ h₂ h₃ ↔ s ∈ t :=
  iff.rfl

@[simp] protected theorem mem_sets {α : Type u} {f : filter α} {s : set α} : s ∈ sets f ↔ s ∈ f :=
  iff.rfl

protected instance inhabited_mem {α : Type u} {f : filter α} : Inhabited (Subtype fun (s : set α) => s ∈ f) :=
  { default := { val := set.univ, property := univ_sets f } }

theorem filter_eq {α : Type u} {f : filter α} {g : filter α} : sets f = sets g → f = g := sorry

theorem filter_eq_iff {α : Type u} {f : filter α} {g : filter α} : f = g ↔ sets f = sets g :=
  { mp := congr_arg fun {f : filter α} => sets f, mpr := filter_eq }

protected theorem ext_iff {α : Type u} {f : filter α} {g : filter α} : f = g ↔ ∀ (s : set α), s ∈ f ↔ s ∈ g := sorry

protected theorem ext {α : Type u} {f : filter α} {g : filter α} : (∀ (s : set α), s ∈ f ↔ s ∈ g) → f = g :=
  iff.mpr filter.ext_iff

@[simp] theorem univ_mem_sets {α : Type u} {f : filter α} : set.univ ∈ f :=
  univ_sets f

theorem mem_sets_of_superset {α : Type u} {f : filter α} {x : set α} {y : set α} : x ∈ f → x ⊆ y → y ∈ f :=
  sets_of_superset f

theorem inter_mem_sets {α : Type u} {f : filter α} {s : set α} {t : set α} : s ∈ f → t ∈ f → s ∩ t ∈ f :=
  inter_sets f

@[simp] theorem inter_mem_sets_iff {α : Type u} {f : filter α} {s : set α} {t : set α} : s ∩ t ∈ f ↔ s ∈ f ∧ t ∈ f := sorry

theorem univ_mem_sets' {α : Type u} {f : filter α} {s : set α} (h : ∀ (a : α), a ∈ s) : s ∈ f :=
  mem_sets_of_superset univ_mem_sets fun (x : α) (_x : x ∈ set.univ) => h x

theorem mp_sets {α : Type u} {f : filter α} {s : set α} {t : set α} (hs : s ∈ f) (h : (set_of fun (x : α) => x ∈ s → x ∈ t) ∈ f) : t ∈ f := sorry

theorem congr_sets {α : Type u} {f : filter α} {s : set α} {t : set α} (h : (set_of fun (x : α) => x ∈ s ↔ x ∈ t) ∈ f) : s ∈ f ↔ t ∈ f :=
  { mp := fun (hs : s ∈ f) => mp_sets hs (mem_sets_of_superset h fun (x : α) => iff.mp),
    mpr := fun (hs : t ∈ f) => mp_sets hs (mem_sets_of_superset h fun (x : α) => iff.mpr) }

@[simp] theorem bInter_mem_sets {α : Type u} {f : filter α} {β : Type v} {s : β → set α} {is : set β} (hf : set.finite is) : (set.Inter fun (i : β) => set.Inter fun (H : i ∈ is) => s i) ∈ f ↔ ∀ (i : β), i ∈ is → s i ∈ f := sorry

@[simp] theorem bInter_finset_mem_sets {α : Type u} {f : filter α} {β : Type v} {s : β → set α} (is : finset β) : (set.Inter fun (i : β) => set.Inter fun (H : i ∈ is) => s i) ∈ f ↔ ∀ (i : β), i ∈ is → s i ∈ f :=
  bInter_mem_sets (finset.finite_to_set is)

protected theorem Mathlib.finset.Inter_mem_sets {α : Type u} {f : filter α} {β : Type v} {s : β → set α} (is : finset β) : (set.Inter fun (i : β) => set.Inter fun (H : i ∈ is) => s i) ∈ f ↔ ∀ (i : β), i ∈ is → s i ∈ f :=
  bInter_finset_mem_sets

@[simp] theorem sInter_mem_sets {α : Type u} {f : filter α} {s : set (set α)} (hfin : set.finite s) : ⋂₀s ∈ f ↔ ∀ (U : set α), U ∈ s → U ∈ f := sorry

@[simp] theorem Inter_mem_sets {α : Type u} {f : filter α} {β : Type v} {s : β → set α} [fintype β] : (set.Inter fun (i : β) => s i) ∈ f ↔ ∀ (i : β), s i ∈ f := sorry

theorem exists_sets_subset_iff {α : Type u} {f : filter α} {s : set α} : (∃ (t : set α), ∃ (H : t ∈ f), t ⊆ s) ↔ s ∈ f := sorry

theorem monotone_mem_sets {α : Type u} {f : filter α} : monotone fun (s : set α) => s ∈ f :=
  fun (s t : set α) (hst : s ≤ t) (h : s ∈ f) => mem_sets_of_superset h hst

end filter


namespace tactic.interactive


/-- `filter_upwards [h1, ⋯, hn]` replaces a goal of the form `s ∈ f`
and terms `h1 : t1 ∈ f, ⋯, hn : tn ∈ f` with `∀x, x ∈ t1 → ⋯ → x ∈ tn → x ∈ s`.

`filter_upwards [h1, ⋯, hn] e` is a short form for `{ filter_upwards [h1, ⋯, hn], exact e }`.
-/
end tactic.interactive


namespace filter


/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal {α : Type u} (s : set α) : filter α :=
  mk (set_of fun (t : set α) => s ⊆ t) (set.subset_univ s) sorry sorry

protected instance inhabited {α : Type u} : Inhabited (filter α) :=
  { default := principal ∅ }

@[simp] theorem mem_principal_sets {α : Type u} {s : set α} {t : set α} : s ∈ principal t ↔ t ⊆ s :=
  iff.rfl

theorem mem_principal_self {α : Type u} (s : set α) : s ∈ principal s :=
  set.subset.refl s

/-- The join of a filter of filters is defined by the relation `s ∈ join f ↔ {t | s ∈ t} ∈ f`. -/
def join {α : Type u} (f : filter (filter α)) : filter α :=
  mk (set_of fun (s : set α) => (set_of fun (t : filter α) => s ∈ t) ∈ f) sorry sorry sorry

@[simp] theorem mem_join_sets {α : Type u} {s : set α} {f : filter (filter α)} : s ∈ join f ↔ (set_of fun (t : filter α) => s ∈ t) ∈ f :=
  iff.rfl

protected instance partial_order {α : Type u} : partial_order (filter α) :=
  partial_order.mk (fun (f g : filter α) => ∀ {U : set α}, U ∈ g → U ∈ f)
    (preorder.lt._default fun (f g : filter α) => ∀ {U : set α}, U ∈ g → U ∈ f) sorry sorry sorry

theorem le_def {α : Type u} {f : filter α} {g : filter α} : f ≤ g ↔ ∀ (x : set α), x ∈ g → x ∈ f :=
  iff.rfl

/-- `generate_sets g s`: `s` is in the filter closure of `g`. -/
inductive generate_sets {α : Type u} (g : set (set α)) : set α → Prop
where
| basic : ∀ {s : set α}, s ∈ g → generate_sets g s
| univ : generate_sets g set.univ
| superset : ∀ {s t : set α}, generate_sets g s → s ⊆ t → generate_sets g t
| inter : ∀ {s t : set α}, generate_sets g s → generate_sets g t → generate_sets g (s ∩ t)

/-- `generate g` is the smallest filter containing the sets `g`. -/
def generate {α : Type u} (g : set (set α)) : filter α :=
  mk (generate_sets g) generate_sets.univ sorry sorry

theorem sets_iff_generate {α : Type u} {s : set (set α)} {f : filter α} : f ≤ generate s ↔ s ⊆ sets f := sorry

theorem mem_generate_iff {α : Type u} {s : set (set α)} {U : set α} : U ∈ generate s ↔ ∃ (t : set (set α)), ∃ (H : t ⊆ s), set.finite t ∧ ⋂₀t ⊆ U := sorry

/-- `mk_of_closure s hs` constructs a filter on `α` whose elements set is exactly
`s : set (set α)`, provided one gives the assumption `hs : (generate s).sets = s`. -/
protected def mk_of_closure {α : Type u} (s : set (set α)) (hs : sets (generate s) = s) : filter α :=
  mk s sorry sorry sorry

theorem mk_of_closure_sets {α : Type u} {s : set (set α)} {hs : sets (generate s) = s} : filter.mk_of_closure s hs = generate s :=
  filter.ext
    fun (u : set α) =>
      (fun (this : u ∈ sets (filter.mk_of_closure s hs) ↔ u ∈ sets (generate s)) => this) (Eq.symm hs ▸ iff.rfl)

/-- Galois insertion from sets of sets into filters. -/
def gi_generate (α : Type u_1) : galois_insertion generate sets :=
  galois_insertion.mk (fun (s : set (set α)) (hs : sets (generate s) ≤ s) => filter.mk_of_closure s sorry) sorry sorry
    sorry

/-- The infimum of filters is the filter generated by intersections
  of elements of the two filters. -/
protected instance has_inf {α : Type u} : has_inf (filter α) :=
  has_inf.mk
    fun (f g : filter α) =>
      mk (set_of fun (s : set α) => ∃ (a : set α), ∃ (H : a ∈ f), ∃ (b : set α), ∃ (H : b ∈ g), a ∩ b ⊆ s) sorry sorry
        sorry

@[simp] theorem mem_inf_sets {α : Type u} {f : filter α} {g : filter α} {s : set α} : s ∈ f ⊓ g ↔ ∃ (t₁ : set α), ∃ (H : t₁ ∈ f), ∃ (t₂ : set α), ∃ (H : t₂ ∈ g), t₁ ∩ t₂ ⊆ s :=
  iff.rfl

theorem mem_inf_sets_of_left {α : Type u} {f : filter α} {g : filter α} {s : set α} (h : s ∈ f) : s ∈ f ⊓ g :=
  Exists.intro s (Exists.intro h (Exists.intro set.univ (Exists.intro univ_mem_sets (set.inter_subset_left s set.univ))))

theorem mem_inf_sets_of_right {α : Type u} {f : filter α} {g : filter α} {s : set α} (h : s ∈ g) : s ∈ f ⊓ g :=
  Exists.intro set.univ (Exists.intro univ_mem_sets (Exists.intro s (Exists.intro h (set.inter_subset_right set.univ s))))

theorem inter_mem_inf_sets {α : Type u} {f : filter α} {g : filter α} {s : set α} {t : set α} (hs : s ∈ f) (ht : t ∈ g) : s ∩ t ∈ f ⊓ g :=
  inter_mem_sets (mem_inf_sets_of_left hs) (mem_inf_sets_of_right ht)

protected instance has_top {α : Type u} : has_top (filter α) :=
  has_top.mk (mk (set_of fun (s : set α) => ∀ (x : α), x ∈ s) sorry sorry sorry)

theorem mem_top_sets_iff_forall {α : Type u} {s : set α} : s ∈ ⊤ ↔ ∀ (x : α), x ∈ s :=
  iff.rfl

@[simp] theorem mem_top_sets {α : Type u} {s : set α} : s ∈ ⊤ ↔ s = set.univ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s ∈ ⊤ ↔ s = set.univ)) (propext mem_top_sets_iff_forall)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((∀ (x : α), x ∈ s) ↔ s = set.univ)) (propext set.eq_univ_iff_forall)))
      (iff.refl (∀ (x : α), x ∈ s)))

/- We lift the complete lattice along the Galois connection `generate` / `sets`. Unfortunately,
  we want to have different definitional equalities for the lattice operations. So we define them
  upfront and change the lattice operations for the complete lattice instance. -/

protected instance complete_lattice {α : Type u} : complete_lattice (filter α) :=
  complete_lattice.copy original_complete_lattice partial_order.le sorry ⊤ sorry complete_lattice.bot sorry
    complete_lattice.sup sorry has_inf.inf sorry (join ∘ principal) sorry complete_lattice.Inf sorry

/-- A filter is `ne_bot` if it is not equal to `⊥`, or equivalently the empty set
does not belong to the filter. Bourbaki include this assumption in the definition
of a filter but we prefer to have a `complete_lattice` structure on filter, so
we use a typeclass argument in lemmas instead. -/
def ne_bot {α : Type u} (f : filter α)  :=
  f ≠ ⊥

theorem ne_bot.ne {α : Type u} {f : filter α} (hf : ne_bot f) : f ≠ ⊥ :=
  hf

@[simp] theorem not_ne_bot {α : Type u_1} {f : filter α} : ¬ne_bot f ↔ f = ⊥ :=
  not_not

theorem ne_bot.mono {α : Type u} {f : filter α} {g : filter α} (hf : ne_bot f) (hg : f ≤ g) : ne_bot g :=
  ne_bot_of_le_ne_bot hf hg

theorem ne_bot_of_le {α : Type u} {f : filter α} {g : filter α} [hf : ne_bot f] (hg : f ≤ g) : ne_bot g :=
  ne_bot.mono hf hg

theorem bot_sets_eq {α : Type u} : sets ⊥ = set.univ :=
  rfl

theorem sup_sets_eq {α : Type u} {f : filter α} {g : filter α} : sets (f ⊔ g) = sets f ∩ sets g :=
  galois_connection.u_inf (galois_insertion.gc (gi_generate α))

theorem Sup_sets_eq {α : Type u} {s : set (filter α)} : sets (Sup s) = set.Inter fun (f : filter α) => set.Inter fun (H : f ∈ s) => sets f :=
  galois_connection.u_Inf (galois_insertion.gc (gi_generate α))

theorem supr_sets_eq {α : Type u} {ι : Sort x} {f : ι → filter α} : sets (supr f) = set.Inter fun (i : ι) => sets (f i) :=
  galois_connection.u_infi (galois_insertion.gc (gi_generate α))

theorem generate_empty {α : Type u} : generate ∅ = ⊤ :=
  galois_connection.l_bot (galois_insertion.gc (gi_generate α))

theorem generate_univ {α : Type u} : generate set.univ = ⊥ :=
  Eq.symm mk_of_closure_sets

theorem generate_union {α : Type u} {s : set (set α)} {t : set (set α)} : generate (s ∪ t) = generate s ⊓ generate t :=
  galois_connection.l_sup (galois_insertion.gc (gi_generate α))

theorem generate_Union {α : Type u} {ι : Sort x} {s : ι → set (set α)} : generate (set.Union fun (i : ι) => s i) = infi fun (i : ι) => generate (s i) :=
  galois_connection.l_supr (galois_insertion.gc (gi_generate α))

@[simp] theorem mem_bot_sets {α : Type u} {s : set α} : s ∈ ⊥ :=
  trivial

@[simp] theorem mem_sup_sets {α : Type u} {f : filter α} {g : filter α} {s : set α} : s ∈ f ⊔ g ↔ s ∈ f ∧ s ∈ g :=
  iff.rfl

theorem union_mem_sup {α : Type u} {f : filter α} {g : filter α} {s : set α} {t : set α} (hs : s ∈ f) (ht : t ∈ g) : s ∪ t ∈ f ⊔ g :=
  { left := mem_sets_of_superset hs (set.subset_union_left s t),
    right := mem_sets_of_superset ht (set.subset_union_right s t) }

@[simp] theorem mem_Sup_sets {α : Type u} {x : set α} {s : set (filter α)} : x ∈ Sup s ↔ ∀ (f : filter α), f ∈ s → x ∈ f :=
  iff.rfl

@[simp] theorem mem_supr_sets {α : Type u} {ι : Sort x} {x : set α} {f : ι → filter α} : x ∈ supr f ↔ ∀ (i : ι), x ∈ f i := sorry

theorem infi_eq_generate {α : Type u} {ι : Sort x} (s : ι → filter α) : infi s = generate (set.Union fun (i : ι) => sets (s i)) := sorry

theorem mem_infi_iff {α : Type u} {ι : Type u_1} {s : ι → filter α} {U : set α} : (U ∈ infi fun (i : ι) => s i) ↔
  ∃ (I : set ι),
    set.finite I ∧
      ∃ (V : ↥(set_of fun (i : ι) => i ∈ I) → set α),
        (∀ (i : ↥(set_of fun (i : ι) => i ∈ I)), V i ∈ s ↑i) ∧
          (set.Inter fun (i : ↥(set_of fun (i : ι) => i ∈ I)) => V i) ⊆ U := sorry

@[simp] theorem le_principal_iff {α : Type u} {s : set α} {f : filter α} : f ≤ principal s ↔ s ∈ f :=
  (fun (this : (∀ {t : set α}, s ⊆ t → t ∈ f) ↔ s ∈ f) => this)
    { mp := fun (h : ∀ {t : set α}, s ⊆ t → t ∈ f) => h (set.subset.refl s),
      mpr := fun (hs : s ∈ f) (t : set α) (ht : s ⊆ t) => mem_sets_of_superset hs ht }

theorem principal_mono {α : Type u} {s : set α} {t : set α} : principal s ≤ principal t ↔ s ⊆ t := sorry

theorem monotone_principal {α : Type u} : monotone principal :=
  fun (_x _x_1 : set α) => iff.mpr principal_mono

@[simp] theorem principal_eq_iff_eq {α : Type u} {s : set α} {t : set α} : principal s = principal t ↔ s = t := sorry

@[simp] theorem join_principal_eq_Sup {α : Type u} {s : set (filter α)} : join (principal s) = Sup s :=
  rfl

@[simp] theorem principal_univ {α : Type u} : principal set.univ = ⊤ := sorry

@[simp] theorem principal_empty {α : Type u} : principal ∅ = ⊥ :=
  bot_unique fun (s : set α) (_x : s ∈ ⊥) => set.empty_subset s

/-! ### Lattice equations -/

theorem empty_in_sets_eq_bot {α : Type u} {f : filter α} : ∅ ∈ f ↔ f = ⊥ :=
  { mp := fun (h : ∅ ∈ f) => bot_unique fun (s : set α) (_x : s ∈ ⊥) => mem_sets_of_superset h (set.empty_subset s),
    mpr := fun (this : f = ⊥) => Eq.symm this ▸ mem_bot_sets }

theorem nonempty_of_mem_sets {α : Type u} {f : filter α} [hf : ne_bot f] {s : set α} (hs : s ∈ f) : set.nonempty s :=
  or.elim (set.eq_empty_or_nonempty s) (fun (h : s = ∅) => absurd hs (Eq.symm h ▸ mt (iff.mp empty_in_sets_eq_bot) hf)) id

theorem ne_bot.nonempty_of_mem {α : Type u} {f : filter α} (hf : ne_bot f) {s : set α} (hs : s ∈ f) : set.nonempty s :=
  nonempty_of_mem_sets hs

@[simp] theorem empty_nmem_sets {α : Type u} (f : filter α) [ne_bot f] : ¬∅ ∈ f :=
  fun (h : ∅ ∈ f) => set.nonempty.ne_empty (nonempty_of_mem_sets h) rfl

theorem nonempty_of_ne_bot {α : Type u} (f : filter α) [ne_bot f] : Nonempty α :=
  nonempty_of_exists (nonempty_of_mem_sets univ_mem_sets)

theorem compl_not_mem_sets {α : Type u} {f : filter α} {s : set α} [ne_bot f] (h : s ∈ f) : ¬sᶜ ∈ f :=
  fun (hsc : sᶜ ∈ f) => set.nonempty.ne_empty (nonempty_of_mem_sets (inter_mem_sets h hsc)) (set.inter_compl_self s)

theorem filter_eq_bot_of_not_nonempty {α : Type u} (f : filter α) (ne : ¬Nonempty α) : f = ⊥ :=
  iff.mp empty_in_sets_eq_bot (univ_mem_sets' fun (x : α) => false.elim (ne (Nonempty.intro x)))

theorem forall_sets_nonempty_iff_ne_bot {α : Type u} {f : filter α} : (∀ (s : set α), s ∈ f → set.nonempty s) ↔ ne_bot f := sorry

theorem nontrivial_iff_nonempty {α : Type u} : nontrivial (filter α) ↔ Nonempty α := sorry

theorem mem_sets_of_eq_bot {α : Type u} {f : filter α} {s : set α} (h : f ⊓ principal (sᶜ) = ⊥) : s ∈ f := sorry

theorem eq_Inf_of_mem_sets_iff_exists_mem {α : Type u} {S : set (filter α)} {l : filter α} (h : ∀ {s : set α}, s ∈ l ↔ ∃ (f : filter α), ∃ (H : f ∈ S), s ∈ f) : l = Inf S := sorry

theorem eq_infi_of_mem_sets_iff_exists_mem {α : Type u} {ι : Sort x} {f : ι → filter α} {l : filter α} (h : ∀ {s : set α}, s ∈ l ↔ ∃ (i : ι), s ∈ f i) : l = infi f :=
  eq_Inf_of_mem_sets_iff_exists_mem fun (s : set α) => iff.trans h (iff.symm set.exists_range_iff)

theorem eq_binfi_of_mem_sets_iff_exists_mem {α : Type u} {ι : Sort x} {f : ι → filter α} {p : ι → Prop} {l : filter α} (h : ∀ {s : set α}, s ∈ l ↔ ∃ (i : ι), ∃ (_x : p i), s ∈ f i) : l = infi fun (i : ι) => infi fun (_x : p i) => f i := sorry

theorem infi_sets_eq {α : Type u} {ι : Sort x} {f : ι → filter α} (h : directed ge f) [ne : Nonempty ι] : sets (infi f) = set.Union fun (i : ι) => sets (f i) := sorry

theorem mem_infi {α : Type u} {ι : Sort x} {f : ι → filter α} (h : directed ge f) [Nonempty ι] (s : set α) : s ∈ infi f ↔ ∃ (i : ι), s ∈ f i := sorry

theorem mem_binfi {α : Type u} {β : Type v} {f : β → filter α} {s : set β} (h : directed_on (f ⁻¹'o ge) s) (ne : set.nonempty s) {t : set α} : (t ∈ infi fun (i : β) => infi fun (H : i ∈ s) => f i) ↔ ∃ (i : β), ∃ (H : i ∈ s), t ∈ f i := sorry

theorem binfi_sets_eq {α : Type u} {β : Type v} {f : β → filter α} {s : set β} (h : directed_on (f ⁻¹'o ge) s) (ne : set.nonempty s) : sets (infi fun (i : β) => infi fun (H : i ∈ s) => f i) =
  set.Union fun (i : β) => set.Union fun (H : i ∈ s) => sets (f i) := sorry

theorem infi_sets_eq_finite {α : Type u} {ι : Type u_1} (f : ι → filter α) : sets (infi fun (i : ι) => f i) = set.Union fun (t : finset ι) => sets (infi fun (i : ι) => infi fun (H : i ∈ t) => f i) := sorry

theorem infi_sets_eq_finite' {α : Type u} {ι : Sort x} (f : ι → filter α) : sets (infi fun (i : ι) => f i) =
  set.Union fun (t : finset (plift ι)) => sets (infi fun (i : plift ι) => infi fun (H : i ∈ t) => f (plift.down i)) := sorry

theorem mem_infi_finite {α : Type u} {ι : Type u_1} {f : ι → filter α} (s : set α) : s ∈ infi f ↔ ∃ (t : finset ι), s ∈ infi fun (i : ι) => infi fun (H : i ∈ t) => f i :=
  iff.trans (iff.mp set.ext_iff (infi_sets_eq_finite f) s) set.mem_Union

theorem mem_infi_finite' {α : Type u} {ι : Sort x} {f : ι → filter α} (s : set α) : s ∈ infi f ↔ ∃ (t : finset (plift ι)), s ∈ infi fun (i : plift ι) => infi fun (H : i ∈ t) => f (plift.down i) :=
  iff.trans (iff.mp set.ext_iff (infi_sets_eq_finite' f) s) set.mem_Union

@[simp] theorem sup_join {α : Type u} {f₁ : filter (filter α)} {f₂ : filter (filter α)} : join f₁ ⊔ join f₂ = join (f₁ ⊔ f₂) := sorry

@[simp] theorem supr_join {α : Type u} {ι : Sort w} {f : ι → filter (filter α)} : (supr fun (x : ι) => join (f x)) = join (supr fun (x : ι) => f x) := sorry

protected instance bounded_distrib_lattice {α : Type u} : bounded_distrib_lattice (filter α) :=
  bounded_distrib_lattice.mk complete_lattice.sup complete_lattice.le complete_lattice.lt sorry sorry sorry sorry sorry
    sorry complete_lattice.inf sorry sorry sorry sorry complete_lattice.top sorry complete_lattice.bot sorry

/- the complementary version with ⨆i, f ⊓ g i does not hold! -/

theorem infi_sup_left {α : Type u} {ι : Sort x} {f : filter α} {g : ι → filter α} : (infi fun (x : ι) => f ⊔ g x) = f ⊔ infi g := sorry

theorem infi_sup_right {α : Type u} {ι : Sort x} {f : filter α} {g : ι → filter α} : (infi fun (x : ι) => g x ⊔ f) = infi g ⊔ f := sorry

theorem binfi_sup_right {α : Type u} {ι : Sort x} (p : ι → Prop) (f : ι → filter α) (g : filter α) : (infi fun (i : ι) => infi fun (h : p i) => f i ⊔ g) = (infi fun (i : ι) => infi fun (h : p i) => f i) ⊔ g := sorry

theorem binfi_sup_left {α : Type u} {ι : Sort x} (p : ι → Prop) (f : ι → filter α) (g : filter α) : (infi fun (i : ι) => infi fun (h : p i) => g ⊔ f i) = g ⊔ infi fun (i : ι) => infi fun (h : p i) => f i := sorry

theorem mem_infi_sets_finset {α : Type u} {β : Type v} {s : finset α} {f : α → filter β} (t : set β) : (t ∈ infi fun (a : α) => infi fun (H : a ∈ s) => f a) ↔
  ∃ (p : α → set β), (∀ (a : α), a ∈ s → p a ∈ f a) ∧ (set.Inter fun (a : α) => set.Inter fun (H : a ∈ s) => p a) ⊆ t := sorry

/-- If `f : ι → filter α` is directed, `ι` is not empty, and `∀ i, f i ≠ ⊥`, then `infi f ≠ ⊥`.
See also `infi_ne_bot_of_directed` for a version assuming `nonempty α` instead of `nonempty ι`. -/
theorem infi_ne_bot_of_directed' {α : Type u} {ι : Sort x} {f : ι → filter α} [Nonempty ι] (hd : directed ge f) (hb : ∀ (i : ι), ne_bot (f i)) : ne_bot (infi f) := sorry

/-- If `f : ι → filter α` is directed, `α` is not empty, and `∀ i, f i ≠ ⊥`, then `infi f ≠ ⊥`.
See also `infi_ne_bot_of_directed'` for a version assuming `nonempty ι` instead of `nonempty α`. -/
theorem infi_ne_bot_of_directed {α : Type u} {ι : Sort x} {f : ι → filter α} [hn : Nonempty α] (hd : directed ge f) (hb : ∀ (i : ι), ne_bot (f i)) : ne_bot (infi f) := sorry

theorem infi_ne_bot_iff_of_directed' {α : Type u} {ι : Sort x} {f : ι → filter α} [Nonempty ι] (hd : directed ge f) : ne_bot (infi f) ↔ ∀ (i : ι), ne_bot (f i) :=
  { mp := fun (H : ne_bot (infi f)) (i : ι) => ne_bot.mono H (infi_le f i), mpr := infi_ne_bot_of_directed' hd }

theorem infi_ne_bot_iff_of_directed {α : Type u} {ι : Sort x} {f : ι → filter α} [Nonempty α] (hd : directed ge f) : ne_bot (infi f) ↔ ∀ (i : ι), ne_bot (f i) :=
  { mp := fun (H : ne_bot (infi f)) (i : ι) => ne_bot.mono H (infi_le f i), mpr := infi_ne_bot_of_directed hd }

theorem mem_infi_sets {α : Type u} {ι : Sort x} {f : ι → filter α} (i : ι) {s : set α} : s ∈ f i → s ∈ infi fun (i : ι) => f i :=
  (fun (this : (infi fun (i : ι) => f i) ≤ f i) => this) (infi_le (fun (i : ι) => f i) i)

theorem infi_sets_induct {α : Type u} {ι : Sort x} {f : ι → filter α} {s : set α} (hs : s ∈ infi f) {p : set α → Prop} (uni : p set.univ) (ins : ∀ {i : ι} {s₁ s₂ : set α}, s₁ ∈ f i → p s₂ → p (s₁ ∩ s₂)) (upw : ∀ {s₁ s₂ : set α}, s₁ ⊆ s₂ → p s₁ → p s₂) : p s := sorry

/- principal equations -/

@[simp] theorem inf_principal {α : Type u} {s : set α} {t : set α} : principal s ⊓ principal t = principal (s ∩ t) := sorry

@[simp] theorem sup_principal {α : Type u} {s : set α} {t : set α} : principal s ⊔ principal t = principal (s ∪ t) := sorry

@[simp] theorem supr_principal {α : Type u} {ι : Sort w} {s : ι → set α} : (supr fun (x : ι) => principal (s x)) = principal (set.Union fun (i : ι) => s i) := sorry

@[simp] theorem principal_eq_bot_iff {α : Type u} {s : set α} : principal s = ⊥ ↔ s = ∅ :=
  iff.trans (iff.symm empty_in_sets_eq_bot) (iff.trans mem_principal_sets set.subset_empty_iff)

@[simp] theorem principal_ne_bot_iff {α : Type u} {s : set α} : ne_bot (principal s) ↔ set.nonempty s :=
  iff.trans (not_congr principal_eq_bot_iff) set.ne_empty_iff_nonempty

theorem is_compl_principal {α : Type u} (s : set α) : is_compl (principal s) (principal (sᶜ)) := sorry

theorem inf_principal_eq_bot {α : Type u} {f : filter α} {s : set α} (hs : sᶜ ∈ f) : f ⊓ principal s = ⊥ := sorry

theorem mem_inf_principal {α : Type u} {f : filter α} {s : set α} {t : set α} : s ∈ f ⊓ principal t ↔ (set_of fun (x : α) => x ∈ t → x ∈ s) ∈ f := sorry

theorem diff_mem_inf_principal_compl {α : Type u} {f : filter α} {s : set α} (hs : s ∈ f) (t : set α) : s \ t ∈ f ⊓ principal (tᶜ) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s \ t ∈ f ⊓ principal (tᶜ))) (propext mem_inf_principal)))
    (mp_sets hs (univ_mem_sets' (id fun (a : α) (has : a ∈ s) (hat : a ∈ (tᶜ)) => { left := has, right := hat })))

theorem principal_le_iff {α : Type u} {s : set α} {f : filter α} : principal s ≤ f ↔ ∀ (V : set α), V ∈ f → s ⊆ V := sorry

@[simp] theorem infi_principal_finset {α : Type u} {ι : Type w} (s : finset ι) (f : ι → set α) : (infi fun (i : ι) => infi fun (H : i ∈ s) => principal (f i)) =
  principal (set.Inter fun (i : ι) => set.Inter fun (H : i ∈ s) => f i) := sorry

@[simp] theorem infi_principal_fintype {α : Type u} {ι : Type w} [fintype ι] (f : ι → set α) : (infi fun (i : ι) => principal (f i)) = principal (set.Inter fun (i : ι) => f i) := sorry

theorem join_mono {α : Type u} {f₁ : filter (filter α)} {f₂ : filter (filter α)} (h : f₁ ≤ f₂) : join f₁ ≤ join f₂ :=
  fun (s : set α) (hs : s ∈ join f₂) => h hs

/-! ### Eventually -/

/-- `f.eventually p` or `∀ᶠ x in f, p x` mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in at_top, p x`
means that `p` holds true for sufficiently large `x`. -/
protected def eventually {α : Type u} (p : α → Prop) (f : filter α)  :=
  (set_of fun (x : α) => p x) ∈ f

theorem eventually_iff {α : Type u} {f : filter α} {P : α → Prop} : filter.eventually (fun (x : α) => P x) f ↔ (set_of fun (x : α) => P x) ∈ f :=
  iff.rfl

protected theorem ext' {α : Type u} {f₁ : filter α} {f₂ : filter α} (h : ∀ (p : α → Prop), filter.eventually (fun (x : α) => p x) f₁ ↔ filter.eventually (fun (x : α) => p x) f₂) : f₁ = f₂ :=
  filter.ext h

theorem eventually.filter_mono {α : Type u} {f₁ : filter α} {f₂ : filter α} (h : f₁ ≤ f₂) {p : α → Prop} (hp : filter.eventually (fun (x : α) => p x) f₂) : filter.eventually (fun (x : α) => p x) f₁ :=
  h hp

theorem eventually_of_mem {α : Type u} {f : filter α} {P : α → Prop} {U : set α} (hU : U ∈ f) (h : ∀ (x : α), x ∈ U → P x) : filter.eventually (fun (x : α) => P x) f :=
  mem_sets_of_superset hU h

protected theorem eventually.and {α : Type u} {p : α → Prop} {q : α → Prop} {f : filter α} : filter.eventually p f → filter.eventually q f → filter.eventually (fun (x : α) => p x ∧ q x) f :=
  inter_mem_sets

@[simp] theorem eventually_true {α : Type u} (f : filter α) : filter.eventually (fun (x : α) => True) f :=
  univ_mem_sets

theorem eventually_of_forall {α : Type u} {p : α → Prop} {f : filter α} (hp : ∀ (x : α), p x) : filter.eventually (fun (x : α) => p x) f :=
  univ_mem_sets' hp

@[simp] theorem eventually_false_iff_eq_bot {α : Type u} {f : filter α} : filter.eventually (fun (x : α) => False) f ↔ f = ⊥ :=
  empty_in_sets_eq_bot

@[simp] theorem eventually_const {α : Type u} {f : filter α} [ne_bot f] {p : Prop} : filter.eventually (fun (x : α) => p) f ↔ p := sorry

theorem eventually_iff_exists_mem {α : Type u} {p : α → Prop} {f : filter α} : filter.eventually (fun (x : α) => p x) f ↔ ∃ (v : set α), ∃ (H : v ∈ f), ∀ (y : α), y ∈ v → p y :=
  iff.symm exists_sets_subset_iff

theorem eventually.exists_mem {α : Type u} {p : α → Prop} {f : filter α} (hp : filter.eventually (fun (x : α) => p x) f) : ∃ (v : set α), ∃ (H : v ∈ f), ∀ (y : α), y ∈ v → p y :=
  iff.mp eventually_iff_exists_mem hp

theorem eventually.mp {α : Type u} {p : α → Prop} {q : α → Prop} {f : filter α} (hp : filter.eventually (fun (x : α) => p x) f) (hq : filter.eventually (fun (x : α) => p x → q x) f) : filter.eventually (fun (x : α) => q x) f :=
  mp_sets hp hq

theorem eventually.mono {α : Type u} {p : α → Prop} {q : α → Prop} {f : filter α} (hp : filter.eventually (fun (x : α) => p x) f) (hq : ∀ (x : α), p x → q x) : filter.eventually (fun (x : α) => q x) f :=
  eventually.mp hp (eventually_of_forall hq)

@[simp] theorem eventually_and {α : Type u} {p : α → Prop} {q : α → Prop} {f : filter α} : filter.eventually (fun (x : α) => p x ∧ q x) f ↔
  filter.eventually (fun (x : α) => p x) f ∧ filter.eventually (fun (x : α) => q x) f :=
  inter_mem_sets_iff

theorem eventually.congr {α : Type u} {f : filter α} {p : α → Prop} {q : α → Prop} (h' : filter.eventually (fun (x : α) => p x) f) (h : filter.eventually (fun (x : α) => p x ↔ q x) f) : filter.eventually (fun (x : α) => q x) f :=
  eventually.mp h' (eventually.mono h fun (x : α) (hx : p x ↔ q x) => iff.mp hx)

theorem eventually_congr {α : Type u} {f : filter α} {p : α → Prop} {q : α → Prop} (h : filter.eventually (fun (x : α) => p x ↔ q x) f) : filter.eventually (fun (x : α) => p x) f ↔ filter.eventually (fun (x : α) => q x) f := sorry

@[simp] theorem eventually_all {α : Type u} {ι : Type u_1} [fintype ι] {l : filter α} {p : ι → α → Prop} : filter.eventually (fun (x : α) => ∀ (i : ι), p i x) l ↔ ∀ (i : ι), filter.eventually (fun (x : α) => p i x) l := sorry

@[simp] theorem eventually_all_finite {α : Type u} {ι : Type u_1} {I : set ι} (hI : set.finite I) {l : filter α} {p : ι → α → Prop} : filter.eventually (fun (x : α) => ∀ (i : ι), i ∈ I → p i x) l ↔
  ∀ (i : ι), i ∈ I → filter.eventually (fun (x : α) => p i x) l := sorry

protected theorem Mathlib.set.finite.eventually_all {α : Type u} {ι : Type u_1} {I : set ι} (hI : set.finite I) {l : filter α} {p : ι → α → Prop} : filter.eventually (fun (x : α) => ∀ (i : ι), i ∈ I → p i x) l ↔
  ∀ (i : ι), i ∈ I → filter.eventually (fun (x : α) => p i x) l :=
  eventually_all_finite

@[simp] theorem eventually_all_finset {α : Type u} {ι : Type u_1} (I : finset ι) {l : filter α} {p : ι → α → Prop} : filter.eventually (fun (x : α) => ∀ (i : ι), i ∈ I → p i x) l ↔
  ∀ (i : ι), i ∈ I → filter.eventually (fun (x : α) => p i x) l :=
  set.finite.eventually_all (finset.finite_to_set I)

protected theorem Mathlib.finset.eventually_all {α : Type u} {ι : Type u_1} (I : finset ι) {l : filter α} {p : ι → α → Prop} : filter.eventually (fun (x : α) => ∀ (i : ι), i ∈ I → p i x) l ↔
  ∀ (i : ι), i ∈ I → filter.eventually (fun (x : α) => p i x) l :=
  eventually_all_finset

@[simp] theorem eventually_or_distrib_left {α : Type u} {f : filter α} {p : Prop} {q : α → Prop} : filter.eventually (fun (x : α) => p ∨ q x) f ↔ p ∨ filter.eventually (fun (x : α) => q x) f := sorry

@[simp] theorem eventually_or_distrib_right {α : Type u} {f : filter α} {p : α → Prop} {q : Prop} : filter.eventually (fun (x : α) => p x ∨ q) f ↔ filter.eventually (fun (x : α) => p x) f ∨ q := sorry

@[simp] theorem eventually_imp_distrib_left {α : Type u} {f : filter α} {p : Prop} {q : α → Prop} : filter.eventually (fun (x : α) => p → q x) f ↔ p → filter.eventually (fun (x : α) => q x) f := sorry

@[simp] theorem eventually_bot {α : Type u} {p : α → Prop} : filter.eventually (fun (x : α) => p x) ⊥ :=
  True.intro

@[simp] theorem eventually_top {α : Type u} {p : α → Prop} : filter.eventually (fun (x : α) => p x) ⊤ ↔ ∀ (x : α), p x :=
  iff.rfl

@[simp] theorem eventually_sup {α : Type u} {p : α → Prop} {f : filter α} {g : filter α} : filter.eventually (fun (x : α) => p x) (f ⊔ g) ↔
  filter.eventually (fun (x : α) => p x) f ∧ filter.eventually (fun (x : α) => p x) g :=
  iff.rfl

@[simp] theorem eventually_Sup {α : Type u} {p : α → Prop} {fs : set (filter α)} : filter.eventually (fun (x : α) => p x) (Sup fs) ↔ ∀ (f : filter α), f ∈ fs → filter.eventually (fun (x : α) => p x) f :=
  iff.rfl

@[simp] theorem eventually_supr {α : Type u} {β : Type v} {p : α → Prop} {fs : β → filter α} : filter.eventually (fun (x : α) => p x) (supr fun (b : β) => fs b) ↔
  ∀ (b : β), filter.eventually (fun (x : α) => p x) (fs b) :=
  mem_supr_sets

@[simp] theorem eventually_principal {α : Type u} {a : set α} {p : α → Prop} : filter.eventually (fun (x : α) => p x) (principal a) ↔ ∀ (x : α), x ∈ a → p x :=
  iff.rfl

theorem eventually_inf_principal {α : Type u} {f : filter α} {p : α → Prop} {s : set α} : filter.eventually (fun (x : α) => p x) (f ⊓ principal s) ↔ filter.eventually (fun (x : α) => x ∈ s → p x) f :=
  mem_inf_principal

/-! ### Frequently -/

/-- `f.frequently p` or `∃ᶠ x in f, p x` mean that `{x | ¬p x} ∉ f`. E.g., `∃ᶠ x in at_top, p x`
means that there exist arbitrarily large `x` for which `p` holds true. -/
protected def frequently {α : Type u} (p : α → Prop) (f : filter α)  :=
  ¬filter.eventually (fun (x : α) => ¬p x) f

theorem eventually.frequently {α : Type u} {f : filter α} [ne_bot f] {p : α → Prop} (h : filter.eventually (fun (x : α) => p x) f) : filter.frequently (fun (x : α) => p x) f :=
  compl_not_mem_sets h

theorem frequently_of_forall {α : Type u} {f : filter α} [ne_bot f] {p : α → Prop} (h : ∀ (x : α), p x) : filter.frequently (fun (x : α) => p x) f :=
  eventually.frequently (eventually_of_forall h)

theorem frequently.mp {α : Type u} {p : α → Prop} {q : α → Prop} {f : filter α} (h : filter.frequently (fun (x : α) => p x) f) (hpq : filter.eventually (fun (x : α) => p x → q x) f) : filter.frequently (fun (x : α) => q x) f := sorry

theorem frequently.mono {α : Type u} {p : α → Prop} {q : α → Prop} {f : filter α} (h : filter.frequently (fun (x : α) => p x) f) (hpq : ∀ (x : α), p x → q x) : filter.frequently (fun (x : α) => q x) f :=
  frequently.mp h (eventually_of_forall hpq)

theorem frequently.and_eventually {α : Type u} {p : α → Prop} {q : α → Prop} {f : filter α} (hp : filter.frequently (fun (x : α) => p x) f) (hq : filter.eventually (fun (x : α) => q x) f) : filter.frequently (fun (x : α) => p x ∧ q x) f := sorry

theorem frequently.exists {α : Type u} {p : α → Prop} {f : filter α} (hp : filter.frequently (fun (x : α) => p x) f) : ∃ (x : α), p x :=
  decidable.by_contradiction fun (H : ¬∃ (x : α), p x) => hp (eventually_of_forall (iff.mp not_exists H))

theorem eventually.exists {α : Type u} {p : α → Prop} {f : filter α} [ne_bot f] (hp : filter.eventually (fun (x : α) => p x) f) : ∃ (x : α), p x :=
  frequently.exists (eventually.frequently hp)

theorem frequently_iff_forall_eventually_exists_and {α : Type u} {p : α → Prop} {f : filter α} : filter.frequently (fun (x : α) => p x) f ↔
  ∀ {q : α → Prop}, filter.eventually (fun (x : α) => q x) f → ∃ (x : α), p x ∧ q x := sorry

theorem frequently_iff {α : Type u} {f : filter α} {P : α → Prop} : filter.frequently (fun (x : α) => P x) f ↔ ∀ {U : set α}, U ∈ f → ∃ (x : α), ∃ (H : x ∈ U), P x := sorry

@[simp] theorem not_eventually {α : Type u} {p : α → Prop} {f : filter α} : ¬filter.eventually (fun (x : α) => p x) f ↔ filter.frequently (fun (x : α) => ¬p x) f := sorry

@[simp] theorem not_frequently {α : Type u} {p : α → Prop} {f : filter α} : ¬filter.frequently (fun (x : α) => p x) f ↔ filter.eventually (fun (x : α) => ¬p x) f := sorry

@[simp] theorem frequently_true_iff_ne_bot {α : Type u} (f : filter α) : filter.frequently (fun (x : α) => True) f ↔ ne_bot f := sorry

@[simp] theorem frequently_false {α : Type u} (f : filter α) : ¬filter.frequently (fun (x : α) => False) f := sorry

@[simp] theorem frequently_const {α : Type u} {f : filter α} [ne_bot f] {p : Prop} : filter.frequently (fun (x : α) => p) f ↔ p := sorry

@[simp] theorem frequently_or_distrib {α : Type u} {f : filter α} {p : α → Prop} {q : α → Prop} : filter.frequently (fun (x : α) => p x ∨ q x) f ↔
  filter.frequently (fun (x : α) => p x) f ∨ filter.frequently (fun (x : α) => q x) f := sorry

theorem frequently_or_distrib_left {α : Type u} {f : filter α} [ne_bot f] {p : Prop} {q : α → Prop} : filter.frequently (fun (x : α) => p ∨ q x) f ↔ p ∨ filter.frequently (fun (x : α) => q x) f := sorry

theorem frequently_or_distrib_right {α : Type u} {f : filter α} [ne_bot f] {p : α → Prop} {q : Prop} : filter.frequently (fun (x : α) => p x ∨ q) f ↔ filter.frequently (fun (x : α) => p x) f ∨ q := sorry

@[simp] theorem frequently_imp_distrib {α : Type u} {f : filter α} {p : α → Prop} {q : α → Prop} : filter.frequently (fun (x : α) => p x → q x) f ↔
  filter.eventually (fun (x : α) => p x) f → filter.frequently (fun (x : α) => q x) f := sorry

theorem frequently_imp_distrib_left {α : Type u} {f : filter α} [ne_bot f] {p : Prop} {q : α → Prop} : filter.frequently (fun (x : α) => p → q x) f ↔ p → filter.frequently (fun (x : α) => q x) f := sorry

theorem frequently_imp_distrib_right {α : Type u} {f : filter α} [ne_bot f] {p : α → Prop} {q : Prop} : filter.frequently (fun (x : α) => p x → q) f ↔ filter.eventually (fun (x : α) => p x) f → q := sorry

@[simp] theorem eventually_imp_distrib_right {α : Type u} {f : filter α} {p : α → Prop} {q : Prop} : filter.eventually (fun (x : α) => p x → q) f ↔ filter.frequently (fun (x : α) => p x) f → q := sorry

@[simp] theorem frequently_bot {α : Type u} {p : α → Prop} : ¬filter.frequently (fun (x : α) => p x) ⊥ :=
  eq.mpr (id (Eq.trans (propext not_frequently) (propext (iff_true_intro eventually_bot)))) trivial

@[simp] theorem frequently_top {α : Type u} {p : α → Prop} : filter.frequently (fun (x : α) => p x) ⊤ ↔ ∃ (x : α), p x := sorry

@[simp] theorem frequently_principal {α : Type u} {a : set α} {p : α → Prop} : filter.frequently (fun (x : α) => p x) (principal a) ↔ ∃ (x : α), ∃ (H : x ∈ a), p x := sorry

theorem frequently_sup {α : Type u} {p : α → Prop} {f : filter α} {g : filter α} : filter.frequently (fun (x : α) => p x) (f ⊔ g) ↔
  filter.frequently (fun (x : α) => p x) f ∨ filter.frequently (fun (x : α) => p x) g := sorry

@[simp] theorem frequently_Sup {α : Type u} {p : α → Prop} {fs : set (filter α)} : filter.frequently (fun (x : α) => p x) (Sup fs) ↔
  ∃ (f : filter α), ∃ (H : f ∈ fs), filter.frequently (fun (x : α) => p x) f := sorry

@[simp] theorem frequently_supr {α : Type u} {β : Type v} {p : α → Prop} {fs : β → filter α} : filter.frequently (fun (x : α) => p x) (supr fun (b : β) => fs b) ↔
  ∃ (b : β), filter.frequently (fun (x : α) => p x) (fs b) := sorry

/-!
### Relation “eventually equal”
-/

/-- Two functions `f` and `g` are *eventually equal* along a filter `l` if the set of `x` such that
`f x = g x` belongs to `l`. -/
def eventually_eq {α : Type u} {β : Type v} (l : filter α) (f : α → β) (g : α → β)  :=
  filter.eventually (fun (x : α) => f x = g x) l

theorem eventually_eq.eventually {α : Type u} {β : Type v} {l : filter α} {f : α → β} {g : α → β} (h : eventually_eq l f g) : filter.eventually (fun (x : α) => f x = g x) l :=
  h

theorem eventually_eq.rw {α : Type u} {β : Type v} {l : filter α} {f : α → β} {g : α → β} (h : eventually_eq l f g) (p : α → β → Prop) (hf : filter.eventually (fun (x : α) => p x (f x)) l) : filter.eventually (fun (x : α) => p x (g x)) l :=
  eventually.congr hf (eventually.mono h fun (x : α) (hx : f x = g x) => hx ▸ iff.rfl)

theorem eventually_eq_set {α : Type u} {s : set α} {t : set α} {l : filter α} : eventually_eq l s t ↔ filter.eventually (fun (x : α) => x ∈ s ↔ x ∈ t) l :=
  eventually_congr (eventually_of_forall fun (x : α) => { mp := eq.to_iff, mpr := iff.to_eq })

theorem eventually.set_eq {α : Type u} {s : set α} {t : set α} {l : filter α} : filter.eventually (fun (x : α) => x ∈ s ↔ x ∈ t) l → eventually_eq l s t :=
  iff.mpr eventually_eq_set

theorem eventually_eq.exists_mem {α : Type u} {β : Type v} {l : filter α} {f : α → β} {g : α → β} (h : eventually_eq l f g) : ∃ (s : set α), ∃ (H : s ∈ l), set.eq_on f g s :=
  eventually.exists_mem h

theorem eventually_eq_of_mem {α : Type u} {β : Type v} {l : filter α} {f : α → β} {g : α → β} {s : set α} (hs : s ∈ l) (h : set.eq_on f g s) : eventually_eq l f g :=
  eventually_of_mem hs h

theorem eventually_eq_iff_exists_mem {α : Type u} {β : Type v} {l : filter α} {f : α → β} {g : α → β} : eventually_eq l f g ↔ ∃ (s : set α), ∃ (H : s ∈ l), set.eq_on f g s :=
  eventually_iff_exists_mem

theorem eventually_eq.filter_mono {α : Type u} {β : Type v} {l : filter α} {l' : filter α} {f : α → β} {g : α → β} (h₁ : eventually_eq l f g) (h₂ : l' ≤ l) : eventually_eq l' f g :=
  h₂ h₁

theorem eventually_eq.refl {α : Type u} {β : Type v} (l : filter α) (f : α → β) : eventually_eq l f f :=
  eventually_of_forall fun (x : α) => rfl

theorem eventually_eq.rfl {α : Type u} {β : Type v} {l : filter α} {f : α → β} : eventually_eq l f f :=
  eventually_eq.refl l f

theorem eventually_eq.symm {α : Type u} {β : Type v} {f : α → β} {g : α → β} {l : filter α} (H : eventually_eq l f g) : eventually_eq l g f :=
  eventually.mono H fun (_x : α) => Eq.symm

theorem eventually_eq.trans {α : Type u} {β : Type v} {f : α → β} {g : α → β} {h : α → β} {l : filter α} (H₁ : eventually_eq l f g) (H₂ : eventually_eq l g h) : eventually_eq l f h :=
  eventually_eq.rw H₂ (fun (x : α) (y : β) => f x = y) H₁

theorem eventually_eq.prod_mk {α : Type u} {β : Type v} {γ : Type w} {l : filter α} {f : α → β} {f' : α → β} (hf : eventually_eq l f f') {g : α → γ} {g' : α → γ} (hg : eventually_eq l g g') : eventually_eq l (fun (x : α) => (f x, g x)) fun (x : α) => (f' x, g' x) := sorry

theorem eventually_eq.fun_comp {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : α → β} {l : filter α} (H : eventually_eq l f g) (h : β → γ) : eventually_eq l (h ∘ f) (h ∘ g) :=
  eventually.mono H fun (x : α) (hx : f x = g x) => congr_arg h hx

theorem eventually_eq.comp₂ {α : Type u} {β : Type v} {γ : Type w} {δ : Type u_1} {f : α → β} {f' : α → β} {g : α → γ} {g' : α → γ} {l : filter α} (Hf : eventually_eq l f f') (h : β → γ → δ) (Hg : eventually_eq l g g') : eventually_eq l (fun (x : α) => h (f x) (g x)) fun (x : α) => h (f' x) (g' x) :=
  eventually_eq.fun_comp (eventually_eq.prod_mk Hf Hg) (function.uncurry h)

theorem eventually_eq.add {α : Type u} {β : Type v} [Add β] {f : α → β} {f' : α → β} {g : α → β} {g' : α → β} {l : filter α} (h : eventually_eq l f g) (h' : eventually_eq l f' g') : eventually_eq l (fun (x : α) => f x + f' x) fun (x : α) => g x + g' x :=
  eventually_eq.comp₂ h Add.add h'

theorem eventually_eq.neg {α : Type u} {β : Type v} [Neg β] {f : α → β} {g : α → β} {l : filter α} (h : eventually_eq l f g) : eventually_eq l (fun (x : α) => -f x) fun (x : α) => -g x :=
  eventually_eq.fun_comp h Neg.neg

theorem eventually_eq.div {α : Type u} {β : Type v} [group_with_zero β] {f : α → β} {f' : α → β} {g : α → β} {g' : α → β} {l : filter α} (h : eventually_eq l f g) (h' : eventually_eq l f' g') : eventually_eq l (fun (x : α) => f x / f' x) fun (x : α) => g x / g' x := sorry

theorem eventually_eq.sub {α : Type u} {β : Type v} [add_group β] {f : α → β} {f' : α → β} {g : α → β} {g' : α → β} {l : filter α} (h : eventually_eq l f g) (h' : eventually_eq l f' g') : eventually_eq l (fun (x : α) => f x - f' x) fun (x : α) => g x - g' x := sorry

theorem eventually_eq.inter {α : Type u} {s : set α} {t : set α} {s' : set α} {t' : set α} {l : filter α} (h : eventually_eq l s t) (h' : eventually_eq l s' t') : eventually_eq l (s ∩ s') (t ∩ t') :=
  eventually_eq.comp₂ h And h'

theorem eventually_eq.union {α : Type u} {s : set α} {t : set α} {s' : set α} {t' : set α} {l : filter α} (h : eventually_eq l s t) (h' : eventually_eq l s' t') : eventually_eq l (s ∪ s') (t ∪ t') :=
  eventually_eq.comp₂ h Or h'

theorem eventually_eq.compl {α : Type u} {s : set α} {t : set α} {l : filter α} (h : eventually_eq l s t) : eventually_eq l (sᶜ) (tᶜ) :=
  eventually_eq.fun_comp h Not

theorem eventually_eq.diff {α : Type u} {s : set α} {t : set α} {s' : set α} {t' : set α} {l : filter α} (h : eventually_eq l s t) (h' : eventually_eq l s' t') : eventually_eq l (s \ s') (t \ t') :=
  eventually_eq.inter h (eventually_eq.compl h')

theorem eventually_eq_empty {α : Type u} {s : set α} {l : filter α} : eventually_eq l s ∅ ↔ filter.eventually (fun (x : α) => ¬x ∈ s) l := sorry

@[simp] theorem eventually_eq_principal {α : Type u} {β : Type v} {s : set α} {f : α → β} {g : α → β} : eventually_eq (principal s) f g ↔ set.eq_on f g s :=
  iff.rfl

theorem eventually_eq_inf_principal_iff {α : Type u} {β : Type v} {F : filter α} {s : set α} {f : α → β} {g : α → β} : eventually_eq (F ⊓ principal s) f g ↔ filter.eventually (fun (x : α) => x ∈ s → f x = g x) F :=
  eventually_inf_principal

/-- A function `f` is eventually less than or equal to a function `g` at a filter `l`. -/
def eventually_le {α : Type u} {β : Type v} [HasLessEq β] (l : filter α) (f : α → β) (g : α → β)  :=
  filter.eventually (fun (x : α) => f x ≤ g x) l

theorem eventually_le.congr {α : Type u} {β : Type v} [HasLessEq β] {l : filter α} {f : α → β} {f' : α → β} {g : α → β} {g' : α → β} (H : eventually_le l f g) (hf : eventually_eq l f f') (hg : eventually_eq l g g') : eventually_le l f' g' := sorry

theorem eventually_le_congr {α : Type u} {β : Type v} [HasLessEq β] {l : filter α} {f : α → β} {f' : α → β} {g : α → β} {g' : α → β} (hf : eventually_eq l f f') (hg : eventually_eq l g g') : eventually_le l f g ↔ eventually_le l f' g' :=
  { mp := fun (H : eventually_le l f g) => eventually_le.congr H hf hg,
    mpr := fun (H : eventually_le l f' g') => eventually_le.congr H (eventually_eq.symm hf) (eventually_eq.symm hg) }

theorem eventually_eq.le {α : Type u} {β : Type v} [preorder β] {l : filter α} {f : α → β} {g : α → β} (h : eventually_eq l f g) : eventually_le l f g :=
  eventually.mono h fun (x : α) => le_of_eq

theorem eventually_le.refl {α : Type u} {β : Type v} [preorder β] (l : filter α) (f : α → β) : eventually_le l f f :=
  eventually_eq.le eventually_eq.rfl

theorem eventually_le.rfl {α : Type u} {β : Type v} [preorder β] {l : filter α} {f : α → β} : eventually_le l f f :=
  eventually_le.refl l f

theorem eventually_le.trans {α : Type u} {β : Type v} [preorder β] {l : filter α} {f : α → β} {g : α → β} {h : α → β} (H₁ : eventually_le l f g) (H₂ : eventually_le l g h) : eventually_le l f h :=
  eventually.mp H₂ (eventually.mono H₁ fun (x : α) => le_trans)

theorem eventually_eq.trans_le {α : Type u} {β : Type v} [preorder β] {l : filter α} {f : α → β} {g : α → β} {h : α → β} (H₁ : eventually_eq l f g) (H₂ : eventually_le l g h) : eventually_le l f h :=
  eventually_le.trans (eventually_eq.le H₁) H₂

theorem eventually_le.trans_eq {α : Type u} {β : Type v} [preorder β] {l : filter α} {f : α → β} {g : α → β} {h : α → β} (H₁ : eventually_le l f g) (H₂ : eventually_eq l g h) : eventually_le l f h :=
  eventually_le.trans H₁ (eventually_eq.le H₂)

theorem eventually_le.antisymm {α : Type u} {β : Type v} [partial_order β] {l : filter α} {f : α → β} {g : α → β} (h₁ : eventually_le l f g) (h₂ : eventually_le l g f) : eventually_eq l f g :=
  eventually.mp h₂ (eventually.mono h₁ fun (x : α) => le_antisymm)

theorem eventually_le_antisymm_iff {α : Type u} {β : Type v} [partial_order β] {l : filter α} {f : α → β} {g : α → β} : eventually_eq l f g ↔ eventually_le l f g ∧ eventually_le l g f := sorry

theorem eventually_le.le_iff_eq {α : Type u} {β : Type v} [partial_order β] {l : filter α} {f : α → β} {g : α → β} (h : eventually_le l f g) : eventually_le l g f ↔ eventually_eq l g f :=
  { mp := fun (h' : eventually_le l g f) => eventually_le.antisymm h' h, mpr := eventually_eq.le }

theorem eventually_le.inter {α : Type u} {s : set α} {t : set α} {s' : set α} {t' : set α} {l : filter α} (h : eventually_le l s t) (h' : eventually_le l s' t') : eventually_le l (s ∩ s') (t ∩ t') :=
  eventually.mp h' (eventually.mono h fun (x : α) => and.imp)

theorem eventually_le.union {α : Type u} {s : set α} {t : set α} {s' : set α} {t' : set α} {l : filter α} (h : eventually_le l s t) (h' : eventually_le l s' t') : eventually_le l (s ∪ s') (t ∪ t') :=
  eventually.mp h' (eventually.mono h fun (x : α) => or.imp)

theorem eventually_le.compl {α : Type u} {s : set α} {t : set α} {l : filter α} (h : eventually_le l s t) : eventually_le l (tᶜ) (sᶜ) :=
  eventually.mono h fun (x : α) => mt

theorem eventually_le.diff {α : Type u} {s : set α} {t : set α} {s' : set α} {t' : set α} {l : filter α} (h : eventually_le l s t) (h' : eventually_le l t' s') : eventually_le l (s \ s') (t \ t') :=
  eventually_le.inter h (eventually_le.compl h')

theorem join_le {α : Type u} {f : filter (filter α)} {l : filter α} (h : filter.eventually (fun (m : filter α) => m ≤ l) f) : join f ≤ l :=
  fun (s : set α) (hs : s ∈ l) => eventually.mono h fun (m : filter α) (hm : m ≤ l) => hm hs

/-! ### Push-forwards, pull-backs, and the monad structure -/

/-- The forward map of a filter -/
def map {α : Type u} {β : Type v} (m : α → β) (f : filter α) : filter β :=
  mk (set.preimage m ⁻¹' sets f) univ_mem_sets sorry sorry

@[simp] theorem map_principal {α : Type u} {β : Type v} {s : set α} {f : α → β} : map f (principal s) = principal (f '' s) :=
  filter_eq (set.ext fun (a : set β) => iff.symm set.image_subset_iff)

@[simp] theorem eventually_map {α : Type u} {β : Type v} {f : filter α} {m : α → β} {P : β → Prop} : filter.eventually (fun (b : β) => P b) (map m f) ↔ filter.eventually (fun (a : α) => P (m a)) f :=
  iff.rfl

@[simp] theorem frequently_map {α : Type u} {β : Type v} {f : filter α} {m : α → β} {P : β → Prop} : filter.frequently (fun (b : β) => P b) (map m f) ↔ filter.frequently (fun (a : α) => P (m a)) f :=
  iff.rfl

@[simp] theorem mem_map {α : Type u} {β : Type v} {f : filter α} {m : α → β} {t : set β} : t ∈ map m f ↔ (set_of fun (x : α) => m x ∈ t) ∈ f :=
  iff.rfl

theorem image_mem_map {α : Type u} {β : Type v} {f : filter α} {m : α → β} {s : set α} (hs : s ∈ f) : m '' s ∈ map m f :=
  sets_of_superset f hs (set.subset_preimage_image m s)

theorem image_mem_map_iff {α : Type u} {β : Type v} {f : filter α} {m : α → β} {s : set α} (hf : function.injective m) : m '' s ∈ map m f ↔ s ∈ f :=
  { mp :=
      fun (h : m '' s ∈ map m f) => eq.mpr (id (Eq._oldrec (Eq.refl (s ∈ f)) (Eq.symm (set.preimage_image_eq s hf)))) h,
    mpr := image_mem_map }

theorem range_mem_map {α : Type u} {β : Type v} {f : filter α} {m : α → β} : set.range m ∈ map m f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (set.range m ∈ map m f)) (Eq.symm set.image_univ))) (image_mem_map univ_mem_sets)

theorem mem_map_sets_iff {α : Type u} {β : Type v} {f : filter α} {m : α → β} {t : set β} : t ∈ map m f ↔ ∃ (s : set α), ∃ (H : s ∈ f), m '' s ⊆ t := sorry

@[simp] theorem map_id {α : Type u} {f : filter α} : map id f = f :=
  filter_eq rfl

@[simp] theorem map_id' {α : Type u} {f : filter α} : map (fun (x : α) => x) f = f :=
  map_id

@[simp] theorem map_compose {α : Type u} {β : Type v} {γ : Type w} {m : α → β} {m' : β → γ} : map m' ∘ map m = map (m' ∘ m) :=
  funext fun (_x : filter α) => filter_eq rfl

@[simp] theorem map_map {α : Type u} {β : Type v} {γ : Type w} {f : filter α} {m : α → β} {m' : β → γ} : map m' (map m f) = map (m' ∘ m) f :=
  congr_fun map_compose f

/-- If functions `m₁` and `m₂` are eventually equal at a filter `f`, then
they map this filter to the same filter. -/
theorem map_congr {α : Type u} {β : Type v} {m₁ : α → β} {m₂ : α → β} {f : filter α} (h : eventually_eq f m₁ m₂) : map m₁ f = map m₂ f := sorry

/-- The inverse map of a filter -/
def comap {α : Type u} {β : Type v} (m : α → β) (f : filter β) : filter α :=
  mk (set_of fun (s : set α) => ∃ (t : set β), ∃ (H : t ∈ f), m ⁻¹' t ⊆ s) sorry sorry sorry

@[simp] theorem eventually_comap {α : Type u} {β : Type v} {f : filter β} {φ : α → β} {P : α → Prop} : filter.eventually (fun (a : α) => P a) (comap φ f) ↔ filter.eventually (fun (b : β) => ∀ (a : α), φ a = b → P a) f := sorry

@[simp] theorem frequently_comap {α : Type u} {β : Type v} {f : filter β} {φ : α → β} {P : α → Prop} : filter.frequently (fun (a : α) => P a) (comap φ f) ↔ filter.frequently (fun (b : β) => ∃ (a : α), φ a = b ∧ P a) f := sorry

/-- The monadic bind operation on filter is defined the usual way in terms of `map` and `join`.

Unfortunately, this `bind` does not result in the expected applicative. See `filter.seq` for the
applicative instance. -/
def bind {α : Type u} {β : Type v} (f : filter α) (m : α → filter β) : filter β :=
  join (map m f)

/-- The applicative sequentiation operation. This is not induced by the bind operation. -/
def seq {α : Type u} {β : Type v} (f : filter (α → β)) (g : filter α) : filter β :=
  mk
    (set_of
      fun (s : set β) =>
        ∃ (u : set (α → β)),
          ∃ (H : u ∈ f), ∃ (t : set α), ∃ (H : t ∈ g), ∀ (m : α → β), m ∈ u → ∀ (x : α), x ∈ t → m x ∈ s)
    sorry sorry sorry

/-- `pure x` is the set of sets that contain `x`. It is equal to `𝓟 {x}` but
with this definition we have `s ∈ pure a` defeq `a ∈ s`. -/
protected instance has_pure : Pure filter :=
  { pure := fun (α : Type u) (x : α) => mk (set_of fun (s : set α) => x ∈ s) trivial sorry sorry }

protected instance has_bind : Bind filter :=
  { bind := bind }

protected instance has_seq : Seq filter :=
  { seq := seq }

protected instance functor : Functor filter :=
  { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β }

theorem pure_sets {α : Type u} (a : α) : sets (pure a) = set_of fun (s : set α) => a ∈ s :=
  rfl

@[simp] theorem mem_pure_sets {α : Type u} {a : α} {s : set α} : s ∈ pure a ↔ a ∈ s :=
  iff.rfl

@[simp] theorem eventually_pure {α : Type u} {a : α} {p : α → Prop} : filter.eventually (fun (x : α) => p x) (pure a) ↔ p a :=
  iff.rfl

@[simp] theorem principal_singleton {α : Type u} (a : α) : principal (singleton a) = pure a := sorry

@[simp] theorem map_pure {α : Type u} {β : Type v} (f : α → β) (a : α) : map f (pure a) = pure (f a) :=
  rfl

@[simp] theorem join_pure {α : Type u} (f : filter α) : join (pure f) = f :=
  filter.ext fun (s : set α) => iff.rfl

@[simp] theorem pure_bind {α : Type u} {β : Type v} (a : α) (m : α → filter β) : bind (pure a) m = m a := sorry

-- this section needs to be before applicative, otherwise the wrong instance will be chosen

/-- The monad structure on filters. -/
protected def monad : Monad filter :=
  { toApplicative :=
      { toFunctor := { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β },
        toPure := filter.has_pure,
        toSeq :=
          { seq :=
              fun (α β : Type u_1) (f : filter (α → β)) (x : filter α) =>
                do 
                  let _x ← f 
                  map _x x },
        toSeqLeft :=
          { seqLeft :=
              fun (α β : Type u_1) (a : filter α) (b : filter β) =>
                (fun (α β : Type u_1) (f : filter (α → β)) (x : filter α) =>
                    do 
                      let _x ← f 
                      map _x x)
                  β α (map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : filter α) (b : filter β) =>
                (fun (α β : Type u_1) (f : filter (α → β)) (x : filter α) =>
                    do 
                      let _x ← f 
                      map _x x)
                  β β (map (function.const α id) a) b } },
    toBind := filter.has_bind }

protected theorem is_lawful_monad : is_lawful_monad filter :=
  is_lawful_monad.mk (fun (α β : Type u_1) => pure_bind)
    fun (α β γ : Type u_1) (f : filter α) (m₁ : α → filter β) (m₂ : β → filter γ) => filter_eq rfl

protected instance applicative : Applicative filter :=
  { toFunctor := { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β }, toPure := filter.has_pure,
    toSeq := { seq := seq },
    toSeqLeft := { seqLeft := fun (α β : Type u_1) (a : filter α) (b : filter β) => seq (map (function.const β) a) b },
    toSeqRight :=
      { seqRight := fun (α β : Type u_1) (a : filter α) (b : filter β) => seq (map (function.const α id) a) b } }

protected instance alternative : alternative filter :=
  alternative.mk fun (α : Type u_1) => ⊥

@[simp] theorem map_def {α : Type u_1} {β : Type u_1} (m : α → β) (f : filter α) : m <$> f = map m f :=
  rfl

@[simp] theorem bind_def {α : Type u_1} {β : Type u_1} (f : filter α) (m : α → filter β) : f >>= m = bind f m :=
  rfl

/- map and comap equations -/

@[simp] theorem mem_comap_sets {α : Type u} {β : Type v} {g : filter β} {m : α → β} {s : set α} : s ∈ comap m g ↔ ∃ (t : set β), ∃ (H : t ∈ g), m ⁻¹' t ⊆ s :=
  iff.rfl

theorem preimage_mem_comap {α : Type u} {β : Type v} {g : filter β} {m : α → β} {t : set β} (ht : t ∈ g) : m ⁻¹' t ∈ comap m g :=
  Exists.intro t (Exists.intro ht (set.subset.refl (m ⁻¹' t)))

theorem comap_id {α : Type u} {f : filter α} : comap id f = f := sorry

theorem comap_const_of_not_mem {α : Type u} {x : α} {f : filter α} {V : set α} (hV : V ∈ f) (hx : ¬x ∈ V) : comap (fun (y : α) => x) f = ⊥ := sorry

theorem comap_const_of_mem {α : Type u} {x : α} {f : filter α} (h : ∀ (V : set α), V ∈ f → x ∈ V) : comap (fun (y : α) => x) f = ⊤ := sorry

theorem comap_comap {α : Type u} {β : Type v} {γ : Type w} {f : filter α} {m : γ → β} {n : β → α} : comap m (comap n f) = comap (n ∘ m) f := sorry

@[simp] theorem comap_principal {α : Type u} {β : Type v} {m : α → β} {t : set β} : comap m (principal t) = principal (m ⁻¹' t) := sorry

@[simp] theorem comap_pure {α : Type u} {β : Type v} {m : α → β} {b : β} : comap m (pure b) = principal (m ⁻¹' singleton b) := sorry

theorem map_le_iff_le_comap {α : Type u} {β : Type v} {f : filter α} {g : filter β} {m : α → β} : map m f ≤ g ↔ f ≤ comap m g := sorry

theorem gc_map_comap {α : Type u} {β : Type v} (m : α → β) : galois_connection (map m) (comap m) :=
  fun (f : filter α) (g : filter β) => map_le_iff_le_comap

theorem map_mono {α : Type u} {β : Type v} {m : α → β} : monotone (map m) :=
  galois_connection.monotone_l (gc_map_comap m)

theorem comap_mono {α : Type u} {β : Type v} {m : α → β} : monotone (comap m) :=
  galois_connection.monotone_u (gc_map_comap m)

@[simp] theorem map_bot {α : Type u} {β : Type v} {m : α → β} : map m ⊥ = ⊥ :=
  galois_connection.l_bot (gc_map_comap m)

@[simp] theorem map_sup {α : Type u} {β : Type v} {f₁ : filter α} {f₂ : filter α} {m : α → β} : map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂ :=
  galois_connection.l_sup (gc_map_comap m)

@[simp] theorem map_supr {α : Type u} {β : Type v} {ι : Sort x} {m : α → β} {f : ι → filter α} : map m (supr fun (i : ι) => f i) = supr fun (i : ι) => map m (f i) :=
  galois_connection.l_supr (gc_map_comap m)

@[simp] theorem comap_top {α : Type u} {β : Type v} {m : α → β} : comap m ⊤ = ⊤ :=
  galois_connection.u_top (gc_map_comap m)

@[simp] theorem comap_inf {α : Type u} {β : Type v} {g₁ : filter β} {g₂ : filter β} {m : α → β} : comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂ :=
  galois_connection.u_inf (gc_map_comap m)

@[simp] theorem comap_infi {α : Type u} {β : Type v} {ι : Sort x} {m : α → β} {f : ι → filter β} : comap m (infi fun (i : ι) => f i) = infi fun (i : ι) => comap m (f i) :=
  galois_connection.u_infi (gc_map_comap m)

theorem le_comap_top {α : Type u} {β : Type v} (f : α → β) (l : filter α) : l ≤ comap f ⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (l ≤ comap f ⊤)) comap_top)) le_top

theorem map_comap_le {α : Type u} {β : Type v} {g : filter β} {m : α → β} : map m (comap m g) ≤ g :=
  galois_connection.l_u_le (gc_map_comap m) g

theorem le_comap_map {α : Type u} {β : Type v} {f : filter α} {m : α → β} : f ≤ comap m (map m f) :=
  galois_connection.le_u_l (gc_map_comap m) f

@[simp] theorem comap_bot {α : Type u} {β : Type v} {m : α → β} : comap m ⊥ = ⊥ := sorry

theorem comap_supr {α : Type u} {β : Type v} {ι : Sort u_1} {f : ι → filter β} {m : α → β} : comap m (supr f) = supr fun (i : ι) => comap m (f i) := sorry

theorem comap_Sup {α : Type u} {β : Type v} {s : set (filter β)} {m : α → β} : comap m (Sup s) = supr fun (f : filter β) => supr fun (H : f ∈ s) => comap m f := sorry

theorem comap_sup {α : Type u} {β : Type v} {g₁ : filter β} {g₂ : filter β} {m : α → β} : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂ := sorry

theorem map_comap {α : Type u} {β : Type v} {f : filter β} {m : α → β} (hf : set.range m ∈ f) : map m (comap m f) = f := sorry

theorem image_mem_sets {α : Type u} {β : Type v} {f : filter α} {c : β → α} (h : set.range c ∈ f) {W : set β} (W_in : W ∈ comap c f) : c '' W ∈ f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (c '' W ∈ f)) (Eq.symm (map_comap h)))) (image_mem_map W_in)

theorem image_coe_mem_sets {α : Type u} {f : filter α} {U : set α} (h : U ∈ f) {W : set ↥U} (W_in : W ∈ comap coe f) : coe '' W ∈ f := sorry

theorem comap_map {α : Type u} {β : Type v} {f : filter α} {m : α → β} (h : function.injective m) : comap m (map m f) = f := sorry

theorem mem_comap_iff {α : Type u} {β : Type v} {f : filter β} {m : α → β} (inj : function.injective m) (large : set.range m ∈ f) {S : set α} : S ∈ comap m f ↔ m '' S ∈ f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (S ∈ comap m f ↔ m '' S ∈ f)) (Eq.symm (propext (image_mem_map_iff inj)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (m '' S ∈ map m (comap m f) ↔ m '' S ∈ f)) (map_comap large)))
      (iff.refl (m '' S ∈ f)))

theorem le_of_map_le_map_inj' {α : Type u} {β : Type v} {f : filter α} {g : filter α} {m : α → β} {s : set α} (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → m x = m y → x = y) (h : map m f ≤ map m g) : f ≤ g := sorry

theorem le_of_map_le_map_inj_iff {α : Type u} {β : Type v} {f : filter α} {g : filter α} {m : α → β} {s : set α} (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → m x = m y → x = y) : map m f ≤ map m g ↔ f ≤ g :=
  { mp := le_of_map_le_map_inj' hsf hsg hm, mpr := fun (h : f ≤ g) => map_mono h }

theorem eq_of_map_eq_map_inj' {α : Type u} {β : Type v} {f : filter α} {g : filter α} {m : α → β} {s : set α} (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → m x = m y → x = y) (h : map m f = map m g) : f = g :=
  le_antisymm (le_of_map_le_map_inj' hsf hsg hm (le_of_eq h)) (le_of_map_le_map_inj' hsg hsf hm (le_of_eq (Eq.symm h)))

theorem map_inj {α : Type u} {β : Type v} {f : filter α} {g : filter α} {m : α → β} (hm : ∀ (x y : α), m x = m y → x = y) (h : map m f = map m g) : f = g := sorry

theorem le_map_comap_of_surjective' {α : Type u} {β : Type v} {f : α → β} {l : filter β} {u : set β} (ul : u ∈ l) (hf : ∀ (y : β), y ∈ u → ∃ (x : α), f x = y) : l ≤ map f (comap f l) := sorry

theorem map_comap_of_surjective' {α : Type u} {β : Type v} {f : α → β} {l : filter β} {u : set β} (ul : u ∈ l) (hf : ∀ (y : β), y ∈ u → ∃ (x : α), f x = y) : map f (comap f l) = l :=
  le_antisymm map_comap_le (le_map_comap_of_surjective' ul hf)

theorem le_map_comap_of_surjective {α : Type u} {β : Type v} {f : α → β} (hf : function.surjective f) (l : filter β) : l ≤ map f (comap f l) :=
  le_map_comap_of_surjective' univ_mem_sets fun (y : β) (_x : y ∈ set.univ) => hf y

theorem map_comap_of_surjective {α : Type u} {β : Type v} {f : α → β} (hf : function.surjective f) (l : filter β) : map f (comap f l) = l :=
  le_antisymm map_comap_le (le_map_comap_of_surjective hf l)

theorem subtype_coe_map_comap {α : Type u} (s : set α) (f : filter α) : map coe (comap coe f) = f ⊓ principal s := sorry

theorem subtype_coe_map_comap_prod {α : Type u} (s : set α) (f : filter (α × α)) : map coe (comap coe f) = f ⊓ principal (set.prod s s) := sorry

theorem comap_ne_bot_iff {α : Type u} {β : Type v} {f : filter β} {m : α → β} : ne_bot (comap m f) ↔ ∀ (t : set β), t ∈ f → ∃ (a : α), m a ∈ t := sorry

theorem comap_ne_bot {α : Type u} {β : Type v} {f : filter β} {m : α → β} (hm : ∀ (t : set β), t ∈ f → ∃ (a : α), m a ∈ t) : ne_bot (comap m f) :=
  iff.mpr comap_ne_bot_iff hm

theorem comap_ne_bot_iff_frequently {α : Type u} {β : Type v} {f : filter β} {m : α → β} : ne_bot (comap m f) ↔ filter.frequently (fun (y : β) => y ∈ set.range m) f := sorry

theorem comap_ne_bot_iff_compl_range {α : Type u} {β : Type v} {f : filter β} {m : α → β} : ne_bot (comap m f) ↔ ¬set.range mᶜ ∈ f :=
  comap_ne_bot_iff_frequently

theorem ne_bot.comap_of_range_mem {α : Type u} {β : Type v} {f : filter β} {m : α → β} (hf : ne_bot f) (hm : set.range m ∈ f) : ne_bot (comap m f) :=
  iff.mpr comap_ne_bot_iff_frequently (eventually.frequently hm)

theorem comap_inf_principal_ne_bot_of_image_mem {α : Type u} {β : Type v} {f : filter β} {m : α → β} (hf : ne_bot f) {s : set α} (hs : m '' s ∈ f) : ne_bot (comap m f ⊓ principal s) := sorry

theorem ne_bot.comap_of_surj {α : Type u} {β : Type v} {f : filter β} {m : α → β} (hf : ne_bot f) (hm : function.surjective m) : ne_bot (comap m f) :=
  ne_bot.comap_of_range_mem hf (univ_mem_sets' hm)

theorem ne_bot.comap_of_image_mem {α : Type u} {β : Type v} {f : filter β} {m : α → β} (hf : ne_bot f) {s : set α} (hs : m '' s ∈ f) : ne_bot (comap m f) :=
  ne_bot.comap_of_range_mem hf (mem_sets_of_superset hs (set.image_subset_range m s))

@[simp] theorem map_eq_bot_iff {α : Type u} {β : Type v} {f : filter α} {m : α → β} : map m f = ⊥ ↔ f = ⊥ := sorry

theorem map_ne_bot_iff {α : Type u} {β : Type v} (f : α → β) {F : filter α} : ne_bot (map f F) ↔ ne_bot F :=
  not_congr map_eq_bot_iff

theorem ne_bot.map {α : Type u} {β : Type v} {f : filter α} (hf : ne_bot f) (m : α → β) : ne_bot (map m f) :=
  iff.mpr (map_ne_bot_iff m) hf

protected instance map_ne_bot {α : Type u} {β : Type v} {f : filter α} {m : α → β} [hf : ne_bot f] : ne_bot (map m f) :=
  ne_bot.map hf m

theorem sInter_comap_sets {α : Type u} {β : Type v} (f : α → β) (F : filter β) : ⋂₀sets (comap f F) = set.Inter fun (U : set β) => set.Inter fun (H : U ∈ F) => f ⁻¹' U := sorry

-- this is a generic rule for monotone functions:

theorem map_infi_le {α : Type u} {β : Type v} {ι : Sort x} {f : ι → filter α} {m : α → β} : map m (infi f) ≤ infi fun (i : ι) => map m (f i) :=
  le_infi fun (i : ι) => map_mono (infi_le f i)

theorem map_infi_eq {α : Type u} {β : Type v} {ι : Sort x} {f : ι → filter α} {m : α → β} (hf : directed ge f) [Nonempty ι] : map m (infi f) = infi fun (i : ι) => map m (f i) := sorry

theorem map_binfi_eq {α : Type u} {β : Type v} {ι : Type w} {f : ι → filter α} {m : α → β} {p : ι → Prop} (h : directed_on (f ⁻¹'o ge) (set_of fun (x : ι) => p x)) (ne : ∃ (x : ι), p x) : map m (infi fun (i : ι) => infi fun (h : p i) => f i) = infi fun (i : ι) => infi fun (h : p i) => map m (f i) := sorry

theorem map_inf_le {α : Type u} {β : Type v} {f : filter α} {g : filter α} {m : α → β} : map m (f ⊓ g) ≤ map m f ⊓ map m g :=
  monotone.map_inf_le map_mono f g

theorem map_inf' {α : Type u} {β : Type v} {f : filter α} {g : filter α} {m : α → β} {t : set α} (htf : t ∈ f) (htg : t ∈ g) (h : ∀ (x : α), x ∈ t → ∀ (y : α), y ∈ t → m x = m y → x = y) : map m (f ⊓ g) = map m f ⊓ map m g := sorry

theorem map_inf {α : Type u} {β : Type v} {f : filter α} {g : filter α} {m : α → β} (h : function.injective m) : map m (f ⊓ g) = map m f ⊓ map m g :=
  map_inf' univ_mem_sets univ_mem_sets
    fun (x : α) (_x : x ∈ set.univ) (y : α) (_x : y ∈ set.univ) (hxy : m x = m y) => h hxy

theorem map_eq_comap_of_inverse {α : Type u} {β : Type v} {f : filter α} {m : α → β} {n : β → α} (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) : map m f = comap n f := sorry

theorem map_swap_eq_comap_swap {α : Type u} {β : Type v} {f : filter (α × β)} : prod.swap <$> f = comap prod.swap f :=
  map_eq_comap_of_inverse prod.swap_swap_eq prod.swap_swap_eq

theorem le_map {α : Type u} {β : Type v} {f : filter α} {m : α → β} {g : filter β} (h : ∀ (s : set α), s ∈ f → m '' s ∈ g) : g ≤ map m f :=
  fun (s : set β) (hs : s ∈ map m f) => mem_sets_of_superset (h (m ⁻¹' s) hs) (set.image_preimage_subset m s)

protected theorem push_pull {α : Type u} {β : Type v} (f : α → β) (F : filter α) (G : filter β) : map f (F ⊓ comap f G) = map f F ⊓ G := sorry

protected theorem push_pull' {α : Type u} {β : Type v} (f : α → β) (F : filter α) (G : filter β) : map f (comap f G ⊓ F) = G ⊓ map f F := sorry

theorem singleton_mem_pure_sets {α : Type u} {a : α} : singleton a ∈ pure a :=
  set.mem_singleton a

theorem pure_injective {α : Type u} : function.injective pure :=
  fun (a b : α) (hab : pure a = pure b) => iff.mp (iff.mp filter.ext_iff hab (set_of fun (x : α) => a = x)) rfl

protected instance pure_ne_bot {α : Type u} {a : α} : ne_bot (pure a) :=
  mt (iff.mpr empty_in_sets_eq_bot) (set.not_mem_empty a)

@[simp] theorem le_pure_iff {α : Type u} {f : filter α} {a : α} : f ≤ pure a ↔ singleton a ∈ f := sorry

theorem mem_seq_sets_def {α : Type u} {β : Type v} {f : filter (α → β)} {g : filter α} {s : set β} : s ∈ seq f g ↔
  ∃ (u : set (α → β)), ∃ (H : u ∈ f), ∃ (t : set α), ∃ (H : t ∈ g), ∀ (x : α → β), x ∈ u → ∀ (y : α), y ∈ t → x y ∈ s :=
  iff.rfl

theorem mem_seq_sets_iff {α : Type u} {β : Type v} {f : filter (α → β)} {g : filter α} {s : set β} : s ∈ seq f g ↔ ∃ (u : set (α → β)), ∃ (H : u ∈ f), ∃ (t : set α), ∃ (H : t ∈ g), set.seq u t ⊆ s := sorry

theorem mem_map_seq_iff {α : Type u} {β : Type v} {γ : Type w} {f : filter α} {g : filter β} {m : α → β → γ} {s : set γ} : s ∈ seq (map m f) g ↔ ∃ (t : set β), ∃ (u : set α), t ∈ g ∧ u ∈ f ∧ ∀ (x : α), x ∈ u → ∀ (y : β), y ∈ t → m x y ∈ s := sorry

theorem seq_mem_seq_sets {α : Type u} {β : Type v} {f : filter (α → β)} {g : filter α} {s : set (α → β)} {t : set α} (hs : s ∈ f) (ht : t ∈ g) : set.seq s t ∈ seq f g := sorry

theorem le_seq {α : Type u} {β : Type v} {f : filter (α → β)} {g : filter α} {h : filter β} (hh : ∀ (t : set (α → β)), t ∈ f → ∀ (u : set α), u ∈ g → set.seq t u ∈ h) : h ≤ seq f g := sorry

theorem seq_mono {α : Type u} {β : Type v} {f₁ : filter (α → β)} {f₂ : filter (α → β)} {g₁ : filter α} {g₂ : filter α} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : seq f₁ g₁ ≤ seq f₂ g₂ :=
  le_seq fun (s : set (α → β)) (hs : s ∈ f₂) (t : set α) (ht : t ∈ g₂) => seq_mem_seq_sets (hf hs) (hg ht)

@[simp] theorem pure_seq_eq_map {α : Type u} {β : Type v} (g : α → β) (f : filter α) : seq (pure g) f = map g f := sorry

@[simp] theorem seq_pure {α : Type u} {β : Type v} (f : filter (α → β)) (a : α) : seq f (pure a) = map (fun (g : α → β) => g a) f := sorry

@[simp] theorem seq_assoc {α : Type u} {β : Type v} {γ : Type w} (x : filter α) (g : filter (α → β)) (h : filter (β → γ)) : seq h (seq g x) = seq (seq (map function.comp h) g) x := sorry

theorem prod_map_seq_comm {α : Type u} {β : Type v} (f : filter α) (g : filter β) : seq (map Prod.mk f) g = seq (map (fun (b : β) (a : α) => (a, b)) g) f := sorry

protected instance is_lawful_functor : is_lawful_functor filter :=
  is_lawful_functor.mk (fun (α : Type u) (f : filter α) => map_id)
    fun (α β γ : Type u) (f : α → β) (g : β → γ) (a : filter α) => Eq.symm map_map

protected instance is_lawful_applicative : is_lawful_applicative filter :=
  is_lawful_applicative.mk (fun (α β : Type u) => pure_seq_eq_map) (fun (α β : Type u) => map_pure)
    (fun (α β : Type u) => seq_pure) fun (α β γ : Type u) => seq_assoc

protected instance is_comm_applicative : is_comm_applicative filter :=
  is_comm_applicative.mk fun (α β : Type u) (f : filter α) (g : filter β) => prod_map_seq_comm f g

theorem seq_eq_filter_seq {α : Type l} {β : Type l} (f : filter (α → β)) (g : filter α) : f <*> g = seq f g :=
  rfl

/- bind equations -/

@[simp] theorem eventually_bind {α : Type u} {β : Type v} {f : filter α} {m : α → filter β} {p : β → Prop} : filter.eventually (fun (y : β) => p y) (bind f m) ↔
  filter.eventually (fun (x : α) => filter.eventually (fun (y : β) => p y) (m x)) f :=
  iff.rfl

@[simp] theorem eventually_eq_bind {α : Type u} {β : Type v} {γ : Type w} {f : filter α} {m : α → filter β} {g₁ : β → γ} {g₂ : β → γ} : eventually_eq (bind f m) g₁ g₂ ↔ filter.eventually (fun (x : α) => eventually_eq (m x) g₁ g₂) f :=
  iff.rfl

@[simp] theorem eventually_le_bind {α : Type u} {β : Type v} {γ : Type w} [HasLessEq γ] {f : filter α} {m : α → filter β} {g₁ : β → γ} {g₂ : β → γ} : eventually_le (bind f m) g₁ g₂ ↔ filter.eventually (fun (x : α) => eventually_le (m x) g₁ g₂) f :=
  iff.rfl

theorem mem_bind_sets' {α : Type u} {β : Type v} {s : set β} {f : filter α} {m : α → filter β} : s ∈ bind f m ↔ (set_of fun (a : α) => s ∈ m a) ∈ f :=
  iff.rfl

@[simp] theorem mem_bind_sets {α : Type u} {β : Type v} {s : set β} {f : filter α} {m : α → filter β} : s ∈ bind f m ↔ ∃ (t : set α), ∃ (H : t ∈ f), ∀ (x : α), x ∈ t → s ∈ m x :=
  iff.trans (iff.trans iff.rfl (iff.symm exists_sets_subset_iff)) iff.rfl

theorem bind_le {α : Type u} {β : Type v} {f : filter α} {g : α → filter β} {l : filter β} (h : filter.eventually (fun (x : α) => g x ≤ l) f) : bind f g ≤ l :=
  join_le (iff.mpr eventually_map h)

theorem bind_mono {α : Type u} {β : Type v} {f₁ : filter α} {f₂ : filter α} {g₁ : α → filter β} {g₂ : α → filter β} (hf : f₁ ≤ f₂) (hg : eventually_le f₁ g₁ g₂) : bind f₁ g₁ ≤ bind f₂ g₂ := sorry

theorem bind_inf_principal {α : Type u} {β : Type v} {f : filter α} {g : α → filter β} {s : set β} : (bind f fun (x : α) => g x ⊓ principal s) = bind f g ⊓ principal s := sorry

theorem sup_bind {α : Type u} {β : Type v} {f : filter α} {g : filter α} {h : α → filter β} : bind (f ⊔ g) h = bind f h ⊔ bind g h := sorry

theorem principal_bind {α : Type u} {β : Type v} {s : set α} {f : α → filter β} : bind (principal s) f = supr fun (x : α) => supr fun (H : x ∈ s) => f x := sorry

/- This is a separate section in order to open `list`, but mostly because of universe
   equality requirements in `traverse` -/

theorem sequence_mono {α : Type u} (as : List (filter α)) (bs : List (filter α)) : list.forall₂ LessEq as bs → sequence as ≤ sequence bs := sorry

theorem mem_traverse_sets {α' : Type u} {β' : Type u} {γ' : Type u} {f : β' → filter α'} {s : γ' → set α'} (fs : List β') (us : List γ') : list.forall₂ (fun (b : β') (c : γ') => s c ∈ f b) fs us → traverse s us ∈ traverse f fs := sorry

theorem mem_traverse_sets_iff {α' : Type u} {β' : Type u} {f : β' → filter α'} (fs : List β') (t : set (List α')) : t ∈ traverse f fs ↔ ∃ (us : List (set α')), list.forall₂ (fun (b : β') (s : set α') => s ∈ f b) fs us ∧ sequence us ⊆ t := sorry

/-! ### Limits -/

/-- `tendsto` is the generic "limit of a function" predicate.
  `tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
def tendsto {α : Type u} {β : Type v} (f : α → β) (l₁ : filter α) (l₂ : filter β)  :=
  map f l₁ ≤ l₂

theorem tendsto_def {α : Type u} {β : Type v} {f : α → β} {l₁ : filter α} {l₂ : filter β} : tendsto f l₁ l₂ ↔ ∀ (s : set β), s ∈ l₂ → f ⁻¹' s ∈ l₁ :=
  iff.rfl

theorem tendsto_iff_eventually {α : Type u} {β : Type v} {f : α → β} {l₁ : filter α} {l₂ : filter β} : tendsto f l₁ l₂ ↔
  ∀ {p : β → Prop}, filter.eventually (fun (y : β) => p y) l₂ → filter.eventually (fun (x : α) => p (f x)) l₁ :=
  iff.rfl

theorem tendsto.eventually {α : Type u} {β : Type v} {f : α → β} {l₁ : filter α} {l₂ : filter β} {p : β → Prop} (hf : tendsto f l₁ l₂) (h : filter.eventually (fun (y : β) => p y) l₂) : filter.eventually (fun (x : α) => p (f x)) l₁ :=
  hf h

theorem tendsto.frequently {α : Type u} {β : Type v} {f : α → β} {l₁ : filter α} {l₂ : filter β} {p : β → Prop} (hf : tendsto f l₁ l₂) (h : filter.frequently (fun (x : α) => p (f x)) l₁) : filter.frequently (fun (y : β) => p y) l₂ :=
  mt (tendsto.eventually hf) h

@[simp] theorem tendsto_bot {α : Type u} {β : Type v} {f : α → β} {l : filter β} : tendsto f ⊥ l := sorry

@[simp] theorem tendsto_top {α : Type u} {β : Type v} {f : α → β} {l : filter α} : tendsto f l ⊤ :=
  le_top

theorem le_map_of_right_inverse {α : Type u} {β : Type v} {mab : α → β} {mba : β → α} {f : filter α} {g : filter β} (h₁ : eventually_eq g (mab ∘ mba) id) (h₂ : tendsto mba g f) : g ≤ map mab f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (g ≤ map mab f)) (Eq.symm map_id)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (map id g ≤ map mab f)) (Eq.symm (map_congr h₁))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (map (mab ∘ mba) g ≤ map mab f)) (Eq.symm map_map))) (map_mono h₂)))

theorem tendsto_of_not_nonempty {α : Type u} {β : Type v} {f : α → β} {la : filter α} {lb : filter β} (h : ¬Nonempty α) : tendsto f la lb := sorry

theorem eventually_eq_of_left_inv_of_right_inv {α : Type u} {β : Type v} {f : α → β} {g₁ : β → α} {g₂ : β → α} {fa : filter α} {fb : filter β} (hleft : filter.eventually (fun (x : α) => g₁ (f x) = x) fa) (hright : filter.eventually (fun (y : β) => f (g₂ y) = y) fb) (htendsto : tendsto g₂ fb fa) : eventually_eq fb g₁ g₂ :=
  eventually.mp (tendsto.eventually htendsto hleft)
    (eventually.mono hright
      fun (y : β) (hr : f (g₂ y) = y) (hl : g₁ (f (g₂ y)) = g₂ y) => Eq.trans (congr_arg g₁ (Eq.symm hr)) hl)

theorem tendsto_iff_comap {α : Type u} {β : Type v} {f : α → β} {l₁ : filter α} {l₂ : filter β} : tendsto f l₁ l₂ ↔ l₁ ≤ comap f l₂ :=
  map_le_iff_le_comap

theorem tendsto.le_comap {α : Type u} {β : Type v} {f : α → β} {l₁ : filter α} {l₂ : filter β} : tendsto f l₁ l₂ → l₁ ≤ comap f l₂ :=
  iff.mp tendsto_iff_comap

theorem tendsto_congr' {α : Type u} {β : Type v} {f₁ : α → β} {f₂ : α → β} {l₁ : filter α} {l₂ : filter β} (hl : eventually_eq l₁ f₁ f₂) : tendsto f₁ l₁ l₂ ↔ tendsto f₂ l₁ l₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (tendsto f₁ l₁ l₂ ↔ tendsto f₂ l₁ l₂)) (tendsto.equations._eqn_1 f₁ l₁ l₂)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (map f₁ l₁ ≤ l₂ ↔ tendsto f₂ l₁ l₂)) (tendsto.equations._eqn_1 f₂ l₁ l₂)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (map f₁ l₁ ≤ l₂ ↔ map f₂ l₁ ≤ l₂)) (map_congr hl))) (iff.refl (map f₂ l₁ ≤ l₂))))

theorem tendsto.congr' {α : Type u} {β : Type v} {f₁ : α → β} {f₂ : α → β} {l₁ : filter α} {l₂ : filter β} (hl : eventually_eq l₁ f₁ f₂) (h : tendsto f₁ l₁ l₂) : tendsto f₂ l₁ l₂ :=
  iff.mp (tendsto_congr' hl) h

theorem tendsto_congr {α : Type u} {β : Type v} {f₁ : α → β} {f₂ : α → β} {l₁ : filter α} {l₂ : filter β} (h : ∀ (x : α), f₁ x = f₂ x) : tendsto f₁ l₁ l₂ ↔ tendsto f₂ l₁ l₂ :=
  tendsto_congr' (univ_mem_sets' h)

theorem tendsto.congr {α : Type u} {β : Type v} {f₁ : α → β} {f₂ : α → β} {l₁ : filter α} {l₂ : filter β} (h : ∀ (x : α), f₁ x = f₂ x) : tendsto f₁ l₁ l₂ → tendsto f₂ l₁ l₂ :=
  iff.mp (tendsto_congr h)

theorem tendsto_id' {α : Type u} {x : filter α} {y : filter α} : x ≤ y → tendsto id x y := sorry

theorem tendsto_id {α : Type u} {x : filter α} : tendsto id x x :=
  tendsto_id' (le_refl x)

theorem tendsto.comp {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : β → γ} {x : filter α} {y : filter β} {z : filter γ} (hg : tendsto g y z) (hf : tendsto f x y) : tendsto (g ∘ f) x z := sorry

theorem tendsto.mono_left {α : Type u} {β : Type v} {f : α → β} {x : filter α} {y : filter α} {z : filter β} (hx : tendsto f x z) (h : y ≤ x) : tendsto f y z :=
  le_trans (map_mono h) hx

theorem tendsto.mono_right {α : Type u} {β : Type v} {f : α → β} {x : filter α} {y : filter β} {z : filter β} (hy : tendsto f x y) (hz : y ≤ z) : tendsto f x z :=
  le_trans hy hz

theorem tendsto.ne_bot {α : Type u} {β : Type v} {f : α → β} {x : filter α} {y : filter β} (h : tendsto f x y) [hx : ne_bot x] : ne_bot y :=
  ne_bot.mono (ne_bot.map hx f) h

theorem tendsto_map {α : Type u} {β : Type v} {f : α → β} {x : filter α} : tendsto f x (map f x) :=
  le_refl (map f x)

theorem tendsto_map' {α : Type u} {β : Type v} {γ : Type w} {f : β → γ} {g : α → β} {x : filter α} {y : filter γ} (h : tendsto (f ∘ g) x y) : tendsto f (map g x) y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (tendsto f (map g x) y)) (tendsto.equations._eqn_1 f (map g x) y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (map f (map g x) ≤ y)) map_map)) h)

theorem tendsto_map'_iff {α : Type u} {β : Type v} {γ : Type w} {f : β → γ} {g : α → β} {x : filter α} {y : filter γ} : tendsto f (map g x) y ↔ tendsto (f ∘ g) x y := sorry

theorem tendsto_comap {α : Type u} {β : Type v} {f : α → β} {x : filter β} : tendsto f (comap f x) x :=
  map_comap_le

theorem tendsto_comap_iff {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : β → γ} {a : filter α} {c : filter γ} : tendsto f a (comap g c) ↔ tendsto (g ∘ f) a c := sorry

theorem tendsto_comap'_iff {α : Type u} {β : Type v} {γ : Type w} {m : α → β} {f : filter α} {g : filter β} {i : γ → α} (h : set.range i ∈ f) : tendsto (m ∘ i) (comap i f) g ↔ tendsto m f g := sorry

theorem comap_eq_of_inverse {α : Type u} {β : Type v} {f : filter α} {g : filter β} {φ : α → β} (ψ : β → α) (eq : ψ ∘ φ = id) (hφ : tendsto φ f g) (hψ : tendsto ψ g f) : comap φ g = f := sorry

theorem map_eq_of_inverse {α : Type u} {β : Type v} {f : filter α} {g : filter β} {φ : α → β} (ψ : β → α) (eq : φ ∘ ψ = id) (hφ : tendsto φ f g) (hψ : tendsto ψ g f) : map φ f = g := sorry

theorem tendsto_inf {α : Type u} {β : Type v} {f : α → β} {x : filter α} {y₁ : filter β} {y₂ : filter β} : tendsto f x (y₁ ⊓ y₂) ↔ tendsto f x y₁ ∧ tendsto f x y₂ := sorry

theorem tendsto_inf_left {α : Type u} {β : Type v} {f : α → β} {x₁ : filter α} {x₂ : filter α} {y : filter β} (h : tendsto f x₁ y) : tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_left) h

theorem tendsto_inf_right {α : Type u} {β : Type v} {f : α → β} {x₁ : filter α} {x₂ : filter α} {y : filter β} (h : tendsto f x₂ y) : tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_right) h

theorem tendsto.inf {α : Type u} {β : Type v} {f : α → β} {x₁ : filter α} {x₂ : filter α} {y₁ : filter β} {y₂ : filter β} (h₁ : tendsto f x₁ y₁) (h₂ : tendsto f x₂ y₂) : tendsto f (x₁ ⊓ x₂) (y₁ ⊓ y₂) :=
  iff.mpr tendsto_inf { left := tendsto_inf_left h₁, right := tendsto_inf_right h₂ }

@[simp] theorem tendsto_infi {α : Type u} {β : Type v} {ι : Sort x} {f : α → β} {x : filter α} {y : ι → filter β} : tendsto f x (infi fun (i : ι) => y i) ↔ ∀ (i : ι), tendsto f x (y i) := sorry

theorem tendsto_infi' {α : Type u} {β : Type v} {ι : Sort x} {f : α → β} {x : ι → filter α} {y : filter β} (i : ι) (hi : tendsto f (x i) y) : tendsto f (infi fun (i : ι) => x i) y :=
  tendsto.mono_left hi (infi_le (fun (i : ι) => x i) i)

theorem tendsto_sup {α : Type u} {β : Type v} {f : α → β} {x₁ : filter α} {x₂ : filter α} {y : filter β} : tendsto f (x₁ ⊔ x₂) y ↔ tendsto f x₁ y ∧ tendsto f x₂ y := sorry

theorem tendsto.sup {α : Type u} {β : Type v} {f : α → β} {x₁ : filter α} {x₂ : filter α} {y : filter β} : tendsto f x₁ y → tendsto f x₂ y → tendsto f (x₁ ⊔ x₂) y :=
  fun (h₁ : tendsto f x₁ y) (h₂ : tendsto f x₂ y) => iff.mpr tendsto_sup { left := h₁, right := h₂ }

@[simp] theorem tendsto_principal {α : Type u} {β : Type v} {f : α → β} {l : filter α} {s : set β} : tendsto f l (principal s) ↔ filter.eventually (fun (a : α) => f a ∈ s) l := sorry

@[simp] theorem tendsto_principal_principal {α : Type u} {β : Type v} {f : α → β} {s : set α} {t : set β} : tendsto f (principal s) (principal t) ↔ ∀ (a : α), a ∈ s → f a ∈ t := sorry

@[simp] theorem tendsto_pure {α : Type u} {β : Type v} {f : α → β} {a : filter α} {b : β} : tendsto f a (pure b) ↔ filter.eventually (fun (x : α) => f x = b) a := sorry

theorem tendsto_pure_pure {α : Type u} {β : Type v} (f : α → β) (a : α) : tendsto f (pure a) (pure (f a)) :=
  iff.mpr tendsto_pure rfl

theorem tendsto_const_pure {α : Type u} {β : Type v} {a : filter α} {b : β} : tendsto (fun (x : α) => b) a (pure b) :=
  iff.mpr tendsto_pure (univ_mem_sets' fun (_x : α) => rfl)

theorem pure_le_iff {α : Type u} {a : α} {l : filter α} : pure a ≤ l ↔ ∀ (s : set α), s ∈ l → a ∈ s :=
  iff.rfl

theorem tendsto_pure_left {α : Type u} {β : Type v} {f : α → β} {a : α} {l : filter β} : tendsto f (pure a) l ↔ ∀ (s : set β), s ∈ l → f a ∈ s :=
  iff.rfl

/-- If two filters are disjoint, then a function cannot tend to both of them along a non-trivial
filter. -/
theorem tendsto.not_tendsto {α : Type u} {β : Type v} {f : α → β} {a : filter α} {b₁ : filter β} {b₂ : filter β} (hf : tendsto f a b₁) [ne_bot a] (hb : disjoint b₁ b₂) : ¬tendsto f a b₂ :=
  fun (hf' : tendsto f a b₂) => tendsto.ne_bot (iff.mpr tendsto_inf { left := hf, right := hf' }) (disjoint.eq_bot hb)

theorem tendsto_if {α : Type u} {β : Type v} {l₁ : filter α} {l₂ : filter β} {f : α → β} {g : α → β} {p : α → Prop} [decidable_pred p] (h₀ : tendsto f (l₁ ⊓ principal p) l₂) (h₁ : tendsto g (l₁ ⊓ principal (set_of fun (x : α) => ¬p x)) l₂) : tendsto (fun (x : α) => ite (p x) (f x) (g x)) l₁ l₂ := sorry

/-! ### Products of filters -/

/- The product filter cannot be defined using the monad structure on filters. For example:

  F := do {x ← seq, y ← top, return (x, y)}
  hence:
    s ∈ F  ↔  ∃n, [n..∞] × univ ⊆ s

  G := do {y ← top, x ← seq, return (x, y)}
  hence:
    s ∈ G  ↔  ∀i:ℕ, ∃n, [n..∞] × {i} ⊆ s

  Now ⋃i, [i..∞] × {i}  is in G but not in F.

  As product filter we want to have F as result.
-/

/-- Product of filters. This is the filter generated by cartesian products
  of elements of the component filters. -/
protected def prod {α : Type u} {β : Type v} (f : filter α) (g : filter β) : filter (α × β) :=
  comap prod.fst f ⊓ comap prod.snd g

theorem prod_mem_prod {α : Type u} {β : Type v} {s : set α} {t : set β} {f : filter α} {g : filter β} (hs : s ∈ f) (ht : t ∈ g) : set.prod s t ∈ filter.prod f g :=
  inter_mem_inf_sets (preimage_mem_comap hs) (preimage_mem_comap ht)

theorem mem_prod_iff {α : Type u} {β : Type v} {s : set (α × β)} {f : filter α} {g : filter β} : s ∈ filter.prod f g ↔ ∃ (t₁ : set α), ∃ (H : t₁ ∈ f), ∃ (t₂ : set β), ∃ (H : t₂ ∈ g), set.prod t₁ t₂ ⊆ s := sorry

theorem comap_prod {α : Type u} {β : Type v} {γ : Type w} (f : α → β × γ) (b : filter β) (c : filter γ) : comap f (filter.prod b c) = comap (prod.fst ∘ f) b ⊓ comap (prod.snd ∘ f) c := sorry

theorem eventually_prod_iff {α : Type u} {β : Type v} {p : α × β → Prop} {f : filter α} {g : filter β} : filter.eventually (fun (x : α × β) => p x) (filter.prod f g) ↔
  ∃ (pa : α → Prop),
    ∃ (ha : filter.eventually (fun (x : α) => pa x) f),
      ∃ (pb : β → Prop),
        ∃ (hb : filter.eventually (fun (y : β) => pb y) g), ∀ {x : α}, pa x → ∀ {y : β}, pb y → p (x, y) := sorry

theorem tendsto_fst {α : Type u} {β : Type v} {f : filter α} {g : filter β} : tendsto prod.fst (filter.prod f g) f :=
  tendsto_inf_left tendsto_comap

theorem tendsto_snd {α : Type u} {β : Type v} {f : filter α} {g : filter β} : tendsto prod.snd (filter.prod f g) g :=
  tendsto_inf_right tendsto_comap

theorem tendsto.prod_mk {α : Type u} {β : Type v} {γ : Type w} {f : filter α} {g : filter β} {h : filter γ} {m₁ : α → β} {m₂ : α → γ} (h₁ : tendsto m₁ f g) (h₂ : tendsto m₂ f h) : tendsto (fun (x : α) => (m₁ x, m₂ x)) f (filter.prod g h) :=
  iff.mpr tendsto_inf { left := iff.mpr tendsto_comap_iff h₁, right := iff.mpr tendsto_comap_iff h₂ }

theorem eventually.prod_inl {α : Type u} {β : Type v} {la : filter α} {p : α → Prop} (h : filter.eventually (fun (x : α) => p x) la) (lb : filter β) : filter.eventually (fun (x : α × β) => p (prod.fst x)) (filter.prod la lb) :=
  tendsto.eventually tendsto_fst h

theorem eventually.prod_inr {α : Type u} {β : Type v} {lb : filter β} {p : β → Prop} (h : filter.eventually (fun (x : β) => p x) lb) (la : filter α) : filter.eventually (fun (x : α × β) => p (prod.snd x)) (filter.prod la lb) :=
  tendsto.eventually tendsto_snd h

theorem eventually.prod_mk {α : Type u} {β : Type v} {la : filter α} {pa : α → Prop} (ha : filter.eventually (fun (x : α) => pa x) la) {lb : filter β} {pb : β → Prop} (hb : filter.eventually (fun (y : β) => pb y) lb) : filter.eventually (fun (p : α × β) => pa (prod.fst p) ∧ pb (prod.snd p)) (filter.prod la lb) :=
  eventually.and (eventually.prod_inl ha lb) (eventually.prod_inr hb la)

theorem eventually.curry {α : Type u} {β : Type v} {la : filter α} {lb : filter β} {p : α × β → Prop} (h : filter.eventually (fun (x : α × β) => p x) (filter.prod la lb)) : filter.eventually (fun (x : α) => filter.eventually (fun (y : β) => p (x, y)) lb) la := sorry

theorem prod_infi_left {α : Type u} {β : Type v} {ι : Sort x} [Nonempty ι] {f : ι → filter α} {g : filter β} : filter.prod (infi fun (i : ι) => f i) g = infi fun (i : ι) => filter.prod (f i) g := sorry

theorem prod_infi_right {α : Type u} {β : Type v} {ι : Sort x} [Nonempty ι] {f : filter α} {g : ι → filter β} : filter.prod f (infi fun (i : ι) => g i) = infi fun (i : ι) => filter.prod f (g i) := sorry

theorem prod_mono {α : Type u} {β : Type v} {f₁ : filter α} {f₂ : filter α} {g₁ : filter β} {g₂ : filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : filter.prod f₁ g₁ ≤ filter.prod f₂ g₂ :=
  inf_le_inf (comap_mono hf) (comap_mono hg)

theorem prod_comap_comap_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} : filter.prod (comap m₁ f₁) (comap m₂ f₂) =
  comap (fun (p : β₁ × β₂) => (m₁ (prod.fst p), m₂ (prod.snd p))) (filter.prod f₁ f₂) := sorry

theorem prod_comm' {α : Type u} {β : Type v} {f : filter α} {g : filter β} : filter.prod f g = comap prod.swap (filter.prod g f) := sorry

theorem prod_comm {α : Type u} {β : Type v} {f : filter α} {g : filter β} : filter.prod f g = map (fun (p : β × α) => (prod.snd p, prod.fst p)) (filter.prod g f) := sorry

theorem prod_map_map_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} : filter.prod (map m₁ f₁) (map m₂ f₂) = map (fun (p : α₁ × α₂) => (m₁ (prod.fst p), m₂ (prod.snd p))) (filter.prod f₁ f₂) := sorry

theorem prod_map_map_eq' {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} (f : α₁ → α₂) (g : β₁ → β₂) (F : filter α₁) (G : filter β₁) : filter.prod (map f F) (map g G) = map (prod.map f g) (filter.prod F G) :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (filter.prod (map f F) (map g G) = map (prod.map f g) (filter.prod F G))) prod_map_map_eq))
    (Eq.refl (map (fun (p : α₁ × β₁) => (f (prod.fst p), g (prod.snd p))) (filter.prod F G)))

theorem tendsto.prod_map {α : Type u} {β : Type v} {γ : Type w} {δ : Type u_1} {f : α → γ} {g : β → δ} {a : filter α} {b : filter β} {c : filter γ} {d : filter δ} (hf : tendsto f a c) (hg : tendsto g b d) : tendsto (prod.map f g) (filter.prod a b) (filter.prod c d) := sorry

theorem map_prod {α : Type u} {β : Type v} {γ : Type w} (m : α × β → γ) (f : filter α) (g : filter β) : map m (filter.prod f g) = seq (map (fun (a : α) (b : β) => m (a, b)) f) g := sorry

theorem prod_eq {α : Type u} {β : Type v} {f : filter α} {g : filter β} : filter.prod f g = seq (map Prod.mk f) g :=
  (fun (h : map id (filter.prod f g) = seq (map (fun (a : α) (b : β) => id (a, b)) f) g) =>
      eq.mp (Eq._oldrec (Eq.refl (map id (filter.prod f g) = seq (map (fun (a : α) (b : β) => id (a, b)) f) g)) map_id) h)
    (map_prod id f g)

theorem prod_inf_prod {α : Type u} {β : Type v} {f₁ : filter α} {f₂ : filter α} {g₁ : filter β} {g₂ : filter β} : filter.prod f₁ g₁ ⊓ filter.prod f₂ g₂ = filter.prod (f₁ ⊓ f₂) (g₁ ⊓ g₂) := sorry

@[simp] theorem prod_bot {α : Type u} {β : Type v} {f : filter α} : filter.prod f ⊥ = ⊥ := sorry

@[simp] theorem bot_prod {α : Type u} {β : Type v} {g : filter β} : filter.prod ⊥ g = ⊥ := sorry

@[simp] theorem prod_principal_principal {α : Type u} {β : Type v} {s : set α} {t : set β} : filter.prod (principal s) (principal t) = principal (set.prod s t) := sorry

@[simp] theorem pure_prod {α : Type u} {β : Type v} {a : α} {f : filter β} : filter.prod (pure a) f = map (Prod.mk a) f := sorry

@[simp] theorem prod_pure {α : Type u} {β : Type v} {f : filter α} {b : β} : filter.prod f (pure b) = map (fun (a : α) => (a, b)) f := sorry

theorem prod_pure_pure {α : Type u} {β : Type v} {a : α} {b : β} : filter.prod (pure a) (pure b) = pure (a, b) := sorry

theorem prod_eq_bot {α : Type u} {β : Type v} {f : filter α} {g : filter β} : filter.prod f g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := sorry

theorem prod_ne_bot {α : Type u} {β : Type v} {f : filter α} {g : filter β} : ne_bot (filter.prod f g) ↔ ne_bot f ∧ ne_bot g :=
  iff.trans (not_congr prod_eq_bot) not_or_distrib

theorem ne_bot.prod {α : Type u} {β : Type v} {f : filter α} {g : filter β} (hf : ne_bot f) (hg : ne_bot g) : ne_bot (filter.prod f g) :=
  iff.mpr prod_ne_bot { left := hf, right := hg }

protected instance prod_ne_bot' {α : Type u} {β : Type v} {f : filter α} {g : filter β} [hf : ne_bot f] [hg : ne_bot g] : ne_bot (filter.prod f g) :=
  ne_bot.prod hf hg

theorem tendsto_prod_iff {α : Type u} {β : Type v} {γ : Type w} {f : α × β → γ} {x : filter α} {y : filter β} {z : filter γ} : tendsto f (filter.prod x y) z ↔
  ∀ (W : set γ) (H : W ∈ z),
    ∃ (U : set α), ∃ (H : U ∈ x), ∃ (V : set β), ∃ (H : V ∈ y), ∀ (x : α) (y : β), x ∈ U → y ∈ V → f (x, y) ∈ W := sorry

end filter


theorem set.eq_on.eventually_eq {α : Type u_1} {β : Type u_2} {s : set α} {f : α → β} {g : α → β} (h : set.eq_on f g s) : filter.eventually_eq (filter.principal s) f g :=
  h

theorem set.eq_on.eventually_eq_of_mem {α : Type u_1} {β : Type u_2} {s : set α} {l : filter α} {f : α → β} {g : α → β} (h : set.eq_on f g s) (hl : s ∈ l) : filter.eventually_eq l f g :=
  filter.eventually_eq.filter_mono (set.eq_on.eventually_eq h) (iff.mpr filter.le_principal_iff hl)

theorem set.subset.eventually_le {α : Type u_1} {l : filter α} {s : set α} {t : set α} (h : s ⊆ t) : filter.eventually_le l s t :=
  filter.eventually_of_forall h

