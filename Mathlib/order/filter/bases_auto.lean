/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.filter.basic
import Mathlib.data.set.countable
import PostPort

universes u_6 l u_1 u_4 u_5 u_2 u_3 

namespace Mathlib

/-!
# Filter bases

A filter basis `B : filter_basis α` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element of
the collection. Compared to filters, filter bases do not require that any set containing
an element of `B` belongs to `B`.
A filter basis `B` can be used to construct `B.filter : filter α` such that a set belongs
to `B.filter` if and only if it contains an element of `B`.

Given an indexing type `ι`, a predicate `p : ι → Prop`, and a map `s : ι → set α`,
the proposition `h : filter.is_basis p s` makes sure the range of `s` bounded by `p`
(ie. `s '' set_of p`) defines a filter basis `h.filter_basis`.

If one already has a filter `l` on `α`, `filter.has_basis l p s` (where `p : ι → Prop`
and `s : ι → set α` as above) means that a set belongs to `l` if and
only if it contains some `s i` with `p i`. It implies `h : filter.is_basis p s`, and
`l = h.filter_basis.filter`. The point of this definition is that checking statements
involving elements of `l` often reduces to checking them on the basis elements.

We define a function `has_basis.index (h : filter.has_basis l p s) (t) (ht : t ∈ l)` that returns
some index `i` such that `p i` and `s i ⊆ t`. This function can be useful to avoid manual
destruction of `h.mem_iff.mpr ht` using `cases` or `let`.

This file also introduces more restricted classes of bases, involving monotonicity or
countability. In particular, for `l : filter α`, `l.is_countably_generated` means
there is a countable set of sets which generates `s`. This is reformulated in term of bases,
and consequences are derived.

## Main statements

* `has_basis.mem_iff`, `has_basis.mem_of_superset`, `has_basis.mem_of_mem` : restate `t ∈ f` in terms
  of a basis;
* `basis_sets` : all sets of a filter form a basis;
* `has_basis.inf`, `has_basis.inf_principal`, `has_basis.prod`, `has_basis.prod_self`,
  `has_basis.map`, `has_basis.comap` : combinators to construct filters of `l ⊓ l'`,
  `l ⊓ 𝓟 t`, `l ×ᶠ l'`, `l ×ᶠ l`, `l.map f`, `l.comap f` respectively;
* `has_basis.le_iff`, `has_basis.ge_iff`, has_basis.le_basis_iff` : restate `l ≤ l'` in terms
  of bases.
* `has_basis.tendsto_right_iff`, `has_basis.tendsto_left_iff`, `has_basis.tendsto_iff` : restate
  `tendsto f l l'` in terms of bases.
* `is_countably_generated_iff_exists_antimono_basis` : proves a filter is
  countably generated if and only if it admis a basis parametrized by a
  decreasing sequence of sets indexed by `ℕ`.
* `tendsto_iff_seq_tendsto ` : an abstract version of "sequentially continuous implies continuous".

## Implementation notes

As with `Union`/`bUnion`/`sUnion`, there are three different approaches to filter bases:

* `has_basis l s`, `s : set (set α)`;
* `has_basis l s`, `s : ι → set α`;
* `has_basis l p s`, `p : ι → Prop`, `s : ι → set α`.

We use the latter one because, e.g., `𝓝 x` in an `emetric_space` or in a `metric_space` has a basis
of this form. The other two can be emulated using `s = id` or `p = λ _, true`.

With this approach sometimes one needs to `simp` the statement provided by the `has_basis`
machinery, e.g., `simp only [exists_prop, true_and]` or `simp only [forall_const]` can help
with the case `p = λ _, true`.
-/

/-- A filter basis `B` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure filter_basis (α : Type u_6) 
where
  sets : set (set α)
  nonempty : set.nonempty sets
  inter_sets : ∀ {x y : set α}, x ∈ sets → y ∈ sets → ∃ (z : set α), ∃ (H : z ∈ sets), z ⊆ x ∩ y

protected instance filter_basis.nonempty_sets {α : Type u_1} (B : filter_basis α) : Nonempty ↥(filter_basis.sets B) :=
  set.nonempty.to_subtype (filter_basis.nonempty B)

/-- If `B` is a filter basis on `α`, and `U` a subset of `α` then we can write `U ∈ B` as on paper. -/
protected instance filter_basis.has_mem {α : Type u_1} : has_mem (set α) (filter_basis α) :=
  has_mem.mk fun (U : set α) (B : filter_basis α) => U ∈ filter_basis.sets B

-- For illustration purposes, the filter basis defining (at_top : filter ℕ)

protected instance filter_basis.inhabited : Inhabited (filter_basis ℕ) :=
  { default := filter_basis.mk (set.range set.Ici) sorry sorry }

/-- `is_basis p s` means the image of `s` bounded by `p` is a filter basis. -/
structure filter.is_basis {α : Type u_1} {ι : Type u_4} (p : ι → Prop) (s : ι → set α) 
where
  nonempty : ∃ (i : ι), p i
  inter : ∀ {i j : ι}, p i → p j → ∃ (k : ι), p k ∧ s k ⊆ s i ∩ s j

namespace filter


namespace is_basis


/-- Constructs a filter basis from an indexed family of sets satisfying `is_basis`. -/
protected def filter_basis {α : Type u_1} {ι : Type u_4} {p : ι → Prop} {s : ι → set α} (h : is_basis p s) : filter_basis α :=
  filter_basis.mk (s '' set_of p) sorry sorry

theorem mem_filter_basis_iff {α : Type u_1} {ι : Type u_4} {p : ι → Prop} {s : ι → set α} (h : is_basis p s) {U : set α} : U ∈ is_basis.filter_basis h ↔ ∃ (i : ι), p i ∧ s i = U :=
  iff.rfl

end is_basis


end filter


namespace filter_basis


/-- The filter associated to a filter basis. -/
protected def filter {α : Type u_1} (B : filter_basis α) : filter α :=
  filter.mk (set_of fun (s : set α) => ∃ (t : set α), ∃ (H : t ∈ B), t ⊆ s) sorry sorry sorry

theorem mem_filter_iff {α : Type u_1} (B : filter_basis α) {U : set α} : U ∈ filter_basis.filter B ↔ ∃ (s : set α), ∃ (H : s ∈ B), s ⊆ U :=
  iff.rfl

theorem mem_filter_of_mem {α : Type u_1} (B : filter_basis α) {U : set α} : U ∈ B → U ∈ filter_basis.filter B :=
  fun (U_in : U ∈ B) => Exists.intro U (Exists.intro U_in (set.subset.refl U))

theorem eq_infi_principal {α : Type u_1} (B : filter_basis α) : filter_basis.filter B = infi fun (s : ↥(sets B)) => filter.principal ↑s := sorry

protected theorem generate {α : Type u_1} (B : filter_basis α) : filter.generate (sets B) = filter_basis.filter B := sorry

end filter_basis


namespace filter


namespace is_basis


/-- Constructs a filter from an indexed family of sets satisfying `is_basis`. -/
protected def filter {α : Type u_1} {ι : Type u_4} {p : ι → Prop} {s : ι → set α} (h : is_basis p s) : filter α :=
  filter_basis.filter (is_basis.filter_basis h)

protected theorem mem_filter_iff {α : Type u_1} {ι : Type u_4} {p : ι → Prop} {s : ι → set α} (h : is_basis p s) {U : set α} : U ∈ is_basis.filter h ↔ ∃ (i : ι), p i ∧ s i ⊆ U := sorry

theorem filter_eq_generate {α : Type u_1} {ι : Type u_4} {p : ι → Prop} {s : ι → set α} (h : is_basis p s) : is_basis.filter h = generate (set_of fun (U : set α) => ∃ (i : ι), p i ∧ s i = U) := sorry

end is_basis


/-- We say that a filter `l` has a basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`. -/
structure has_basis {α : Type u_1} {ι : Type u_4} (l : filter α) (p : ι → Prop) (s : ι → set α) 
where
  mem_iff' : ∀ (t : set α), t ∈ l ↔ ∃ (i : ι), ∃ (hi : p i), s i ⊆ t

theorem has_basis_generate {α : Type u_1} (s : set (set α)) : has_basis (generate s) (fun (t : set (set α)) => set.finite t ∧ t ⊆ s) fun (t : set (set α)) => ⋂₀t := sorry

/-- The smallest filter basis containing a given collection of sets. -/
def filter_basis.of_sets {α : Type u_1} (s : set (set α)) : filter_basis α :=
  filter_basis.mk (set.sInter '' set_of fun (t : set (set α)) => set.finite t ∧ t ⊆ s) sorry sorry

/-- Definition of `has_basis` unfolded with implicit set argument. -/
theorem has_basis.mem_iff {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} {t : set α} (hl : has_basis l p s) : t ∈ l ↔ ∃ (i : ι), ∃ (hi : p i), s i ⊆ t :=
  has_basis.mem_iff' hl t

theorem has_basis_iff {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} : has_basis l p s ↔ ∀ (t : set α), t ∈ l ↔ ∃ (i : ι), ∃ (hi : p i), s i ⊆ t := sorry

theorem has_basis.ex_mem {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (h : has_basis l p s) : ∃ (i : ι), p i := sorry

protected theorem is_basis.has_basis {α : Type u_1} {ι : Type u_4} {p : ι → Prop} {s : ι → set α} (h : is_basis p s) : has_basis (is_basis.filter h) p s := sorry

theorem has_basis.mem_of_superset {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} {t : set α} {i : ι} (hl : has_basis l p s) (hi : p i) (ht : s i ⊆ t) : t ∈ l :=
  iff.mpr (has_basis.mem_iff hl) (Exists.intro i (Exists.intro hi ht))

theorem has_basis.mem_of_mem {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} {i : ι} (hl : has_basis l p s) (hi : p i) : s i ∈ l :=
  has_basis.mem_of_superset hl hi (set.subset.refl (s i))

/-- Index of a basis set such that `s i ⊆ t` as an element of `subtype p`. -/
def has_basis.index {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (h : has_basis l p s) (t : set α) (ht : t ∈ l) : Subtype fun (i : ι) => p i :=
  { val := Exists.some sorry, property := sorry }

theorem has_basis.property_index {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} {t : set α} (h : has_basis l p s) (ht : t ∈ l) : p ↑(has_basis.index h t ht) :=
  subtype.property (has_basis.index h t ht)

theorem has_basis.set_index_mem {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} {t : set α} (h : has_basis l p s) (ht : t ∈ l) : s ↑(has_basis.index h t ht) ∈ l :=
  has_basis.mem_of_mem h (has_basis.property_index h ht)

theorem has_basis.set_index_subset {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} {t : set α} (h : has_basis l p s) (ht : t ∈ l) : s ↑(has_basis.index h t ht) ⊆ t :=
  Exists.snd (Exists.some_spec (iff.mp (has_basis.mem_iff h) ht))

theorem has_basis.is_basis {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (h : has_basis l p s) : is_basis p s := sorry

theorem has_basis.filter_eq {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (h : has_basis l p s) : is_basis.filter (has_basis.is_basis h) = l := sorry

theorem has_basis.eq_generate {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (h : has_basis l p s) : l = generate (set_of fun (U : set α) => ∃ (i : ι), p i ∧ s i = U) := sorry

theorem generate_eq_generate_inter {α : Type u_1} (s : set (set α)) : generate s = generate (set.sInter '' set_of fun (t : set (set α)) => set.finite t ∧ t ⊆ s) := sorry

theorem of_sets_filter_eq_generate {α : Type u_1} (s : set (set α)) : filter_basis.filter (filter_basis.of_sets s) = generate s := sorry

theorem has_basis.to_has_basis {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} {l : filter α} {p : ι → Prop} {s : ι → set α} {p' : ι' → Prop} {s' : ι' → set α} (hl : has_basis l p s) (h : ∀ (i : ι), p i → ∃ (i' : ι'), p' i' ∧ s' i' ⊆ s i) (h' : ∀ (i' : ι'), p' i' → ∃ (i : ι), p i ∧ s i ⊆ s' i') : has_basis l p' s' := sorry

theorem has_basis.eventually_iff {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (hl : has_basis l p s) {q : α → Prop} : filter.eventually (fun (x : α) => q x) l ↔ ∃ (i : ι), p i ∧ ∀ {x : α}, x ∈ s i → q x := sorry

theorem has_basis.frequently_iff {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (hl : has_basis l p s) {q : α → Prop} : filter.frequently (fun (x : α) => q x) l ↔ ∀ (i : ι), p i → ∃ (x : α), ∃ (H : x ∈ s i), q x := sorry

theorem has_basis.exists_iff {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (hl : has_basis l p s) {P : set α → Prop} (mono : ∀ {s t : set α}, s ⊆ t → P t → P s) : (∃ (s : set α), ∃ (H : s ∈ l), P s) ↔ ∃ (i : ι), ∃ (hi : p i), P (s i) := sorry

theorem has_basis.forall_iff {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (hl : has_basis l p s) {P : set α → Prop} (mono : ∀ {s t : set α}, s ⊆ t → P s → P t) : (∀ (s : set α), s ∈ l → P s) ↔ ∀ (i : ι), p i → P (s i) := sorry

theorem has_basis.ne_bot_iff {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (hl : has_basis l p s) : ne_bot l ↔ ∀ {i : ι}, p i → set.nonempty (s i) :=
  iff.trans (iff.symm forall_sets_nonempty_iff_ne_bot)
    (has_basis.forall_iff hl fun (_x _x_1 : set α) => set.nonempty.mono)

theorem has_basis.eq_bot_iff {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (hl : has_basis l p s) : l = ⊥ ↔ ∃ (i : ι), p i ∧ s i = ∅ := sorry

theorem basis_sets {α : Type u_1} (l : filter α) : has_basis l (fun (s : set α) => s ∈ l) id :=
  has_basis.mk fun (t : set α) => iff.symm exists_sets_subset_iff

theorem has_basis_self {α : Type u_1} {l : filter α} {P : set α → Prop} : has_basis l (fun (s : set α) => s ∈ l ∧ P s) id ↔ ∀ (t : set α), t ∈ l ↔ ∃ (r : set α), ∃ (H : r ∈ l), P r ∧ r ⊆ t := sorry

/-- If `{s i | p i}` is a basis of a filter `l` and each `s i` includes `s j` such that
`p j ∧ q j`, then `{s j | p j ∧ q j}` is a basis of `l`. -/
theorem has_basis.restrict {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (h : has_basis l p s) {q : ι → Prop} (hq : ∀ (i : ι), p i → ∃ (j : ι), p j ∧ q j ∧ s j ⊆ s i) : has_basis l (fun (i : ι) => p i ∧ q i) s := sorry

/-- If `{s i | p i}` is a basis of a filter `l` and `V ∈ l`, then `{s i | p i ∧ s i ⊆ V}`
is a basis of `l`. -/
theorem has_basis.restrict_subset {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (h : has_basis l p s) {V : set α} (hV : V ∈ l) : has_basis l (fun (i : ι) => p i ∧ s i ⊆ V) s := sorry

theorem has_basis.has_basis_self_subset {α : Type u_1} {l : filter α} {p : set α → Prop} (h : has_basis l (fun (s : set α) => s ∈ l ∧ p s) id) {V : set α} (hV : V ∈ l) : has_basis l (fun (s : set α) => s ∈ l ∧ p s ∧ s ⊆ V) id := sorry

theorem has_basis.ge_iff {α : Type u_1} {ι' : Type u_5} {l : filter α} {l' : filter α} {p' : ι' → Prop} {s' : ι' → set α} (hl' : has_basis l' p' s') : l ≤ l' ↔ ∀ (i' : ι'), p' i' → s' i' ∈ l := sorry

theorem has_basis.le_iff {α : Type u_1} {ι : Type u_4} {l : filter α} {l' : filter α} {p : ι → Prop} {s : ι → set α} (hl : has_basis l p s) : l ≤ l' ↔ ∀ (t : set α), t ∈ l' → ∃ (i : ι), ∃ (hi : p i), s i ⊆ t := sorry

theorem has_basis.le_basis_iff {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} {l : filter α} {l' : filter α} {p : ι → Prop} {s : ι → set α} {p' : ι' → Prop} {s' : ι' → set α} (hl : has_basis l p s) (hl' : has_basis l' p' s') : l ≤ l' ↔ ∀ (i' : ι'), p' i' → ∃ (i : ι), ∃ (hi : p i), s i ⊆ s' i' := sorry

theorem has_basis.ext {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} {l : filter α} {l' : filter α} {p : ι → Prop} {s : ι → set α} {p' : ι' → Prop} {s' : ι' → set α} (hl : has_basis l p s) (hl' : has_basis l' p' s') (h : ∀ (i : ι), p i → ∃ (i' : ι'), p' i' ∧ s' i' ⊆ s i) (h' : ∀ (i' : ι'), p' i' → ∃ (i : ι), p i ∧ s i ⊆ s' i') : l = l' := sorry

theorem has_basis.inf {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} {l : filter α} {l' : filter α} {p : ι → Prop} {s : ι → set α} {p' : ι' → Prop} {s' : ι' → set α} (hl : has_basis l p s) (hl' : has_basis l' p' s') : has_basis (l ⊓ l') (fun (i : ι × ι') => p (prod.fst i) ∧ p' (prod.snd i))
  fun (i : ι × ι') => s (prod.fst i) ∩ s' (prod.snd i) := sorry

theorem has_basis_principal {α : Type u_1} (t : set α) : has_basis (principal t) (fun (i : Unit) => True) fun (i : Unit) => t := sorry

theorem has_basis.sup {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} {l : filter α} {l' : filter α} {p : ι → Prop} {s : ι → set α} {p' : ι' → Prop} {s' : ι' → set α} (hl : has_basis l p s) (hl' : has_basis l' p' s') : has_basis (l ⊔ l') (fun (i : ι × ι') => p (prod.fst i) ∧ p' (prod.snd i))
  fun (i : ι × ι') => s (prod.fst i) ∪ s' (prod.snd i) := sorry

theorem has_basis.inf_principal {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (hl : has_basis l p s) (s' : set α) : has_basis (l ⊓ principal s') p fun (i : ι) => s i ∩ s' := sorry

theorem has_basis.inf_basis_ne_bot_iff {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} {l : filter α} {l' : filter α} {p : ι → Prop} {s : ι → set α} {p' : ι' → Prop} {s' : ι' → set α} (hl : has_basis l p s) (hl' : has_basis l' p' s') : ne_bot (l ⊓ l') ↔ ∀ {i : ι}, p i → ∀ {i' : ι'}, p' i' → set.nonempty (s i ∩ s' i') := sorry

theorem has_basis.inf_ne_bot_iff {α : Type u_1} {ι : Type u_4} {l : filter α} {l' : filter α} {p : ι → Prop} {s : ι → set α} (hl : has_basis l p s) : ne_bot (l ⊓ l') ↔ ∀ {i : ι}, p i → ∀ {s' : set α}, s' ∈ l' → set.nonempty (s i ∩ s') :=
  has_basis.inf_basis_ne_bot_iff hl (basis_sets l')

theorem has_basis.inf_principal_ne_bot_iff {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (hl : has_basis l p s) {t : set α} : ne_bot (l ⊓ principal t) ↔ ∀ {i : ι}, p i → set.nonempty (s i ∩ t) :=
  has_basis.ne_bot_iff (has_basis.inf_principal hl t)

theorem inf_ne_bot_iff {α : Type u_1} {l : filter α} {l' : filter α} : ne_bot (l ⊓ l') ↔ ∀ {s : set α}, s ∈ l → ∀ {s' : set α}, s' ∈ l' → set.nonempty (s ∩ s') :=
  has_basis.inf_ne_bot_iff (basis_sets l)

theorem inf_principal_ne_bot_iff {α : Type u_1} {l : filter α} {s : set α} : ne_bot (l ⊓ principal s) ↔ ∀ (U : set α), U ∈ l → set.nonempty (U ∩ s) :=
  has_basis.inf_principal_ne_bot_iff (basis_sets l)

theorem inf_eq_bot_iff {α : Type u_1} {f : filter α} {g : filter α} : f ⊓ g = ⊥ ↔ ∃ (U : set α), ∃ (H : U ∈ f), ∃ (V : set α), ∃ (H : V ∈ g), U ∩ V = ∅ := sorry

protected theorem disjoint_iff {α : Type u_1} {f : filter α} {g : filter α} : disjoint f g ↔ ∃ (U : set α), ∃ (H : U ∈ f), ∃ (V : set α), ∃ (H : V ∈ g), U ∩ V = ∅ :=
  iff.trans disjoint_iff inf_eq_bot_iff

theorem mem_iff_inf_principal_compl {α : Type u_1} {f : filter α} {s : set α} : s ∈ f ↔ f ⊓ principal (sᶜ) = ⊥ := sorry

theorem mem_iff_disjoint_principal_compl {α : Type u_1} {f : filter α} {s : set α} : s ∈ f ↔ disjoint f (principal (sᶜ)) :=
  iff.trans mem_iff_inf_principal_compl (iff.symm disjoint_iff)

theorem le_iff_forall_disjoint_principal_compl {α : Type u_1} {f : filter α} {g : filter α} : f ≤ g ↔ ∀ (V : set α), V ∈ g → disjoint f (principal (Vᶜ)) :=
  forall_congr fun (_x : set α) => forall_congr fun (_x_1 : _x ∈ g) => mem_iff_disjoint_principal_compl

theorem le_iff_forall_inf_principal_compl {α : Type u_1} {f : filter α} {g : filter α} : f ≤ g ↔ ∀ (V : set α), V ∈ g → f ⊓ principal (Vᶜ) = ⊥ :=
  forall_congr fun (_x : set α) => forall_congr fun (_x_1 : _x ∈ g) => mem_iff_inf_principal_compl

theorem inf_ne_bot_iff_frequently_left {α : Type u_1} {f : filter α} {g : filter α} : ne_bot (f ⊓ g) ↔ ∀ {p : α → Prop}, filter.eventually (fun (x : α) => p x) f → filter.frequently (fun (x : α) => p x) g := sorry

theorem inf_ne_bot_iff_frequently_right {α : Type u_1} {f : filter α} {g : filter α} : ne_bot (f ⊓ g) ↔ ∀ {p : α → Prop}, filter.eventually (fun (x : α) => p x) g → filter.frequently (fun (x : α) => p x) f := sorry

theorem has_basis.eq_binfi {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (h : has_basis l p s) : l = infi fun (i : ι) => infi fun (_x : p i) => principal (s i) := sorry

theorem has_basis.eq_infi {α : Type u_1} {ι : Type u_4} {l : filter α} {s : ι → set α} (h : has_basis l (fun (_x : ι) => True) s) : l = infi fun (i : ι) => principal (s i) := sorry

theorem has_basis_infi_principal {α : Type u_1} {ι : Type u_4} {s : ι → set α} (h : directed ge s) [Nonempty ι] : has_basis (infi fun (i : ι) => principal (s i)) (fun (_x : ι) => True) s := sorry

/-- If `s : ι → set α` is an indexed family of sets, then finite intersections of `s i` form a basis
of `⨅ i, 𝓟 (s i)`.  -/
theorem has_basis_infi_principal_finite {α : Type u_1} {ι : Type u_4} (s : ι → set α) : has_basis (infi fun (i : ι) => principal (s i)) (fun (t : set ι) => set.finite t)
  fun (t : set ι) => set.Inter fun (i : ι) => set.Inter fun (H : i ∈ t) => s i := sorry

theorem has_basis_binfi_principal {α : Type u_1} {β : Type u_2} {s : β → set α} {S : set β} (h : directed_on (s ⁻¹'o ge) S) (ne : set.nonempty S) : has_basis (infi fun (i : β) => infi fun (H : i ∈ S) => principal (s i)) (fun (i : β) => i ∈ S) s := sorry

theorem has_basis_binfi_principal' {α : Type u_1} {ι : Type u_4} {p : ι → Prop} {s : ι → set α} (h : ∀ (i : ι), p i → ∀ (j : ι), p j → ∃ (k : ι), ∃ (h : p k), s k ⊆ s i ∧ s k ⊆ s j) (ne : ∃ (i : ι), p i) : has_basis (infi fun (i : ι) => infi fun (h : p i) => principal (s i)) p s :=
  has_basis_binfi_principal h ne

theorem has_basis.map {α : Type u_1} {β : Type u_2} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (f : α → β) (hl : has_basis l p s) : has_basis (map f l) p fun (i : ι) => f '' s i := sorry

theorem has_basis.comap {α : Type u_1} {β : Type u_2} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (f : β → α) (hl : has_basis l p s) : has_basis (comap f l) p fun (i : ι) => f ⁻¹' s i := sorry

theorem comap_has_basis {α : Type u_1} {β : Type u_2} (f : α → β) (l : filter β) : has_basis (comap f l) (fun (s : set β) => s ∈ l) fun (s : set β) => f ⁻¹' s :=
  has_basis.mk fun (t : set α) => mem_comap_sets

theorem has_basis.prod_self {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (hl : has_basis l p s) : has_basis (filter.prod l l) p fun (i : ι) => set.prod (s i) (s i) := sorry

theorem mem_prod_self_iff {α : Type u_1} {l : filter α} {s : set (α × α)} : s ∈ filter.prod l l ↔ ∃ (t : set α), ∃ (H : t ∈ l), set.prod t t ⊆ s :=
  has_basis.mem_iff (has_basis.prod_self (basis_sets l))

theorem has_basis.sInter_sets {α : Type u_1} {ι : Type u_4} {l : filter α} {p : ι → Prop} {s : ι → set α} (h : has_basis l p s) : ⋂₀sets l = set.Inter fun (i : ι) => set.Inter fun (H : i ∈ set_of p) => s i := sorry

/-- `is_antimono_basis p s` means the image of `s` bounded by `p` is a filter basis
such that `s` is decreasing and `p` is increasing, ie `i ≤ j → p i → p j`. -/
structure is_antimono_basis {α : Type u_1} {ι : Type u_4} (p : ι → Prop) (s : ι → set α) [preorder ι] 
extends is_basis p s
where
  decreasing : ∀ {i j : ι}, p i → p j → i ≤ j → s j ⊆ s i
  mono : monotone p

/-- We say that a filter `l` has a antimono basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`,
and `s` is decreasing and `p` is increasing, ie `i ≤ j → p i → p j`. -/
structure has_antimono_basis {α : Type u_1} {ι : Type u_4} [preorder ι] [preorder ι] (l : filter α) (p : ι → Prop) (s : ι → set α) 
extends has_basis l p s
where
  decreasing : ∀ {i j : ι}, p i → p j → i ≤ j → s j ⊆ s i
  mono : monotone p

theorem has_basis.tendsto_left_iff {α : Type u_1} {β : Type u_2} {ι : Type u_4} {la : filter α} {pa : ι → Prop} {sa : ι → set α} {lb : filter β} {f : α → β} (hla : has_basis la pa sa) : tendsto f la lb ↔ ∀ (t : set β), t ∈ lb → ∃ (i : ι), ∃ (hi : pa i), ∀ (x : α), x ∈ sa i → f x ∈ t := sorry

theorem has_basis.tendsto_right_iff {α : Type u_1} {β : Type u_2} {ι' : Type u_5} {la : filter α} {lb : filter β} {pb : ι' → Prop} {sb : ι' → set β} {f : α → β} (hlb : has_basis lb pb sb) : tendsto f la lb ↔ ∀ (i : ι'), pb i → filter.eventually (fun (x : α) => f x ∈ sb i) la := sorry

theorem has_basis.tendsto_iff {α : Type u_1} {β : Type u_2} {ι : Type u_4} {ι' : Type u_5} {la : filter α} {pa : ι → Prop} {sa : ι → set α} {lb : filter β} {pb : ι' → Prop} {sb : ι' → set β} {f : α → β} (hla : has_basis la pa sa) (hlb : has_basis lb pb sb) : tendsto f la lb ↔ ∀ (ib : ι'), pb ib → ∃ (ia : ι), ∃ (hia : pa ia), ∀ (x : α), x ∈ sa ia → f x ∈ sb ib := sorry

theorem tendsto.basis_left {α : Type u_1} {β : Type u_2} {ι : Type u_4} {la : filter α} {pa : ι → Prop} {sa : ι → set α} {lb : filter β} {f : α → β} (H : tendsto f la lb) (hla : has_basis la pa sa) (t : set β) : t ∈ lb → ∃ (i : ι), ∃ (hi : pa i), ∀ (x : α), x ∈ sa i → f x ∈ t :=
  iff.mp (has_basis.tendsto_left_iff hla) H

theorem tendsto.basis_right {α : Type u_1} {β : Type u_2} {ι' : Type u_5} {la : filter α} {lb : filter β} {pb : ι' → Prop} {sb : ι' → set β} {f : α → β} (H : tendsto f la lb) (hlb : has_basis lb pb sb) (i : ι') (hi : pb i) : filter.eventually (fun (x : α) => f x ∈ sb i) la :=
  iff.mp (has_basis.tendsto_right_iff hlb) H

theorem tendsto.basis_both {α : Type u_1} {β : Type u_2} {ι : Type u_4} {ι' : Type u_5} {la : filter α} {pa : ι → Prop} {sa : ι → set α} {lb : filter β} {pb : ι' → Prop} {sb : ι' → set β} {f : α → β} (H : tendsto f la lb) (hla : has_basis la pa sa) (hlb : has_basis lb pb sb) (ib : ι') (hib : pb ib) : ∃ (ia : ι), ∃ (hia : pa ia), ∀ (x : α), x ∈ sa ia → f x ∈ sb ib :=
  iff.mp (has_basis.tendsto_iff hla hlb) H

theorem has_basis.prod {α : Type u_1} {β : Type u_2} {ι : Type u_4} {ι' : Type u_5} {la : filter α} {pa : ι → Prop} {sa : ι → set α} {lb : filter β} {pb : ι' → Prop} {sb : ι' → set β} (hla : has_basis la pa sa) (hlb : has_basis lb pb sb) : has_basis (filter.prod la lb) (fun (i : ι × ι') => pa (prod.fst i) ∧ pb (prod.snd i))
  fun (i : ι × ι') => set.prod (sa (prod.fst i)) (sb (prod.snd i)) :=
  has_basis.inf (has_basis.comap prod.fst hla) (has_basis.comap prod.snd hlb)

theorem has_basis.prod' {α : Type u_1} {β : Type u_2} {la : filter α} {lb : filter β} {ι : Type u_3} {p : ι → Prop} {sa : ι → set α} {sb : ι → set β} (hla : has_basis la p sa) (hlb : has_basis lb p sb) (h_dir : ∀ {i j : ι}, p i → p j → ∃ (k : ι), p k ∧ sa k ⊆ sa i ∧ sb k ⊆ sb j) : has_basis (filter.prod la lb) p fun (i : ι) => set.prod (sa i) (sb i) := sorry

/-- `is_countably_generated f` means `f = generate s` for some countable `s`. -/
def is_countably_generated {α : Type u_1} (f : filter α)  :=
  ∃ (s : set (set α)), set.countable s ∧ f = generate s

/-- `is_countable_basis p s` means the image of `s` bounded by `p` is a countable filter basis. -/
structure is_countable_basis {α : Type u_1} {ι : Type u_4} (p : ι → Prop) (s : ι → set α) 
extends is_basis p s
where
  countable : set.countable (set_of p)

/-- We say that a filter `l` has a countable basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`, and the set
defined by `p` is countable. -/
structure has_countable_basis {α : Type u_1} {ι : Type u_4} (l : filter α) (p : ι → Prop) (s : ι → set α) 
extends has_basis l p s
where
  countable : set.countable (set_of p)

/-- A countable filter basis `B` on a type `α` is a nonempty countable collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure countable_filter_basis (α : Type u_6) 
extends filter_basis α
where
  countable : set.countable (filter_basis.sets _to_filter_basis)

-- For illustration purposes, the countable filter basis defining (at_top : filter ℕ)

protected instance nat.inhabited_countable_filter_basis : Inhabited (countable_filter_basis ℕ) :=
  { default := countable_filter_basis.mk (filter_basis.mk (filter_basis.sets Inhabited.default) sorry sorry) sorry }

theorem antimono_seq_of_seq {α : Type u_1} (s : ℕ → set α) : ∃ (t : ℕ → set α),
  (∀ (i j : ℕ), i ≤ j → t j ⊆ t i) ∧ (infi fun (i : ℕ) => principal (s i)) = infi fun (i : ℕ) => principal (t i) := sorry

theorem countable_binfi_eq_infi_seq {α : Type u_1} {ι : Type u_4} [complete_lattice α] {B : set ι} (Bcbl : set.countable B) (Bne : set.nonempty B) (f : ι → α) : ∃ (x : ℕ → ι), (infi fun (t : ι) => infi fun (H : t ∈ B) => f t) = infi fun (i : ℕ) => f (x i) := sorry

theorem countable_binfi_eq_infi_seq' {α : Type u_1} {ι : Type u_4} [complete_lattice α] {B : set ι} (Bcbl : set.countable B) (f : ι → α) {i₀ : ι} (h : f i₀ = ⊤) : ∃ (x : ℕ → ι), (infi fun (t : ι) => infi fun (H : t ∈ B) => f t) = infi fun (i : ℕ) => f (x i) := sorry

theorem countable_binfi_principal_eq_seq_infi {α : Type u_1} {B : set (set α)} (Bcbl : set.countable B) : ∃ (x : ℕ → set α), (infi fun (t : set α) => infi fun (H : t ∈ B) => principal t) = infi fun (i : ℕ) => principal (x i) :=
  countable_binfi_eq_infi_seq' Bcbl principal principal_univ

namespace is_countably_generated


/-- A set generating a countably generated filter. -/
def generating_set {α : Type u_1} {f : filter α} (h : is_countably_generated f) : set (set α) :=
  classical.some h

theorem countable_generating_set {α : Type u_1} {f : filter α} (h : is_countably_generated f) : set.countable (generating_set h) :=
  and.left (classical.some_spec h)

theorem eq_generate {α : Type u_1} {f : filter α} (h : is_countably_generated f) : f = generate (generating_set h) :=
  and.right (classical.some_spec h)

/-- A countable filter basis for a countably generated filter. -/
def countable_filter_basis {α : Type u_1} {l : filter α} (h : is_countably_generated l) : countable_filter_basis α :=
  countable_filter_basis.mk (filter_basis.mk (filter_basis.sets (filter_basis.of_sets (generating_set h))) sorry sorry)
    sorry

theorem filter_basis_filter {α : Type u_1} {l : filter α} (h : is_countably_generated l) : filter_basis.filter (countable_filter_basis.to_filter_basis (countable_filter_basis h)) = l := sorry

theorem has_countable_basis {α : Type u_1} {l : filter α} (h : is_countably_generated l) : has_countable_basis l (fun (t : set (set α)) => set.finite t ∧ t ⊆ generating_set h) fun (t : set (set α)) => ⋂₀t := sorry

theorem exists_countable_infi_principal {α : Type u_1} {f : filter α} (h : is_countably_generated f) : ∃ (s : set (set α)), set.countable s ∧ f = infi fun (t : set α) => infi fun (H : t ∈ s) => principal t := sorry

theorem exists_seq {α : Type u_1} {f : filter α} (cblb : is_countably_generated f) : ∃ (x : ℕ → set α), f = infi fun (i : ℕ) => principal (x i) := sorry

/-- If `f` is countably generated and `f.has_basis p s`, then `f` admits a decreasing basis
enumerated by natural numbers such that all sets have the form `s i`. More precisely, there is a
sequence `i n` such that `p (i n)` for all `n` and `s (i n)` is a decreasing sequence of sets which
forms a basis of `f`-/
theorem exists_antimono_subbasis {α : Type u_1} {ι : Type u_4} {f : filter α} (cblb : is_countably_generated f) {p : ι → Prop} {s : ι → set α} (hs : has_basis f p s) : ∃ (x : ℕ → ι), (∀ (i : ℕ), p (x i)) ∧ has_antimono_basis f (fun (_x : ℕ) => True) fun (i : ℕ) => s (x i) := sorry

/-- A countably generated filter admits a basis formed by a monotonically decreasing sequence of
sets. -/
theorem exists_antimono_basis {α : Type u_1} {f : filter α} (cblb : is_countably_generated f) : ∃ (x : ℕ → set α), has_antimono_basis f (fun (_x : ℕ) => True) x := sorry

end is_countably_generated


theorem has_countable_basis.is_countably_generated {α : Type u_1} {ι : Type u_4} {f : filter α} {p : ι → Prop} {s : ι → set α} (h : has_countable_basis f p s) : is_countably_generated f :=
  Exists.intro (set_of fun (t : set α) => ∃ (i : ι), p i ∧ s i = t)
    { left := set.countable.image (has_countable_basis.countable h) s,
      right := has_basis.eq_generate (has_countable_basis.to_has_basis h) }

theorem is_countably_generated_seq {α : Type u_1} (x : ℕ → set α) : is_countably_generated (infi fun (i : ℕ) => principal (x i)) := sorry

theorem is_countably_generated_of_seq {α : Type u_1} {f : filter α} (h : ∃ (x : ℕ → set α), f = infi fun (i : ℕ) => principal (x i)) : is_countably_generated f := sorry

theorem is_countably_generated_binfi_principal {α : Type u_1} {B : set (set α)} (h : set.countable B) : is_countably_generated (infi fun (s : set α) => infi fun (H : s ∈ B) => principal s) :=
  is_countably_generated_of_seq (countable_binfi_principal_eq_seq_infi h)

theorem is_countably_generated_iff_exists_antimono_basis {α : Type u_1} {f : filter α} : is_countably_generated f ↔ ∃ (x : ℕ → set α), has_antimono_basis f (fun (_x : ℕ) => True) x := sorry

theorem is_countably_generated_principal {α : Type u_1} (s : set α) : is_countably_generated (principal s) := sorry

namespace is_countably_generated


theorem inf {α : Type u_1} {f : filter α} {g : filter α} (hf : is_countably_generated f) (hg : is_countably_generated g) : is_countably_generated (f ⊓ g) := sorry

theorem inf_principal {α : Type u_1} {f : filter α} (h : is_countably_generated f) (s : set α) : is_countably_generated (f ⊓ principal s) :=
  inf h (is_countably_generated_principal s)

theorem exists_antimono_seq' {α : Type u_1} {f : filter α} (cblb : is_countably_generated f) : ∃ (x : ℕ → set α), (∀ (i j : ℕ), i ≤ j → x j ⊆ x i) ∧ ∀ {s : set α}, s ∈ f ↔ ∃ (i : ℕ), x i ⊆ s := sorry

protected theorem comap {α : Type u_1} {β : Type u_2} {l : filter β} (h : is_countably_generated l) (f : α → β) : is_countably_generated (comap f l) := sorry

