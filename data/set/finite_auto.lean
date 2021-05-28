/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.fintype.basic
import PostPort

universes u u_1 v u_2 x u_3 

namespace Mathlib

/-!
# Finite sets

This file defines predicates `finite : set α → Prop` and `infinite : set α → Prop` and proves some
basic facts about finite sets.
-/

namespace set


/-- A set is finite if the subtype is a fintype, i.e. there is a
  list that enumerates its members. -/
def finite {α : Type u} (s : set α)  :=
  Nonempty (fintype ↥s)

/-- A set is infinite if it is not finite. -/
def infinite {α : Type u} (s : set α)  :=
  ¬finite s

/-- The subtype corresponding to a finite set is a finite type. Note
that because `finite` isn't a typeclass, this will not fire if it
is made into an instance -/
def finite.fintype {α : Type u} {s : set α} (h : finite s) : fintype ↥s :=
  Classical.choice h

/-- Get a finset from a finite set -/
def finite.to_finset {α : Type u} {s : set α} (h : finite s) : finset α :=
  to_finset s

@[simp] theorem finite.mem_to_finset {α : Type u} {s : set α} {h : finite s} {a : α} : a ∈ finite.to_finset h ↔ a ∈ s :=
  mem_to_finset

@[simp] theorem finite.to_finset.nonempty {α : Type u} {s : set α} (h : finite s) : finset.nonempty (finite.to_finset h) ↔ set.nonempty s :=
  (fun (this : (∃ (x : α), x ∈ finite.to_finset h) ↔ ∃ (x : α), x ∈ s) => this)
    (exists_congr fun (_x : α) => finite.mem_to_finset)

@[simp] theorem finite.coe_to_finset {α : Type u_1} {s : set α} (h : finite s) : ↑(finite.to_finset h) = s :=
  coe_to_finset s

theorem finite.exists_finset {α : Type u} {s : set α} : finite s → ∃ (s' : finset α), ∀ (a : α), a ∈ s' ↔ a ∈ s := sorry

theorem finite.exists_finset_coe {α : Type u} {s : set α} (hs : finite s) : ∃ (s' : finset α), ↑s' = s :=
  Exists.intro (finite.to_finset hs) (finite.coe_to_finset hs)

/-- Finite sets can be lifted to finsets. -/
protected instance finset.can_lift {α : Type u} : can_lift (set α) (finset α) :=
  can_lift.mk coe finite sorry

theorem finite_mem_finset {α : Type u} (s : finset α) : finite (set_of fun (a : α) => a ∈ s) :=
  Nonempty.intro (fintype.of_finset s fun (_x : α) => iff.rfl)

theorem finite.of_fintype {α : Type u} [fintype α] (s : set α) : finite s :=
  Nonempty.intro (set_fintype s)

theorem exists_finite_iff_finset {α : Type u} {p : set α → Prop} : (∃ (s : set α), finite s ∧ p s) ↔ ∃ (s : finset α), p ↑s := sorry

/-- Membership of a subset of a finite type is decidable.

Using this as an instance leads to potential loops with `subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
def decidable_mem_of_fintype {α : Type u} [DecidableEq α] (s : set α) [fintype ↥s] (a : α) : Decidable (a ∈ s) :=
  decidable_of_iff (a ∈ to_finset s) mem_to_finset

protected instance fintype_empty {α : Type u} : fintype ↥∅ :=
  fintype.of_finset ∅ sorry

theorem empty_card {α : Type u} : fintype.card ↥∅ = 0 :=
  rfl

@[simp] theorem empty_card' {α : Type u} {h : fintype ↥∅} : fintype.card ↥∅ = 0 := sorry

@[simp] theorem finite_empty {α : Type u} : finite ∅ :=
  Nonempty.intro set.fintype_empty

protected instance finite.inhabited {α : Type u} : Inhabited (Subtype fun (s : set α) => finite s) :=
  { default := { val := ∅, property := finite_empty } }

/-- A `fintype` structure on `insert a s`. -/
def fintype_insert' {α : Type u} {a : α} (s : set α) [fintype ↥s] (h : ¬a ∈ s) : fintype ↥(insert a s) :=
  fintype.of_finset (finset.mk (a ::ₘ finset.val (to_finset s)) sorry) sorry

theorem card_fintype_insert' {α : Type u} {a : α} (s : set α) [fintype ↥s] (h : ¬a ∈ s) : fintype.card ↥(insert a s) = fintype.card ↥s + 1 := sorry

@[simp] theorem card_insert {α : Type u} {a : α} (s : set α) [fintype ↥s] (h : ¬a ∈ s) {d : fintype ↥(insert a s)} : fintype.card ↥(insert a s) = fintype.card ↥s + 1 := sorry

theorem card_image_of_inj_on {α : Type u} {β : Type v} {s : set α} [fintype ↥s] {f : α → β} [fintype ↥(f '' s)] (H : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → f x = f y → x = y) : fintype.card ↥(f '' s) = fintype.card ↥s := sorry

theorem card_image_of_injective {α : Type u} {β : Type v} (s : set α) [fintype ↥s] {f : α → β} [fintype ↥(f '' s)] (H : function.injective f) : fintype.card ↥(f '' s) = fintype.card ↥s :=
  card_image_of_inj_on fun (_x : α) (_x_1 : _x ∈ s) (_x_2 : α) (_x_3 : _x_2 ∈ s) (h : f _x = f _x_2) => H h

protected instance fintype_insert {α : Type u} [DecidableEq α] (a : α) (s : set α) [fintype ↥s] : fintype ↥(insert a s) :=
  dite (a ∈ s) (fun (h : a ∈ s) => eq.mpr sorry (eq.mpr sorry _inst_2)) fun (h : ¬a ∈ s) => fintype_insert' s h

@[simp] theorem finite.insert {α : Type u} (a : α) {s : set α} : finite s → finite (insert a s) :=
  fun (ᾰ : finite s) =>
    nonempty.dcases_on ᾰ
      fun (ᾰ : fintype ↥s) => idRhs (Nonempty (fintype ↥(insert a s))) (Nonempty.intro (set.fintype_insert a s))

theorem to_finset_insert {α : Type u} [DecidableEq α] {a : α} {s : set α} (hs : finite s) : finite.to_finset (finite.insert a hs) = insert a (finite.to_finset hs) := sorry

theorem finite.induction_on {α : Type u} {C : set α → Prop} {s : set α} (h : finite s) (H0 : C ∅) (H1 : ∀ {a : α} {s : set α}, ¬a ∈ s → finite s → C s → C (insert a s)) : C s := sorry

theorem finite.dinduction_on {α : Type u} {C : (s : set α) → finite s → Prop} {s : set α} (h : finite s) (H0 : C ∅ finite_empty) (H1 : ∀ {a : α} {s : set α}, ¬a ∈ s → ∀ (h : finite s), C s h → C (insert a s) (finite.insert a h)) : C s h := sorry

protected instance fintype_singleton {α : Type u} (a : α) : fintype ↥(singleton a) :=
  unique.fintype

@[simp] theorem card_singleton {α : Type u} (a : α) : fintype.card ↥(singleton a) = 1 :=
  fintype.card_of_subsingleton Inhabited.default

@[simp] theorem finite_singleton {α : Type u} (a : α) : finite (singleton a) :=
  Nonempty.intro (set.fintype_singleton a)

protected instance fintype_pure {α : Type u} (a : α) : fintype ↥(pure a) :=
  set.fintype_singleton

theorem finite_pure {α : Type u} (a : α) : finite (pure a) :=
  Nonempty.intro (set.fintype_pure a)

protected instance fintype_univ {α : Type u} [fintype α] : fintype ↥univ :=
  fintype.of_equiv α (equiv.symm (equiv.set.univ α))

theorem finite_univ {α : Type u} [fintype α] : finite univ :=
  Nonempty.intro set.fintype_univ

theorem infinite_univ_iff {α : Type u} : infinite univ ↔ infinite α := sorry

theorem infinite_univ {α : Type u} [h : infinite α] : infinite univ :=
  iff.mpr infinite_univ_iff h

theorem infinite_coe_iff {α : Type u} {s : set α} : infinite ↥s ↔ infinite s := sorry

theorem infinite.to_subtype {α : Type u} {s : set α} (h : infinite s) : infinite ↥s :=
  iff.mpr infinite_coe_iff h

/-- Embedding of `ℕ` into an infinite set. -/
def infinite.nat_embedding {α : Type u} (s : set α) (h : infinite s) : ℕ ↪ ↥s :=
  infinite.nat_embedding ↥s

theorem infinite.exists_subset_card_eq {α : Type u} {s : set α} (hs : infinite s) (n : ℕ) : ∃ (t : finset α), ↑t ⊆ s ∧ finset.card t = n := sorry

protected instance fintype_union {α : Type u} [DecidableEq α] (s : set α) (t : set α) [fintype ↥s] [fintype ↥t] : fintype ↥(s ∪ t) :=
  fintype.of_finset (to_finset s ∪ to_finset t) sorry

theorem finite.union {α : Type u} {s : set α} {t : set α} : finite s → finite t → finite (s ∪ t) := sorry

protected instance fintype_sep {α : Type u} (s : set α) (p : α → Prop) [fintype ↥s] [decidable_pred p] : fintype ↥(has_sep.sep (fun (a : α) => p a) s) :=
  fintype.of_finset (finset.filter p (to_finset s)) sorry

protected instance fintype_inter {α : Type u} (s : set α) (t : set α) [fintype ↥s] [decidable_pred t] : fintype ↥(s ∩ t) :=
  set.fintype_sep s t

/-- A `fintype` structure on a set defines a `fintype` structure on its subset. -/
def fintype_subset {α : Type u} (s : set α) {t : set α} [fintype ↥s] [decidable_pred t] (h : t ⊆ s) : fintype ↥t :=
  eq.mpr sorry (set.fintype_inter s t)

theorem finite.subset {α : Type u} {s : set α} : finite s → ∀ {t : set α}, t ⊆ s → finite t :=
  fun (ᾰ : finite s) {t : set α} (ᾰ_1 : t ⊆ s) =>
    nonempty.dcases_on ᾰ fun (ᾰ_1_1 : fintype ↥s) => idRhs (Nonempty (fintype ↥t)) (Nonempty.intro (fintype_subset s ᾰ_1))

theorem infinite_mono {α : Type u} {s : set α} {t : set α} (h : s ⊆ t) : infinite s → infinite t :=
  mt fun (ht : finite t) => finite.subset ht h

protected instance fintype_image {α : Type u} {β : Type v} [DecidableEq β] (s : set α) (f : α → β) [fintype ↥s] : fintype ↥(f '' s) :=
  fintype.of_finset (finset.image f (to_finset s)) sorry

protected instance fintype_range {α : Type u} {β : Type v} [DecidableEq β] (f : α → β) [fintype α] : fintype ↥(range f) :=
  fintype.of_finset (finset.image f finset.univ) sorry

theorem finite_range {α : Type u} {β : Type v} (f : α → β) [fintype α] : finite (range f) :=
  Nonempty.intro (set.fintype_range f)

theorem finite.image {α : Type u} {β : Type v} {s : set α} (f : α → β) : finite s → finite (f '' s) :=
  fun (ᾰ : finite s) =>
    nonempty.dcases_on ᾰ
      fun (ᾰ : fintype ↥s) => idRhs (Nonempty (fintype ↥(f '' s))) (Nonempty.intro (set.fintype_image s f))

theorem infinite_of_infinite_image {α : Type u} {β : Type v} (f : α → β) {s : set α} (hs : infinite (f '' s)) : infinite s :=
  mt (finite.image f) hs

theorem finite.dependent_image {α : Type u} {β : Type v} {s : set α} (hs : finite s) {F : (i : α) → i ∈ s → β} {t : set β} (H : ∀ (y : β), y ∈ t → ∃ (x : α), ∃ (hx : x ∈ s), y = F x hx) : finite t := sorry

protected instance fintype_map {α : Type u_1} {β : Type u_1} [DecidableEq β] (s : set α) (f : α → β) [fintype ↥s] : fintype ↥(f <$> s) :=
  set.fintype_image

theorem finite.map {α : Type u_1} {β : Type u_1} {s : set α} (f : α → β) : finite s → finite (f <$> s) :=
  finite.image

/-- If a function `f` has a partial inverse and sends a set `s` to a set with `[fintype]` instance,
then `s` has a `fintype` structure as well. -/
def fintype_of_fintype_image {α : Type u} {β : Type v} (s : set α) {f : α → β} {g : β → Option α} (I : function.is_partial_inv f g) [fintype ↥(f '' s)] : fintype ↥s :=
  fintype.of_finset (finset.mk (multiset.filter_map g (finset.val (to_finset (f '' s)))) sorry) sorry

theorem finite_of_finite_image {α : Type u} {β : Type v} {s : set α} {f : α → β} (hi : inj_on f s) : finite (f '' s) → finite s := sorry

theorem finite_image_iff {α : Type u} {β : Type v} {s : set α} {f : α → β} (hi : inj_on f s) : finite (f '' s) ↔ finite s :=
  { mp := finite_of_finite_image hi, mpr := finite.image f }

theorem infinite_image_iff {α : Type u} {β : Type v} {s : set α} {f : α → β} (hi : inj_on f s) : infinite (f '' s) ↔ infinite s :=
  not_congr (finite_image_iff hi)

theorem infinite_of_inj_on_maps_to {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (hi : inj_on f s) (hm : maps_to f s t) (hs : infinite s) : infinite t :=
  infinite_mono (iff.mp maps_to' hm) (iff.mpr (infinite_image_iff hi) hs)

theorem infinite_range_of_injective {α : Type u} {β : Type v} [infinite α] {f : α → β} (hi : function.injective f) : infinite (range f) := sorry

theorem infinite_of_injective_forall_mem {α : Type u} {β : Type v} [infinite α] {s : set β} {f : α → β} (hi : function.injective f) (hf : ∀ (x : α), f x ∈ s) : infinite s :=
  infinite_mono (eq.mp (Eq._oldrec (Eq.refl (∀ (x : α), f x ∈ s)) (Eq.symm (propext range_subset_iff))) hf)
    (infinite_range_of_injective hi)

theorem finite.preimage {α : Type u} {β : Type v} {s : set β} {f : α → β} (I : inj_on f (f ⁻¹' s)) (h : finite s) : finite (f ⁻¹' s) :=
  finite_of_finite_image I (finite.subset h (image_preimage_subset f s))

theorem finite.preimage_embedding {α : Type u} {β : Type v} {s : set β} (f : α ↪ β) (h : finite s) : finite (⇑f ⁻¹' s) := sorry

protected instance fintype_Union {α : Type u} [DecidableEq α] {ι : Type u_1} [fintype ι] (f : ι → set α) [(i : ι) → fintype ↥(f i)] : fintype ↥(Union fun (i : ι) => f i) :=
  fintype.of_finset (finset.bUnion finset.univ fun (i : ι) => to_finset (f i)) sorry

theorem finite_Union {α : Type u} {ι : Type u_1} [fintype ι] {f : ι → set α} (H : ∀ (i : ι), finite (f i)) : finite (Union fun (i : ι) => f i) :=
  Nonempty.intro (set.fintype_Union fun (i : ι) => f i)

/-- A union of sets with `fintype` structure over a set with `fintype` structure has a `fintype`
structure. -/
def fintype_set_bUnion {α : Type u} [DecidableEq α] {ι : Type u_1} {s : set ι} [fintype ↥s] (f : ι → set α) (H : (i : ι) → i ∈ s → fintype ↥(f i)) : fintype ↥(Union fun (i : ι) => Union fun (H : i ∈ s) => f i) :=
  eq.mpr sorry (set.fintype_Union fun (x : ↥s) => f ↑x)

protected instance fintype_set_bUnion' {α : Type u} [DecidableEq α] {ι : Type u_1} {s : set ι} [fintype ↥s] (f : ι → set α) [H : (i : ι) → fintype ↥(f i)] : fintype ↥(Union fun (i : ι) => Union fun (H : i ∈ s) => f i) :=
  fintype_set_bUnion (fun (i : ι) => f i) fun (i : ι) (_x : i ∈ s) => H i

theorem finite.sUnion {α : Type u} {s : set (set α)} (h : finite s) (H : ∀ (t : set α), t ∈ s → finite t) : finite (⋃₀s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finite (⋃₀s))) sUnion_eq_Union))
    (finite_Union (eq.mpr (id (propext set_coe.forall)) (eq.mp (Eq.refl (∀ (t : set α), t ∈ s → finite t)) H)))

theorem finite.bUnion {α : Type u_1} {ι : Type u_2} {s : set ι} {f : (i : ι) → i ∈ s → set α} : finite s → (∀ (i : ι) (H : i ∈ s), finite (f i H)) → finite (Union fun (i : ι) => Union fun (H : i ∈ s) => f i H) := sorry

protected instance fintype_lt_nat (n : ℕ) : fintype ↥(set_of fun (i : ℕ) => i < n) :=
  fintype.of_finset (finset.range n) sorry

protected instance fintype_le_nat (n : ℕ) : fintype ↥(set_of fun (i : ℕ) => i ≤ n) :=
  eq.mpr sorry (eq.mp sorry (set.fintype_lt_nat (n + 1)))

theorem finite_le_nat (n : ℕ) : finite (set_of fun (i : ℕ) => i ≤ n) :=
  Nonempty.intro (set.fintype_le_nat n)

theorem finite_lt_nat (n : ℕ) : finite (set_of fun (i : ℕ) => i < n) :=
  Nonempty.intro (set.fintype_lt_nat n)

protected instance fintype_prod {α : Type u} {β : Type v} (s : set α) (t : set β) [fintype ↥s] [fintype ↥t] : fintype ↥(set.prod s t) :=
  fintype.of_finset (finset.product (to_finset s) (to_finset t)) sorry

theorem finite.prod {α : Type u} {β : Type v} {s : set α} {t : set β} : finite s → finite t → finite (set.prod s t) := sorry

/-- `image2 f s t` is finitype if `s` and `t` are. -/
protected instance fintype_image2 {α : Type u} {β : Type v} {γ : Type x} [DecidableEq γ] (f : α → β → γ) (s : set α) (t : set β) [hs : fintype ↥s] [ht : fintype ↥t] : fintype ↥(image2 f s t) :=
  eq.mpr sorry (set.fintype_image (set.prod s t) fun (x : α × β) => f (prod.fst x) (prod.snd x))

theorem finite.image2 {α : Type u} {β : Type v} {γ : Type x} (f : α → β → γ) {s : set α} {t : set β} (hs : finite s) (ht : finite t) : finite (image2 f s t) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finite (image2 f s t))) (Eq.symm (image_prod f))))
    (finite.image (fun (x : α × β) => f (prod.fst x) (prod.snd x)) (finite.prod hs ht))

/-- If `s : set α` is a set with `fintype` instance and `f : α → set β` is a function such that
each `f a`, `a ∈ s`, has a `fintype` structure, then `s >>= f` has a `fintype` structure. -/
def fintype_bUnion {α : Type u_1} {β : Type u_1} [DecidableEq β] (s : set α) [fintype ↥s] (f : α → set β) (H : (a : α) → a ∈ s → fintype ↥(f a)) : fintype ↥(s >>= f) :=
  fintype_set_bUnion (fun (i : α) => f i) H

protected instance fintype_bUnion' {α : Type u_1} {β : Type u_1} [DecidableEq β] (s : set α) [fintype ↥s] (f : α → set β) [H : (a : α) → fintype ↥(f a)] : fintype ↥(s >>= f) :=
  fintype_bUnion s f fun (i : α) (_x : i ∈ s) => H i

theorem finite_bUnion {α : Type u_1} {β : Type u_1} {s : set α} {f : α → set β} : finite s → (∀ (a : α), a ∈ s → finite (f a)) → finite (s >>= f) := sorry

protected instance fintype_seq {α : Type u} {β : Type u} [DecidableEq β] (f : set (α → β)) (s : set α) [fintype ↥f] [fintype ↥s] : fintype ↥(f <*> s) :=
  eq.mpr sorry (set.fintype_bUnion' f fun (_x : α → β) => _x <$> s)

theorem finite.seq {α : Type u} {β : Type u} {f : set (α → β)} {s : set α} : finite f → finite s → finite (f <*> s) := sorry

/-- There are finitely many subsets of a given finite set -/
theorem finite.finite_subsets {α : Type u} {a : set α} (h : finite a) : finite (set_of fun (b : set α) => b ⊆ a) := sorry

theorem exists_min_image {α : Type u} {β : Type v} [linear_order β] (s : set α) (f : α → β) (h1 : finite s) : set.nonempty s → ∃ (a : α), ∃ (H : a ∈ s), ∀ (b : α), b ∈ s → f a ≤ f b := sorry

theorem exists_max_image {α : Type u} {β : Type v} [linear_order β] (s : set α) (f : α → β) (h1 : finite s) : set.nonempty s → ∃ (a : α), ∃ (H : a ∈ s), ∀ (b : α), b ∈ s → f b ≤ f a := sorry

end set


namespace finset


theorem finite_to_set {α : Type u} (s : finset α) : set.finite ↑s :=
  set.finite_mem_finset s

@[simp] theorem coe_bUnion {α : Type u} {β : Type v} [DecidableEq β] {s : finset α} {f : α → finset β} : ↑(finset.bUnion s f) = set.Union fun (x : α) => set.Union fun (H : x ∈ ↑s) => ↑(f x) := sorry

@[simp] theorem finite_to_set_to_finset {α : Type u_1} (s : finset α) : set.finite.to_finset (finite_to_set s) = s := sorry

end finset


namespace set


theorem finite_subset_Union {α : Type u} {s : set α} (hs : finite s) {ι : Type u_1} {t : ι → set α} (h : s ⊆ Union fun (i : ι) => t i) : ∃ (I : set ι), finite I ∧ s ⊆ Union fun (i : ι) => Union fun (H : i ∈ I) => t i := sorry

theorem eq_finite_Union_of_finite_subset_Union {α : Type u} {ι : Type u_1} {s : ι → set α} {t : set α} (tfin : finite t) (h : t ⊆ Union fun (i : ι) => s i) : ∃ (I : set ι),
  finite I ∧
    ∃ (σ : ↥(set_of fun (i : ι) => i ∈ I) → set α),
      (∀ (i : ↥(set_of fun (i : ι) => i ∈ I)), finite (σ i)) ∧
        (∀ (i : ↥(set_of fun (i : ι) => i ∈ I)), σ i ⊆ s ↑i) ∧ t = Union fun (i : ↥(set_of fun (i : ι) => i ∈ I)) => σ i := sorry

/-- An increasing union distributes over finite intersection. -/
theorem Union_Inter_of_monotone {ι : Type u_1} {ι' : Type u_2} {α : Type u_3} [fintype ι] [linear_order ι'] [Nonempty ι'] {s : ι → ι' → set α} (hs : ∀ (i : ι), monotone (s i)) : (Union fun (j : ι') => Inter fun (i : ι) => s i j) = Inter fun (i : ι) => Union fun (j : ι') => s i j := sorry

protected instance nat.fintype_Iio (n : ℕ) : fintype ↥(Iio n) :=
  fintype.of_finset (finset.range n) sorry

/--
If `P` is some relation between terms of `γ` and sets in `γ`,
such that every finite set `t : set γ` has some `c : γ` related to it,
then there is a recursively defined sequence `u` in `γ`
so `u n` is related to the image of `{0, 1, ..., n-1}` under `u`.

(We use this later to show sequentially compact sets
are totally bounded.)
-/
theorem seq_of_forall_finite_exists {γ : Type u_1} {P : γ → set γ → Prop} (h : ∀ (t : set γ), finite t → ∃ (c : γ), P c t) : ∃ (u : ℕ → γ), ∀ (n : ℕ), P (u n) (u '' Iio n) := sorry

theorem finite_range_ite {α : Type u} {β : Type v} {p : α → Prop} [decidable_pred p] {f : α → β} {g : α → β} (hf : finite (range f)) (hg : finite (range g)) : finite (range fun (x : α) => ite (p x) (f x) (g x)) :=
  finite.subset (finite.union hf hg) range_ite_subset

theorem finite_range_const {α : Type u} {β : Type v} {c : β} : finite (range fun (x : α) => c) :=
  finite.subset (finite_singleton c) range_const_subset

theorem range_find_greatest_subset {α : Type u} {P : α → ℕ → Prop} [(x : α) → decidable_pred (P x)] {b : ℕ} : (range fun (x : α) => nat.find_greatest (P x) b) ⊆ ↑(finset.range (b + 1)) := sorry

theorem finite_range_find_greatest {α : Type u} {P : α → ℕ → Prop} [(x : α) → decidable_pred (P x)] {b : ℕ} : finite (range fun (x : α) => nat.find_greatest (P x) b) :=
  finite.subset (finset.finite_to_set (finset.range (b + 1))) range_find_greatest_subset

theorem card_lt_card {α : Type u} {s : set α} {t : set α} [fintype ↥s] [fintype ↥t] (h : s ⊂ t) : fintype.card ↥s < fintype.card ↥t := sorry

theorem card_le_of_subset {α : Type u} {s : set α} {t : set α} [fintype ↥s] [fintype ↥t] (hsub : s ⊆ t) : fintype.card ↥s ≤ fintype.card ↥t := sorry

theorem eq_of_subset_of_card_le {α : Type u} {s : set α} {t : set α} [fintype ↥s] [fintype ↥t] (hsub : s ⊆ t) (hcard : fintype.card ↥t ≤ fintype.card ↥s) : s = t :=
  or.elim (eq_or_ssubset_of_subset hsub) id fun (h : s ⊂ t) => absurd hcard (not_le_of_lt (card_lt_card h))

theorem subset_iff_to_finset_subset {α : Type u} (s : set α) (t : set α) [fintype ↥s] [fintype ↥t] : s ⊆ t ↔ to_finset s ⊆ to_finset t :=
  { mp := fun (h : s ⊆ t) (x : α) (hx : x ∈ to_finset s) => iff.mpr mem_to_finset (h (iff.mp mem_to_finset hx)),
    mpr :=
      fun (h : to_finset s ⊆ to_finset t) (x : α) (hx : x ∈ s) => iff.mp mem_to_finset (h (iff.mpr mem_to_finset hx)) }

theorem card_range_of_injective {α : Type u} {β : Type v} [fintype α] {f : α → β} (hf : function.injective f) [fintype ↥(range f)] : fintype.card ↥(range f) = fintype.card α :=
  Eq.symm (fintype.card_congr (equiv.set.range f hf))

theorem finite.exists_maximal_wrt {α : Type u} {β : Type v} [partial_order β] (f : α → β) (s : set α) (h : finite s) : set.nonempty s → ∃ (a : α), ∃ (H : a ∈ s), ∀ (a' : α), a' ∈ s → f a ≤ f a' → f a = f a' := sorry

theorem finite.card_to_finset {α : Type u} {s : set α} [fintype ↥s] (h : finite s) : finset.card (finite.to_finset h) = fintype.card ↥s := sorry

theorem to_finset_compl {α : Type u_1} [fintype α] (s : set α) : to_finset (sᶜ) = (to_finset sᶜ) := sorry

theorem to_finset_inter {α : Type u_1} [fintype α] (s : set α) (t : set α) : to_finset (s ∩ t) = to_finset s ∩ to_finset t := sorry

theorem to_finset_union {α : Type u_1} [fintype α] (s : set α) (t : set α) : to_finset (s ∪ t) = to_finset s ∪ to_finset t := sorry

/--A finite set is bounded above.-/
protected theorem finite.bdd_above {α : Type u} [semilattice_sup α] [Nonempty α] {s : set α} (hs : finite s) : bdd_above s :=
  finite.induction_on hs bdd_above_empty
    fun (a : α) (s : set α) (_x : ¬a ∈ s) (_x : finite s) (h : bdd_above s) => bdd_above.insert a h

/--A finite union of sets which are all bounded above is still bounded above.-/
theorem finite.bdd_above_bUnion {α : Type u} {β : Type v} [semilattice_sup α] [Nonempty α] {I : set β} {S : β → set α} (H : finite I) : bdd_above (Union fun (i : β) => Union fun (H : i ∈ I) => S i) ↔ ∀ (i : β), i ∈ I → bdd_above (S i) := sorry

/--A finite set is bounded below.-/
protected theorem finite.bdd_below {α : Type u} [semilattice_inf α] [Nonempty α] {s : set α} (hs : finite s) : bdd_below s :=
  finite.bdd_above hs

/--A finite union of sets which are all bounded below is still bounded below.-/
theorem finite.bdd_below_bUnion {α : Type u} {β : Type v} [semilattice_inf α] [Nonempty α] {I : set β} {S : β → set α} (H : finite I) : bdd_below (Union fun (i : β) => Union fun (H : i ∈ I) => S i) ↔ ∀ (i : β), i ∈ I → bdd_below (S i) :=
  finite.bdd_above_bUnion H

end set


namespace finset


/-- A finset is bounded above. -/
protected theorem bdd_above {α : Type u} [semilattice_sup α] [Nonempty α] (s : finset α) : bdd_above ↑s :=
  set.finite.bdd_above (finite_to_set s)

/-- A finset is bounded below. -/
protected theorem bdd_below {α : Type u} [semilattice_inf α] [Nonempty α] (s : finset α) : bdd_below ↑s :=
  set.finite.bdd_below (finite_to_set s)

end finset


theorem fintype.exists_max {α : Type u} [fintype α] [Nonempty α] {β : Type u_1} [linear_order β] (f : α → β) : ∃ (x₀ : α), ∀ (x : α), f x ≤ f x₀ := sorry

