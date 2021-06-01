/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.outer_measure
import Mathlib.order.filter.countable_Inter
import Mathlib.data.set.accumulate
import Mathlib.PostPort

universes u_6 l u_1 u_2 u_5 u_3 u_4 

namespace Mathlib

/-!
# Measure spaces

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ennreal`.

We introduce the following typeclasses for measures:

* `probability_measure μ`: `μ univ = 1`;
* `finite_measure μ`: `μ univ < ⊤`;
* `sigma_finite μ`: there exists a countable collection of measurable sets that cover `univ`
  where `μ` is finite;
* `locally_finite_measure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ⊤`;
* `has_no_atoms μ` : `∀ x, μ {x} = 0`; possibly should be redefined as
  `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `measure.of_measurable` and `outer_measure.to_measure` are two important ways to define a measure.

## Implementation notes

Given `μ : measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `measure.of_measurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `outer_measure.to_measure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generate_from_of_Union`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of the
  more general `ext_of_generate_from_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generate_from_of_Union` using
  `C ∪ {univ}`, but is easier to work with.

A `measure_space` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/

namespace measure_theory


/-- A measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure. -/
structure measure (α : Type u_6) [measurable_space α] extends outer_measure α where
  m_Union :
    ∀ {f : ℕ → set α},
      (∀ (i : ℕ), is_measurable (f i)) →
        pairwise (disjoint on f) →
          outer_measure.measure_of _to_outer_measure (set.Union fun (i : ℕ) => f i) =
            tsum fun (i : ℕ) => outer_measure.measure_of _to_outer_measure (f i)
  trimmed : outer_measure.trim _to_outer_measure = _to_outer_measure

/-- Measure projections for a measure space.

For measurable sets this returns the measure assigned by the `measure_of` field in `measure`.
But we can extend this to _all_ sets, but using the outer measure. This gives us monotonicity and
subadditivity for all sets.
-/
protected instance measure.has_coe_to_fun {α : Type u_1} [measurable_space α] :
    has_coe_to_fun (measure α) :=
  has_coe_to_fun.mk (fun (_x : measure α) => set α → ennreal)
    fun (m : measure α) => ⇑(measure.to_outer_measure m)

namespace measure


/-! ### General facts about measures -/

/-- Obtain a measure by giving a countably additive function that sends `∅` to `0`. -/
def of_measurable {α : Type u_1} [measurable_space α] (m : (s : set α) → is_measurable s → ennreal)
    (m0 : m ∅ is_measurable.empty = 0)
    (mU :
      ∀ {f : ℕ → set α} (h : ∀ (i : ℕ), is_measurable (f i)),
        pairwise (disjoint on f) →
          m (set.Union fun (i : ℕ) => f i) (of_measurable._proof_1 h) =
            tsum fun (i : ℕ) => m (f i) (h i)) :
    measure α :=
  mk
    (outer_measure.mk (outer_measure.measure_of (induced_outer_measure m is_measurable.empty m0))
      sorry sorry sorry)
    sorry sorry

theorem of_measurable_apply {α : Type u_1} [measurable_space α]
    {m : (s : set α) → is_measurable s → ennreal} {m0 : m ∅ is_measurable.empty = 0}
    {mU :
      ∀ {f : ℕ → set α} (h : ∀ (i : ℕ), is_measurable (f i)),
        pairwise (disjoint on f) →
          m (set.Union fun (i : ℕ) => f i) (is_measurable.Union h) =
            tsum fun (i : ℕ) => m (f i) (h i)}
    (s : set α) (hs : is_measurable s) : coe_fn (of_measurable m m0 mU) s = m s hs :=
  induced_outer_measure_eq m0 mU hs

theorem to_outer_measure_injective {α : Type u_1} [measurable_space α] :
    function.injective to_outer_measure :=
  sorry

theorem ext {α : Type u_1} [measurable_space α] {μ₁ : measure α} {μ₂ : measure α}
    (h : ∀ (s : set α), is_measurable s → coe_fn μ₁ s = coe_fn μ₂ s) : μ₁ = μ₂ :=
  sorry

theorem ext_iff {α : Type u_1} [measurable_space α] {μ₁ : measure α} {μ₂ : measure α} :
    μ₁ = μ₂ ↔ ∀ (s : set α), is_measurable s → coe_fn μ₁ s = coe_fn μ₂ s :=
  { mp :=
      fun (ᾰ : μ₁ = μ₂) (s : set α) (hs : is_measurable s) => Eq._oldrec (Eq.refl (coe_fn μ₁ s)) ᾰ,
    mpr := ext }

end measure


@[simp] theorem coe_to_outer_measure {α : Type u_1} [measurable_space α] {μ : measure α} :
    ⇑(measure.to_outer_measure μ) = ⇑μ :=
  rfl

theorem to_outer_measure_apply {α : Type u_1} [measurable_space α] {μ : measure α} (s : set α) :
    coe_fn (measure.to_outer_measure μ) s = coe_fn μ s :=
  rfl

theorem measure_eq_trim {α : Type u_1} [measurable_space α] {μ : measure α} (s : set α) :
    coe_fn μ s = coe_fn (outer_measure.trim (measure.to_outer_measure μ)) s :=
  sorry

theorem measure_eq_infi {α : Type u_1} [measurable_space α] {μ : measure α} (s : set α) :
    coe_fn μ s =
        infi
          fun (t : set α) =>
            infi fun (st : s ⊆ t) => infi fun (ht : is_measurable t) => coe_fn μ t :=
  sorry

/-- A variant of `measure_eq_infi` which has a single `infi`. This is useful when applying a
  lemma next that only works for non-empty infima, in which case you can use
  `nonempty_measurable_superset`. -/
theorem measure_eq_infi' {α : Type u_1} [measurable_space α] (μ : measure α) (s : set α) :
    coe_fn μ s = infi fun (t : Subtype fun (t : set α) => s ⊆ t ∧ is_measurable t) => coe_fn μ ↑t :=
  sorry

theorem measure_eq_induced_outer_measure {α : Type u_1} [measurable_space α] {μ : measure α}
    {s : set α} :
    coe_fn μ s =
        coe_fn
          (induced_outer_measure (fun (s : set α) (_x : is_measurable s) => coe_fn μ s)
            is_measurable.empty (outer_measure.empty (measure.to_outer_measure μ)))
          s :=
  measure_eq_trim s

theorem to_outer_measure_eq_induced_outer_measure {α : Type u_1} [measurable_space α]
    {μ : measure α} :
    measure.to_outer_measure μ =
        induced_outer_measure (fun (s : set α) (_x : is_measurable s) => coe_fn μ s)
          is_measurable.empty (outer_measure.empty (measure.to_outer_measure μ)) :=
  Eq.symm (measure.trimmed μ)

theorem measure_eq_extend {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    (hs : is_measurable s) :
    coe_fn μ s = extend (fun (t : set α) (ht : is_measurable t) => coe_fn μ t) s :=
  sorry

@[simp] theorem measure_empty {α : Type u_1} [measurable_space α] {μ : measure α} :
    coe_fn μ ∅ = 0 :=
  outer_measure.empty (measure.to_outer_measure μ)

theorem nonempty_of_measure_ne_zero {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    (h : coe_fn μ s ≠ 0) : set.nonempty s :=
  iff.mp set.ne_empty_iff_nonempty fun (h' : s = ∅) => h (Eq.symm h' ▸ measure_empty)

theorem measure_mono {α : Type u_1} [measurable_space α] {μ : measure α} {s₁ : set α} {s₂ : set α}
    (h : s₁ ⊆ s₂) : coe_fn μ s₁ ≤ coe_fn μ s₂ :=
  outer_measure.mono (measure.to_outer_measure μ) h

theorem measure_mono_null {α : Type u_1} [measurable_space α] {μ : measure α} {s₁ : set α}
    {s₂ : set α} (h : s₁ ⊆ s₂) (h₂ : coe_fn μ s₂ = 0) : coe_fn μ s₁ = 0 :=
  iff.mp nonpos_iff_eq_zero (h₂ ▸ measure_mono h)

theorem measure_mono_top {α : Type u_1} [measurable_space α] {μ : measure α} {s₁ : set α}
    {s₂ : set α} (h : s₁ ⊆ s₂) (h₁ : coe_fn μ s₁ = ⊤) : coe_fn μ s₂ = ⊤ :=
  top_unique (h₁ ▸ measure_mono h)

theorem exists_is_measurable_superset {α : Type u_1} [measurable_space α] (μ : measure α)
    (s : set α) : ∃ (t : set α), s ⊆ t ∧ is_measurable t ∧ coe_fn μ t = coe_fn μ s :=
  sorry

/-- A measurable set `t ⊇ s` such that `μ t = μ s`. -/
def to_measurable {α : Type u_1} [measurable_space α] (μ : measure α) (s : set α) : set α :=
  classical.some (exists_is_measurable_superset μ s)

theorem subset_to_measurable {α : Type u_1} [measurable_space α] (μ : measure α) (s : set α) :
    s ⊆ to_measurable μ s :=
  and.left (classical.some_spec (exists_is_measurable_superset μ s))

@[simp] theorem is_measurable_to_measurable {α : Type u_1} [measurable_space α] (μ : measure α)
    (s : set α) : is_measurable (to_measurable μ s) :=
  and.left (and.right (classical.some_spec (exists_is_measurable_superset μ s)))

@[simp] theorem measure_to_measurable {α : Type u_1} [measurable_space α] {μ : measure α}
    (s : set α) : coe_fn μ (to_measurable μ s) = coe_fn μ s :=
  and.right (and.right (classical.some_spec (exists_is_measurable_superset μ s)))

theorem exists_is_measurable_superset_of_null {α : Type u_1} [measurable_space α] {μ : measure α}
    {s : set α} (h : coe_fn μ s = 0) : ∃ (t : set α), s ⊆ t ∧ is_measurable t ∧ coe_fn μ t = 0 :=
  sorry

theorem exists_is_measurable_superset_iff_measure_eq_zero {α : Type u_1} [measurable_space α]
    {μ : measure α} {s : set α} :
    (∃ (t : set α), s ⊆ t ∧ is_measurable t ∧ coe_fn μ t = 0) ↔ coe_fn μ s = 0 :=
  sorry

theorem measure_Union_le {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α}
    [encodable β] (s : β → set α) :
    coe_fn μ (set.Union fun (i : β) => s i) ≤ tsum fun (i : β) => coe_fn μ (s i) :=
  outer_measure.Union (measure.to_outer_measure μ) fun (i : β) => s i

theorem measure_bUnion_le {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α}
    {s : set β} (hs : set.countable s) (f : β → set α) :
    coe_fn μ (set.Union fun (b : β) => set.Union fun (H : b ∈ s) => f b) ≤
        tsum fun (p : ↥s) => coe_fn μ (f ↑p) :=
  sorry

theorem measure_bUnion_finset_le {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α}
    (s : finset β) (f : β → set α) :
    coe_fn μ (set.Union fun (b : β) => set.Union fun (H : b ∈ s) => f b) ≤
        finset.sum s fun (p : β) => coe_fn μ (f p) :=
  sorry

theorem measure_bUnion_lt_top {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α}
    {s : set β} {f : β → set α} (hs : set.finite s) (hfin : ∀ (i : β), i ∈ s → coe_fn μ (f i) < ⊤) :
    coe_fn μ (set.Union fun (i : β) => set.Union fun (H : i ∈ s) => f i) < ⊤ :=
  sorry

theorem measure_Union_null {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α}
    [encodable β] {s : β → set α} :
    (∀ (i : β), coe_fn μ (s i) = 0) → coe_fn μ (set.Union fun (i : β) => s i) = 0 :=
  outer_measure.Union_null (measure.to_outer_measure μ)

theorem measure_Union_null_iff {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    [encodable ι] {s : ι → set α} :
    coe_fn μ (set.Union fun (i : ι) => s i) = 0 ↔ ∀ (i : ι), coe_fn μ (s i) = 0 :=
  { mp :=
      fun (h : coe_fn μ (set.Union fun (i : ι) => s i) = 0) (i : ι) =>
        measure_mono_null (set.subset_Union s i) h,
    mpr := measure_Union_null }

theorem measure_union_le {α : Type u_1} [measurable_space α] {μ : measure α} (s₁ : set α)
    (s₂ : set α) : coe_fn μ (s₁ ∪ s₂) ≤ coe_fn μ s₁ + coe_fn μ s₂ :=
  outer_measure.union (measure.to_outer_measure μ) s₁ s₂

theorem measure_union_null {α : Type u_1} [measurable_space α] {μ : measure α} {s₁ : set α}
    {s₂ : set α} : coe_fn μ s₁ = 0 → coe_fn μ s₂ = 0 → coe_fn μ (s₁ ∪ s₂) = 0 :=
  outer_measure.union_null (measure.to_outer_measure μ)

theorem measure_union_null_iff {α : Type u_1} [measurable_space α] {μ : measure α} {s₁ : set α}
    {s₂ : set α} : coe_fn μ (s₁ ∪ s₂) = 0 ↔ coe_fn μ s₁ = 0 ∧ coe_fn μ s₂ = 0 :=
  sorry

theorem measure_Union {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α}
    [encodable β] {f : β → set α} (hn : pairwise (disjoint on f))
    (h : ∀ (i : β), is_measurable (f i)) :
    coe_fn μ (set.Union fun (i : β) => f i) = tsum fun (i : β) => coe_fn μ (f i) :=
  sorry

theorem measure_union {α : Type u_1} [measurable_space α] {μ : measure α} {s₁ : set α} {s₂ : set α}
    (hd : disjoint s₁ s₂) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) :
    coe_fn μ (s₁ ∪ s₂) = coe_fn μ s₁ + coe_fn μ s₂ :=
  sorry

theorem measure_bUnion {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α}
    {s : set β} {f : β → set α} (hs : set.countable s) (hd : set.pairwise_on s (disjoint on f))
    (h : ∀ (b : β), b ∈ s → is_measurable (f b)) :
    coe_fn μ (set.Union fun (b : β) => set.Union fun (H : b ∈ s) => f b) =
        tsum fun (p : ↥s) => coe_fn μ (f ↑p) :=
  sorry

theorem measure_sUnion {α : Type u_1} [measurable_space α] {μ : measure α} {S : set (set α)}
    (hs : set.countable S) (hd : set.pairwise_on S disjoint)
    (h : ∀ (s : set α), s ∈ S → is_measurable s) :
    coe_fn μ (⋃₀S) = tsum fun (s : ↥S) => coe_fn μ ↑s :=
  sorry

theorem measure_bUnion_finset {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    {s : finset ι} {f : ι → set α} (hd : set.pairwise_on (↑s) (disjoint on f))
    (hm : ∀ (b : ι), b ∈ s → is_measurable (f b)) :
    coe_fn μ (set.Union fun (b : ι) => set.Union fun (H : b ∈ s) => f b) =
        finset.sum s fun (p : ι) => coe_fn μ (f p) :=
  sorry

/-- If `s` is a countable set, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem tsum_measure_preimage_singleton {α : Type u_1} {β : Type u_2} [measurable_space α]
    {μ : measure α} {s : set β} (hs : set.countable s) {f : α → β}
    (hf : ∀ (y : β), y ∈ s → is_measurable (f ⁻¹' singleton y)) :
    (tsum fun (b : ↥s) => coe_fn μ (f ⁻¹' singleton ↑b)) = coe_fn μ (f ⁻¹' s) :=
  sorry

/-- If `s` is a `finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem sum_measure_preimage_singleton {α : Type u_1} {β : Type u_2} [measurable_space α]
    {μ : measure α} (s : finset β) {f : α → β}
    (hf : ∀ (y : β), y ∈ s → is_measurable (f ⁻¹' singleton y)) :
    (finset.sum s fun (b : β) => coe_fn μ (f ⁻¹' singleton b)) = coe_fn μ (f ⁻¹' ↑s) :=
  sorry

theorem measure_diff {α : Type u_1} [measurable_space α] {μ : measure α} {s₁ : set α} {s₂ : set α}
    (h : s₂ ⊆ s₁) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) (h_fin : coe_fn μ s₂ < ⊤) :
    coe_fn μ (s₁ \ s₂) = coe_fn μ s₁ - coe_fn μ s₂ :=
  sorry

theorem measure_compl {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    (h₁ : is_measurable s) (h_fin : coe_fn μ s < ⊤) :
    coe_fn μ (sᶜ) = coe_fn μ set.univ - coe_fn μ s :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (coe_fn μ (sᶜ) = coe_fn μ set.univ - coe_fn μ s))
        (set.compl_eq_univ_diff s)))
    (measure_diff (set.subset_univ s) is_measurable.univ h₁ h_fin)

theorem sum_measure_le_measure_univ {α : Type u_1} {ι : Type u_5} [measurable_space α]
    {μ : measure α} {s : finset ι} {t : ι → set α} (h : ∀ (i : ι), i ∈ s → is_measurable (t i))
    (H : set.pairwise_on (↑s) (disjoint on t)) :
    (finset.sum s fun (i : ι) => coe_fn μ (t i)) ≤ coe_fn μ set.univ :=
  sorry

theorem tsum_measure_le_measure_univ {α : Type u_1} {ι : Type u_5} [measurable_space α]
    {μ : measure α} {s : ι → set α} (hs : ∀ (i : ι), is_measurable (s i))
    (H : pairwise (disjoint on s)) : (tsum fun (i : ι) => coe_fn μ (s i)) ≤ coe_fn μ set.univ :=
  sorry

/-- Pigeonhole principle for measure spaces: if `∑' i, μ (s i) > μ univ`, then
one of the intersections `s i ∩ s j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_tsum_measure {α : Type u_1} {ι : Type u_5}
    [measurable_space α] (μ : measure α) {s : ι → set α} (hs : ∀ (i : ι), is_measurable (s i))
    (H : coe_fn μ set.univ < tsum fun (i : ι) => coe_fn μ (s i)) :
    ∃ (i : ι), ∃ (j : ι), ∃ (h : i ≠ j), set.nonempty (s i ∩ s j) :=
  sorry

/-- Pigeonhole principle for measure spaces: if `s` is a `finset` and
`∑ i in s, μ (t i) > μ univ`, then one of the intersections `t i ∩ t j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_sum_measure {α : Type u_1} {ι : Type u_5}
    [measurable_space α] (μ : measure α) {s : finset ι} {t : ι → set α}
    (h : ∀ (i : ι), i ∈ s → is_measurable (t i))
    (H : coe_fn μ set.univ < finset.sum s fun (i : ι) => coe_fn μ (t i)) :
    ∃ (i : ι), ∃ (H : i ∈ s), ∃ (j : ι), ∃ (H : j ∈ s), ∃ (h : i ≠ j), set.nonempty (t i ∩ t j) :=
  sorry

/-- Continuity from below: the measure of the union of a directed sequence of measurable sets
is the supremum of the measures. -/
theorem measure_Union_eq_supr {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    [encodable ι] {s : ι → set α} (h : ∀ (i : ι), is_measurable (s i))
    (hd : directed has_subset.subset s) :
    coe_fn μ (set.Union fun (i : ι) => s i) = supr fun (i : ι) => coe_fn μ (s i) :=
  sorry

theorem measure_bUnion_eq_supr {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    {s : ι → set α} {t : set ι} (ht : set.countable t) (h : ∀ (i : ι), i ∈ t → is_measurable (s i))
    (hd : directed_on (has_subset.subset on s) t) :
    coe_fn μ (set.Union fun (i : ι) => set.Union fun (H : i ∈ t) => s i) =
        supr fun (i : ι) => supr fun (H : i ∈ t) => coe_fn μ (s i) :=
  sorry

/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the infimum of the measures. -/
theorem measure_Inter_eq_infi {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    [encodable ι] {s : ι → set α} (h : ∀ (i : ι), is_measurable (s i)) (hd : directed superset s)
    (hfin : ∃ (i : ι), coe_fn μ (s i) < ⊤) :
    coe_fn μ (set.Inter fun (i : ι) => s i) = infi fun (i : ι) => coe_fn μ (s i) :=
  sorry

theorem measure_eq_inter_diff {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {t : set α} (hs : is_measurable s) (ht : is_measurable t) :
    coe_fn μ s = coe_fn μ (s ∩ t) + coe_fn μ (s \ t) :=
  sorry

theorem measure_union_add_inter {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {t : set α} (hs : is_measurable s) (ht : is_measurable t) :
    coe_fn μ (s ∪ t) + coe_fn μ (s ∩ t) = coe_fn μ s + coe_fn μ t :=
  sorry

/-- Continuity from below: the measure of the union of an increasing sequence of measurable sets
is the limit of the measures. -/
theorem tendsto_measure_Union {α : Type u_1} [measurable_space α] {μ : measure α} {s : ℕ → set α}
    (hs : ∀ (n : ℕ), is_measurable (s n)) (hm : monotone s) :
    filter.tendsto (⇑μ ∘ s) filter.at_top (nhds (coe_fn μ (set.Union fun (n : ℕ) => s n))) :=
  sorry

/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the limit of the measures. -/
theorem tendsto_measure_Inter {α : Type u_1} [measurable_space α] {μ : measure α} {s : ℕ → set α}
    (hs : ∀ (n : ℕ), is_measurable (s n)) (hm : ∀ {n m : ℕ}, n ≤ m → s m ⊆ s n)
    (hf : ∃ (i : ℕ), coe_fn μ (s i) < ⊤) :
    filter.tendsto (⇑μ ∘ s) filter.at_top (nhds (coe_fn μ (set.Inter fun (n : ℕ) => s n))) :=
  sorry

/-- One direction of the Borel-Cantelli lemma: if (sᵢ) is a sequence of measurable sets such that
  ∑ μ sᵢ exists, then the limit superior of the sᵢ is a null set. -/
theorem measure_limsup_eq_zero {α : Type u_1} [measurable_space α] {μ : measure α} {s : ℕ → set α}
    (hs : ∀ (i : ℕ), is_measurable (s i)) (hs' : (tsum fun (i : ℕ) => coe_fn μ (s i)) ≠ ⊤) :
    coe_fn μ (filter.limsup filter.at_top s) = 0 :=
  sorry

theorem measure_if {α : Type u_1} {β : Type u_2} [measurable_space α] {x : β} {t : set β}
    {s : set α} {μ : measure α} :
    coe_fn μ (ite (x ∈ t) s ∅) = set.indicator t (fun (_x : β) => coe_fn μ s) x :=
  sorry

/-- Obtain a measure by giving an outer measure where all sets in the σ-algebra are
  Carathéodory measurable. -/
def outer_measure.to_measure {α : Type u_1} [ms : measurable_space α] (m : outer_measure α)
    (h : ms ≤ outer_measure.caratheodory m) : measure α :=
  measure.of_measurable (fun (s : set α) (_x : is_measurable s) => coe_fn m s)
    (outer_measure.empty m) sorry

theorem le_to_outer_measure_caratheodory {α : Type u_1} [ms : measurable_space α] (μ : measure α) :
    ms ≤ outer_measure.caratheodory (measure.to_outer_measure μ) :=
  sorry

@[simp] theorem to_measure_to_outer_measure {α : Type u_1} [ms : measurable_space α]
    (m : outer_measure α) (h : ms ≤ outer_measure.caratheodory m) :
    measure.to_outer_measure (outer_measure.to_measure m h) = outer_measure.trim m :=
  rfl

@[simp] theorem to_measure_apply {α : Type u_1} [ms : measurable_space α] (m : outer_measure α)
    (h : ms ≤ outer_measure.caratheodory m) {s : set α} (hs : is_measurable s) :
    coe_fn (outer_measure.to_measure m h) s = coe_fn m s :=
  outer_measure.trim_eq m hs

theorem le_to_measure_apply {α : Type u_1} [ms : measurable_space α] (m : outer_measure α)
    (h : ms ≤ outer_measure.caratheodory m) (s : set α) :
    coe_fn m s ≤ coe_fn (outer_measure.to_measure m h) s :=
  outer_measure.le_trim m s

@[simp] theorem to_outer_measure_to_measure {α : Type u_1} [ms : measurable_space α]
    {μ : measure α} :
    outer_measure.to_measure (measure.to_outer_measure μ) (le_to_outer_measure_caratheodory μ) =
        μ :=
  measure.ext fun (s : set α) => outer_measure.trim_eq (measure.to_outer_measure μ)

namespace measure


protected theorem caratheodory {α : Type u_1} [measurable_space α] {s : set α} {t : set α}
    (μ : measure α) (hs : is_measurable s) : coe_fn μ (t ∩ s) + coe_fn μ (t \ s) = coe_fn μ t :=
  Eq.symm (le_to_outer_measure_caratheodory μ s hs t)

/-! ### The `ennreal`-module of measures -/

protected instance has_zero {α : Type u_1} [measurable_space α] : HasZero (measure α) :=
  { zero := mk 0 sorry outer_measure.trim_zero }

@[simp] theorem zero_to_outer_measure {α : Type u_1} [measurable_space α] :
    to_outer_measure 0 = 0 :=
  rfl

@[simp] theorem coe_zero {α : Type u_1} [measurable_space α] : ⇑0 = 0 := rfl

theorem eq_zero_of_not_nonempty {α : Type u_1} [measurable_space α] (h : ¬Nonempty α)
    (μ : measure α) : μ = 0 :=
  sorry

protected instance inhabited {α : Type u_1} [measurable_space α] : Inhabited (measure α) :=
  { default := 0 }

protected instance has_add {α : Type u_1} [measurable_space α] : Add (measure α) :=
  { add := fun (μ₁ μ₂ : measure α) => mk (to_outer_measure μ₁ + to_outer_measure μ₂) sorry sorry }

@[simp] theorem add_to_outer_measure {α : Type u_1} [measurable_space α] (μ₁ : measure α)
    (μ₂ : measure α) : to_outer_measure (μ₁ + μ₂) = to_outer_measure μ₁ + to_outer_measure μ₂ :=
  rfl

@[simp] theorem coe_add {α : Type u_1} [measurable_space α] (μ₁ : measure α) (μ₂ : measure α) :
    ⇑(μ₁ + μ₂) = ⇑μ₁ + ⇑μ₂ :=
  rfl

theorem add_apply {α : Type u_1} [measurable_space α] (μ₁ : measure α) (μ₂ : measure α)
    (s : set α) : coe_fn (μ₁ + μ₂) s = coe_fn μ₁ s + coe_fn μ₂ s :=
  rfl

protected instance add_comm_monoid {α : Type u_1} [measurable_space α] :
    add_comm_monoid (measure α) :=
  function.injective.add_comm_monoid to_outer_measure to_outer_measure_injective
    zero_to_outer_measure add_to_outer_measure

protected instance has_scalar {α : Type u_1} [measurable_space α] :
    has_scalar ennreal (measure α) :=
  has_scalar.mk fun (c : ennreal) (μ : measure α) => mk (c • to_outer_measure μ) sorry sorry

@[simp] theorem smul_to_outer_measure {α : Type u_1} [measurable_space α] (c : ennreal)
    (μ : measure α) : to_outer_measure (c • μ) = c • to_outer_measure μ :=
  rfl

@[simp] theorem coe_smul {α : Type u_1} [measurable_space α] (c : ennreal) (μ : measure α) :
    ⇑(c • μ) = c • ⇑μ :=
  rfl

theorem smul_apply {α : Type u_1} [measurable_space α] (c : ennreal) (μ : measure α) (s : set α) :
    coe_fn (c • μ) s = c * coe_fn μ s :=
  rfl

protected instance semimodule {α : Type u_1} [measurable_space α] :
    semimodule ennreal (measure α) :=
  function.injective.semimodule ennreal
    (add_monoid_hom.mk to_outer_measure zero_to_outer_measure add_to_outer_measure)
    to_outer_measure_injective smul_to_outer_measure

/-! ### The complete lattice of measures -/

protected instance partial_order {α : Type u_1} [measurable_space α] : partial_order (measure α) :=
  partial_order.mk
    (fun (m₁ m₂ : measure α) => ∀ (s : set α), is_measurable s → coe_fn m₁ s ≤ coe_fn m₂ s)
    (preorder.lt._default
      fun (m₁ m₂ : measure α) => ∀ (s : set α), is_measurable s → coe_fn m₁ s ≤ coe_fn m₂ s)
    sorry sorry sorry

theorem le_iff {α : Type u_1} [measurable_space α] {μ₁ : measure α} {μ₂ : measure α} :
    μ₁ ≤ μ₂ ↔ ∀ (s : set α), is_measurable s → coe_fn μ₁ s ≤ coe_fn μ₂ s :=
  iff.rfl

theorem to_outer_measure_le {α : Type u_1} [measurable_space α] {μ₁ : measure α} {μ₂ : measure α} :
    to_outer_measure μ₁ ≤ to_outer_measure μ₂ ↔ μ₁ ≤ μ₂ :=
  sorry

theorem le_iff' {α : Type u_1} [measurable_space α] {μ₁ : measure α} {μ₂ : measure α} :
    μ₁ ≤ μ₂ ↔ ∀ (s : set α), coe_fn μ₁ s ≤ coe_fn μ₂ s :=
  iff.symm to_outer_measure_le

theorem lt_iff {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α} :
    μ < ν ↔ μ ≤ ν ∧ ∃ (s : set α), is_measurable s ∧ coe_fn μ s < coe_fn ν s :=
  sorry

theorem lt_iff' {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α} :
    μ < ν ↔ μ ≤ ν ∧ ∃ (s : set α), coe_fn μ s < coe_fn ν s :=
  sorry

-- TODO: add typeclasses for `∀ c, monotone ((*) c)` and `∀ c, monotone ((+) c)`

protected theorem add_le_add_left {α : Type u_1} [measurable_space α] {μ₁ : measure α}
    {μ₂ : measure α} (ν : measure α) (hμ : μ₁ ≤ μ₂) : ν + μ₁ ≤ ν + μ₂ :=
  fun (s : set α) (hs : is_measurable s) =>
    add_le_add_left (hμ s hs) (coe_fn (to_outer_measure ν) s)

protected theorem add_le_add_right {α : Type u_1} [measurable_space α] {μ₁ : measure α}
    {μ₂ : measure α} (hμ : μ₁ ≤ μ₂) (ν : measure α) : μ₁ + ν ≤ μ₂ + ν :=
  fun (s : set α) (hs : is_measurable s) =>
    add_le_add_right (hμ s hs) (coe_fn (to_outer_measure ν) s)

protected theorem add_le_add {α : Type u_1} [measurable_space α] {μ₁ : measure α} {μ₂ : measure α}
    {ν₁ : measure α} {ν₂ : measure α} (hμ : μ₁ ≤ μ₂) (hν : ν₁ ≤ ν₂) : μ₁ + ν₁ ≤ μ₂ + ν₂ :=
  fun (s : set α) (hs : is_measurable s) => add_le_add (hμ s hs) (hν s hs)

protected theorem le_add_left {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    {ν' : measure α} (h : μ ≤ ν) : μ ≤ ν' + ν :=
  fun (s : set α) (hs : is_measurable s) => le_add_left (h s hs)

protected theorem le_add_right {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    {ν' : measure α} (h : μ ≤ ν) : μ ≤ ν + ν' :=
  fun (s : set α) (hs : is_measurable s) => le_add_right (h s hs)

theorem Inf_caratheodory {α : Type u_1} [measurable_space α] {m : set (measure α)} (s : set α)
    (hs : is_measurable s) :
    measurable_space.is_measurable' (outer_measure.caratheodory (Inf (to_outer_measure '' m))) s :=
  sorry

protected instance has_Inf {α : Type u_1} [measurable_space α] : has_Inf (measure α) :=
  has_Inf.mk
    fun (m : set (measure α)) =>
      outer_measure.to_measure (Inf (to_outer_measure '' m)) Inf_caratheodory

theorem Inf_apply {α : Type u_1} [measurable_space α] {s : set α} {m : set (measure α)}
    (hs : is_measurable s) : coe_fn (Inf m) s = coe_fn (Inf (to_outer_measure '' m)) s :=
  to_measure_apply (Inf (to_outer_measure '' m)) Inf_caratheodory hs

protected instance complete_lattice {α : Type u_1} [measurable_space α] :
    complete_lattice (measure α) :=
  complete_lattice.mk complete_lattice.sup complete_lattice.le complete_lattice.lt sorry sorry sorry
    sorry sorry sorry complete_lattice.inf sorry sorry sorry complete_lattice.top sorry 0 sorry
    complete_lattice.Sup complete_lattice.Inf sorry sorry sorry sorry

/- Adding an explicit `top` makes `leanchecker` fail, see lean#364, disable for now

  top := (⊤ : outer_measure α).to_measure (by rw [outer_measure.top_caratheodory]; exact le_top),
  le_top := assume a s hs,
    by cases s.eq_empty_or_nonempty with h  h;
      simp [h, to_measure_apply ⊤ _ hs, outer_measure.top_apply],
-/

protected theorem zero_le {α : Type u_1} [measurable_space α] (μ : measure α) : 0 ≤ μ := bot_le

theorem nonpos_iff_eq_zero' {α : Type u_1} [measurable_space α] {μ : measure α} : μ ≤ 0 ↔ μ = 0 :=
  has_le.le.le_iff_eq (measure.zero_le μ)

@[simp] theorem measure_univ_eq_zero {α : Type u_1} [measurable_space α] {μ : measure α} :
    coe_fn μ set.univ = 0 ↔ μ = 0 :=
  sorry

/-! ### Pushforward and pullback -/

/-- Lift a linear map between `outer_measure` spaces such that for each measure `μ` every measurable
set is caratheodory-measurable w.r.t. `f μ` to a linear map between `measure` spaces. -/
def lift_linear {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    (f : linear_map ennreal (outer_measure α) (outer_measure β))
    (hf : ∀ (μ : measure α), _inst_2 ≤ outer_measure.caratheodory (coe_fn f (to_outer_measure μ))) :
    linear_map ennreal (measure α) (measure β) :=
  linear_map.mk
    (fun (μ : measure α) => outer_measure.to_measure (coe_fn f (to_outer_measure μ)) (hf μ)) sorry
    sorry

@[simp] theorem lift_linear_apply {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {μ : measure α}
    {f : linear_map ennreal (outer_measure α) (outer_measure β)}
    (hf : ∀ (μ : measure α), _inst_2 ≤ outer_measure.caratheodory (coe_fn f (to_outer_measure μ)))
    {s : set β} (hs : is_measurable s) :
    coe_fn (coe_fn (lift_linear f hf) μ) s = coe_fn (coe_fn f (to_outer_measure μ)) s :=
  to_measure_apply (coe_fn f (to_outer_measure μ)) (hf μ) hs

theorem le_lift_linear_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure α} {f : linear_map ennreal (outer_measure α) (outer_measure β)}
    (hf : ∀ (μ : measure α), _inst_2 ≤ outer_measure.caratheodory (coe_fn f (to_outer_measure μ)))
    (s : set β) :
    coe_fn (coe_fn f (to_outer_measure μ)) s ≤ coe_fn (coe_fn (lift_linear f hf) μ) s :=
  le_to_measure_apply (coe_fn f (to_outer_measure μ)) (hf μ) s

/-- The pushforward of a measure. It is defined to be `0` if `f` is not a measurable function. -/
def map {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] (f : α → β) :
    linear_map ennreal (measure α) (measure β) :=
  dite (measurable f) (fun (hf : measurable f) => lift_linear (outer_measure.map f) sorry)
    fun (hf : ¬measurable f) => 0

/-- We can evaluate the pushforward on measurable sets. For non-measurable sets, see
  `measure_theory.measure.le_map_apply` and `measurable_equiv.map_apply`. -/
@[simp] theorem map_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure α} {f : α → β} (hf : measurable f) {s : set β} (hs : is_measurable s) :
    coe_fn (coe_fn (map f) μ) s = coe_fn μ (f ⁻¹' s) :=
  sorry

@[simp] theorem map_id {α : Type u_1} [measurable_space α] {μ : measure α} :
    coe_fn (map id) μ = μ :=
  ext fun (s : set α) => map_apply measurable_id

theorem map_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α]
    [measurable_space β] [measurable_space γ] {μ : measure α} {g : β → γ} {f : α → β}
    (hg : measurable g) (hf : measurable f) :
    coe_fn (map g) (coe_fn (map f) μ) = coe_fn (map (g ∘ f)) μ :=
  sorry

theorem map_mono {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure α} {ν : measure α} {f : α → β} (hf : measurable f) (h : μ ≤ ν) :
    coe_fn (map f) μ ≤ coe_fn (map f) ν :=
  sorry

/-- Even if `s` is not measurable, we can bound `map f μ s` from below.
  See also `measurable_equiv.map_apply`. -/
theorem le_map_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure α} {f : α → β} (hf : measurable f) (s : set β) :
    coe_fn μ (f ⁻¹' s) ≤ coe_fn (coe_fn (map f) μ) s :=
  sorry

/-- Pullback of a `measure`. If `f` sends each `measurable` set to a `measurable` set, then for each
measurable set `s` we have `comap f μ s = μ (f '' s)`. -/
def comap {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] (f : α → β) :
    linear_map ennreal (measure β) (measure α) :=
  dite (function.injective f ∧ ∀ (s : set α), is_measurable s → is_measurable (f '' s))
    (fun (hf : function.injective f ∧ ∀ (s : set α), is_measurable s → is_measurable (f '' s)) =>
      lift_linear (outer_measure.comap f) sorry)
    fun (hf : ¬(function.injective f ∧ ∀ (s : set α), is_measurable s → is_measurable (f '' s))) =>
      0

theorem comap_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {s : set α} (f : α → β) (hfi : function.injective f)
    (hf : ∀ (s : set α), is_measurable s → is_measurable (f '' s)) (μ : measure β)
    (hs : is_measurable s) : coe_fn (coe_fn (comap f) μ) s = coe_fn μ (f '' s) :=
  sorry

/-! ### Restricting a measure -/

/-- Restrict a measure `μ` to a set `s` as an `ennreal`-linear map. -/
def restrictₗ {α : Type u_1} [measurable_space α] (s : set α) :
    linear_map ennreal (measure α) (measure α) :=
  lift_linear (outer_measure.restrict s) sorry

/-- Restrict a measure `μ` to a set `s`. -/
def restrict {α : Type u_1} [measurable_space α] (μ : measure α) (s : set α) : measure α :=
  coe_fn (restrictₗ s) μ

@[simp] theorem restrictₗ_apply {α : Type u_1} [measurable_space α] (s : set α) (μ : measure α) :
    coe_fn (restrictₗ s) μ = restrict μ s :=
  rfl

@[simp] theorem restrict_apply {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {t : set α} (ht : is_measurable t) : coe_fn (restrict μ s) t = coe_fn μ (t ∩ s) :=
  sorry

theorem restrict_apply_univ {α : Type u_1} [measurable_space α] {μ : measure α} (s : set α) :
    coe_fn (restrict μ s) set.univ = coe_fn μ s :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (coe_fn (restrict μ s) set.univ = coe_fn μ s))
        (restrict_apply is_measurable.univ)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn μ (set.univ ∩ s) = coe_fn μ s)) (set.univ_inter s)))
      (Eq.refl (coe_fn μ s)))

theorem le_restrict_apply {α : Type u_1} [measurable_space α] {μ : measure α} (s : set α)
    (t : set α) : coe_fn μ (t ∩ s) ≤ coe_fn (restrict μ s) t :=
  sorry

@[simp] theorem restrict_add {α : Type u_1} [measurable_space α] (μ : measure α) (ν : measure α)
    (s : set α) : restrict (μ + ν) s = restrict μ s + restrict ν s :=
  linear_map.map_add (restrictₗ s) μ ν

@[simp] theorem restrict_zero {α : Type u_1} [measurable_space α] (s : set α) : restrict 0 s = 0 :=
  linear_map.map_zero (restrictₗ s)

@[simp] theorem restrict_smul {α : Type u_1} [measurable_space α] (c : ennreal) (μ : measure α)
    (s : set α) : restrict (c • μ) s = c • restrict μ s :=
  linear_map.map_smul (restrictₗ s) c μ

@[simp] theorem restrict_restrict {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {t : set α} (hs : is_measurable s) : restrict (restrict μ t) s = restrict μ (s ∩ t) :=
  sorry

theorem restrict_apply_eq_zero {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {t : set α} (ht : is_measurable t) : coe_fn (restrict μ s) t = 0 ↔ coe_fn μ (t ∩ s) = 0 :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (coe_fn (restrict μ s) t = 0 ↔ coe_fn μ (t ∩ s) = 0))
        (restrict_apply ht)))
    (iff.refl (coe_fn μ (t ∩ s) = 0))

theorem measure_inter_eq_zero_of_restrict {α : Type u_1} [measurable_space α] {μ : measure α}
    {s : set α} {t : set α} (h : coe_fn (restrict μ s) t = 0) : coe_fn μ (t ∩ s) = 0 :=
  iff.mp nonpos_iff_eq_zero (h ▸ le_restrict_apply s t)

theorem restrict_apply_eq_zero' {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {t : set α} (hs : is_measurable s) : coe_fn (restrict μ s) t = 0 ↔ coe_fn μ (t ∩ s) = 0 :=
  sorry

@[simp] theorem restrict_eq_zero {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} :
    restrict μ s = 0 ↔ coe_fn μ s = 0 :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (restrict μ s = 0 ↔ coe_fn μ s = 0))
        (Eq.symm (propext measure_univ_eq_zero))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (coe_fn (restrict μ s) set.univ = 0 ↔ coe_fn μ s = 0))
          (restrict_apply_univ s)))
      (iff.refl (coe_fn μ s = 0)))

@[simp] theorem restrict_empty {α : Type u_1} [measurable_space α] {μ : measure α} :
    restrict μ ∅ = 0 :=
  sorry

@[simp] theorem restrict_univ {α : Type u_1} [measurable_space α] {μ : measure α} :
    restrict μ set.univ = μ :=
  sorry

theorem restrict_union_apply {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {s' : set α} {t : set α} (h : disjoint (t ∩ s) (t ∩ s')) (hs : is_measurable s)
    (hs' : is_measurable s') (ht : is_measurable t) :
    coe_fn (restrict μ (s ∪ s')) t = coe_fn (restrict μ s) t + coe_fn (restrict μ s') t :=
  sorry

theorem restrict_union {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} {t : set α}
    (h : disjoint s t) (hs : is_measurable s) (ht : is_measurable t) :
    restrict μ (s ∪ t) = restrict μ s + restrict μ t :=
  ext
    fun (t' : set α) (ht' : is_measurable t') =>
      restrict_union_apply (disjoint.mono inf_le_right inf_le_right h) hs ht ht'

theorem restrict_union_add_inter {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {t : set α} (hs : is_measurable s) (ht : is_measurable t) :
    restrict μ (s ∪ t) + restrict μ (s ∩ t) = restrict μ s + restrict μ t :=
  sorry

@[simp] theorem restrict_add_restrict_compl {α : Type u_1} [measurable_space α] {μ : measure α}
    {s : set α} (hs : is_measurable s) : restrict μ s + restrict μ (sᶜ) = μ :=
  sorry

@[simp] theorem restrict_compl_add_restrict {α : Type u_1} [measurable_space α] {μ : measure α}
    {s : set α} (hs : is_measurable s) : restrict μ (sᶜ) + restrict μ s = μ :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (restrict μ (sᶜ) + restrict μ s = μ))
        (add_comm (restrict μ (sᶜ)) (restrict μ s))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (restrict μ s + restrict μ (sᶜ) = μ))
          (restrict_add_restrict_compl hs)))
      (Eq.refl μ))

theorem restrict_union_le {α : Type u_1} [measurable_space α] {μ : measure α} (s : set α)
    (s' : set α) : restrict μ (s ∪ s') ≤ restrict μ s + restrict μ s' :=
  sorry

theorem restrict_Union_apply {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    [encodable ι] {s : ι → set α} (hd : pairwise (disjoint on s))
    (hm : ∀ (i : ι), is_measurable (s i)) {t : set α} (ht : is_measurable t) :
    coe_fn (restrict μ (set.Union fun (i : ι) => s i)) t =
        tsum fun (i : ι) => coe_fn (restrict μ (s i)) t :=
  sorry

theorem restrict_Union_apply_eq_supr {α : Type u_1} {ι : Type u_5} [measurable_space α]
    {μ : measure α} [encodable ι] {s : ι → set α} (hm : ∀ (i : ι), is_measurable (s i))
    (hd : directed has_subset.subset s) {t : set α} (ht : is_measurable t) :
    coe_fn (restrict μ (set.Union fun (i : ι) => s i)) t =
        supr fun (i : ι) => coe_fn (restrict μ (s i)) t :=
  sorry

theorem restrict_map {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure α} {f : α → β} (hf : measurable f) {s : set β} (hs : is_measurable s) :
    restrict (coe_fn (map f) μ) s = coe_fn (map f) (restrict μ (f ⁻¹' s)) :=
  sorry

theorem map_comap_subtype_coe {α : Type u_1} [measurable_space α] {s : set α}
    (hs : is_measurable s) : linear_map.comp (map coe) (comap coe) = restrictₗ s :=
  sorry

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
theorem restrict_mono {α : Type u_1} [measurable_space α] {s : set α} {s' : set α} (hs : s ⊆ s')
    {μ : measure α} {ν : measure α} (hμν : μ ≤ ν) : restrict μ s ≤ restrict ν s' :=
  sorry

theorem restrict_le_self {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} :
    restrict μ s ≤ μ :=
  fun (t : set α) (ht : is_measurable t) =>
    trans_rel_right LessEq (restrict_apply ht) (measure_mono (set.inter_subset_left t s))

theorem restrict_congr_meas {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    {s : set α} (hs : is_measurable s) :
    restrict μ s = restrict ν s ↔
        ∀ (t : set α), t ⊆ s → is_measurable t → coe_fn μ t = coe_fn ν t :=
  sorry

theorem restrict_congr_mono {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    {s : set α} {t : set α} (hs : s ⊆ t) (hm : is_measurable s) (h : restrict μ t = restrict ν t) :
    restrict μ s = restrict ν s :=
  sorry

/-- If two measures agree on all measurable subsets of `s` and `t`, then they agree on all
measurable subsets of `s ∪ t`. -/
theorem restrict_union_congr {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    {s : set α} {t : set α} (hsm : is_measurable s) (htm : is_measurable t) :
    restrict μ (s ∪ t) = restrict ν (s ∪ t) ↔
        restrict μ s = restrict ν s ∧ restrict μ t = restrict ν t :=
  sorry

theorem restrict_finset_bUnion_congr {α : Type u_1} {ι : Type u_5} [measurable_space α]
    {μ : measure α} {ν : measure α} {s : finset ι} {t : ι → set α}
    (htm : ∀ (i : ι), i ∈ s → is_measurable (t i)) :
    restrict μ (set.Union fun (i : ι) => set.Union fun (H : i ∈ s) => t i) =
          restrict ν (set.Union fun (i : ι) => set.Union fun (H : i ∈ s) => t i) ↔
        ∀ (i : ι), i ∈ s → restrict μ (t i) = restrict ν (t i) :=
  sorry

theorem restrict_Union_congr {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    {ν : measure α} [encodable ι] {s : ι → set α} (hm : ∀ (i : ι), is_measurable (s i)) :
    restrict μ (set.Union fun (i : ι) => s i) = restrict ν (set.Union fun (i : ι) => s i) ↔
        ∀ (i : ι), restrict μ (s i) = restrict ν (s i) :=
  sorry

theorem restrict_bUnion_congr {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    {ν : measure α} {s : set ι} {t : ι → set α} (hc : set.countable s)
    (htm : ∀ (i : ι), i ∈ s → is_measurable (t i)) :
    restrict μ (set.Union fun (i : ι) => set.Union fun (H : i ∈ s) => t i) =
          restrict ν (set.Union fun (i : ι) => set.Union fun (H : i ∈ s) => t i) ↔
        ∀ (i : ι), i ∈ s → restrict μ (t i) = restrict ν (t i) :=
  sorry

theorem restrict_sUnion_congr {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    {S : set (set α)} (hc : set.countable S) (hm : ∀ (s : set α), s ∈ S → is_measurable s) :
    restrict μ (⋃₀S) = restrict ν (⋃₀S) ↔ ∀ (s : set α), s ∈ S → restrict μ s = restrict ν s :=
  sorry

/-- This lemma shows that `restrict` and `to_outer_measure` commute. Note that the LHS has a
restrict on measures and the RHS has a restrict on outer measures. -/
theorem restrict_to_outer_measure_eq_to_outer_measure_restrict {α : Type u_1} [measurable_space α]
    {μ : measure α} {s : set α} (h : is_measurable s) :
    to_outer_measure (restrict μ s) = coe_fn (outer_measure.restrict s) (to_outer_measure μ) :=
  sorry

/-- This lemma shows that `Inf` and `restrict` commute for measures. -/
theorem restrict_Inf_eq_Inf_restrict {α : Type u_1} [measurable_space α] {t : set α}
    {m : set (measure α)} (hm : set.nonempty m) (ht : is_measurable t) :
    restrict (Inf m) t = Inf ((fun (μ : measure α) => restrict μ t) '' m) :=
  sorry

/-! ### Extensionality results -/

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `Union`). -/
theorem ext_iff_of_Union_eq_univ {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    {ν : measure α} [encodable ι] {s : ι → set α} (hm : ∀ (i : ι), is_measurable (s i))
    (hs : (set.Union fun (i : ι) => s i) = set.univ) :
    μ = ν ↔ ∀ (i : ι), restrict μ (s i) = restrict ν (s i) :=
  sorry

theorem ext_of_Union_eq_univ {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    {ν : measure α} [encodable ι] {s : ι → set α} (hm : ∀ (i : ι), is_measurable (s i))
    (hs : (set.Union fun (i : ι) => s i) = set.univ) :
    (∀ (i : ι), restrict μ (s i) = restrict ν (s i)) → μ = ν :=
  iff.mpr (ext_iff_of_Union_eq_univ hm hs)

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `bUnion`). -/
theorem ext_iff_of_bUnion_eq_univ {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    {ν : measure α} {S : set ι} {s : ι → set α} (hc : set.countable S)
    (hm : ∀ (i : ι), i ∈ S → is_measurable (s i))
    (hs : (set.Union fun (i : ι) => set.Union fun (H : i ∈ S) => s i) = set.univ) :
    μ = ν ↔ ∀ (i : ι), i ∈ S → restrict μ (s i) = restrict ν (s i) :=
  sorry

theorem ext_of_bUnion_eq_univ {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    {ν : measure α} {S : set ι} {s : ι → set α} (hc : set.countable S)
    (hm : ∀ (i : ι), i ∈ S → is_measurable (s i))
    (hs : (set.Union fun (i : ι) => set.Union fun (H : i ∈ S) => s i) = set.univ) :
    (∀ (i : ι), i ∈ S → restrict μ (s i) = restrict ν (s i)) → μ = ν :=
  iff.mpr (ext_iff_of_bUnion_eq_univ hc hm hs)

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `sUnion`). -/
theorem ext_iff_of_sUnion_eq_univ {α : Type u_1} [measurable_space α] {μ : measure α}
    {ν : measure α} {S : set (set α)} (hc : set.countable S)
    (hm : ∀ (s : set α), s ∈ S → is_measurable s) (hs : ⋃₀S = set.univ) :
    μ = ν ↔ ∀ (s : set α), s ∈ S → restrict μ s = restrict ν s :=
  sorry

theorem ext_of_sUnion_eq_univ {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    {S : set (set α)} (hc : set.countable S) (hm : ∀ (s : set α), s ∈ S → is_measurable s)
    (hs : ⋃₀S = set.univ) : (∀ (s : set α), s ∈ S → restrict μ s = restrict ν s) → μ = ν :=
  iff.mpr (ext_iff_of_sUnion_eq_univ hc hm hs)

theorem ext_of_generate_from_of_cover {α : Type u_1} [measurable_space α] {μ : measure α}
    {ν : measure α} {S : set (set α)} {T : set (set α)}
    (h_gen : _inst_1 = measurable_space.generate_from S) (hc : set.countable T)
    (h_inter : is_pi_system S) (hm : ∀ (t : set α), t ∈ T → is_measurable t) (hU : ⋃₀T = set.univ)
    (htop : ∀ (t : set α), t ∈ T → coe_fn μ t < ⊤)
    (ST_eq : ∀ (t : set α), t ∈ T → ∀ (s : set α), s ∈ S → coe_fn μ (s ∩ t) = coe_fn ν (s ∩ t))
    (T_eq : ∀ (t : set α), t ∈ T → coe_fn μ t = coe_fn ν t) : μ = ν :=
  sorry

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on a increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `sUnion`. -/
theorem ext_of_generate_from_of_cover_subset {α : Type u_1} [measurable_space α] {μ : measure α}
    {ν : measure α} {S : set (set α)} {T : set (set α)}
    (h_gen : _inst_1 = measurable_space.generate_from S) (h_inter : is_pi_system S) (h_sub : T ⊆ S)
    (hc : set.countable T) (hU : ⋃₀T = set.univ) (htop : ∀ (s : set α), s ∈ T → coe_fn μ s < ⊤)
    (h_eq : ∀ (s : set α), s ∈ S → coe_fn μ s = coe_fn ν s) : μ = ν :=
  sorry

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on a increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `Union`.
  `finite_spanning_sets_in.ext` is a reformulation of this lemma. -/
theorem ext_of_generate_from_of_Union {α : Type u_1} [measurable_space α] {μ : measure α}
    {ν : measure α} (C : set (set α)) (B : ℕ → set α)
    (hA : _inst_1 = measurable_space.generate_from C) (hC : is_pi_system C)
    (h1B : (set.Union fun (i : ℕ) => B i) = set.univ) (h2B : ∀ (i : ℕ), B i ∈ C)
    (hμB : ∀ (i : ℕ), coe_fn μ (B i) < ⊤) (h_eq : ∀ (s : set α), s ∈ C → coe_fn μ s = coe_fn ν s) :
    μ = ν :=
  sorry

/-- The dirac measure. -/
def dirac {α : Type u_1} [measurable_space α] (a : α) : measure α :=
  outer_measure.to_measure (outer_measure.dirac a) sorry

theorem le_dirac_apply {α : Type u_1} [measurable_space α] {s : set α} {a : α} :
    set.indicator s 1 a ≤ coe_fn (dirac a) s :=
  outer_measure.dirac_apply a s ▸ le_to_measure_apply (outer_measure.dirac a) (dirac._proof_1 a) s

@[simp] theorem dirac_apply' {α : Type u_1} [measurable_space α] {s : set α} (a : α)
    (hs : is_measurable s) : coe_fn (dirac a) s = set.indicator s 1 a :=
  to_measure_apply (outer_measure.dirac a) (dirac._proof_1 a) hs

@[simp] theorem dirac_apply_of_mem {α : Type u_1} [measurable_space α] {s : set α} {a : α}
    (h : a ∈ s) : coe_fn (dirac a) s = 1 :=
  sorry

@[simp] theorem dirac_apply {α : Type u_1} [measurable_space α] [measurable_singleton_class α]
    (a : α) (s : set α) : coe_fn (dirac a) s = set.indicator s 1 a :=
  sorry

theorem map_dirac {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {f : α → β} (hf : measurable f) (a : α) : coe_fn (map f) (dirac a) = dirac (f a) :=
  sorry

/-- Sum of an indexed family of measures. -/
def sum {α : Type u_1} {ι : Type u_5} [measurable_space α] (f : ι → measure α) : measure α :=
  outer_measure.to_measure (outer_measure.sum fun (i : ι) => to_outer_measure (f i)) sorry

theorem le_sum_apply {α : Type u_1} {ι : Type u_5} [measurable_space α] (f : ι → measure α)
    (s : set α) : (tsum fun (i : ι) => coe_fn (f i) s) ≤ coe_fn (sum f) s :=
  le_to_measure_apply (outer_measure.sum fun (i : ι) => to_outer_measure (f i)) (sum._proof_1 f) s

@[simp] theorem sum_apply {α : Type u_1} {ι : Type u_5} [measurable_space α] (f : ι → measure α)
    {s : set α} (hs : is_measurable s) : coe_fn (sum f) s = tsum fun (i : ι) => coe_fn (f i) s :=
  to_measure_apply (outer_measure.sum fun (i : ι) => to_outer_measure (f i)) (sum._proof_1 f) hs

theorem le_sum {α : Type u_1} {ι : Type u_5} [measurable_space α] (μ : ι → measure α) (i : ι) :
    μ i ≤ sum μ :=
  sorry

theorem restrict_Union {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    [encodable ι] {s : ι → set α} (hd : pairwise (disjoint on s))
    (hm : ∀ (i : ι), is_measurable (s i)) :
    restrict μ (set.Union fun (i : ι) => s i) = sum fun (i : ι) => restrict μ (s i) :=
  sorry

theorem restrict_Union_le {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α}
    [encodable ι] {s : ι → set α} :
    restrict μ (set.Union fun (i : ι) => s i) ≤ sum fun (i : ι) => restrict μ (s i) :=
  sorry

@[simp] theorem sum_bool {α : Type u_1} [measurable_space α] (f : Bool → measure α) :
    sum f = f tt + f false :=
  sorry

@[simp] theorem sum_cond {α : Type u_1} [measurable_space α] (μ : measure α) (ν : measure α) :
    (sum fun (b : Bool) => cond b μ ν) = μ + ν :=
  sum_bool fun (b : Bool) => cond b μ ν

@[simp] theorem restrict_sum {α : Type u_1} {ι : Type u_5} [measurable_space α] (μ : ι → measure α)
    {s : set α} (hs : is_measurable s) : restrict (sum μ) s = sum fun (i : ι) => restrict (μ i) s :=
  sorry

/-- Counting measure on any measurable space. -/
def count {α : Type u_1} [measurable_space α] : measure α := sum dirac

theorem le_count_apply {α : Type u_1} [measurable_space α] {s : set α} :
    (tsum fun (i : ↥s) => 1) ≤ coe_fn count s :=
  le_trans
    (trans_rel_right LessEq (tsum_subtype s 1) (ennreal.tsum_le_tsum fun (x : α) => le_dirac_apply))
    (le_sum_apply (fun (i : α) => dirac i) s)

theorem count_apply {α : Type u_1} [measurable_space α] {s : set α} (hs : is_measurable s) :
    coe_fn count s = tsum fun (i : ↥s) => 1 :=
  sorry

@[simp] theorem count_apply_finset {α : Type u_1} [measurable_space α]
    [measurable_singleton_class α] (s : finset α) : coe_fn count ↑s = ↑(finset.card s) :=
  sorry

theorem count_apply_finite {α : Type u_1} [measurable_space α] [measurable_singleton_class α]
    (s : set α) (hs : set.finite s) : coe_fn count s = ↑(finset.card (set.finite.to_finset hs)) :=
  sorry

/-- `count` measure evaluates to infinity at infinite sets. -/
theorem count_apply_infinite {α : Type u_1} [measurable_space α] {s : set α} (hs : set.infinite s) :
    coe_fn count s = ⊤ :=
  sorry

@[simp] theorem count_apply_eq_top {α : Type u_1} [measurable_space α] {s : set α}
    [measurable_singleton_class α] : coe_fn count s = ⊤ ↔ set.infinite s :=
  sorry

@[simp] theorem count_apply_lt_top {α : Type u_1} [measurable_space α] {s : set α}
    [measurable_singleton_class α] : coe_fn count s < ⊤ ↔ set.finite s :=
  iff.trans (iff.trans lt_top_iff_ne_top (not_congr count_apply_eq_top)) not_not

/-! ### The almost everywhere filter -/

/-- The “almost everywhere” filter of co-null sets. -/
def ae {α : Type u_1} [measurable_space α] (μ : measure α) : filter α :=
  filter.mk (set_of fun (s : set α) => coe_fn μ (sᶜ) = 0) sorry sorry sorry

/-- The filter of sets `s` such that `sᶜ` has finite measure. -/
def cofinite {α : Type u_1} [measurable_space α] (μ : measure α) : filter α :=
  filter.mk (set_of fun (s : set α) => coe_fn μ (sᶜ) < ⊤) sorry sorry sorry

theorem mem_cofinite {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} :
    s ∈ cofinite μ ↔ coe_fn μ (sᶜ) < ⊤ :=
  iff.rfl

theorem compl_mem_cofinite {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} :
    sᶜ ∈ cofinite μ ↔ coe_fn μ s < ⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sᶜ ∈ cofinite μ ↔ coe_fn μ s < ⊤)) (propext mem_cofinite)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn μ (sᶜᶜ) < ⊤ ↔ coe_fn μ s < ⊤)) (compl_compl s)))
      (iff.refl (coe_fn μ s < ⊤)))

theorem eventually_cofinite {α : Type u_1} [measurable_space α] {μ : measure α} {p : α → Prop} :
    filter.eventually (fun (x : α) => p x) (cofinite μ) ↔
        coe_fn μ (set_of fun (x : α) => ¬p x) < ⊤ :=
  iff.rfl

end measure


theorem mem_ae_iff {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} :
    s ∈ measure.ae μ ↔ coe_fn μ (sᶜ) = 0 :=
  iff.rfl

theorem ae_iff {α : Type u_1} [measurable_space α] {μ : measure α} {p : α → Prop} :
    filter.eventually (fun (a : α) => p a) (measure.ae μ) ↔
        coe_fn μ (set_of fun (a : α) => ¬p a) = 0 :=
  iff.rfl

theorem compl_mem_ae_iff {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} :
    sᶜ ∈ measure.ae μ ↔ coe_fn μ s = 0 :=
  sorry

theorem measure_zero_iff_ae_nmem {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} :
    coe_fn μ s = 0 ↔ filter.eventually (fun (a : α) => ¬a ∈ s) (measure.ae μ) :=
  iff.symm compl_mem_ae_iff

@[simp] theorem ae_eq_bot {α : Type u_1} [measurable_space α] {μ : measure α} :
    measure.ae μ = ⊥ ↔ μ = 0 :=
  sorry

@[simp] theorem ae_zero {α : Type u_1} [measurable_space α] : measure.ae 0 = ⊥ :=
  iff.mpr ae_eq_bot rfl

theorem ae_of_all {α : Type u_1} [measurable_space α] {p : α → Prop} (μ : measure α) :
    (∀ (a : α), p a) → filter.eventually (fun (a : α) => p a) (measure.ae μ) :=
  filter.eventually_of_forall

theorem ae_mono {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α} (h : μ ≤ ν) :
    measure.ae μ ≤ measure.ae ν :=
  fun (s : set α) (hs : s ∈ measure.ae ν) =>
    bot_unique (trans_rel_left LessEq (iff.mp measure.le_iff' h (sᶜ)) hs)

protected instance measure.ae.countable_Inter_filter {α : Type u_1} [measurable_space α]
    {μ : measure α} : countable_Inter_filter (measure.ae μ) :=
  countable_Inter_filter.mk
    fun (S : set (set α)) (hSc : set.countable S) (hS : ∀ (s : set α), s ∈ S → s ∈ measure.ae μ) =>
      eq.mpr
        (id
          (Eq.trans (propext mem_ae_iff)
            ((fun (a a_1 : ennreal) (e_1 : a = a_1) (ᾰ ᾰ_1 : ennreal) (e_2 : ᾰ = ᾰ_1) =>
                congr (congr_arg Eq e_1) e_2)
              (coe_fn μ (⋂₀Sᶜ)) (coe_fn μ (set.Union fun (x : ↥S) => ↑xᶜ))
              ((fun (x x_1 : measure α) (e_1 : x = x_1) (ᾰ ᾰ_1 : set α) (e_2 : ᾰ = ᾰ_1) =>
                  congr (congr_arg coe_fn e_1) e_2)
                μ μ (Eq.refl μ) (⋂₀Sᶜ) (set.Union fun (x : ↥S) => ↑xᶜ)
                (Eq.trans (Eq.trans (set.compl_sInter S) (set.sUnion_image compl S))
                  (set.bUnion_eq_Union S fun (x : set α) (H : x ∈ S) => xᶜ)))
              0 0 (Eq.refl 0))))
        (measure_Union_null
          (iff.mpr subtype.forall
            (eq.mp
              (forall_congr_eq
                fun (s : set α) => imp_congr_eq (Eq.refl (s ∈ S)) (propext mem_ae_iff))
              hS)))

protected instance ae_is_measurably_generated {α : Type u_1} [measurable_space α] {μ : measure α} :
    filter.is_measurably_generated (measure.ae μ) :=
  filter.is_measurably_generated.mk fun (s : set α) (hs : s ∈ measure.ae μ) => sorry

theorem ae_all_iff {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α} [encodable ι]
    {p : α → ι → Prop} :
    filter.eventually (fun (a : α) => ∀ (i : ι), p a i) (measure.ae μ) ↔
        ∀ (i : ι), filter.eventually (fun (a : α) => p a i) (measure.ae μ) :=
  eventually_countable_forall

theorem ae_ball_iff {α : Type u_1} {ι : Type u_5} [measurable_space α] {μ : measure α} {S : set ι}
    (hS : set.countable S) {p : α → (i : ι) → i ∈ S → Prop} :
    filter.eventually (fun (x : α) => ∀ (i : ι) (H : i ∈ S), p x i H) (measure.ae μ) ↔
        ∀ (i : ι) (H : i ∈ S), filter.eventually (fun (x : α) => p x i H) (measure.ae μ) :=
  eventually_countable_ball hS

theorem ae_eq_refl {α : Type u_1} {δ : Type u_4} [measurable_space α] {μ : measure α} (f : α → δ) :
    filter.eventually_eq (measure.ae μ) f f :=
  filter.eventually_eq.rfl

theorem ae_eq_symm {α : Type u_1} {δ : Type u_4} [measurable_space α] {μ : measure α} {f : α → δ}
    {g : α → δ} (h : filter.eventually_eq (measure.ae μ) f g) :
    filter.eventually_eq (measure.ae μ) g f :=
  filter.eventually_eq.symm h

theorem ae_eq_trans {α : Type u_1} {δ : Type u_4} [measurable_space α] {μ : measure α} {f : α → δ}
    {g : α → δ} {h : α → δ} (h₁ : filter.eventually_eq (measure.ae μ) f g)
    (h₂ : filter.eventually_eq (measure.ae μ) g h) : filter.eventually_eq (measure.ae μ) f h :=
  filter.eventually_eq.trans h₁ h₂

theorem ae_eq_empty {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} :
    filter.eventually_eq (measure.ae μ) s ∅ ↔ coe_fn μ s = 0 :=
  sorry

theorem ae_le_set {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} {t : set α} :
    filter.eventually_le (measure.ae μ) s t ↔ coe_fn μ (s \ t) = 0 :=
  sorry

theorem union_ae_eq_right {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {t : set α} : filter.eventually_eq (measure.ae μ) (s ∪ t) t ↔ coe_fn μ (s \ t) = 0 :=
  sorry

theorem diff_ae_eq_self {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {t : set α} : filter.eventually_eq (measure.ae μ) (s \ t) s ↔ coe_fn μ (s ∩ t) = 0 :=
  sorry

theorem ae_eq_set {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} {t : set α} :
    filter.eventually_eq (measure.ae μ) s t ↔ coe_fn μ (s \ t) = 0 ∧ coe_fn μ (t \ s) = 0 :=
  sorry

theorem mem_ae_map_iff {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure α} {f : α → β} (hf : measurable f) {s : set β} (hs : is_measurable s) :
    s ∈ measure.ae (coe_fn (measure.map f) μ) ↔ f ⁻¹' s ∈ measure.ae μ :=
  sorry

theorem ae_map_iff {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure α} {f : α → β} (hf : measurable f) {p : β → Prop}
    (hp : is_measurable (set_of fun (x : β) => p x)) :
    filter.eventually (fun (x : β) => p x) (measure.ae (coe_fn (measure.map f) μ)) ↔
        filter.eventually (fun (x : α) => p (f x)) (measure.ae μ) :=
  mem_ae_map_iff hf hp

theorem ae_restrict_iff {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {p : α → Prop} (hp : is_measurable (set_of fun (x : α) => p x)) :
    filter.eventually (fun (x : α) => p x) (measure.ae (measure.restrict μ s)) ↔
        filter.eventually (fun (x : α) => x ∈ s → p x) (measure.ae μ) :=
  sorry

theorem ae_imp_of_ae_restrict {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {p : α → Prop}
    (h : filter.eventually (fun (x : α) => p x) (measure.ae (measure.restrict μ s))) :
    filter.eventually (fun (x : α) => x ∈ s → p x) (measure.ae μ) :=
  sorry

theorem ae_restrict_iff' {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {p : α → Prop} (hp : is_measurable s) :
    filter.eventually (fun (x : α) => p x) (measure.ae (measure.restrict μ s)) ↔
        filter.eventually (fun (x : α) => x ∈ s → p x) (measure.ae μ) :=
  sorry

theorem ae_smul_measure {α : Type u_1} [measurable_space α] {μ : measure α} {p : α → Prop}
    (h : filter.eventually (fun (x : α) => p x) (measure.ae μ)) (c : ennreal) :
    filter.eventually (fun (x : α) => p x) (measure.ae (c • μ)) :=
  sorry

theorem ae_smul_measure_iff {α : Type u_1} [measurable_space α] {μ : measure α} {p : α → Prop}
    {c : ennreal} (hc : c ≠ 0) :
    filter.eventually (fun (x : α) => p x) (measure.ae (c • μ)) ↔
        filter.eventually (fun (x : α) => p x) (measure.ae μ) :=
  sorry

theorem ae_add_measure_iff {α : Type u_1} [measurable_space α] {μ : measure α} {p : α → Prop}
    {ν : measure α} :
    filter.eventually (fun (x : α) => p x) (measure.ae (μ + ν)) ↔
        filter.eventually (fun (x : α) => p x) (measure.ae μ) ∧
          filter.eventually (fun (x : α) => p x) (measure.ae ν) :=
  add_eq_zero_iff

theorem ae_eq_comp {α : Type u_1} {β : Type u_2} {δ : Type u_4} [measurable_space α]
    [measurable_space β] {μ : measure α} {f : α → β} {g : β → δ} {g' : β → δ} (hf : measurable f)
    (h : filter.eventually_eq (measure.ae (coe_fn (measure.map f) μ)) g g') :
    filter.eventually_eq (measure.ae μ) (g ∘ f) (g' ∘ f) :=
  sorry

theorem le_ae_restrict {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} :
    measure.ae μ ⊓ filter.principal s ≤ measure.ae (measure.restrict μ s) :=
  fun (s_1 : set α) (hs : s_1 ∈ measure.ae (measure.restrict μ s)) =>
    iff.mpr filter.eventually_inf_principal (ae_imp_of_ae_restrict hs)

@[simp] theorem ae_restrict_eq {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    (hs : is_measurable s) :
    measure.ae (measure.restrict μ s) = measure.ae μ ⊓ filter.principal s :=
  sorry

@[simp] theorem ae_restrict_eq_bot {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} :
    measure.ae (measure.restrict μ s) = ⊥ ↔ coe_fn μ s = 0 :=
  iff.trans ae_eq_bot measure.restrict_eq_zero

@[simp] theorem ae_restrict_ne_bot {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} :
    filter.ne_bot (measure.ae (measure.restrict μ s)) ↔ 0 < coe_fn μ s :=
  iff.trans (not_congr ae_restrict_eq_bot) (iff.symm pos_iff_ne_zero)

theorem self_mem_ae_restrict {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    (hs : is_measurable s) : s ∈ measure.ae (measure.restrict μ s) :=
  sorry

/-- A version of the Borel-Cantelli lemma: if `sᵢ` is a sequence of measurable sets such that
`∑ μ sᵢ` exists, then for almost all `x`, `x` does not belong to almost all `sᵢ`. -/
theorem ae_eventually_not_mem {α : Type u_1} [measurable_space α] {μ : measure α} {s : ℕ → set α}
    (hs : ∀ (i : ℕ), is_measurable (s i)) (hs' : (tsum fun (i : ℕ) => coe_fn μ (s i)) ≠ ⊤) :
    filter.eventually (fun (x : α) => filter.eventually (fun (n : ℕ) => ¬x ∈ s n) filter.at_top)
        (measure.ae μ) :=
  sorry

theorem mem_ae_dirac_iff {α : Type u_1} [measurable_space α] {s : set α} {a : α}
    (hs : is_measurable s) : s ∈ measure.ae (measure.dirac a) ↔ a ∈ s :=
  sorry

theorem ae_dirac_iff {α : Type u_1} [measurable_space α] {a : α} {p : α → Prop}
    (hp : is_measurable (set_of fun (x : α) => p x)) :
    filter.eventually (fun (x : α) => p x) (measure.ae (measure.dirac a)) ↔ p a :=
  mem_ae_dirac_iff hp

@[simp] theorem ae_dirac_eq {α : Type u_1} [measurable_space α] [measurable_singleton_class α]
    (a : α) : measure.ae (measure.dirac a) = pure a :=
  sorry

theorem ae_eq_dirac' {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    [measurable_singleton_class β] {a : α} {f : α → β} (hf : measurable f) :
    filter.eventually_eq (measure.ae (measure.dirac a)) f (function.const α (f a)) :=
  iff.mpr
    (ae_dirac_iff
      ((fun (this : is_measurable (f ⁻¹' singleton (f a))) => this)
        (hf (is_measurable_singleton (f a)))))
    rfl

theorem ae_eq_dirac {α : Type u_1} {δ : Type u_4} [measurable_space α]
    [measurable_singleton_class α] {a : α} (f : α → δ) :
    filter.eventually_eq (measure.ae (measure.dirac a)) f (function.const α (f a)) :=
  sorry

/-- If `s ⊆ t` modulo a set of measure `0`, then `μ s ≤ μ t`. -/
theorem measure_mono_ae {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} {t : set α}
    (H : filter.eventually_le (measure.ae μ) s t) : coe_fn μ s ≤ coe_fn μ t :=
  sorry

theorem Mathlib.filter.eventually_le.measure_le {α : Type u_1} [measurable_space α] {μ : measure α}
    {s : set α} {t : set α} (H : filter.eventually_le (measure.ae μ) s t) :
    coe_fn μ s ≤ coe_fn μ t :=
  measure_mono_ae

/-- If two sets are equal modulo a set of measure zero, then `μ s = μ t`. -/
theorem measure_congr {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} {t : set α}
    (H : filter.eventually_eq (measure.ae μ) s t) : coe_fn μ s = coe_fn μ t :=
  le_antisymm (filter.eventually_le.measure_le (filter.eventually_eq.le H))
    (filter.eventually_le.measure_le (filter.eventually_eq.le (filter.eventually_eq.symm H)))

theorem restrict_mono_ae {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α} {t : set α}
    (h : filter.eventually_le (measure.ae μ) s t) : measure.restrict μ s ≤ measure.restrict μ t :=
  sorry

theorem restrict_congr_set {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    {t : set α} (H : filter.eventually_eq (measure.ae μ) s t) :
    measure.restrict μ s = measure.restrict μ t :=
  le_antisymm (restrict_mono_ae (filter.eventually_eq.le H))
    (restrict_mono_ae (filter.eventually_eq.le (filter.eventually_eq.symm H)))

/-- A measure `μ` is called a probability measure if `μ univ = 1`. -/
class probability_measure {α : Type u_1} [measurable_space α] (μ : measure α) where
  measure_univ : coe_fn μ set.univ = 1

protected instance measure.dirac.probability_measure {α : Type u_1} [measurable_space α] {x : α} :
    probability_measure (measure.dirac x) :=
  probability_measure.mk (measure.dirac_apply_of_mem (set.mem_univ x))

/-- A measure `μ` is called finite if `μ univ < ⊤`. -/
class finite_measure {α : Type u_1} [measurable_space α] (μ : measure α) where
  measure_univ_lt_top : coe_fn μ set.univ < ⊤

protected instance restrict.finite_measure {α : Type u_1} [measurable_space α] {s : set α}
    (μ : measure α) [hs : fact (coe_fn μ s < ⊤)] : finite_measure (measure.restrict μ s) :=
  finite_measure.mk
    (eq.mpr
      (id
        (Eq.trans
          ((fun (ᾰ ᾰ_1 : ennreal) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ennreal) (e_3 : ᾰ_2 = ᾰ_3) =>
              congr (congr_arg Less e_2) e_3)
            (coe_fn (measure.restrict μ s) set.univ) (coe_fn μ s)
            (Eq.trans
              (measure.restrict_apply (iff.mpr (iff_true_intro is_measurable.univ) True.intro))
              ((fun (x x_1 : measure α) (e_1 : x = x_1) (ᾰ ᾰ_1 : set α) (e_2 : ᾰ = ᾰ_1) =>
                  congr (congr_arg coe_fn e_1) e_2)
                μ μ (Eq.refl μ) (set.univ ∩ s) s (set.univ_inter s)))
            ⊤ ⊤ (Eq.refl ⊤))
          (propext (iff_true_intro (fact.elim hs)))))
      trivial)

/-- Measure `μ` *has no atoms* if the measure of each singleton is zero.

NB: Wikipedia assumes that for any measurable set `s` with positive `μ`-measure,
there exists a measurable `t ⊆ s` such that `0 < μ t < μ s`. While this implies `μ {x} = 0`,
the converse is not true. -/
class has_no_atoms {α : Type u_1} [measurable_space α] (μ : measure α) where
  measure_singleton : ∀ (x : α), coe_fn μ (singleton x) = 0

theorem measure_lt_top {α : Type u_1} [measurable_space α] (μ : measure α) [finite_measure μ]
    (s : set α) : coe_fn μ s < ⊤ :=
  has_le.le.trans_lt (measure_mono (set.subset_univ s)) finite_measure.measure_univ_lt_top

theorem measure_ne_top {α : Type u_1} [measurable_space α] (μ : measure α) [finite_measure μ]
    (s : set α) : coe_fn μ s ≠ ⊤ :=
  ne_of_lt (measure_lt_top μ s)

/-- `le_of_add_le_add_left` is normally applicable to `ordered_cancel_add_comm_monoid`,
but it holds for measures with the additional assumption that μ is finite. -/
theorem measure.le_of_add_le_add_left {α : Type u_1} [measurable_space α] {μ : measure α}
    {ν₁ : measure α} {ν₂ : measure α} [finite_measure μ] (A2 : μ + ν₁ ≤ μ + ν₂) : ν₁ ≤ ν₂ :=
  fun (S : set α) (B1 : is_measurable S) =>
    ennreal.le_of_add_le_add_left (measure_lt_top μ S) (A2 S B1)

protected instance probability_measure.to_finite_measure {α : Type u_1} [measurable_space α]
    (μ : measure α) [probability_measure μ] : finite_measure μ :=
  finite_measure.mk
    (eq.mpr
      (id
        (Eq.trans
          ((fun (ᾰ ᾰ_1 : ennreal) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ennreal) (e_3 : ᾰ_2 = ᾰ_3) =>
              congr (congr_arg Less e_2) e_3)
            (coe_fn μ set.univ) 1 measure_univ ⊤ ⊤ (Eq.refl ⊤))
          (propext (iff_true_intro ennreal.one_lt_top))))
      trivial)

theorem probability_measure.ne_zero {α : Type u_1} [measurable_space α] (μ : measure α)
    [probability_measure μ] : μ ≠ 0 :=
  sorry

theorem measure_countable {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    [has_no_atoms μ] (h : set.countable s) : coe_fn μ s = 0 :=
  sorry

theorem measure_finite {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    [has_no_atoms μ] (h : set.finite s) : coe_fn μ s = 0 :=
  measure_countable (set.finite.countable h)

theorem measure_finset {α : Type u_1} [measurable_space α] {μ : measure α} [has_no_atoms μ]
    (s : finset α) : coe_fn μ ↑s = 0 :=
  measure_finite (finset.finite_to_set s)

theorem insert_ae_eq_self {α : Type u_1} [measurable_space α] {μ : measure α} [has_no_atoms μ]
    (a : α) (s : set α) : filter.eventually_eq (measure.ae μ) (insert a s) s :=
  iff.mpr union_ae_eq_right
    (measure_mono_null (set.diff_subset (fun (b : α) => b = a) s) (measure_singleton a))

theorem Iio_ae_eq_Iic {α : Type u_1} [measurable_space α] {μ : measure α} [has_no_atoms μ]
    [partial_order α] {a : α} : filter.eventually_eq (measure.ae μ) (set.Iio a) (set.Iic a) :=
  sorry

theorem Ioi_ae_eq_Ici {α : Type u_1} [measurable_space α] {μ : measure α} [has_no_atoms μ]
    [partial_order α] {a : α} : filter.eventually_eq (measure.ae μ) (set.Ioi a) (set.Ici a) :=
  Iio_ae_eq_Iic

theorem Ioo_ae_eq_Ioc {α : Type u_1} [measurable_space α] {μ : measure α} [has_no_atoms μ]
    [partial_order α] {a : α} {b : α} :
    filter.eventually_eq (measure.ae μ) (set.Ioo a b) (set.Ioc a b) :=
  filter.eventually_eq.inter (ae_eq_refl fun (x : α) => preorder.lt a x) Iio_ae_eq_Iic

theorem Ioc_ae_eq_Icc {α : Type u_1} [measurable_space α] {μ : measure α} [has_no_atoms μ]
    [partial_order α] {a : α} {b : α} :
    filter.eventually_eq (measure.ae μ) (set.Ioc a b) (set.Icc a b) :=
  filter.eventually_eq.inter Ioi_ae_eq_Ici (ae_eq_refl fun (x : α) => preorder.le x b)

theorem Ioo_ae_eq_Ico {α : Type u_1} [measurable_space α] {μ : measure α} [has_no_atoms μ]
    [partial_order α] {a : α} {b : α} :
    filter.eventually_eq (measure.ae μ) (set.Ioo a b) (set.Ico a b) :=
  filter.eventually_eq.inter Ioi_ae_eq_Ici (ae_eq_refl fun (x : α) => preorder.lt x b)

theorem Ioo_ae_eq_Icc {α : Type u_1} [measurable_space α] {μ : measure α} [has_no_atoms μ]
    [partial_order α] {a : α} {b : α} :
    filter.eventually_eq (measure.ae μ) (set.Ioo a b) (set.Icc a b) :=
  filter.eventually_eq.inter Ioi_ae_eq_Ici Iio_ae_eq_Iic

theorem Ico_ae_eq_Icc {α : Type u_1} [measurable_space α] {μ : measure α} [has_no_atoms μ]
    [partial_order α] {a : α} {b : α} :
    filter.eventually_eq (measure.ae μ) (set.Ico a b) (set.Icc a b) :=
  filter.eventually_eq.inter (ae_eq_refl fun (x : α) => preorder.le a x) Iio_ae_eq_Iic

theorem Ico_ae_eq_Ioc {α : Type u_1} [measurable_space α] {μ : measure α} [has_no_atoms μ]
    [partial_order α] {a : α} {b : α} :
    filter.eventually_eq (measure.ae μ) (set.Ico a b) (set.Ioc a b) :=
  filter.eventually_eq.trans (filter.eventually_eq.symm Ioo_ae_eq_Ico) Ioo_ae_eq_Ioc

theorem ite_ae_eq_of_measure_zero {α : Type u_1} [measurable_space α] {μ : measure α} {γ : Type u_2}
    (f : α → γ) (g : α → γ) (s : set α) (hs_zero : coe_fn μ s = 0) :
    filter.eventually_eq (measure.ae μ) (fun (x : α) => ite (x ∈ s) (f x) (g x)) g :=
  sorry

theorem ite_ae_eq_of_measure_compl_zero {α : Type u_1} [measurable_space α] {μ : measure α}
    {γ : Type u_2} (f : α → γ) (g : α → γ) (s : set α) (hs_zero : coe_fn μ (sᶜ) = 0) :
    filter.eventually_eq (measure.ae μ) (fun (x : α) => ite (x ∈ s) (f x) (g x)) f :=
  sorry

namespace measure


/-- A measure is called finite at filter `f` if it is finite at some set `s ∈ f`.
Equivalently, it is eventually finite at `s` in `f.lift' powerset`. -/
def finite_at_filter {α : Type u_1} [measurable_space α] (μ : measure α) (f : filter α) :=
  ∃ (s : set α), ∃ (H : s ∈ f), coe_fn μ s < ⊤

theorem finite_at_filter_of_finite {α : Type u_1} [measurable_space α] (μ : measure α)
    [finite_measure μ] (f : filter α) : finite_at_filter μ f :=
  Exists.intro set.univ (Exists.intro filter.univ_mem_sets (measure_lt_top μ set.univ))

theorem finite_at_filter.exists_mem_basis {α : Type u_1} {ι : Type u_5} [measurable_space α]
    {μ : measure α} {f : filter α} (hμ : finite_at_filter μ f) {p : ι → Prop} {s : ι → set α}
    (hf : filter.has_basis f p s) : ∃ (i : ι), ∃ (hi : p i), coe_fn μ (s i) < ⊤ :=
  sorry

theorem finite_at_bot {α : Type u_1} [measurable_space α] (μ : measure α) : finite_at_filter μ ⊥ :=
  sorry

/-- `μ` has finite spanning sets in `C` if there is a countable sequence of sets in `C` that have
  finite measures. This structure is a type, which is useful if we want to record extra properties
  about the sets, such as that they are monotone.
  `sigma_finite` is defined in terms of this: `μ` is σ-finite if there exists a sequence of
  finite spanning sets in the collection of all measurable sets. -/
structure finite_spanning_sets_in {α : Type u_1} [measurable_space α] (μ : measure α)
    (C : set (set α))
    where
  set : ℕ → set α
  set_mem : ∀ (i : ℕ), set i ∈ C
  finite : ∀ (i : ℕ), coe_fn μ (set i) < ⊤
  spanning : (set.Union fun (i : ℕ) => set i) = set.univ

end measure


/-- A measure `μ` is called σ-finite if there is a countable collection of sets
  `{ A i | i ∈ ℕ }` such that `μ (A i) < ⊤` and `⋃ i, A i = s`. -/
def sigma_finite {α : Type u_1} [measurable_space α] (μ : measure α) :=
  Nonempty (measure.finite_spanning_sets_in μ (set_of fun (s : set α) => is_measurable s))

/-- If `μ` is σ-finite it has finite spanning sets in the collection of all measurable sets. -/
def measure.to_finite_spanning_sets_in {α : Type u_1} [measurable_space α] (μ : measure α)
    [h : sigma_finite μ] :
    measure.finite_spanning_sets_in μ (set_of fun (s : set α) => is_measurable s) :=
  Classical.choice h

/-- A noncomputable way to get a monotone collection of sets that span `univ` and have finite
  measure using `classical.some`. This definition satisfies monotonicity in addition to all other
  properties in `sigma_finite`. -/
def spanning_sets {α : Type u_1} [measurable_space α] (μ : measure α) [sigma_finite μ] (i : ℕ) :
    set α :=
  set.accumulate (measure.finite_spanning_sets_in.set (measure.to_finite_spanning_sets_in μ)) i

theorem monotone_spanning_sets {α : Type u_1} [measurable_space α] (μ : measure α)
    [sigma_finite μ] : monotone (spanning_sets μ) :=
  set.monotone_accumulate

theorem is_measurable_spanning_sets {α : Type u_1} [measurable_space α] (μ : measure α)
    [sigma_finite μ] (i : ℕ) : is_measurable (spanning_sets μ i) :=
  sorry

theorem measure_spanning_sets_lt_top {α : Type u_1} [measurable_space α] (μ : measure α)
    [sigma_finite μ] (i : ℕ) : coe_fn μ (spanning_sets μ i) < ⊤ :=
  measure_bUnion_lt_top (set.finite_le_nat i)
    fun (j : ℕ) (_x : j ∈ fun (y : ℕ) => nat.less_than_or_equal y i) =>
      measure.finite_spanning_sets_in.finite (measure.to_finite_spanning_sets_in μ) j

theorem Union_spanning_sets {α : Type u_1} [measurable_space α] (μ : measure α) [sigma_finite μ] :
    (set.Union fun (i : ℕ) => spanning_sets μ i) = set.univ :=
  sorry

theorem is_countably_spanning_spanning_sets {α : Type u_1} [measurable_space α] (μ : measure α)
    [sigma_finite μ] : is_countably_spanning (set.range (spanning_sets μ)) :=
  Exists.intro (spanning_sets μ) { left := set.mem_range_self, right := Union_spanning_sets μ }

namespace measure


theorem supr_restrict_spanning_sets {α : Type u_1} [measurable_space α] {μ : measure α} {s : set α}
    [sigma_finite μ] (hs : is_measurable s) :
    (supr fun (i : ℕ) => coe_fn (restrict μ (spanning_sets μ i)) s) = coe_fn μ s :=
  sorry

namespace finite_spanning_sets_in


/-- If `μ` has finite spanning sets in `C` and `C ⊆ D` then `μ` has finite spanning sets in `D`. -/
protected def mono {α : Type u_1} [measurable_space α] {μ : measure α} {C : set (set α)}
    {D : set (set α)} (h : finite_spanning_sets_in μ C) (hC : C ⊆ D) :
    finite_spanning_sets_in μ D :=
  mk (finite_spanning_sets_in.set h) sorry (finite_spanning_sets_in.finite h)
    (finite_spanning_sets_in.spanning h)

/-- If `μ` has finite spanning sets in the collection of measurable sets `C`, then `μ` is σ-finite.
-/
protected theorem sigma_finite {α : Type u_1} [measurable_space α] {μ : measure α} {C : set (set α)}
    (h : finite_spanning_sets_in μ C) (hC : ∀ (s : set α), s ∈ C → is_measurable s) :
    sigma_finite μ :=
  Nonempty.intro (finite_spanning_sets_in.mono h hC)

/-- An extensionality for measures. It is `ext_of_generate_from_of_Union` formulated in terms of
`finite_spanning_sets_in`. -/
protected theorem ext {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    {C : set (set α)} (hA : _inst_1 = measurable_space.generate_from C) (hC : is_pi_system C)
    (h : finite_spanning_sets_in μ C) (h_eq : ∀ (s : set α), s ∈ C → coe_fn μ s = coe_fn ν s) :
    μ = ν :=
  ext_of_generate_from_of_Union C (fun (i : ℕ) => finite_spanning_sets_in.set h i) hA hC
    (finite_spanning_sets_in.spanning h) (finite_spanning_sets_in.set_mem h)
    (finite_spanning_sets_in.finite h) h_eq

protected theorem is_countably_spanning {α : Type u_1} [measurable_space α] {μ : measure α}
    {C : set (set α)} (h : finite_spanning_sets_in μ C) : is_countably_spanning C :=
  Exists.intro (fun (i : ℕ) => finite_spanning_sets_in.set h i)
    { left := finite_spanning_sets_in.set_mem h, right := finite_spanning_sets_in.spanning h }

end finite_spanning_sets_in


theorem sigma_finite_of_not_nonempty {α : Type u_1} [measurable_space α] (μ : measure α)
    (hα : ¬Nonempty α) : sigma_finite μ :=
  sorry

theorem sigma_finite_of_countable {α : Type u_1} [measurable_space α] {μ : measure α}
    {S : set (set α)} (hc : set.countable S) (hμ : ∀ (s : set α), s ∈ S → coe_fn μ s < ⊤)
    (hU : ⋃₀S = set.univ) : sigma_finite μ :=
  sorry

end measure


/-- Every finite measure is σ-finite. -/
protected instance finite_measure.to_sigma_finite {α : Type u_1} [measurable_space α]
    (μ : measure α) [finite_measure μ] : sigma_finite μ :=
  Nonempty.intro
    (measure.finite_spanning_sets_in.mk (fun (_x : ℕ) => set.univ)
      (fun (_x : ℕ) => is_measurable.univ) (fun (_x : ℕ) => measure_lt_top μ set.univ)
      (set.Union_const set.univ))

protected instance restrict.sigma_finite {α : Type u_1} [measurable_space α] (μ : measure α)
    [sigma_finite μ] (s : set α) : sigma_finite (measure.restrict μ s) :=
  Nonempty.intro
    (measure.finite_spanning_sets_in.mk (spanning_sets μ) (is_measurable_spanning_sets μ)
      (fun (i : ℕ) =>
        eq.mpr
          (id
            (Eq._oldrec (Eq.refl (coe_fn (measure.restrict μ s) (spanning_sets μ i) < ⊤))
              (measure.restrict_apply (is_measurable_spanning_sets μ i))))
          (has_le.le.trans_lt (measure_mono (set.inter_subset_left (spanning_sets μ i) s))
            (measure_spanning_sets_lt_top μ i)))
      (Union_spanning_sets μ))

protected instance sum.sigma_finite {α : Type u_1} [measurable_space α] {ι : Type u_2} [fintype ι]
    (μ : ι → measure α) [∀ (i : ι), sigma_finite (μ i)] : sigma_finite (measure.sum μ) :=
  sorry

protected instance add.sigma_finite {α : Type u_1} [measurable_space α] (μ : measure α)
    (ν : measure α) [sigma_finite μ] [sigma_finite ν] : sigma_finite (μ + ν) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sigma_finite (μ + ν))) (Eq.symm (measure.sum_cond μ ν))))
    (sum.sigma_finite fun (b : Bool) => cond b μ ν)

/-- A measure is called locally finite if it is finite in some neighborhood of each point. -/
class locally_finite_measure {α : Type u_1} [measurable_space α] [topological_space α]
    (μ : measure α)
    where
  finite_at_nhds : ∀ (x : α), measure.finite_at_filter μ (nhds x)

protected instance finite_measure.to_locally_finite_measure {α : Type u_1} [measurable_space α]
    [topological_space α] (μ : measure α) [finite_measure μ] : locally_finite_measure μ :=
  locally_finite_measure.mk fun (x : α) => measure.finite_at_filter_of_finite μ (nhds x)

theorem measure.finite_at_nhds {α : Type u_1} [measurable_space α] [topological_space α]
    (μ : measure α) [locally_finite_measure μ] (x : α) : measure.finite_at_filter μ (nhds x) :=
  locally_finite_measure.finite_at_nhds x

theorem measure.smul_finite {α : Type u_1} [measurable_space α] (μ : measure α) [finite_measure μ]
    {c : ennreal} (hc : c < ⊤) : finite_measure (c • μ) :=
  finite_measure.mk
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (coe_fn (c • μ) set.univ < ⊤)) (measure.smul_apply c μ set.univ)))
      (ennreal.mul_lt_top hc (measure_lt_top μ set.univ)))

theorem measure.exists_is_open_measure_lt_top {α : Type u_1} [measurable_space α]
    [topological_space α] (μ : measure α) [locally_finite_measure μ] (x : α) :
    ∃ (s : set α), x ∈ s ∧ is_open s ∧ coe_fn μ s < ⊤ :=
  sorry

protected instance sigma_finite_of_locally_finite {α : Type u_1} [measurable_space α]
    [topological_space α] [topological_space.second_countable_topology α] {μ : measure α}
    [locally_finite_measure μ] : sigma_finite μ :=
  sorry

/-- If two finite measures give the same mass to the whole space and coincide on a π-system made
of measurable sets, then they coincide on all sets in the σ-algebra generated by the π-system. -/
theorem ext_on_measurable_space_of_generate_finite {α : Type u_1} (m₀ : measurable_space α)
    {μ : measure α} {ν : measure α} [finite_measure μ] (C : set (set α))
    (hμν : ∀ (s : set α), s ∈ C → coe_fn μ s = coe_fn ν s) {m : measurable_space α} (h : m ≤ m₀)
    (hA : m = measurable_space.generate_from C) (hC : is_pi_system C)
    (h_univ : coe_fn μ set.univ = coe_fn ν set.univ) {s : set α}
    (hs : measurable_space.is_measurable' m s) : coe_fn μ s = coe_fn ν s :=
  sorry

/-- Two finite measures are equal if they are equal on the π-system generating the σ-algebra
  (and `univ`). -/
theorem ext_of_generate_finite {α : Type u_1} [measurable_space α] (C : set (set α))
    (hA : _inst_1 = measurable_space.generate_from C) (hC : is_pi_system C) {μ : measure α}
    {ν : measure α} [finite_measure μ] (hμν : ∀ (s : set α), s ∈ C → coe_fn μ s = coe_fn ν s)
    (h_univ : coe_fn μ set.univ = coe_fn ν set.univ) : μ = ν :=
  measure.ext
    fun (s : set α) (hs : is_measurable s) =>
      ext_on_measurable_space_of_generate_finite _inst_1 C hμν (le_refl _inst_1) hA hC h_univ hs

namespace measure


namespace finite_at_filter


theorem filter_mono {α : Type u_1} [measurable_space α] {μ : measure α} {f : filter α}
    {g : filter α} (h : f ≤ g) : finite_at_filter μ g → finite_at_filter μ f :=
  sorry

theorem inf_of_left {α : Type u_1} [measurable_space α] {μ : measure α} {f : filter α}
    {g : filter α} (h : finite_at_filter μ f) : finite_at_filter μ (f ⊓ g) :=
  filter_mono inf_le_left h

theorem inf_of_right {α : Type u_1} [measurable_space α] {μ : measure α} {f : filter α}
    {g : filter α} (h : finite_at_filter μ g) : finite_at_filter μ (f ⊓ g) :=
  filter_mono inf_le_right h

@[simp] theorem inf_ae_iff {α : Type u_1} [measurable_space α] {μ : measure α} {f : filter α} :
    finite_at_filter μ (f ⊓ ae μ) ↔ finite_at_filter μ f :=
  sorry

theorem of_inf_ae {α : Type u_1} [measurable_space α] {μ : measure α} {f : filter α} :
    finite_at_filter μ (f ⊓ ae μ) → finite_at_filter μ f :=
  iff.mp inf_ae_iff

theorem filter_mono_ae {α : Type u_1} [measurable_space α] {μ : measure α} {f : filter α}
    {g : filter α} (h : f ⊓ ae μ ≤ g) (hg : finite_at_filter μ g) : finite_at_filter μ f :=
  iff.mp inf_ae_iff (filter_mono h hg)

protected theorem measure_mono {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    {f : filter α} (h : μ ≤ ν) : finite_at_filter ν f → finite_at_filter μ f :=
  sorry

protected theorem mono {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    {f : filter α} {g : filter α} (hf : f ≤ g) (hμ : μ ≤ ν) :
    finite_at_filter ν g → finite_at_filter μ f :=
  fun (h : finite_at_filter ν g) => finite_at_filter.measure_mono hμ (filter_mono hf h)

protected theorem eventually {α : Type u_1} [measurable_space α] {μ : measure α} {f : filter α}
    (h : finite_at_filter μ f) :
    filter.eventually (fun (s : set α) => coe_fn μ s < ⊤) (filter.lift' f set.powerset) :=
  sorry

theorem filter_sup {α : Type u_1} [measurable_space α] {μ : measure α} {f : filter α}
    {g : filter α} : finite_at_filter μ f → finite_at_filter μ g → finite_at_filter μ (f ⊔ g) :=
  sorry

end finite_at_filter


theorem finite_at_nhds_within {α : Type u_1} [measurable_space α] [topological_space α]
    (μ : measure α) [locally_finite_measure μ] (x : α) (s : set α) :
    finite_at_filter μ (nhds_within x s) :=
  finite_at_filter.inf_of_left (finite_at_nhds μ x)

@[simp] theorem finite_at_principal {α : Type u_1} [measurable_space α] {μ : measure α}
    {s : set α} : finite_at_filter μ (filter.principal s) ↔ coe_fn μ s < ⊤ :=
  sorry

/-! ### Subtraction of measures -/

/-- The measure `μ - ν` is defined to be the least measure `τ` such that `μ ≤ τ + ν`.
It is the equivalent of `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ennreal.has_sub`.
Specifically, note that if you have `α = {1,2}`, and  `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ⊤`, then `(μ - ν) + ν = μ`. -/
protected instance has_sub {α : Type u_1} [measurable_space α] : Sub (measure α) :=
  { sub := fun (μ ν : measure α) => Inf (set_of fun (τ : measure α) => μ ≤ τ + ν) }

theorem sub_def {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α} :
    μ - ν = Inf (set_of fun (d : measure α) => μ ≤ d + ν) :=
  rfl

theorem sub_eq_zero_of_le {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    (h : μ ≤ ν) : μ - ν = 0 :=
  sorry

/-- This application lemma only works in special circumstances. Given knowledge of
when `μ ≤ ν` and `ν ≤ μ`, a more general application lemma can be written. -/
theorem sub_apply {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α} {s : set α}
    [finite_measure ν] (h₁ : is_measurable s) (h₂ : ν ≤ μ) :
    coe_fn (μ - ν) s = coe_fn μ s - coe_fn ν s :=
  sorry

theorem sub_add_cancel_of_le {α : Type u_1} [measurable_space α] {μ : measure α} {ν : measure α}
    [finite_measure ν] (h₁ : ν ≤ μ) : μ - ν + ν = μ :=
  sorry

end measure


end measure_theory


namespace measurable_equiv


/-! Interactions of measurable equivalences and measures -/

/-- If we map a measure along a measurable equivalence, we can compute the measure on all sets
  (not just the measurable ones). -/
protected theorem map_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure_theory.measure α} (f : α ≃ᵐ β) (s : set β) :
    coe_fn (coe_fn (measure_theory.measure.map ⇑f) μ) s = coe_fn μ (⇑f ⁻¹' s) :=
  sorry

@[simp] theorem map_symm_map {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure_theory.measure α} (e : α ≃ᵐ β) :
    coe_fn (measure_theory.measure.map ⇑(symm e)) (coe_fn (measure_theory.measure.map ⇑e) μ) = μ :=
  sorry

@[simp] theorem map_map_symm {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {ν : measure_theory.measure β} (e : α ≃ᵐ β) :
    coe_fn (measure_theory.measure.map ⇑e) (coe_fn (measure_theory.measure.map ⇑(symm e)) ν) = ν :=
  sorry

theorem map_measurable_equiv_injective {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] (e : α ≃ᵐ β) : function.injective ⇑(measure_theory.measure.map ⇑e) :=
  sorry

theorem map_apply_eq_iff_map_symm_apply_eq {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {μ : measure_theory.measure α} {ν : measure_theory.measure β}
    (e : α ≃ᵐ β) :
    coe_fn (measure_theory.measure.map ⇑e) μ = ν ↔
        coe_fn (measure_theory.measure.map ⇑(symm e)) ν = μ :=
  sorry

end measurable_equiv


/-- A measure is complete if every null set is also measurable.
  A null set is a subset of a measurable set with measure `0`.
  Since every measure is defined as a special case of an outer measure, we can more simply state
  that a set `s` is null if `μ s = 0`. -/
def measure_theory.measure.is_complete {α : Type u_1} {_x : measurable_space α}
    (μ : measure_theory.measure α) :=
  ∀ (s : set α), coe_fn μ s = 0 → is_measurable s

/-- A set is null measurable if it is the union of a null set and a measurable set. -/
def is_null_measurable {α : Type u_1} [measurable_space α] (μ : measure_theory.measure α)
    (s : set α) :=
  ∃ (t : set α), ∃ (z : set α), s = t ∪ z ∧ is_measurable t ∧ coe_fn μ z = 0

theorem is_null_measurable_iff {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α}
    {s : set α} :
    is_null_measurable μ s ↔ ∃ (t : set α), t ⊆ s ∧ is_measurable t ∧ coe_fn μ (s \ t) = 0 :=
  sorry

theorem is_null_measurable_measure_eq {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {s : set α} {t : set α} (st : t ⊆ s)
    (hz : coe_fn μ (s \ t) = 0) : coe_fn μ s = coe_fn μ t :=
  sorry

theorem is_measurable.is_null_measurable {α : Type u_1} [measurable_space α] {s : set α}
    (μ : measure_theory.measure α) (hs : is_measurable s) : is_null_measurable μ s :=
  sorry

theorem is_null_measurable_of_complete {α : Type u_1} [measurable_space α] {s : set α}
    (μ : measure_theory.measure α) [c : measure_theory.measure.is_complete μ] :
    is_null_measurable μ s ↔ is_measurable s :=
  sorry

theorem is_null_measurable.union_null {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {s : set α} {z : set α} (hs : is_null_measurable μ s)
    (hz : coe_fn μ z = 0) : is_null_measurable μ (s ∪ z) :=
  sorry

theorem null_is_null_measurable {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α}
    {z : set α} (hz : coe_fn μ z = 0) : is_null_measurable μ z :=
  sorry

theorem is_null_measurable.Union_nat {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {s : ℕ → set α} (hs : ∀ (i : ℕ), is_null_measurable μ (s i)) :
    is_null_measurable μ (set.Union s) :=
  sorry

theorem is_measurable.diff_null {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α}
    {s : set α} {z : set α} (hs : is_measurable s) (hz : coe_fn μ z = 0) :
    is_null_measurable μ (s \ z) :=
  sorry

theorem is_null_measurable.diff_null {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {s : set α} {z : set α} (hs : is_null_measurable μ s)
    (hz : coe_fn μ z = 0) : is_null_measurable μ (s \ z) :=
  sorry

theorem is_null_measurable.compl {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α}
    {s : set α} (hs : is_null_measurable μ s) : is_null_measurable μ (sᶜ) :=
  sorry

theorem is_null_measurable_iff_ae {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α}
    {s : set α} :
    is_null_measurable μ s ↔
        ∃ (t : set α), is_measurable t ∧ filter.eventually_eq (measure_theory.measure.ae μ) s t :=
  sorry

theorem is_null_measurable_iff_sandwich {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {s : set α} :
    is_null_measurable μ s ↔
        ∃ (t : set α),
          ∃ (u : set α), is_measurable t ∧ is_measurable u ∧ t ⊆ s ∧ s ⊆ u ∧ coe_fn μ (u \ t) = 0 :=
  sorry

theorem restrict_apply_of_is_null_measurable {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {s : set α} {t : set α}
    (ht : is_null_measurable (measure_theory.measure.restrict μ s) t) :
    coe_fn (measure_theory.measure.restrict μ s) t = coe_fn μ (t ∩ s) :=
  sorry

/-- The measurable space of all null measurable sets. -/
def null_measurable {α : Type u_1} [measurable_space α] (μ : measure_theory.measure α) :
    measurable_space α :=
  measurable_space.mk (is_null_measurable μ) sorry sorry sorry

/-- Given a measure we can complete it to a (complete) measure on all null measurable sets. -/
def completion {α : Type u_1} [measurable_space α] (μ : measure_theory.measure α) :
    measure_theory.measure α :=
  measure_theory.measure.mk (measure_theory.measure.to_outer_measure μ) sorry sorry

protected instance completion.is_complete {α : Type u_1} [measurable_space α]
    (μ : measure_theory.measure α) : measure_theory.measure.is_complete (completion μ) :=
  fun (z : set α) (hz : coe_fn (completion μ) z = 0) => null_is_null_measurable hz

theorem measurable.ae_eq {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure_theory.measure α} [hμ : measure_theory.measure.is_complete μ] {f : α → β}
    {g : α → β} (hf : measurable f) (hfg : filter.eventually_eq (measure_theory.measure.ae μ) f g) :
    measurable g :=
  sorry

namespace measure_theory


/-- A measure space is a measurable space equipped with a
  measure, referred to as `volume`. -/
class measure_space (α : Type u_6) extends measurable_space α where
  volume : measure α

/-- `volume` is the canonical  measure on `α`. -/
/-- The tactic `exact volume`, to be used in optional (`auto_param`) arguments. -/
end measure_theory


/-!
# Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. We define this property, called `ae_measurable f μ`, and discuss several of its properties
that are analogous to properties of measurable functions.
-/

/-- A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. -/
def ae_measurable {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    (f : α → β)
    (μ :
      autoParam (measure_theory.measure α)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.measure_theory.volume_tac")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory")
            "volume_tac")
          [])) :=
  ∃ (g : α → β), measurable g ∧ filter.eventually_eq (measure_theory.measure.ae μ) f g

theorem measurable.ae_measurable {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {f : α → β} {μ : measure_theory.measure α} (h : measurable f) :
    ae_measurable f :=
  Exists.intro f { left := h, right := measure_theory.ae_eq_refl f }

theorem subsingleton.ae_measurable {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {f : α → β} {μ : measure_theory.measure α} [subsingleton α] :
    ae_measurable f :=
  measurable.ae_measurable subsingleton.measurable

@[simp] theorem ae_measurable_zero {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {f : α → β} : ae_measurable f :=
  sorry

theorem ae_measurable_iff_measurable {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {f : α → β} {μ : measure_theory.measure α}
    [measure_theory.measure.is_complete μ] : ae_measurable f ↔ measurable f :=
  sorry

namespace ae_measurable


/-- Given an almost everywhere measurable function `f`, associate to it a measurable function
that coincides with it almost everywhere. `f` is explicit in the definition to make sure that
it shows in pretty-printing. -/
def mk {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure_theory.measure α} (f : α → β) (h : ae_measurable f) : α → β :=
  classical.some h

theorem measurable_mk {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {f : α → β} {μ : measure_theory.measure α} (h : ae_measurable f) : measurable (mk f h) :=
  and.left (classical.some_spec h)

theorem ae_eq_mk {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] {f : α → β}
    {μ : measure_theory.measure α} (h : ae_measurable f) :
    filter.eventually_eq (measure_theory.measure.ae μ) f (mk f h) :=
  and.right (classical.some_spec h)

theorem congr {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] {f : α → β}
    {g : α → β} {μ : measure_theory.measure α} (hf : ae_measurable f)
    (h : filter.eventually_eq (measure_theory.measure.ae μ) f g) : ae_measurable g :=
  Exists.intro (mk f hf)
    { left := measurable_mk hf,
      right := filter.eventually_eq.trans (filter.eventually_eq.symm h) (ae_eq_mk hf) }

theorem mono_measure {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {f : α → β} {μ : measure_theory.measure α} {ν : measure_theory.measure α} (h : ae_measurable f)
    (h' : ν ≤ μ) : ae_measurable f :=
  Exists.intro (mk f h)
    { left := measurable_mk h,
      right := filter.eventually.filter_mono (measure_theory.ae_mono h') (ae_eq_mk h) }

theorem mono_set {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] {f : α → β}
    {μ : measure_theory.measure α} {s : set α} {t : set α} (h : s ⊆ t) (ht : ae_measurable f) :
    ae_measurable f :=
  mono_measure ht (measure_theory.measure.restrict_mono h le_rfl)

theorem ae_mem_imp_eq_mk {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {f : α → β} {μ : measure_theory.measure α} {s : set α} (h : ae_measurable f) :
    filter.eventually (fun (x : α) => x ∈ s → f x = mk f h x) (measure_theory.measure.ae μ) :=
  measure_theory.ae_imp_of_ae_restrict (ae_eq_mk h)

theorem ae_inf_principal_eq_mk {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {f : α → β} {μ : measure_theory.measure α} {s : set α}
    (h : ae_measurable f) :
    filter.eventually_eq (measure_theory.measure.ae μ ⊓ filter.principal s) f (mk f h) :=
  measure_theory.le_ae_restrict (ae_eq_mk h)

theorem add_measure {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure_theory.measure α} {ν : measure_theory.measure α} {f : α → β} (hμ : ae_measurable f)
    (hν : ae_measurable f) : ae_measurable f :=
  sorry

theorem smul_measure {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {f : α → β} {μ : measure_theory.measure α} (h : ae_measurable f) (c : ennreal) :
    ae_measurable f :=
  Exists.intro (mk f h)
    { left := measurable_mk h, right := measure_theory.ae_smul_measure (ae_eq_mk h) c }

theorem comp_measurable {α : Type u_1} {β : Type u_2} {δ : Type u_4} [measurable_space α]
    [measurable_space β] {μ : measure_theory.measure α} [measurable_space δ] {f : α → δ} {g : δ → β}
    (hg : ae_measurable g) (hf : measurable f) : ae_measurable (g ∘ f) :=
  Exists.intro (mk g hg ∘ f)
    { left := measurable.comp (measurable_mk hg) hf,
      right := measure_theory.ae_eq_comp hf (ae_eq_mk hg) }

theorem prod_mk {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {μ : measure_theory.measure α} {γ : Type u_3} [measurable_space γ] {f : α → β} {g : α → γ}
    (hf : ae_measurable f) (hg : ae_measurable g) : ae_measurable fun (x : α) => (f x, g x) :=
  Exists.intro (fun (a : α) => (mk f hf a, mk g hg a))
    { left := measurable.prod_mk (measurable_mk hf) (measurable_mk hg),
      right := filter.eventually_eq.prod_mk (ae_eq_mk hf) (ae_eq_mk hg) }

theorem is_null_measurable {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {f : α → β} {μ : measure_theory.measure α} (h : ae_measurable f) {s : set β}
    (hs : is_measurable s) : is_null_measurable μ (f ⁻¹' s) :=
  sorry

end ae_measurable


theorem ae_measurable_congr {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    {f : α → β} {g : α → β} {μ : measure_theory.measure α}
    (h : filter.eventually_eq (measure_theory.measure.ae μ) f g) :
    ae_measurable f ↔ ae_measurable g :=
  { mp := fun (hf : ae_measurable f) => ae_measurable.congr hf h,
    mpr := fun (hg : ae_measurable g) => ae_measurable.congr hg (filter.eventually_eq.symm h) }

@[simp] theorem ae_measurable_add_measure_iff {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {f : α → β} {μ : measure_theory.measure α} {ν : measure_theory.measure α} :
    ae_measurable f ↔ ae_measurable f ∧ ae_measurable f :=
  sorry

@[simp] theorem ae_measurable_const {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {μ : measure_theory.measure α} {b : β} : ae_measurable fun (a : α) => b :=
  measurable.ae_measurable measurable_const

@[simp] theorem ae_measurable_smul_measure_iff {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {f : α → β} {μ : measure_theory.measure α} {c : ennreal} (hc : c ≠ 0) :
    ae_measurable f ↔ ae_measurable f :=
  sorry

theorem measurable.comp_ae_measurable {α : Type u_1} {β : Type u_2} {δ : Type u_4}
    [measurable_space α] [measurable_space β] {μ : measure_theory.measure α} [measurable_space δ]
    {f : α → δ} {g : δ → β} (hg : measurable g) (hf : ae_measurable f) : ae_measurable (g ∘ f) :=
  Exists.intro (g ∘ ae_measurable.mk f hf)
    { left := measurable.comp hg (ae_measurable.measurable_mk hf),
      right := filter.eventually_eq.fun_comp (ae_measurable.ae_eq_mk hf) g }

theorem ae_measurable_of_zero_measure {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {f : α → β} : ae_measurable f :=
  dite (Nonempty α) (fun (h : Nonempty α) => ae_measurable.congr ae_measurable_const rfl)
    fun (h : ¬Nonempty α) => measurable.ae_measurable (measurable_of_not_nonempty h f)

namespace is_compact


theorem finite_measure_of_nhds_within {α : Type u_1} [topological_space α] [measurable_space α]
    {μ : measure_theory.measure α} {s : set α} (hs : is_compact s) :
    (∀ (a : α), a ∈ s → measure_theory.measure.finite_at_filter μ (nhds_within a s)) →
        coe_fn μ s < ⊤ :=
  sorry

theorem finite_measure {α : Type u_1} [topological_space α] [measurable_space α]
    {μ : measure_theory.measure α} {s : set α} [measure_theory.locally_finite_measure μ]
    (hs : is_compact s) : coe_fn μ s < ⊤ :=
  finite_measure_of_nhds_within hs
    fun (a : α) (ha : a ∈ s) => measure_theory.measure.finite_at_nhds_within μ a s

theorem measure_zero_of_nhds_within {α : Type u_1} [topological_space α] [measurable_space α]
    {μ : measure_theory.measure α} {s : set α} (hs : is_compact s) :
    (∀ (a : α) (H : a ∈ s), ∃ (t : set α), ∃ (H : t ∈ nhds_within a s), coe_fn μ t = 0) →
        coe_fn μ s = 0 :=
  sorry

end is_compact


theorem metric.bounded.finite_measure {α : Type u_1} [metric_space α] [proper_space α]
    [measurable_space α] {μ : measure_theory.measure α} [measure_theory.locally_finite_measure μ]
    {s : set α} (hs : metric.bounded s) : coe_fn μ s < ⊤ :=
  sorry

end Mathlib