/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.bochner_integration
import Mathlib.analysis.normed_space.indicator_function
import Mathlib.PostPort

universes u_1 u_2 u_3 u_5 u_4 

namespace Mathlib

/-!
# Set integral

In this file we prove some properties of `∫ x in s, f x ∂μ`. Recall that this notation
is defined as `∫ x, f x ∂(μ.restrict s)`. In `integral_indicator` we prove that for a measurable
function `f` and a measurable set `s` this definition coincides with another natural definition:
`∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ`, where `indicator s f x` is equal to `f x` for `x ∈ s`
and is zero otherwise.

Since `∫ x in s, f x ∂μ` is a notation, one can rewrite or apply any theorem about `∫ x, f x ∂μ`
directly. In this file we prove some theorems about dependence of `∫ x in s, f x ∂μ` on `s`, e.g.
`integral_union`, `integral_empty`, `integral_univ`.

We also define `integrable_on f s μ := integrable f (μ.restrict s)` and prove theorems like
`integrable_on_union : integrable_on f (s ∪ t) μ ↔ integrable_on f s μ ∧ integrable_on f t μ`.

Next we define a predicate `integrable_at_filter (f : α → E) (l : filter α) (μ : measure α)`
saying that `f` is integrable at some set `s ∈ l` and prove that a measurable function is integrable
at `l` with respect to `μ` provided that `f` is bounded above at `l ⊓ μ.ae` and `μ` is finite
at `l`.

Finally, we prove a version of the
[Fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for set integral, see `filter.tendsto.integral_sub_linear_is_o_ae` and its corollaries.
Namely, consider a measurably generated filter `l`, a measure `μ` finite at this filter, and
a function `f` that has a finite limit `c` at `l ⊓ μ.ae`. Then `∫ x in s, f x ∂μ = μ s • c + o(μ s)`
as `s` tends to `l.lift' powerset`, i.e. for any `ε>0` there exists `t ∈ l` such that
`∥∫ x in s, f x ∂μ - μ s • c∥ ≤ ε * μ s` whenever `s ⊆ t`. We also formulate a version of this
theorem for a locally finite measure `μ` and a function `f` continuous at a point `a`.

## Notation

`∫ a in s, f a` is `measure_theory.integral (s.indicator f)`

## TODO

The file ends with over a hundred lines of commented out code. This is the old contents of this file
using the `indicator` approach to the definition of `∫ x in s, f x ∂μ`. This code should be
migrated to the new definition.

-/

theorem piecewise_ae_eq_restrict {α : Type u_1} {β : Type u_2} [measurable_space α]
    {μ : measure_theory.measure α} {s : set α} {f : α → β} {g : α → β} (hs : is_measurable s) :
    filter.eventually_eq (measure_theory.measure.ae (measure_theory.measure.restrict μ s))
        (set.piecewise s f g) f :=
  sorry

theorem piecewise_ae_eq_restrict_compl {α : Type u_1} {β : Type u_2} [measurable_space α]
    {μ : measure_theory.measure α} {s : set α} {f : α → β} {g : α → β} (hs : is_measurable s) :
    filter.eventually_eq (measure_theory.measure.ae (measure_theory.measure.restrict μ (sᶜ)))
        (set.piecewise s f g) g :=
  sorry

theorem indicator_ae_eq_restrict {α : Type u_1} {β : Type u_2} [measurable_space α] [HasZero β]
    {μ : measure_theory.measure α} {s : set α} {f : α → β} (hs : is_measurable s) :
    filter.eventually_eq (measure_theory.measure.ae (measure_theory.measure.restrict μ s))
        (set.indicator s f) f :=
  piecewise_ae_eq_restrict hs

theorem indicator_ae_eq_restrict_compl {α : Type u_1} {β : Type u_2} [measurable_space α]
    [HasZero β] {μ : measure_theory.measure α} {s : set α} {f : α → β} (hs : is_measurable s) :
    filter.eventually_eq (measure_theory.measure.ae (measure_theory.measure.restrict μ (sᶜ)))
        (set.indicator s f) 0 :=
  piecewise_ae_eq_restrict_compl hs

/-- A function `f` is measurable at filter `l` w.r.t. a measure `μ` if it is ae-measurable
w.r.t. `μ.restrict s` for some `s ∈ l`. -/
def measurable_at_filter {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β]
    (f : α → β) (l : filter α)
    (μ :
      autoParam (measure_theory.measure α)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.measure_theory.volume_tac")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory")
            "volume_tac")
          [])) :=
  ∃ (s : set α), ∃ (H : s ∈ l), ae_measurable f

@[simp] theorem measurable_at_bot {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {μ : measure_theory.measure α} {f : α → β} : measurable_at_filter f ⊥ :=
  sorry

protected theorem measurable_at_filter.eventually {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {l : filter α} {f : α → β} {μ : measure_theory.measure α}
    (h : measurable_at_filter f l) :
    filter.eventually (fun (s : set α) => ae_measurable f) (filter.lift' l set.powerset) :=
  iff.mpr (filter.eventually_lift'_powerset' fun (s t : set α) => ae_measurable.mono_set) h

protected theorem measurable_at_filter.filter_mono {α : Type u_1} {β : Type u_2}
    [measurable_space α] [measurable_space β] {l : filter α} {l' : filter α} {f : α → β}
    {μ : measure_theory.measure α} (h : measurable_at_filter f l) (h' : l' ≤ l) :
    measurable_at_filter f l' :=
  sorry

protected theorem ae_measurable.measurable_at_filter {α : Type u_1} {β : Type u_2}
    [measurable_space α] [measurable_space β] {l : filter α} {f : α → β}
    {μ : measure_theory.measure α} (h : ae_measurable f) : measurable_at_filter f l :=
  Exists.intro set.univ
    (Exists.intro filter.univ_mem_sets
      (eq.mpr (id (Eq._oldrec (Eq.refl (ae_measurable f)) measure_theory.measure.restrict_univ)) h))

theorem ae_measurable.measurable_at_filter_of_mem {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {l : filter α} {f : α → β} {μ : measure_theory.measure α} {s : set α}
    (h : ae_measurable f) (hl : s ∈ l) : measurable_at_filter f l :=
  Exists.intro s (Exists.intro hl h)

protected theorem measurable.measurable_at_filter {α : Type u_1} {β : Type u_2} [measurable_space α]
    [measurable_space β] {l : filter α} {f : α → β} {μ : measure_theory.measure α}
    (h : measurable f) : measurable_at_filter f l :=
  ae_measurable.measurable_at_filter (measurable.ae_measurable h)

namespace measure_theory


theorem has_finite_integral_restrict_of_bounded {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] {f : α → E} {s : set α} {μ : measure α} {C : ℝ} (hs : coe_fn μ s < ⊤)
    (hf : filter.eventually (fun (x : α) => norm (f x) ≤ C) (measure.ae (measure.restrict μ s))) :
    has_finite_integral f :=
  has_finite_integral_of_bounded hf

/-- A function is `integrable_on` a set `s` if it is a measurable function and if the integral of
  its pointwise norm over `s` is less than infinity. -/
def integrable_on {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] (f : α → E) (s : set α)
    (μ :
      autoParam (measure α)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.measure_theory.volume_tac")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory")
            "volume_tac")
          [])) :=
  integrable f

theorem integrable_on.integrable {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {s : set α} {μ : measure α} (h : integrable_on f s) :
    integrable f :=
  h

@[simp] theorem integrable_on_empty {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {μ : measure α} : integrable_on f ∅ :=
  sorry

@[simp] theorem integrable_on_univ {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {μ : measure α} :
    integrable_on f set.univ ↔ integrable f :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (integrable_on f set.univ ↔ integrable f))
        (integrable_on.equations._eqn_1 f set.univ)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (integrable f ↔ integrable f)) measure.restrict_univ))
      (iff.refl (integrable f)))

theorem integrable_on_zero {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {s : set α} {μ : measure α} : integrable_on (fun (_x : α) => 0) s :=
  integrable_zero α E (measure.restrict μ s)

theorem integrable_on_const {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {s : set α} {μ : measure α} {C : E} :
    integrable_on (fun (_x : α) => C) s ↔ C = 0 ∨ coe_fn μ s < ⊤ :=
  sorry

theorem integrable_on.mono {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {s : set α} {t : set α} {μ : measure α} {ν : measure α}
    (h : integrable_on f t) (hs : s ⊆ t) (hμ : μ ≤ ν) : integrable_on f s :=
  integrable.mono_measure h (measure.restrict_mono hs hμ)

theorem integrable_on.mono_set {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {s : set α} {t : set α} {μ : measure α} (h : integrable_on f t)
    (hst : s ⊆ t) : integrable_on f s :=
  integrable_on.mono h hst (le_refl μ)

theorem integrable_on.mono_measure {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {μ : measure α} {ν : measure α}
    (h : integrable_on f s) (hμ : μ ≤ ν) : integrable_on f s :=
  integrable_on.mono h (set.subset.refl s) hμ

theorem integrable_on.mono_set_ae {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {t : set α} {μ : measure α}
    (h : integrable_on f t) (hst : filter.eventually_le (measure.ae μ) s t) : integrable_on f s :=
  integrable.mono_measure (integrable_on.integrable h) (restrict_mono_ae hst)

theorem integrable.integrable_on {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {s : set α} {μ : measure α} (h : integrable f) :
    integrable_on f s :=
  integrable.mono_measure h measure.restrict_le_self

theorem integrable.integrable_on' {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {μ : measure α}
    (h : integrable f) : integrable_on f s :=
  h

theorem integrable_on.left_of_union {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {t : set α} {μ : measure α}
    (h : integrable_on f (s ∪ t)) : integrable_on f s :=
  integrable_on.mono_set h (set.subset_union_left s t)

theorem integrable_on.right_of_union {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {t : set α} {μ : measure α}
    (h : integrable_on f (s ∪ t)) : integrable_on f t :=
  integrable_on.mono_set h (set.subset_union_right s t)

theorem integrable_on.union {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {s : set α} {t : set α} {μ : measure α}
    (hs : integrable_on f s) (ht : integrable_on f t) : integrable_on f (s ∪ t) :=
  integrable.mono_measure (integrable.add_measure hs ht) (measure.restrict_union_le s t)

@[simp] theorem integrable_on_union {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {t : set α} {μ : measure α} :
    integrable_on f (s ∪ t) ↔ integrable_on f s ∧ integrable_on f t :=
  sorry

@[simp] theorem integrable_on_finite_union {α : Type u_1} {β : Type u_2} {E : Type u_3}
    [measurable_space α] [normed_group E] [measurable_space E] {f : α → E} {μ : measure α}
    {s : set β} (hs : set.finite s) {t : β → set α} :
    integrable_on f (set.Union fun (i : β) => set.Union fun (H : i ∈ s) => t i) ↔
        ∀ (i : β), i ∈ s → integrable_on f (t i) :=
  sorry

@[simp] theorem integrable_on_finset_union {α : Type u_1} {β : Type u_2} {E : Type u_3}
    [measurable_space α] [normed_group E] [measurable_space E] {f : α → E} {μ : measure α}
    {s : finset β} {t : β → set α} :
    integrable_on f (set.Union fun (i : β) => set.Union fun (H : i ∈ s) => t i) ↔
        ∀ (i : β), i ∈ s → integrable_on f (t i) :=
  integrable_on_finite_union (finset.finite_to_set s)

theorem integrable_on.add_measure {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {μ : measure α} {ν : measure α}
    (hμ : integrable_on f s) (hν : integrable_on f s) : integrable_on f s :=
  id
    (eq.mpr (id (Eq._oldrec (Eq.refl (integrable f)) (measure.restrict_add μ ν s)))
      (integrable.add_measure (integrable_on.integrable hμ) hν))

@[simp] theorem integrable_on_add_measure {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {μ : measure α} {ν : measure α} :
    integrable_on f s ↔ integrable_on f s ∧ integrable_on f s :=
  sorry

theorem ae_measurable_indicator_iff {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {μ : measure α}
    (hs : is_measurable s) : ae_measurable f ↔ ae_measurable (set.indicator s f) :=
  sorry

theorem integrable_indicator_iff {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {s : set α} {μ : measure α} (hs : is_measurable s) :
    integrable (set.indicator s f) ↔ integrable_on f s :=
  sorry

theorem integrable_on.indicator {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {s : set α} {μ : measure α} (h : integrable_on f s)
    (hs : is_measurable s) : integrable (set.indicator s f) :=
  iff.mpr (integrable_indicator_iff hs) h

/-- We say that a function `f` is *integrable at filter* `l` if it is integrable on some
set `s ∈ l`. Equivalently, it is eventually integrable on `s` in `l.lift' powerset`. -/
def integrable_at_filter {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] (f : α → E) (l : filter α)
    (μ :
      autoParam (measure α)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.measure_theory.volume_tac")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory")
            "volume_tac")
          [])) :=
  ∃ (s : set α), ∃ (H : s ∈ l), integrable_on f s

protected theorem integrable_at_filter.eventually {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {μ : measure α} {l : filter α}
    (h : integrable_at_filter f l) :
    filter.eventually (fun (s : set α) => integrable_on f s) (filter.lift' l set.powerset) :=
  sorry

theorem integrable_at_filter.filter_mono {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {μ : measure α} {l : filter α} {l' : filter α}
    (hl : l ≤ l') (hl' : integrable_at_filter f l') : integrable_at_filter f l :=
  sorry

theorem integrable_at_filter.inf_of_left {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {μ : measure α} {l : filter α} {l' : filter α}
    (hl : integrable_at_filter f l) : integrable_at_filter f (l ⊓ l') :=
  integrable_at_filter.filter_mono inf_le_left hl

theorem integrable_at_filter.inf_of_right {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {μ : measure α} {l : filter α} {l' : filter α}
    (hl : integrable_at_filter f l) : integrable_at_filter f (l' ⊓ l) :=
  integrable_at_filter.filter_mono inf_le_right hl

@[simp] theorem integrable_at_filter.inf_ae_iff {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {μ : measure α} {l : filter α} :
    integrable_at_filter f (l ⊓ measure.ae μ) ↔ integrable_at_filter f l :=
  sorry

theorem integrable_at_filter.of_inf_ae {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {μ : measure α} {l : filter α} :
    integrable_at_filter f (l ⊓ measure.ae μ) → integrable_at_filter f l :=
  iff.mp integrable_at_filter.inf_ae_iff

/-- If `μ` is a measure finite at filter `l` and `f` is a function such that its norm is bounded
above at `l`, then `f` is integrable at `l`. -/
theorem measure.finite_at_filter.integrable_at_filter {α : Type u_1} {E : Type u_3}
    [measurable_space α] [normed_group E] [measurable_space E] {f : α → E} {μ : measure α}
    {l : filter α} [filter.is_measurably_generated l] (hfm : measurable_at_filter f l)
    (hμ : measure.finite_at_filter μ l) (hf : filter.is_bounded_under LessEq l (norm ∘ f)) :
    integrable_at_filter f l :=
  sorry

theorem measure.finite_at_filter.integrable_at_filter_of_tendsto_ae {α : Type u_1} {E : Type u_3}
    [measurable_space α] [normed_group E] [measurable_space E] {f : α → E} {μ : measure α}
    {l : filter α} [filter.is_measurably_generated l] (hfm : measurable_at_filter f l)
    (hμ : measure.finite_at_filter μ l) {b : E}
    (hf : filter.tendsto f (l ⊓ measure.ae μ) (nhds b)) : integrable_at_filter f l :=
  integrable_at_filter.of_inf_ae
    (measure.finite_at_filter.integrable_at_filter
      (measurable_at_filter.filter_mono hfm inf_le_left) (measure.finite_at_filter.inf_of_left hμ)
      (filter.tendsto.is_bounded_under_le (filter.tendsto.norm hf)))

theorem Mathlib.filter.tendsto.integrable_at_filter_ae {α : Type u_1} {E : Type u_3}
    [measurable_space α] [normed_group E] [measurable_space E] {f : α → E} {μ : measure α}
    {l : filter α} [filter.is_measurably_generated l] (hfm : measurable_at_filter f l)
    (hμ : measure.finite_at_filter μ l) {b : E}
    (hf : filter.tendsto f (l ⊓ measure.ae μ) (nhds b)) : integrable_at_filter f l :=
  measure.finite_at_filter.integrable_at_filter_of_tendsto_ae

theorem measure.finite_at_filter.integrable_at_filter_of_tendsto {α : Type u_1} {E : Type u_3}
    [measurable_space α] [normed_group E] [measurable_space E] {f : α → E} {μ : measure α}
    {l : filter α} [filter.is_measurably_generated l] (hfm : measurable_at_filter f l)
    (hμ : measure.finite_at_filter μ l) {b : E} (hf : filter.tendsto f l (nhds b)) :
    integrable_at_filter f l :=
  measure.finite_at_filter.integrable_at_filter hfm hμ
    (filter.tendsto.is_bounded_under_le (filter.tendsto.norm hf))

theorem Mathlib.filter.tendsto.integrable_at_filter {α : Type u_1} {E : Type u_3}
    [measurable_space α] [normed_group E] [measurable_space E] {f : α → E} {μ : measure α}
    {l : filter α} [filter.is_measurably_generated l] (hfm : measurable_at_filter f l)
    (hμ : measure.finite_at_filter μ l) {b : E} (hf : filter.tendsto f l (nhds b)) :
    integrable_at_filter f l :=
  measure.finite_at_filter.integrable_at_filter_of_tendsto

theorem integrable_add {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [opens_measurable_space E] {f : α → E}
    {g : α → E} (h : set.univ ⊆ f ⁻¹' singleton 0 ∪ g ⁻¹' singleton 0) (hf : measurable f)
    (hg : measurable g) : integrable (f + g) ↔ integrable f ∧ integrable g :=
  sorry

/-- To prove something for an arbitrary integrable function in a second countable
Borel normed group, it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `L¹` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_sum` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`).
-/
theorem integrable.induction {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] (P : (α → E) → Prop)
    (h_ind :
      ∀ (c : E) {s : set α},
        is_measurable s → coe_fn μ s < ⊤ → P (set.indicator s fun (_x : α) => c))
    (h_sum :
      ∀ {f g : α → E},
        set.univ ⊆ f ⁻¹' singleton 0 ∪ g ⁻¹' singleton 0 →
          integrable f → integrable g → P f → P g → P (f + g))
    (h_closed : is_closed (set_of fun (f : l1 α E μ) => P ⇑f))
    (h_ae : ∀ {f g : α → E}, filter.eventually_eq (measure.ae μ) f g → integrable f → P f → P g)
    {f : α → E} (hf : integrable f) : P f :=
  sorry

theorem set_integral_congr_ae {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {g : α → E} {s : set α} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E]
    (hs : is_measurable s)
    (h : filter.eventually (fun (x : α) => x ∈ s → f x = g x) (measure.ae μ)) :
    (integral (measure.restrict μ s) fun (x : α) => f x) =
        integral (measure.restrict μ s) fun (x : α) => g x :=
  integral_congr_ae (iff.mpr (ae_restrict_iff' hs) h)

theorem set_integral_congr {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {g : α → E} {s : set α} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E]
    (hs : is_measurable s) (h : set.eq_on f g s) :
    (integral (measure.restrict μ s) fun (x : α) => f x) =
        integral (measure.restrict μ s) fun (x : α) => g x :=
  set_integral_congr_ae hs (filter.eventually_of_forall h)

theorem integral_union {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {s : set α} {t : set α} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E]
    (hst : disjoint s t) (hs : is_measurable s) (ht : is_measurable t) (hfs : integrable_on f s)
    (hft : integrable_on f t) :
    (integral (measure.restrict μ (s ∪ t)) fun (x : α) => f x) =
        (integral (measure.restrict μ s) fun (x : α) => f x) +
          integral (measure.restrict μ t) fun (x : α) => f x :=
  sorry

theorem integral_empty {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] :
    (integral (measure.restrict μ ∅) fun (x : α) => f x) = 0 :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl ((integral (measure.restrict μ ∅) fun (x : α) => f x) = 0))
        measure.restrict_empty))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl ((integral 0 fun (x : α) => f x) = 0))
          (integral_zero_measure fun (x : α) => f x)))
      (Eq.refl 0))

theorem integral_univ {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] :
    (integral (measure.restrict μ set.univ) fun (x : α) => f x) = integral μ fun (x : α) => f x :=
  sorry

theorem integral_add_compl {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {s : set α} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E]
    (hs : is_measurable s) (hfi : integrable f) :
    ((integral (measure.restrict μ s) fun (x : α) => f x) +
          integral (measure.restrict μ (sᶜ)) fun (x : α) => f x) =
        integral μ fun (x : α) => f x :=
  sorry

/-- For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ x in s, f x ∂μ` defined as `∫ x, f x ∂(μ.restrict s)`. -/
theorem integral_indicator {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {f : α → E} {s : set α} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E]
    (hs : is_measurable s) :
    (integral μ fun (x : α) => set.indicator s f x) =
        integral (measure.restrict μ s) fun (x : α) => f x :=
  sorry

theorem set_integral_const {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {s : set α} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] (c : E) :
    (integral (measure.restrict μ s) fun (x : α) => c) = ennreal.to_real (coe_fn μ s) • c :=
  sorry

@[simp] theorem integral_indicator_const {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] (e : E)
    {s : set α} (s_meas : is_measurable s) :
    (integral μ fun (a : α) => set.indicator s (fun (x : α) => e) a) =
        ennreal.to_real (coe_fn μ s) • e :=
  sorry

theorem set_integral_map {α : Type u_1} {E : Type u_3} [measurable_space α] [normed_group E]
    [measurable_space E] {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E]
    {β : Type u_2} [measurable_space β] {g : α → β} {f : β → E} {s : set β} (hs : is_measurable s)
    (hf : ae_measurable f) (hg : measurable g) :
    (integral (measure.restrict (coe_fn (measure.map g) μ) s) fun (y : β) => f y) =
        integral (measure.restrict μ (g ⁻¹' s)) fun (x : α) => f (g x) :=
  sorry

theorem norm_set_integral_le_of_norm_le_const_ae {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] {C : ℝ}
    (hs : coe_fn μ s < ⊤)
    (hC : filter.eventually (fun (x : α) => norm (f x) ≤ C) (measure.ae (measure.restrict μ s))) :
    norm (integral (measure.restrict μ s) fun (x : α) => f x) ≤ C * ennreal.to_real (coe_fn μ s) :=
  sorry

theorem norm_set_integral_le_of_norm_le_const_ae' {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] {C : ℝ}
    (hs : coe_fn μ s < ⊤)
    (hC : filter.eventually (fun (x : α) => x ∈ s → norm (f x) ≤ C) (measure.ae μ))
    (hfm : ae_measurable f) :
    norm (integral (measure.restrict μ s) fun (x : α) => f x) ≤ C * ennreal.to_real (coe_fn μ s) :=
  sorry

theorem norm_set_integral_le_of_norm_le_const_ae'' {α : Type u_1} {E : Type u_3}
    [measurable_space α] [normed_group E] [measurable_space E] {f : α → E} {s : set α}
    {μ : measure α} [borel_space E] [topological_space.second_countable_topology E]
    [complete_space E] [normed_space ℝ E] {C : ℝ} (hs : coe_fn μ s < ⊤) (hsm : is_measurable s)
    (hC : filter.eventually (fun (x : α) => x ∈ s → norm (f x) ≤ C) (measure.ae μ)) :
    norm (integral (measure.restrict μ s) fun (x : α) => f x) ≤ C * ennreal.to_real (coe_fn μ s) :=
  sorry

theorem norm_set_integral_le_of_norm_le_const {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] {C : ℝ}
    (hs : coe_fn μ s < ⊤) (hC : ∀ (x : α), x ∈ s → norm (f x) ≤ C) (hfm : ae_measurable f) :
    norm (integral (measure.restrict μ s) fun (x : α) => f x) ≤ C * ennreal.to_real (coe_fn μ s) :=
  norm_set_integral_le_of_norm_le_const_ae' hs (filter.eventually_of_forall hC) hfm

theorem norm_set_integral_le_of_norm_le_const' {α : Type u_1} {E : Type u_3} [measurable_space α]
    [normed_group E] [measurable_space E] {f : α → E} {s : set α} {μ : measure α} [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] {C : ℝ}
    (hs : coe_fn μ s < ⊤) (hsm : is_measurable s) (hC : ∀ (x : α), x ∈ s → norm (f x) ≤ C) :
    norm (integral (measure.restrict μ s) fun (x : α) => f x) ≤ C * ennreal.to_real (coe_fn μ s) :=
  norm_set_integral_le_of_norm_le_const_ae'' hs hsm (filter.eventually_of_forall hC)

theorem set_integral_eq_zero_iff_of_nonneg_ae {α : Type u_1} [measurable_space α] {s : set α}
    {μ : measure α} {f : α → ℝ} (hf : filter.eventually_le (measure.ae (measure.restrict μ s)) 0 f)
    (hfi : integrable_on f s) :
    (integral (measure.restrict μ s) fun (x : α) => f x) = 0 ↔
        filter.eventually_eq (measure.ae (measure.restrict μ s)) f 0 :=
  integral_eq_zero_iff_of_nonneg_ae hf hfi

theorem set_integral_pos_iff_support_of_nonneg_ae {α : Type u_1} [measurable_space α] {s : set α}
    {μ : measure α} {f : α → ℝ} (hf : filter.eventually_le (measure.ae (measure.restrict μ s)) 0 f)
    (hfi : integrable_on f s) :
    (0 < integral (measure.restrict μ s) fun (x : α) => f x) ↔
        0 < coe_fn μ (function.support f ∩ s) :=
  sorry

end measure_theory


/-- Fundamental theorem of calculus for set integrals: if `μ` is a measure that is finite at a
filter `l` and `f` is a measurable function that has a finite limit `b` at `l ⊓ μ.ae`, then `∫ x in
s i, f x ∂μ = μ (s i) • b + o(μ (s i))` at a filter `li` provided that `s i` tends to `l.lift'
powerset` along `li`. Since `μ (s i)` is an `ennreal` number, we use `(μ (s i)).to_real` in the
actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem filter.tendsto.integral_sub_linear_is_o_ae {α : Type u_1} {E : Type u_3}
    [measurable_space α] {ι : Type u_5} [measurable_space E] [normed_group E] [normed_space ℝ E]
    [topological_space.second_countable_topology E] [complete_space E] [borel_space E]
    {μ : measure_theory.measure α} {l : filter α} [filter.is_measurably_generated l] {f : α → E}
    {b : E} (h : filter.tendsto f (l ⊓ measure_theory.measure.ae μ) (nhds b))
    (hfm : measurable_at_filter f l) (hμ : measure_theory.measure.finite_at_filter μ l)
    {s : ι → set α} {li : filter ι} (hs : filter.tendsto s li (filter.lift' l set.powerset))
    (m : optParam (ι → ℝ) fun (i : ι) => ennreal.to_real (coe_fn μ (s i)))
    (hsμ :
      autoParam (filter.eventually_eq li (fun (i : ι) => ennreal.to_real (coe_fn μ (s i))) m)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.tactic.interactive.refl")
          (Lean.Name.mkStr
            (Lean.Name.mkStr
              (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
              "interactive")
            "refl")
          [])) :
    asymptotics.is_o
        (fun (i : ι) =>
          (measure_theory.integral (measure_theory.measure.restrict μ (s i)) fun (x : α) => f x) -
            m i • b)
        m li :=
  sorry

/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure and `f` is an almost everywhere measurable function that is continuous at a point `a`
within a measurable set `t`, then `∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at a filter `li`
provided that `s i` tends to `(𝓝[t] a).lift' powerset` along `li`.  Since `μ (s i)` is an `ennreal`
number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem continuous_within_at.integral_sub_linear_is_o_ae {α : Type u_1} {E : Type u_3}
    [measurable_space α] {ι : Type u_5} [measurable_space E] [normed_group E] [topological_space α]
    [opens_measurable_space α] [normed_space ℝ E] [topological_space.second_countable_topology E]
    [complete_space E] [borel_space E] {μ : measure_theory.measure α}
    [measure_theory.locally_finite_measure μ] {a : α} {t : set α} {f : α → E}
    (ha : continuous_within_at f t a) (ht : is_measurable t)
    (hfm : measurable_at_filter f (nhds_within a t)) {s : ι → set α} {li : filter ι}
    (hs : filter.tendsto s li (filter.lift' (nhds_within a t) set.powerset))
    (m : optParam (ι → ℝ) fun (i : ι) => ennreal.to_real (coe_fn μ (s i)))
    (hsμ :
      autoParam (filter.eventually_eq li (fun (i : ι) => ennreal.to_real (coe_fn μ (s i))) m)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.tactic.interactive.refl")
          (Lean.Name.mkStr
            (Lean.Name.mkStr
              (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
              "interactive")
            "refl")
          [])) :
    asymptotics.is_o
        (fun (i : ι) =>
          (measure_theory.integral (measure_theory.measure.restrict μ (s i)) fun (x : α) => f x) -
            m i • f a)
        m li :=
  filter.tendsto.integral_sub_linear_is_o_ae (filter.tendsto.mono_left ha inf_le_left) hfm
    (measure_theory.measure.finite_at_nhds_within μ a t) hs m

/-- Fundamental theorem of calculus for set integrals, `nhds` version: if `μ` is a locally finite
measure and `f` is an almost everywhere measurable function that is continuous at a point `a`, then
`∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at `li` provided that `s` tends to `(𝓝 a).lift'
powerset` along `li.  Since `μ (s i)` is an `ennreal` number, we use `(μ (s i)).to_real` in the
actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem continuous_at.integral_sub_linear_is_o_ae {α : Type u_1} {E : Type u_3} [measurable_space α]
    {ι : Type u_5} [measurable_space E] [normed_group E] [topological_space α]
    [opens_measurable_space α] [normed_space ℝ E] [topological_space.second_countable_topology E]
    [complete_space E] [borel_space E] {μ : measure_theory.measure α}
    [measure_theory.locally_finite_measure μ] {a : α} {f : α → E} (ha : continuous_at f a)
    (hfm : measurable_at_filter f (nhds a)) {s : ι → set α} {li : filter ι}
    (hs : filter.tendsto s li (filter.lift' (nhds a) set.powerset))
    (m : optParam (ι → ℝ) fun (i : ι) => ennreal.to_real (coe_fn μ (s i)))
    (hsμ :
      autoParam (filter.eventually_eq li (fun (i : ι) => ennreal.to_real (coe_fn μ (s i))) m)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.tactic.interactive.refl")
          (Lean.Name.mkStr
            (Lean.Name.mkStr
              (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
              "interactive")
            "refl")
          [])) :
    asymptotics.is_o
        (fun (i : ι) =>
          (measure_theory.integral (measure_theory.measure.restrict μ (s i)) fun (x : α) => f x) -
            m i • f a)
        m li :=
  filter.tendsto.integral_sub_linear_is_o_ae (filter.tendsto.mono_left ha inf_le_left) hfm
    (measure_theory.measure.finite_at_nhds μ a) hs m

/-- If a function is integrable at `𝓝[s] x` for each point `x` of a compact set `s`, then it is
integrable on `s`. -/
theorem is_compact.integrable_on_of_nhds_within {α : Type u_1} {E : Type u_3} [measurable_space α]
    [measurable_space E] [normed_group E] [topological_space α] {μ : measure_theory.measure α}
    {s : set α} (hs : is_compact s) {f : α → E}
    (hf : ∀ (x : α), x ∈ s → measure_theory.integrable_at_filter f (nhds_within x s)) :
    measure_theory.integrable_on f s :=
  sorry

/-- A function which is continuous on a set `s` is almost everywhere measurable with respect to
`μ.restrict s`. -/
theorem continuous_on.ae_measurable {α : Type u_1} {E : Type u_3} [measurable_space α]
    [measurable_space E] [normed_group E] [topological_space α] [opens_measurable_space α]
    [borel_space E] {f : α → E} {s : set α} {μ : measure_theory.measure α} (hf : continuous_on f s)
    (hs : is_measurable s) : ae_measurable f :=
  sorry

theorem continuous_on.integrable_at_nhds_within {α : Type u_1} {E : Type u_3} [measurable_space α]
    [measurable_space E] [normed_group E] [topological_space α] [opens_measurable_space α]
    [borel_space E] {μ : measure_theory.measure α} [measure_theory.locally_finite_measure μ] {a : α}
    {t : set α} {f : α → E} (hft : continuous_on f t) (ht : is_measurable t) (ha : a ∈ t) :
    measure_theory.integrable_at_filter f (nhds_within a t) :=
  filter.tendsto.integrable_at_filter
    (Exists.intro t (Exists.intro self_mem_nhds_within (continuous_on.ae_measurable hft ht)))
    (measure_theory.measure.finite_at_nhds_within μ a t) (hft a ha)

/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure, `f` is continuous on a measurable set `t`, and `a ∈ t`, then `∫ x in (s i), f x ∂μ =
μ (s i) • f a + o(μ (s i))` at `li` provided that `s i` tends to `(𝓝[t] a).lift' powerset` along
`li`.  Since `μ (s i)` is an `ennreal` number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem continuous_on.integral_sub_linear_is_o_ae {α : Type u_1} {E : Type u_3} [measurable_space α]
    {ι : Type u_5} [measurable_space E] [normed_group E] [topological_space α]
    [opens_measurable_space α] [normed_space ℝ E] [topological_space.second_countable_topology E]
    [complete_space E] [borel_space E] {μ : measure_theory.measure α}
    [measure_theory.locally_finite_measure μ] {a : α} {t : set α} {f : α → E}
    (hft : continuous_on f t) (ha : a ∈ t) (ht : is_measurable t) {s : ι → set α} {li : filter ι}
    (hs : filter.tendsto s li (filter.lift' (nhds_within a t) set.powerset))
    (m : optParam (ι → ℝ) fun (i : ι) => ennreal.to_real (coe_fn μ (s i)))
    (hsμ :
      autoParam (filter.eventually_eq li (fun (i : ι) => ennreal.to_real (coe_fn μ (s i))) m)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.tactic.interactive.refl")
          (Lean.Name.mkStr
            (Lean.Name.mkStr
              (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
              "interactive")
            "refl")
          [])) :
    asymptotics.is_o
        (fun (i : ι) =>
          (measure_theory.integral (measure_theory.measure.restrict μ (s i)) fun (x : α) => f x) -
            m i • f a)
        m li :=
  continuous_within_at.integral_sub_linear_is_o_ae (hft a ha) ht
    (Exists.intro t (Exists.intro self_mem_nhds_within (continuous_on.ae_measurable hft ht))) hs m

/-- A function `f` continuous on a compact set `s` is integrable on this set with respect to any
locally finite measure. -/
theorem continuous_on.integrable_on_compact {α : Type u_1} {E : Type u_3} [measurable_space α]
    [measurable_space E] [normed_group E] [topological_space α] [opens_measurable_space α]
    [borel_space E] [t2_space α] {μ : measure_theory.measure α}
    [measure_theory.locally_finite_measure μ] {s : set α} (hs : is_compact s) {f : α → E}
    (hf : continuous_on f s) : measure_theory.integrable_on f s :=
  is_compact.integrable_on_of_nhds_within hs
    fun (x : α) (hx : x ∈ s) =>
      continuous_on.integrable_at_nhds_within hf (is_compact.is_measurable hs) hx

/-- A continuous function `f` is integrable on any compact set with respect to any locally finite
measure. -/
theorem continuous.integrable_on_compact {α : Type u_1} {E : Type u_3} [measurable_space α]
    [measurable_space E] [normed_group E] [topological_space α] [opens_measurable_space α]
    [t2_space α] [borel_space E] {μ : measure_theory.measure α}
    [measure_theory.locally_finite_measure μ] {s : set α} (hs : is_compact s) {f : α → E}
    (hf : continuous f) : measure_theory.integrable_on f s :=
  continuous_on.integrable_on_compact hs (continuous.continuous_on hf)

/-- A continuous function with compact closure of the support is integrable on the whole space. -/
theorem continuous.integrable_of_compact_closure_support {α : Type u_1} {E : Type u_3}
    [measurable_space α] [measurable_space E] [normed_group E] [topological_space α]
    [opens_measurable_space α] [t2_space α] [borel_space E] {μ : measure_theory.measure α}
    [measure_theory.locally_finite_measure μ] {f : α → E} (hf : continuous f)
    (hfc : is_compact (closure (function.support f))) : measure_theory.integrable f :=
  sorry

/-! ### Continuous linear maps composed with integration

The goal of this section is to prove that integration commutes with continuous linear maps.
The first step is to prove that, given a function `φ : α → E` which is measurable and integrable,
and a continuous linear map `L : E →L[ℝ] F`, the function `λ a, L(φ a)` is also measurable
and integrable. Note we cannot write this as `L ∘ φ` since the type of `L` is not an actual
function type.

The next step is translate this to `l1`, replacing the function `φ` by a term with type
`α →₁[μ] E` (an equivalence class of integrable functions).
The corresponding "composition" is `L.comp_l1 φ : α →₁[μ] F`. This is then upgraded to
a linear map `L.comp_l1ₗ : (α →₁[μ] E) →ₗ[ℝ] (α →₁[μ] F)` and a continuous linear map
`L.comp_l1L : (α →₁[μ] E) →L[ℝ] (α →₁[μ] F)`.

Then we can prove the commutation result using continuity of all relevant operations
and the result on simple functions.
-/

namespace continuous_linear_map


theorem norm_comp_l1_apply_le {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [opens_measurable_space E]
    [topological_space.second_countable_topology E] (φ : measure_theory.l1 α E μ)
    (L : continuous_linear_map ℝ E F) :
    filter.eventually (fun (a : α) => norm (coe_fn L (coe_fn φ a)) ≤ norm L * norm (coe_fn φ a))
        (measure_theory.measure.ae μ) :=
  filter.eventually_of_forall fun (a : α) => le_op_norm L (coe_fn φ a)

theorem integrable_comp {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
    [opens_measurable_space E] {φ : α → E} (L : continuous_linear_map ℝ E F)
    (φ_int : measure_theory.integrable φ) :
    measure_theory.integrable fun (a : α) => coe_fn L (φ a) :=
  measure_theory.integrable.mono'
    (measure_theory.integrable.const_mul (measure_theory.integrable.norm φ_int) (norm L))
    (measurable.comp_ae_measurable (continuous_linear_map.measurable L)
      (measure_theory.integrable.ae_measurable φ_int))
    (filter.eventually_of_forall fun (a : α) => le_op_norm L (φ a))

/-- Composing `φ : α →₁[μ] E` with `L : E →L[ℝ] F`. -/
def comp_l1 {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α] [measurable_space E]
    [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E] [normed_group F]
    [normed_space ℝ F] [measurable_space F] [borel_space F] [borel_space E]
    [topological_space.second_countable_topology E] [topological_space.second_countable_topology F]
    (L : continuous_linear_map ℝ E F) (φ : measure_theory.l1 α E μ) : measure_theory.l1 α F μ :=
  measure_theory.l1.of_fun (fun (a : α) => coe_fn L (coe_fn φ a)) sorry

theorem comp_l1_apply {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F] [borel_space E]
    [topological_space.second_countable_topology E] [topological_space.second_countable_topology F]
    (L : continuous_linear_map ℝ E F) (φ : measure_theory.l1 α E μ) :
    filter.eventually (fun (a : α) => coe_fn (comp_l1 L φ) a = coe_fn L (coe_fn φ a))
        (measure_theory.measure.ae μ) :=
  measure_theory.l1.to_fun_of_fun (fun (a : α) => coe_fn L (coe_fn φ a)) (comp_l1._proof_6 L φ)

theorem integrable_comp_l1 {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F] [borel_space E]
    [topological_space.second_countable_topology E] (L : continuous_linear_map ℝ E F)
    (φ : measure_theory.l1 α E μ) :
    measure_theory.integrable fun (a : α) => coe_fn L (coe_fn φ a) :=
  integrable_comp L (measure_theory.l1.integrable φ)

theorem measurable_comp_l1 {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F] [borel_space E]
    [topological_space.second_countable_topology E] (L : continuous_linear_map ℝ E F)
    (φ : measure_theory.l1 α E μ) : measurable fun (a : α) => coe_fn L (coe_fn φ a) :=
  measurable.comp (continuous_linear_map.measurable L) (measure_theory.l1.measurable φ)

theorem integral_comp_l1 {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F] [borel_space E]
    [topological_space.second_countable_topology E] [topological_space.second_countable_topology F]
    [complete_space F] (L : continuous_linear_map ℝ E F) (φ : measure_theory.l1 α E μ) :
    (measure_theory.integral μ fun (a : α) => coe_fn (comp_l1 L φ) a) =
        measure_theory.integral μ fun (a : α) => coe_fn L (coe_fn φ a) :=
  sorry

/-- Composing `φ : α →₁[μ] E` with `L : E →L[ℝ] F`, seen as a `ℝ`-linear map on `α →₁[μ] E`. -/
def comp_l1ₗ {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α] [measurable_space E]
    [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E] [normed_group F]
    [normed_space ℝ F] [measurable_space F] [borel_space F] [borel_space E]
    [topological_space.second_countable_topology E] [topological_space.second_countable_topology F]
    (L : continuous_linear_map ℝ E F) :
    linear_map ℝ (measure_theory.l1 α E μ) (measure_theory.l1 α F μ) :=
  linear_map.mk (fun (φ : measure_theory.l1 α E μ) => comp_l1 L φ) sorry sorry

theorem norm_comp_l1_le {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F] [borel_space E]
    [topological_space.second_countable_topology E] [topological_space.second_countable_topology F]
    (φ : measure_theory.l1 α E μ) (L : continuous_linear_map ℝ E F) :
    norm (comp_l1 L φ) ≤ norm L * norm φ :=
  sorry

/-- Composing `φ : α →₁[μ] E` with `L : E →L[ℝ] F`, seen as a continuous `ℝ`-linear map on
`α →₁[μ] E`. -/
def comp_l1L {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α] [measurable_space E]
    [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E] [normed_group F]
    [normed_space ℝ F] [measurable_space F] [borel_space F] [borel_space E]
    [topological_space.second_countable_topology E] [topological_space.second_countable_topology F]
    (L : continuous_linear_map ℝ E F) :
    continuous_linear_map ℝ (measure_theory.l1 α E μ) (measure_theory.l1 α F μ) :=
  linear_map.mk_continuous (comp_l1ₗ L) (norm L) sorry

theorem norm_compl1L_le {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F] [borel_space E]
    [topological_space.second_countable_topology E] [topological_space.second_countable_topology F]
    (L : continuous_linear_map ℝ E F) : norm (comp_l1L L) ≤ norm L :=
  op_norm_le_bound (comp_l1L L) (norm_nonneg L)
    fun (φ : measure_theory.l1 α E μ) => norm_comp_l1_le φ L

theorem continuous_integral_comp_l1 {α : Type u_1} {E : Type u_3} {F : Type u_4}
    [measurable_space α] [measurable_space E] [normed_group E] {μ : measure_theory.measure α}
    [normed_space ℝ E] [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
    [borel_space E] [topological_space.second_countable_topology E]
    [topological_space.second_countable_topology F] [complete_space F]
    (L : continuous_linear_map ℝ E F) :
    continuous
        fun (φ : measure_theory.l1 α E μ) =>
          measure_theory.integral μ fun (a : α) => coe_fn L (coe_fn φ a) :=
  sorry

theorem integral_comp_comm {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F] [borel_space E]
    [topological_space.second_countable_topology E] [topological_space.second_countable_topology F]
    [complete_space F] [complete_space E] (L : continuous_linear_map ℝ E F) {φ : α → E}
    (φ_int : measure_theory.integrable φ) :
    (measure_theory.integral μ fun (a : α) => coe_fn L (φ a)) =
        coe_fn L (measure_theory.integral μ fun (a : α) => φ a) :=
  sorry

theorem integral_comp_l1_comm {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F] [borel_space E]
    [topological_space.second_countable_topology E] [topological_space.second_countable_topology F]
    [complete_space F] [complete_space E] (L : continuous_linear_map ℝ E F)
    (φ : measure_theory.l1 α E μ) :
    (measure_theory.integral μ fun (a : α) => coe_fn L (coe_fn φ a)) =
        coe_fn L (measure_theory.integral μ fun (a : α) => coe_fn φ a) :=
  integral_comp_comm L (measure_theory.l1.integrable φ)

end continuous_linear_map


theorem fst_integral {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [measurable_space F]
    [borel_space F] [topological_space.second_countable_topology F] [complete_space F]
    {f : α → E × F} (hf : measure_theory.integrable f) :
    prod.fst (measure_theory.integral μ fun (x : α) => f x) =
        measure_theory.integral μ fun (x : α) => prod.fst (f x) :=
  Eq.symm (continuous_linear_map.integral_comp_comm (continuous_linear_map.fst ℝ E F) hf)

theorem snd_integral {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [measurable_space F]
    [borel_space F] [topological_space.second_countable_topology F] [complete_space F]
    {f : α → E × F} (hf : measure_theory.integrable f) :
    prod.snd (measure_theory.integral μ fun (x : α) => f x) =
        measure_theory.integral μ fun (x : α) => prod.snd (f x) :=
  Eq.symm (continuous_linear_map.integral_comp_comm (continuous_linear_map.snd ℝ E F) hf)

theorem integral_pair {α : Type u_1} {E : Type u_3} {F : Type u_4} [measurable_space α]
    [measurable_space E] [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E]
    [normed_group F] [normed_space ℝ F] [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] [measurable_space F]
    [borel_space F] [topological_space.second_countable_topology F] [complete_space F] {f : α → E}
    {g : α → F} (hf : measure_theory.integrable f) (hg : measure_theory.integrable g) :
    (measure_theory.integral μ fun (x : α) => (f x, g x)) =
        (measure_theory.integral μ fun (x : α) => f x,
        measure_theory.integral μ fun (x : α) => g x) :=
  (fun (this : measure_theory.integrable fun (x : α) => (f x, g x)) =>
      prod.ext (fst_integral this) (snd_integral this))
    (measure_theory.integrable.prod_mk hf hg)

theorem integral_smul_const {α : Type u_1} {E : Type u_3} [measurable_space α] [measurable_space E]
    [normed_group E] {μ : measure_theory.measure α} [normed_space ℝ E] [borel_space E]
    [topological_space.second_countable_topology E] [complete_space E] (f : α → ℝ) (c : E) :
    (measure_theory.integral μ fun (x : α) => f x • c) =
        (measure_theory.integral μ fun (x : α) => f x) • c :=
  sorry

end Mathlib