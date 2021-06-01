/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.prod
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Product measures

In this file we define and prove properties about finite products of measures
(and at some point, countable products of measures).

## Main definition

* `measure_theory.measure.pi`: The product of finitely many σ-finite measures.
  Given `μ : Π i : ι, measure (α i)` for `[fintype ι]` it has type `measure (Π i : ι, α i)`.

## Implementation Notes

We define `measure_theory.outer_measure.pi`, the product of finitely many outer measures, as the
maximal outer measure `n` with the property that `n (pi univ s) ≤ ∏ i, m i (s i)`,
where `pi univ s` is the product of the sets `{ s i | i : ι }`.

We then show that this induces a product of measures, called `measure_theory.measure.pi`.
For a collection of σ-finite measures `μ` and a collection of measurable sets `s` we show that
`measure.pi μ (pi univ s) = ∏ i, m i (s i)`. To do this, we follow the following steps:
* We know that there is some ordering on `ι`, given by an element of `[encodable ι]`.
* Using this, we have an equivalence `measurable_equiv.pi_measurable_equiv_tprod` between
  `Π ι, α i` and an iterated product of `α i`, called `list.tprod α l` for some list `l`.
* On this iterated product we can easily define a product measure `measure_theory.measure.tprod`
  by iterating `measure_theory.measure.prod`
* Using the previous two steps we construct `measure_theory.measure.pi'` on `Π ι, α i` for encodable
  `ι`.
* We know that `measure_theory.measure.pi'` sends products of sets to products of measures, and
  since `measure_theory.measure.pi` is the maximal such measure (or at least, it comes from an outer
  measure which is the maximal such outer measure), we get the same rule for
  `measure_theory.measure.pi`.

## Tags

finitary product measure

-/

namespace measure_theory


/-- An upper bound for the measure in a finite product space.
  It is defined to by taking the image of the set under all projections, and taking the product
  of the measures of these images.
  For measurable boxes it is equal to the correct measure. -/
@[simp] def pi_premeasure {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    (m : (i : ι) → outer_measure (α i)) (s : set ((i : ι) → α i)) : ennreal :=
  finset.prod finset.univ fun (i : ι) => coe_fn (m i) (function.eval i '' s)

theorem pi_premeasure_pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    {m : (i : ι) → outer_measure (α i)} {s : (i : ι) → set (α i)}
    (hs : set.nonempty (set.pi set.univ s)) :
    pi_premeasure m (set.pi set.univ s) =
        finset.prod finset.univ fun (i : ι) => coe_fn (m i) (s i) :=
  sorry

theorem pi_premeasure_pi' {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    {m : (i : ι) → outer_measure (α i)} [Nonempty ι] {s : (i : ι) → set (α i)} :
    pi_premeasure m (set.pi set.univ s) =
        finset.prod finset.univ fun (i : ι) => coe_fn (m i) (s i) :=
  sorry

theorem pi_premeasure_pi_mono {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    {m : (i : ι) → outer_measure (α i)} {s : set ((i : ι) → α i)} {t : set ((i : ι) → α i)}
    (h : s ⊆ t) : pi_premeasure m s ≤ pi_premeasure m t :=
  finset.prod_le_prod'
    fun (i : ι) (_x : i ∈ finset.univ) =>
      outer_measure.mono' (m i) (set.image_subset (function.eval i) h)

theorem pi_premeasure_pi_eval {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    {m : (i : ι) → outer_measure (α i)} [Nonempty ι] {s : set ((i : ι) → α i)} :
    pi_premeasure m (set.pi set.univ fun (i : ι) => function.eval i '' s) = pi_premeasure m s :=
  sorry

namespace outer_measure


/-- `outer_measure.pi m` is the finite product of the outer measures `{m i | i : ι}`.
  It is defined to be the maximal outer measure `n` with the property that
  `n (pi univ s) ≤ ∏ i, m i (s i)`, where `pi univ s` is the product of the sets
  `{ s i | i : ι }`. -/
protected def pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2} (m : (i : ι) → outer_measure (α i)) :
    outer_measure ((i : ι) → α i) :=
  bounded_by (pi_premeasure m)

theorem pi_pi_le {ι : Type u_1} [fintype ι] {α : ι → Type u_2} (m : (i : ι) → outer_measure (α i))
    (s : (i : ι) → set (α i)) :
    coe_fn (outer_measure.pi m) (set.pi set.univ s) ≤
        finset.prod finset.univ fun (i : ι) => coe_fn (m i) (s i) :=
  sorry

theorem le_pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2} {m : (i : ι) → outer_measure (α i)}
    {n : outer_measure ((i : ι) → α i)} :
    n ≤ outer_measure.pi m ↔
        ∀ (s : (i : ι) → set (α i)),
          set.nonempty (set.pi set.univ s) →
            coe_fn n (set.pi set.univ s) ≤
              finset.prod finset.univ fun (i : ι) => coe_fn (m i) (s i) :=
  sorry

end outer_measure


namespace measure


/-- A product of measures in `tprod α l`. -/
-- for some reason the equation compiler doesn't like this definition

protected def tprod {δ : Type u_3} {π : δ → Type u_4} [(x : δ) → measurable_space (π x)]
    (l : List δ) (μ : (i : δ) → measure (π i)) : measure (list.tprod π l) :=
  List.rec (dirac PUnit.unit)
    (fun (i : δ) (l : List δ) (ih : measure (list.tprod π l)) => measure.prod (μ i) ih) l

@[simp] theorem tprod_nil {δ : Type u_3} {π : δ → Type u_4} [(x : δ) → measurable_space (π x)]
    (μ : (i : δ) → measure (π i)) : measure.tprod [] μ = dirac PUnit.unit :=
  rfl

@[simp] theorem tprod_cons {δ : Type u_3} {π : δ → Type u_4} [(x : δ) → measurable_space (π x)]
    (i : δ) (l : List δ) (μ : (i : δ) → measure (π i)) :
    measure.tprod (i :: l) μ = measure.prod (μ i) (measure.tprod l μ) :=
  rfl

protected instance sigma_finite_tprod {δ : Type u_3} {π : δ → Type u_4}
    [(x : δ) → measurable_space (π x)] (l : List δ) (μ : (i : δ) → measure (π i))
    [∀ (i : δ), sigma_finite (μ i)] : sigma_finite (measure.tprod l μ) :=
  List.rec
    (eq.mpr (id (Eq._oldrec (Eq.refl (sigma_finite (measure.tprod [] μ))) (tprod_nil μ)))
      (finite_measure.to_sigma_finite (dirac PUnit.unit)))
    (fun (i : δ) (l : List δ) (ih : sigma_finite (measure.tprod l μ)) =>
      eq.mpr
        (id (Eq._oldrec (Eq.refl (sigma_finite (measure.tprod (i :: l) μ))) (tprod_cons i l μ)))
        prod.sigma_finite)
    l

theorem tprod_tprod {δ : Type u_3} {π : δ → Type u_4} [(x : δ) → measurable_space (π x)]
    (l : List δ) (μ : (i : δ) → measure (π i)) [∀ (i : δ), sigma_finite (μ i)]
    {s : (i : δ) → set (π i)} (hs : ∀ (i : δ), is_measurable (s i)) :
    coe_fn (measure.tprod l μ) (set.tprod l s) =
        list.prod (list.map (fun (i : δ) => coe_fn (μ i) (s i)) l) :=
  sorry

theorem tprod_tprod_le {δ : Type u_3} {π : δ → Type u_4} [(x : δ) → measurable_space (π x)]
    (l : List δ) (μ : (i : δ) → measure (π i)) [∀ (i : δ), sigma_finite (μ i)]
    (s : (i : δ) → set (π i)) :
    coe_fn (measure.tprod l μ) (set.tprod l s) ≤
        list.prod (list.map (fun (i : δ) => coe_fn (μ i) (s i)) l) :=
  sorry

/-- The product measure on an encodable finite type, defined by mapping `measure.tprod` along the
  equivalence `measurable_equiv.pi_measurable_equiv_tprod`.
  The definition `measure_theory.measure.pi` should be used instead of this one. -/
def pi' {ι : Type u_1} [fintype ι] {α : ι → Type u_2} [(i : ι) → measurable_space (α i)]
    (μ : (i : ι) → measure (α i)) [encodable ι] : measure ((i : ι) → α i) :=
  coe_fn (map (list.tprod.elim' encodable.mem_sorted_univ))
    (measure.tprod (encodable.sorted_univ ι) μ)

theorem pi'_pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2} [(i : ι) → measurable_space (α i)]
    (μ : (i : ι) → measure (α i)) [encodable ι] [∀ (i : ι), sigma_finite (μ i)]
    {s : (i : ι) → set (α i)} (hs : ∀ (i : ι), is_measurable (s i)) :
    coe_fn (pi' μ) (set.pi set.univ s) =
        finset.prod finset.univ fun (i : ι) => coe_fn (μ i) (s i) :=
  sorry

theorem pi'_pi_le {ι : Type u_1} [fintype ι] {α : ι → Type u_2} [(i : ι) → measurable_space (α i)]
    (μ : (i : ι) → measure (α i)) [encodable ι] [∀ (i : ι), sigma_finite (μ i)]
    {s : (i : ι) → set (α i)} :
    coe_fn (pi' μ) (set.pi set.univ s) ≤
        finset.prod finset.univ fun (i : ι) => coe_fn (μ i) (s i) :=
  sorry

theorem pi_caratheodory {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] (μ : (i : ι) → measure (α i)) :
    measurable_space.pi ≤
        outer_measure.caratheodory (outer_measure.pi fun (i : ι) => to_outer_measure (μ i)) :=
  sorry

/-- `measure.pi μ` is the finite product of the measures `{μ i | i : ι}`.
  It is defined to be measure corresponding to `measure_theory.outer_measure.pi`. -/
protected def pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2} [(i : ι) → measurable_space (α i)]
    (μ : (i : ι) → measure (α i)) : measure ((i : ι) → α i) :=
  outer_measure.to_measure (outer_measure.pi fun (i : ι) => to_outer_measure (μ i)) sorry

theorem pi_pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2} [(i : ι) → measurable_space (α i)]
    (μ : (i : ι) → measure (α i)) [∀ (i : ι), sigma_finite (μ i)] (s : (i : ι) → set (α i))
    (hs : ∀ (i : ι), is_measurable (s i)) :
    coe_fn (measure.pi μ) (set.pi set.univ s) =
        finset.prod finset.univ fun (i : ι) => coe_fn (μ i) (s i) :=
  sorry

theorem pi_eval_preimage_null {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] (μ : (i : ι) → measure (α i)) [∀ (i : ι), sigma_finite (μ i)]
    {i : ι} {s : set (α i)} (hs : coe_fn (μ i) s = 0) :
    coe_fn (measure.pi μ) (function.eval i ⁻¹' s) = 0 :=
  sorry

theorem pi_hyperplane {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] (μ : (i : ι) → measure (α i)) [∀ (i : ι), sigma_finite (μ i)]
    (i : ι) [has_no_atoms (μ i)] (x : α i) :
    coe_fn (measure.pi μ) (set_of fun (f : (i : ι) → α i) => f i = x) = 0 :=
  (fun (this : coe_fn (measure.pi μ) (function.eval i ⁻¹' singleton x) = 0) => this)
    (pi_eval_preimage_null μ (measure_singleton x))

theorem ae_eval_ne {ι : Type u_1} [fintype ι] {α : ι → Type u_2} [(i : ι) → measurable_space (α i)]
    (μ : (i : ι) → measure (α i)) [∀ (i : ι), sigma_finite (μ i)] (i : ι) [has_no_atoms (μ i)]
    (x : α i) : filter.eventually (fun (y : (i : ι) → α i) => y i ≠ x) (ae (measure.pi μ)) :=
  iff.mpr compl_mem_ae_iff (pi_hyperplane μ i x)

theorem tendsto_eval_ae_ae {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    {i : ι} : filter.tendsto (function.eval i) (ae (measure.pi μ)) (ae (μ i)) :=
  fun (s : set (α i)) (hs : s ∈ ae (μ i)) => pi_eval_preimage_null μ hs

-- TODO: should we introduce `filter.pi` and prove some basic facts about it?

-- The same combinator appears here and in `nhds_pi`

theorem ae_pi_le_infi_comap {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)}
    [∀ (i : ι), sigma_finite (μ i)] :
    ae (measure.pi μ) ≤ infi fun (i : ι) => filter.comap (function.eval i) (ae (μ i)) :=
  le_infi fun (i : ι) => filter.tendsto.le_comap tendsto_eval_ae_ae

theorem ae_eq_pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2} [(i : ι) → measurable_space (α i)]
    {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)] {β : ι → Type u_3}
    {f : (i : ι) → α i → β i} {f' : (i : ι) → α i → β i}
    (h : ∀ (i : ι), filter.eventually_eq (ae (μ i)) (f i) (f' i)) :
    filter.eventually_eq (ae (measure.pi μ)) (fun (x : (i : ι) → α i) (i : ι) => f i (x i))
        fun (x : (i : ι) → α i) (i : ι) => f' i (x i) :=
  filter.eventually.mono
    (iff.mpr filter.eventually_all
      fun (i : ι) => filter.tendsto.eventually tendsto_eval_ae_ae (h i))
    fun (x : (x : ι) → α x) (hx : ∀ (i : ι), f i (function.eval i x) = f' i (function.eval i x)) =>
      funext hx

theorem ae_le_pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2} [(i : ι) → measurable_space (α i)]
    {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)] {β : ι → Type u_3}
    [(i : ι) → preorder (β i)] {f : (i : ι) → α i → β i} {f' : (i : ι) → α i → β i}
    (h : ∀ (i : ι), filter.eventually_le (ae (μ i)) (f i) (f' i)) :
    filter.eventually_le (ae (measure.pi μ)) (fun (x : (i : ι) → α i) (i : ι) => f i (x i))
        fun (x : (i : ι) → α i) (i : ι) => f' i (x i) :=
  filter.eventually.mono
    (iff.mpr filter.eventually_all
      fun (i : ι) => filter.tendsto.eventually tendsto_eval_ae_ae (h i))
    fun (x : (x : ι) → α x) (hx : ∀ (i : ι), f i (function.eval i x) ≤ f' i (function.eval i x)) =>
      hx

theorem ae_le_set_pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    {I : set ι} {s : (i : ι) → set (α i)} {t : (i : ι) → set (α i)}
    (h : ∀ (i : ι), i ∈ I → filter.eventually_le (ae (μ i)) (s i) (t i)) :
    filter.eventually_le (ae (measure.pi μ)) (set.pi I s) (set.pi I t) :=
  sorry

theorem ae_eq_set_pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    {I : set ι} {s : (i : ι) → set (α i)} {t : (i : ι) → set (α i)}
    (h : ∀ (i : ι), i ∈ I → filter.eventually_eq (ae (μ i)) (s i) (t i)) :
    filter.eventually_eq (ae (measure.pi μ)) (set.pi I s) (set.pi I t) :=
  filter.eventually_le.antisymm
    (ae_le_set_pi fun (i : ι) (hi : i ∈ I) => filter.eventually_eq.le (h i hi))
    (ae_le_set_pi
      fun (i : ι) (hi : i ∈ I) => filter.eventually_eq.le (filter.eventually_eq.symm (h i hi)))

theorem pi_Iio_ae_eq_pi_Iic {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    [(i : ι) → partial_order (α i)] [∀ (i : ι), has_no_atoms (μ i)] {s : set ι}
    {f : (i : ι) → α i} :
    filter.eventually_eq (ae (measure.pi μ)) (set.pi s fun (i : ι) => set.Iio (f i))
        (set.pi s fun (i : ι) => set.Iic (f i)) :=
  ae_eq_set_pi fun (i : ι) (hi : i ∈ s) => Iio_ae_eq_Iic

theorem pi_Ioi_ae_eq_pi_Ici {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    [(i : ι) → partial_order (α i)] [∀ (i : ι), has_no_atoms (μ i)] {s : set ι}
    {f : (i : ι) → α i} :
    filter.eventually_eq (ae (measure.pi μ)) (set.pi s fun (i : ι) => set.Ioi (f i))
        (set.pi s fun (i : ι) => set.Ici (f i)) :=
  ae_eq_set_pi fun (i : ι) (hi : i ∈ s) => Ioi_ae_eq_Ici

theorem univ_pi_Iio_ae_eq_Iic {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    [(i : ι) → partial_order (α i)] [∀ (i : ι), has_no_atoms (μ i)] {f : (i : ι) → α i} :
    filter.eventually_eq (ae (measure.pi μ)) (set.pi set.univ fun (i : ι) => set.Iio (f i))
        (set.Iic f) :=
  sorry

theorem univ_pi_Ioi_ae_eq_Ici {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    [(i : ι) → partial_order (α i)] [∀ (i : ι), has_no_atoms (μ i)] {f : (i : ι) → α i} :
    filter.eventually_eq (ae (measure.pi μ)) (set.pi set.univ fun (i : ι) => set.Ioi (f i))
        (set.Ici f) :=
  sorry

theorem pi_Ioo_ae_eq_pi_Icc {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    [(i : ι) → partial_order (α i)] [∀ (i : ι), has_no_atoms (μ i)] {s : set ι} {f : (i : ι) → α i}
    {g : (i : ι) → α i} :
    filter.eventually_eq (ae (measure.pi μ)) (set.pi s fun (i : ι) => set.Ioo (f i) (g i))
        (set.pi s fun (i : ι) => set.Icc (f i) (g i)) :=
  ae_eq_set_pi fun (i : ι) (hi : i ∈ s) => Ioo_ae_eq_Icc

theorem univ_pi_Ioo_ae_eq_Icc {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    [(i : ι) → partial_order (α i)] [∀ (i : ι), has_no_atoms (μ i)] {f : (i : ι) → α i}
    {g : (i : ι) → α i} :
    filter.eventually_eq (ae (measure.pi μ)) (set.pi set.univ fun (i : ι) => set.Ioo (f i) (g i))
        (set.Icc f g) :=
  sorry

theorem pi_Ioc_ae_eq_pi_Icc {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    [(i : ι) → partial_order (α i)] [∀ (i : ι), has_no_atoms (μ i)] {s : set ι} {f : (i : ι) → α i}
    {g : (i : ι) → α i} :
    filter.eventually_eq (ae (measure.pi μ)) (set.pi s fun (i : ι) => set.Ioc (f i) (g i))
        (set.pi s fun (i : ι) => set.Icc (f i) (g i)) :=
  ae_eq_set_pi fun (i : ι) (hi : i ∈ s) => Ioc_ae_eq_Icc

theorem univ_pi_Ioc_ae_eq_Icc {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    [(i : ι) → partial_order (α i)] [∀ (i : ι), has_no_atoms (μ i)] {f : (i : ι) → α i}
    {g : (i : ι) → α i} :
    filter.eventually_eq (ae (measure.pi μ)) (set.pi set.univ fun (i : ι) => set.Ioc (f i) (g i))
        (set.Icc f g) :=
  sorry

theorem pi_Ico_ae_eq_pi_Icc {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    [(i : ι) → partial_order (α i)] [∀ (i : ι), has_no_atoms (μ i)] {s : set ι} {f : (i : ι) → α i}
    {g : (i : ι) → α i} :
    filter.eventually_eq (ae (measure.pi μ)) (set.pi s fun (i : ι) => set.Ico (f i) (g i))
        (set.pi s fun (i : ι) => set.Icc (f i) (g i)) :=
  ae_eq_set_pi fun (i : ι) (hi : i ∈ s) => Ico_ae_eq_Icc

theorem univ_pi_Ico_ae_eq_Icc {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    [(i : ι) → partial_order (α i)] [∀ (i : ι), has_no_atoms (μ i)] {f : (i : ι) → α i}
    {g : (i : ι) → α i} :
    filter.eventually_eq (ae (measure.pi μ)) (set.pi set.univ fun (i : ι) => set.Ico (f i) (g i))
        (set.Icc f g) :=
  sorry

/-- If one of the measures `μ i` has no atoms, them `measure.pi µ`
has no atoms. The instance below assumes that all `μ i` have no atoms. -/
theorem pi_has_no_atoms {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    (i : ι) [has_no_atoms (μ i)] : has_no_atoms (measure.pi μ) :=
  has_no_atoms.mk
    fun (x : (i : ι) → α i) =>
      flip measure_mono_null (pi_hyperplane μ i (x i)) (iff.mpr set.singleton_subset_iff rfl)

protected instance pi.measure_theory.has_no_atoms {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)} [∀ (i : ι), sigma_finite (μ i)]
    [h : Nonempty ι] [∀ (i : ι), has_no_atoms (μ i)] : has_no_atoms (measure.pi μ) :=
  nonempty.elim h fun (i : ι) => pi_has_no_atoms i

protected instance pi.measure_theory.locally_finite_measure {ι : Type u_1} [fintype ι]
    {α : ι → Type u_2} [(i : ι) → measurable_space (α i)] {μ : (i : ι) → measure (α i)}
    [∀ (i : ι), sigma_finite (μ i)] [(i : ι) → topological_space (α i)]
    [∀ (i : ι), opens_measurable_space (α i)] [∀ (i : ι), locally_finite_measure (μ i)] :
    locally_finite_measure (measure.pi μ) :=
  sorry

end measure


protected instance measure_space.pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2}
    [(i : ι) → measure_space (α i)] : measure_space ((i : ι) → α i) :=
  measure_space.mk (measure.pi fun (i : ι) => volume)

theorem volume_pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2} [(i : ι) → measure_space (α i)] :
    volume = measure.pi fun (i : ι) => volume :=
  rfl

theorem volume_pi_pi {ι : Type u_1} [fintype ι] {α : ι → Type u_2} [(i : ι) → measure_space (α i)]
    [ι → sigma_finite volume] (s : (i : ι) → set (α i)) (hs : ∀ (i : ι), is_measurable (s i)) :
    coe_fn volume (set.pi set.univ s) =
        finset.prod finset.univ fun (i : ι) => coe_fn volume (s i) :=
  measure.pi_pi (fun (i : ι) => volume) s hs

end Mathlib