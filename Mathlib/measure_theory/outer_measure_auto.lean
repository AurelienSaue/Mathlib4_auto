/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.specific_limits
import Mathlib.measure_theory.measurable_space
import Mathlib.topology.algebra.infinite_sum
import Mathlib.PostPort

universes u_1 l u_2 u_3 u 

namespace Mathlib

/-!
# Outer Measures

An outer measure is a function `μ : set α → ennreal`, from the powerset of a type to the extended
nonnegative real numbers that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is monotone;
3. `μ` is countably subadditive. This means that the outer measure of a countable union is at most
   the sum of the outer measure on the individual sets.

Note that we do not need `α` to be measurable to define an outer measure.

The outer measures on a type `α` form a complete lattice.

Given an arbitrary function `m : set α → ennreal` that sends `∅` to `0` we can define an outer
measure on `α` that on `s` is defined to be the infimum of `∑ᵢ, m (sᵢ)` for all collections of sets
`sᵢ` that cover `s`. This is the unique maximal outer measure that is at most the given function.
We also define this for functions `m` defined on a subset of `set α`, by treating the function as
having value `∞` outside its domain.

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `outer_measure.bounded_by` is the greatest outer measure that is at most the given function.
  If you know that the given functions sends `∅` to `0`, then `outer_measure.of_function` is a
  special case.
* `caratheodory` is the Carathéodory-measurable space of an outer measure.
* `Inf_eq_of_function_Inf_gen` is a characterization of the infimum of outer measures.
* `induced_outer_measure` is the measure induced by a function on a subset of `set α`

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

outer measure, Carathéodory-measurable, Carathéodory's criterion
-/

namespace measure_theory


/-- An outer measure is a countably subadditive monotone function that sends `∅` to `0`. -/
structure outer_measure (α : Type u_1) where
  measure_of : set α → ennreal
  empty : measure_of ∅ = 0
  mono : ∀ {s₁ s₂ : set α}, s₁ ⊆ s₂ → measure_of s₁ ≤ measure_of s₂
  Union_nat :
    ∀ (s : ℕ → set α),
      measure_of (set.Union fun (i : ℕ) => s i) ≤ tsum fun (i : ℕ) => measure_of (s i)

namespace outer_measure


protected instance has_coe_to_fun {α : Type u_1} : has_coe_to_fun (outer_measure α) :=
  has_coe_to_fun.mk (fun (m : outer_measure α) => set α → ennreal)
    fun (m : outer_measure α) => measure_of m

@[simp] theorem measure_of_eq_coe {α : Type u_1} (m : outer_measure α) : measure_of m = ⇑m := rfl

@[simp] theorem empty' {α : Type u_1} (m : outer_measure α) : coe_fn m ∅ = 0 := empty m

theorem mono' {α : Type u_1} (m : outer_measure α) {s₁ : set α} {s₂ : set α} (h : s₁ ⊆ s₂) :
    coe_fn m s₁ ≤ coe_fn m s₂ :=
  mono m h

protected theorem Union {α : Type u_1} (m : outer_measure α) {β : Type u_2} [encodable β]
    (s : β → set α) :
    coe_fn m (set.Union fun (i : β) => s i) ≤ tsum fun (i : β) => coe_fn m (s i) :=
  rel_supr_tsum (⇑m) (empty m) LessEq (Union_nat m) s

theorem Union_null {α : Type u_1} (m : outer_measure α) {β : Type u_2} [encodable β] {s : β → set α}
    (h : ∀ (i : β), coe_fn m (s i) = 0) : coe_fn m (set.Union fun (i : β) => s i) = 0 :=
  sorry

protected theorem Union_finset {α : Type u_1} {β : Type u_2} (m : outer_measure α) (s : β → set α)
    (t : finset β) :
    coe_fn m (set.Union fun (i : β) => set.Union fun (H : i ∈ t) => s i) ≤
        finset.sum t fun (i : β) => coe_fn m (s i) :=
  rel_supr_sum (⇑m) (empty m) LessEq (Union_nat m) s t

protected theorem union {α : Type u_1} (m : outer_measure α) (s₁ : set α) (s₂ : set α) :
    coe_fn m (s₁ ∪ s₂) ≤ coe_fn m s₁ + coe_fn m s₂ :=
  rel_sup_add (⇑m) (empty m) LessEq (Union_nat m) s₁ s₂

theorem le_inter_add_diff {α : Type u_1} {m : outer_measure α} {t : set α} (s : set α) :
    coe_fn m t ≤ coe_fn m (t ∩ s) + coe_fn m (t \ s) :=
  sorry

theorem diff_null {α : Type u_1} (m : outer_measure α) (s : set α) {t : set α}
    (ht : coe_fn m t = 0) : coe_fn m (s \ t) = coe_fn m s :=
  sorry

theorem union_null {α : Type u_1} (m : outer_measure α) {s₁ : set α} {s₂ : set α}
    (h₁ : coe_fn m s₁ = 0) (h₂ : coe_fn m s₂ = 0) : coe_fn m (s₁ ∪ s₂) = 0 :=
  sorry

theorem injective_coe_fn {α : Type u_1} :
    function.injective fun (μ : outer_measure α) (s : set α) => coe_fn μ s :=
  sorry

theorem ext {α : Type u_1} {μ₁ : outer_measure α} {μ₂ : outer_measure α}
    (h : ∀ (s : set α), coe_fn μ₁ s = coe_fn μ₂ s) : μ₁ = μ₂ :=
  injective_coe_fn (funext h)

protected instance has_zero {α : Type u_1} : HasZero (outer_measure α) :=
  { zero := mk (fun (_x : set α) => 0) sorry sorry sorry }

@[simp] theorem coe_zero {α : Type u_1} : ⇑0 = 0 := rfl

protected instance inhabited {α : Type u_1} : Inhabited (outer_measure α) := { default := 0 }

protected instance has_add {α : Type u_1} : Add (outer_measure α) :=
  { add :=
      fun (m₁ m₂ : outer_measure α) =>
        mk (fun (s : set α) => coe_fn m₁ s + coe_fn m₂ s) sorry sorry sorry }

@[simp] theorem coe_add {α : Type u_1} (m₁ : outer_measure α) (m₂ : outer_measure α) :
    ⇑(m₁ + m₂) = ⇑m₁ + ⇑m₂ :=
  rfl

theorem add_apply {α : Type u_1} (m₁ : outer_measure α) (m₂ : outer_measure α) (s : set α) :
    coe_fn (m₁ + m₂) s = coe_fn m₁ s + coe_fn m₂ s :=
  rfl

protected instance add_comm_monoid {α : Type u_1} : add_comm_monoid (outer_measure α) :=
  add_comm_monoid.mk Add.add sorry 0 sorry sorry sorry

protected instance has_scalar {α : Type u_1} : has_scalar ennreal (outer_measure α) :=
  has_scalar.mk
    fun (c : ennreal) (m : outer_measure α) =>
      mk (fun (s : set α) => c * coe_fn m s) sorry sorry sorry

@[simp] theorem coe_smul {α : Type u_1} (c : ennreal) (m : outer_measure α) : ⇑(c • m) = c • ⇑m :=
  rfl

theorem smul_apply {α : Type u_1} (c : ennreal) (m : outer_measure α) (s : set α) :
    coe_fn (c • m) s = c * coe_fn m s :=
  rfl

protected instance semimodule {α : Type u_1} : semimodule ennreal (outer_measure α) :=
  semimodule.mk sorry sorry

protected instance has_bot {α : Type u_1} : has_bot (outer_measure α) := has_bot.mk 0

protected instance outer_measure.order_bot {α : Type u_1} : order_bot (outer_measure α) :=
  order_bot.mk 0 (fun (m₁ m₂ : outer_measure α) => ∀ (s : set α), coe_fn m₁ s ≤ coe_fn m₂ s)
    (partial_order.lt._default
      fun (m₁ m₂ : outer_measure α) => ∀ (s : set α), coe_fn m₁ s ≤ coe_fn m₂ s)
    sorry sorry sorry sorry

protected instance has_Sup {α : Type u_1} : has_Sup (outer_measure α) :=
  has_Sup.mk
    fun (ms : set (outer_measure α)) =>
      mk (fun (s : set α) => supr fun (m : outer_measure α) => supr fun (H : m ∈ ms) => coe_fn m s)
        sorry sorry sorry

protected instance complete_lattice {α : Type u_1} : complete_lattice (outer_measure α) :=
  complete_lattice.mk complete_lattice.sup order_bot.le order_bot.lt sorry sorry sorry sorry sorry
    sorry complete_lattice.inf sorry sorry sorry complete_lattice.top sorry order_bot.bot sorry
    complete_lattice.Sup complete_lattice.Inf sorry sorry sorry sorry

@[simp] theorem Sup_apply {α : Type u_1} (ms : set (outer_measure α)) (s : set α) :
    coe_fn (Sup ms) s = supr fun (m : outer_measure α) => supr fun (H : m ∈ ms) => coe_fn m s :=
  rfl

@[simp] theorem supr_apply {α : Type u_1} {ι : Sort u_2} (f : ι → outer_measure α) (s : set α) :
    coe_fn (supr fun (i : ι) => f i) s = supr fun (i : ι) => coe_fn (f i) s :=
  sorry

theorem coe_supr {α : Type u_1} {ι : Sort u_2} (f : ι → outer_measure α) :
    ⇑(supr fun (i : ι) => f i) = supr fun (i : ι) => ⇑(f i) :=
  sorry

@[simp] theorem sup_apply {α : Type u_1} (m₁ : outer_measure α) (m₂ : outer_measure α) (s : set α) :
    coe_fn (m₁ ⊔ m₂) s = coe_fn m₁ s ⊔ coe_fn m₂ s :=
  sorry

/-- The pushforward of `m` along `f`. The outer measure on `s` is defined to be `m (f ⁻¹' s)`. -/
def map {α : Type u_1} {β : Type u_2} (f : α → β) :
    linear_map ennreal (outer_measure α) (outer_measure β) :=
  linear_map.mk
    (fun (m : outer_measure α) => mk (fun (s : set β) => coe_fn m (f ⁻¹' s)) (empty m) sorry sorry)
    sorry sorry

@[simp] theorem map_apply {α : Type u_1} {β : Type u_2} (f : α → β) (m : outer_measure α)
    (s : set β) : coe_fn (coe_fn (map f) m) s = coe_fn m (f ⁻¹' s) :=
  rfl

@[simp] theorem map_id {α : Type u_1} (m : outer_measure α) : coe_fn (map id) m = m :=
  ext fun (s : set α) => rfl

@[simp] theorem map_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β) (g : β → γ)
    (m : outer_measure α) : coe_fn (map g) (coe_fn (map f) m) = coe_fn (map (g ∘ f)) m :=
  ext fun (s : set γ) => rfl

protected instance functor : Functor outer_measure :=
  { map := fun (α β : Type u_1) (f : α → β) => ⇑(map f),
    mapConst := fun (α β : Type u_1) => (fun (f : β → α) => ⇑(map f)) ∘ function.const β }

protected instance is_lawful_functor : is_lawful_functor outer_measure :=
  is_lawful_functor.mk (fun (α : Type u_1) => map_id)
    fun (α β γ : Type u_1) (f : α → β) (g : β → γ) (m : outer_measure α) => Eq.symm (map_map f g m)

/-- The dirac outer measure. -/
def dirac {α : Type u_1} (a : α) : outer_measure α :=
  mk (fun (s : set α) => set.indicator s (fun (_x : α) => 1) a) sorry sorry sorry

@[simp] theorem dirac_apply {α : Type u_1} (a : α) (s : set α) :
    coe_fn (dirac a) s = set.indicator s (fun (_x : α) => 1) a :=
  rfl

/-- The sum of an (arbitrary) collection of outer measures. -/
def sum {α : Type u_1} {ι : Type u_2} (f : ι → outer_measure α) : outer_measure α :=
  mk (fun (s : set α) => tsum fun (i : ι) => coe_fn (f i) s) sorry sorry sorry

@[simp] theorem sum_apply {α : Type u_1} {ι : Type u_2} (f : ι → outer_measure α) (s : set α) :
    coe_fn (sum f) s = tsum fun (i : ι) => coe_fn (f i) s :=
  rfl

theorem smul_dirac_apply {α : Type u_1} (a : ennreal) (b : α) (s : set α) :
    coe_fn (a • dirac b) s = set.indicator s (fun (_x : α) => a) b :=
  sorry

/-- Pullback of an `outer_measure`: `comap f μ s = μ (f '' s)`. -/
def comap {α : Type u_1} {β : Type u_2} (f : α → β) :
    linear_map ennreal (outer_measure β) (outer_measure α) :=
  linear_map.mk
    (fun (m : outer_measure β) => mk (fun (s : set α) => coe_fn m (f '' s)) sorry sorry sorry) sorry
    sorry

@[simp] theorem comap_apply {α : Type u_1} {β : Type u_2} (f : α → β) (m : outer_measure β)
    (s : set α) : coe_fn (coe_fn (comap f) m) s = coe_fn m (f '' s) :=
  rfl

/-- Restrict an `outer_measure` to a set. -/
def restrict {α : Type u_1} (s : set α) : linear_map ennreal (outer_measure α) (outer_measure α) :=
  linear_map.comp (map coe) (comap coe)

@[simp] theorem restrict_apply {α : Type u_1} (s : set α) (t : set α) (m : outer_measure α) :
    coe_fn (coe_fn (restrict s) m) t = coe_fn m (t ∩ s) :=
  sorry

theorem top_apply {α : Type u_1} {s : set α} (h : set.nonempty s) : coe_fn ⊤ s = ⊤ := sorry

/-- Given any function `m` assigning measures to sets satisying `m ∅ = 0`, there is
  a unique maximal outer measure `μ` satisfying `μ s ≤ m s` for all `s : set α`. -/
protected def of_function {α : Type u_1} (m : set α → ennreal) (m_empty : m ∅ = 0) :
    outer_measure α :=
  let μ : set α → ennreal :=
    fun (s : set α) =>
      infi
        fun {f : ℕ → set α} =>
          infi fun (h : s ⊆ set.Union fun (i : ℕ) => f i) => tsum fun (i : ℕ) => m (f i);
  mk μ sorry sorry sorry

theorem of_function_apply {α : Type u_1} (m : set α → ennreal) (m_empty : m ∅ = 0) (s : set α) :
    coe_fn (outer_measure.of_function m m_empty) s =
        infi fun (t : ℕ → set α) => infi fun (h : s ⊆ set.Union t) => tsum fun (n : ℕ) => m (t n) :=
  rfl

theorem of_function_le {α : Type u_1} {m : set α → ennreal} {m_empty : m ∅ = 0} (s : set α) :
    coe_fn (outer_measure.of_function m m_empty) s ≤ m s :=
  sorry

theorem of_function_eq {α : Type u_1} {m : set α → ennreal} {m_empty : m ∅ = 0} (s : set α)
    (m_mono : ∀ {t : set α}, s ⊆ t → m s ≤ m t)
    (m_subadd : ∀ (s : ℕ → set α), m (set.Union fun (i : ℕ) => s i) ≤ tsum fun (i : ℕ) => m (s i)) :
    coe_fn (outer_measure.of_function m m_empty) s = m s :=
  le_antisymm (of_function_le s)
    (le_infi
      fun (f : ℕ → set α) =>
        le_infi fun (hf : s ⊆ set.Union fun (i : ℕ) => f i) => le_trans (m_mono hf) (m_subadd f))

theorem le_of_function {α : Type u_1} {m : set α → ennreal} {m_empty : m ∅ = 0}
    {μ : outer_measure α} :
    μ ≤ outer_measure.of_function m m_empty ↔ ∀ (s : set α), coe_fn μ s ≤ m s :=
  sorry

/-- Given any function `m` assigning measures to sets, there is a unique maximal outer measure `μ`
  satisfying `μ s ≤ m s` for all `s : set α`. This is the same as `outer_measure.of_function`,
  except that it doesn't require `m ∅ = 0`. -/
def bounded_by {α : Type u_1} (m : set α → ennreal) : outer_measure α :=
  outer_measure.of_function (fun (s : set α) => supr fun (h : set.nonempty s) => m s) sorry

theorem bounded_by_le {α : Type u_1} {m : set α → ennreal} (s : set α) :
    coe_fn (bounded_by m) s ≤ m s :=
  has_le.le.trans (of_function_le s) supr_const_le

theorem bounded_by_eq_of_function {α : Type u_1} {m : set α → ennreal} (m_empty : m ∅ = 0)
    (s : set α) : coe_fn (bounded_by m) s = coe_fn (outer_measure.of_function m m_empty) s :=
  sorry

theorem bounded_by_apply {α : Type u_1} {m : set α → ennreal} (s : set α) :
    coe_fn (bounded_by m) s =
        infi
          fun (t : ℕ → set α) =>
            infi
              fun (h : s ⊆ set.Union t) =>
                tsum fun (n : ℕ) => supr fun (h : set.nonempty (t n)) => m (t n) :=
  sorry

theorem bounded_by_eq {α : Type u_1} {m : set α → ennreal} (s : set α) (m_empty : m ∅ = 0)
    (m_mono : ∀ {t : set α}, s ⊆ t → m s ≤ m t)
    (m_subadd : ∀ (s : ℕ → set α), m (set.Union fun (i : ℕ) => s i) ≤ tsum fun (i : ℕ) => m (s i)) :
    coe_fn (bounded_by m) s = m s :=
  sorry

theorem le_bounded_by {α : Type u_1} {m : set α → ennreal} {μ : outer_measure α} :
    μ ≤ bounded_by m ↔ ∀ (s : set α), coe_fn μ s ≤ m s :=
  sorry

theorem le_bounded_by' {α : Type u_1} {m : set α → ennreal} {μ : outer_measure α} :
    μ ≤ bounded_by m ↔ ∀ (s : set α), set.nonempty s → coe_fn μ s ≤ m s :=
  sorry

/-- A set `s` is Carathéodory-measurable for an outer measure `m` if for all sets `t` we have
  `m t = m (t ∩ s) + m (t \ s)`. -/
def is_caratheodory {α : Type u} (m : outer_measure α) (s : set α) :=
  ∀ (t : set α), coe_fn m t = coe_fn m (t ∩ s) + coe_fn m (t \ s)

theorem is_caratheodory_iff_le' {α : Type u} (m : outer_measure α) {s : set α} :
    is_caratheodory m s ↔ ∀ (t : set α), coe_fn m (t ∩ s) + coe_fn m (t \ s) ≤ coe_fn m t :=
  forall_congr fun (t : set α) => iff.trans le_antisymm_iff (and_iff_right (le_inter_add_diff s))

@[simp] theorem is_caratheodory_empty {α : Type u} (m : outer_measure α) : is_caratheodory m ∅ :=
  sorry

theorem is_caratheodory_compl {α : Type u} (m : outer_measure α) {s₁ : set α} :
    is_caratheodory m s₁ → is_caratheodory m (s₁ᶜ) :=
  sorry

@[simp] theorem is_caratheodory_compl_iff {α : Type u} (m : outer_measure α) {s : set α} :
    is_caratheodory m (sᶜ) ↔ is_caratheodory m s :=
  sorry

theorem is_caratheodory_union {α : Type u} (m : outer_measure α) {s₁ : set α} {s₂ : set α}
    (h₁ : is_caratheodory m s₁) (h₂ : is_caratheodory m s₂) : is_caratheodory m (s₁ ∪ s₂) :=
  sorry

theorem measure_inter_union {α : Type u} (m : outer_measure α) {s₁ : set α} {s₂ : set α}
    (h : s₁ ∩ s₂ ⊆ ∅) (h₁ : is_caratheodory m s₁) {t : set α} :
    coe_fn m (t ∩ (s₁ ∪ s₂)) = coe_fn m (t ∩ s₁) + coe_fn m (t ∩ s₂) :=
  sorry

theorem is_caratheodory_Union_lt {α : Type u} (m : outer_measure α) {s : ℕ → set α} {n : ℕ} :
    (∀ (i : ℕ), i < n → is_caratheodory m (s i)) →
        is_caratheodory m (set.Union fun (i : ℕ) => set.Union fun (H : i < n) => s i) :=
  sorry

theorem is_caratheodory_inter {α : Type u} (m : outer_measure α) {s₁ : set α} {s₂ : set α}
    (h₁ : is_caratheodory m s₁) (h₂ : is_caratheodory m s₂) : is_caratheodory m (s₁ ∩ s₂) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (is_caratheodory m (s₁ ∩ s₂)))
        (Eq.symm (propext (is_caratheodory_compl_iff m)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_caratheodory m (s₁ ∩ s₂ᶜ))) (set.compl_inter s₁ s₂)))
      (is_caratheodory_union m (is_caratheodory_compl m h₁) (is_caratheodory_compl m h₂)))

theorem is_caratheodory_sum {α : Type u} (m : outer_measure α) {s : ℕ → set α}
    (h : ∀ (i : ℕ), is_caratheodory m (s i)) (hd : pairwise (disjoint on s)) {t : set α} {n : ℕ} :
    (finset.sum (finset.range n) fun (i : ℕ) => coe_fn m (t ∩ s i)) =
        coe_fn m (t ∩ set.Union fun (i : ℕ) => set.Union fun (H : i < n) => s i) :=
  sorry

theorem is_caratheodory_Union_nat {α : Type u} (m : outer_measure α) {s : ℕ → set α}
    (h : ∀ (i : ℕ), is_caratheodory m (s i)) (hd : pairwise (disjoint on s)) :
    is_caratheodory m (set.Union fun (i : ℕ) => s i) :=
  sorry

theorem f_Union {α : Type u} (m : outer_measure α) {s : ℕ → set α}
    (h : ∀ (i : ℕ), is_caratheodory m (s i)) (hd : pairwise (disjoint on s)) :
    coe_fn m (set.Union fun (i : ℕ) => s i) = tsum fun (i : ℕ) => coe_fn m (s i) :=
  sorry

/-- The Carathéodory-measurable sets for an outer measure `m` form a Dynkin system.  -/
def caratheodory_dynkin {α : Type u} (m : outer_measure α) : measurable_space.dynkin_system α :=
  measurable_space.dynkin_system.mk (is_caratheodory m) (is_caratheodory_empty m) sorry sorry

/-- Given an outer measure `μ`, the Carathéodory-measurable space is
  defined such that `s` is measurable if `∀t, μ t = μ (t ∩ s) + μ (t \ s)`. -/
protected def caratheodory {α : Type u} (m : outer_measure α) : measurable_space α :=
  measurable_space.dynkin_system.to_measurable_space (caratheodory_dynkin m) sorry

theorem is_caratheodory_iff {α : Type u} (m : outer_measure α) {s : set α} :
    measurable_space.is_measurable' (outer_measure.caratheodory m) s ↔
        ∀ (t : set α), coe_fn m t = coe_fn m (t ∩ s) + coe_fn m (t \ s) :=
  iff.rfl

theorem is_caratheodory_iff_le {α : Type u} (m : outer_measure α) {s : set α} :
    measurable_space.is_measurable' (outer_measure.caratheodory m) s ↔
        ∀ (t : set α), coe_fn m (t ∩ s) + coe_fn m (t \ s) ≤ coe_fn m t :=
  is_caratheodory_iff_le' m

protected theorem Union_eq_of_caratheodory {α : Type u} (m : outer_measure α) {s : ℕ → set α}
    (h : ∀ (i : ℕ), measurable_space.is_measurable' (outer_measure.caratheodory m) (s i))
    (hd : pairwise (disjoint on s)) :
    coe_fn m (set.Union fun (i : ℕ) => s i) = tsum fun (i : ℕ) => coe_fn m (s i) :=
  f_Union m h hd

theorem of_function_caratheodory {α : Type u_1} {m : set α → ennreal} {s : set α} {h₀ : m ∅ = 0}
    (hs : ∀ (t : set α), m (t ∩ s) + m (t \ s) ≤ m t) :
    measurable_space.is_measurable' (outer_measure.caratheodory (outer_measure.of_function m h₀))
        s :=
  sorry

theorem bounded_by_caratheodory {α : Type u_1} {m : set α → ennreal} {s : set α}
    (hs : ∀ (t : set α), m (t ∩ s) + m (t \ s) ≤ m t) :
    measurable_space.is_measurable' (outer_measure.caratheodory (bounded_by m)) s :=
  sorry

@[simp] theorem zero_caratheodory {α : Type u_1} : outer_measure.caratheodory 0 = ⊤ :=
  top_unique
    fun (s : set α) (_x : measurable_space.is_measurable' ⊤ s) (t : set α) =>
      Eq.symm (add_zero (coe_fn 0 t))

theorem top_caratheodory {α : Type u_1} : outer_measure.caratheodory ⊤ = ⊤ := sorry

theorem le_add_caratheodory {α : Type u_1} (m₁ : outer_measure α) (m₂ : outer_measure α) :
    outer_measure.caratheodory m₁ ⊓ outer_measure.caratheodory m₂ ≤
        outer_measure.caratheodory (m₁ + m₂) :=
  sorry

theorem le_sum_caratheodory {α : Type u_1} {ι : Type u_2} (m : ι → outer_measure α) :
    (infi fun (i : ι) => outer_measure.caratheodory (m i)) ≤ outer_measure.caratheodory (sum m) :=
  sorry

theorem le_smul_caratheodory {α : Type u_1} (a : ennreal) (m : outer_measure α) :
    outer_measure.caratheodory m ≤ outer_measure.caratheodory (a • m) :=
  sorry

@[simp] theorem dirac_caratheodory {α : Type u_1} (a : α) :
    outer_measure.caratheodory (dirac a) = ⊤ :=
  sorry

/-- Given a set of outer measures, we define a new function that on a set `s` is defined to be the
  infimum of `μ(s)` for the outer measures `μ` in the collection. We ensure that this
  function is defined to be `0` on `∅`, even if the collection of outer measures is empty.
  The outer measure generated by this function is the infimum of the given outer measures. -/
def Inf_gen {α : Type u_1} (m : set (outer_measure α)) (s : set α) : ennreal :=
  infi fun (μ : outer_measure α) => infi fun (h : μ ∈ m) => coe_fn μ s

theorem Inf_gen_def {α : Type u_1} (m : set (outer_measure α)) (t : set α) :
    Inf_gen m t = infi fun (μ : outer_measure α) => infi fun (h : μ ∈ m) => coe_fn μ t :=
  rfl

theorem Inf_eq_bounded_by_Inf_gen {α : Type u_1} (m : set (outer_measure α)) :
    Inf m = bounded_by (Inf_gen m) :=
  sorry

theorem supr_Inf_gen_nonempty {α : Type u_1} {m : set (outer_measure α)} (h : set.nonempty m)
    (t : set α) :
    (supr fun (h : set.nonempty t) => Inf_gen m t) =
        infi fun (μ : outer_measure α) => infi fun (h : μ ∈ m) => coe_fn μ t :=
  sorry

/-- The value of the Infimum of a nonempty set of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem Inf_apply {α : Type u_1} {m : set (outer_measure α)} {s : set α} (h : set.nonempty m) :
    coe_fn (Inf m) s =
        infi
          fun (t : ℕ → set α) =>
            infi
              fun (h2 : s ⊆ set.Union t) =>
                tsum
                  fun (n : ℕ) =>
                    infi fun (μ : outer_measure α) => infi fun (h3 : μ ∈ m) => coe_fn μ (t n) :=
  sorry

/-- This proves that Inf and restrict commute for outer measures, so long as the set of
outer measures is nonempty. -/
theorem restrict_Inf_eq_Inf_restrict {α : Type u_1} (m : set (outer_measure α)) {s : set α}
    (hm : set.nonempty m) : coe_fn (restrict s) (Inf m) = Inf (⇑(restrict s) '' m) :=
  sorry

end outer_measure


/-! ### Induced Outer Measure

  We can extend a function defined on a subset of `set α` to an outer measure.
  The underlying function is called `extend`, and the measure it induces is called
  `induced_outer_measure`.

  Some lemmas below are proven twice, once in the general case, and one where the function `m`
  is only defined on measurable sets (i.e. when `P = is_measurable`). In the latter cases, we can
  remove some hypotheses in the statement. The general version has the same name, but with a prime
  at the end. -/

/-- We can trivially extend a function defined on a subclass of objects (with codomain `ennreal`)
  to all objects by defining it to be `∞` on the objects not in the class. -/
def extend {α : Type u_1} {P : α → Prop} (m : (s : α) → P s → ennreal) (s : α) : ennreal :=
  infi fun (h : P s) => m s h

theorem extend_eq {α : Type u_1} {P : α → Prop} (m : (s : α) → P s → ennreal) {s : α} (h : P s) :
    extend m s = m s h :=
  sorry

theorem le_extend {α : Type u_1} {P : α → Prop} (m : (s : α) → P s → ennreal) {s : α} (h : P s) :
    m s h ≤ extend m s :=
  sorry

theorem extend_empty {α : Type u_1} {P : set α → Prop} {m : (s : set α) → P s → ennreal} (P0 : P ∅)
    (m0 : m ∅ P0 = 0) : extend m ∅ = 0 :=
  Eq.trans (extend_eq m P0) m0

theorem extend_Union_nat {α : Type u_1} {P : set α → Prop} {m : (s : set α) → P s → ennreal}
    (PU : ∀ {f : ℕ → set α}, (∀ (i : ℕ), P (f i)) → P (set.Union fun (i : ℕ) => f i))
    {f : ℕ → set α} (hm : ∀ (i : ℕ), P (f i))
    (mU : m (set.Union fun (i : ℕ) => f i) (PU hm) = tsum fun (i : ℕ) => m (f i) (hm i)) :
    extend m (set.Union fun (i : ℕ) => f i) = tsum fun (i : ℕ) => extend m (f i) :=
  sorry

theorem extend_Union_le_tsum_nat' {α : Type u_1} {P : set α → Prop}
    {m : (s : set α) → P s → ennreal}
    (PU : ∀ {f : ℕ → set α}, (∀ (i : ℕ), P (f i)) → P (set.Union fun (i : ℕ) => f i))
    (msU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), P (f i)),
        m (set.Union fun (i : ℕ) => f i) (PU hm) ≤ tsum fun (i : ℕ) => m (f i) (hm i))
    (s : ℕ → set α) :
    extend m (set.Union fun (i : ℕ) => s i) ≤ tsum fun (i : ℕ) => extend m (s i) :=
  sorry

theorem extend_mono' {α : Type u_1} {P : set α → Prop} {m : (s : set α) → P s → ennreal}
    (m_mono : ∀ {s₁ s₂ : set α} (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)
    {s₁ : set α} {s₂ : set α} (h₁ : P s₁) (hs : s₁ ⊆ s₂) : extend m s₁ ≤ extend m s₂ :=
  le_infi
    fun (h₂ : P s₂) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (extend m s₁ ≤ m s₂ h₂)) (extend_eq m h₁))) (m_mono h₁ h₂ hs)

theorem extend_Union {α : Type u_1} {P : set α → Prop} {m : (s : set α) → P s → ennreal} (P0 : P ∅)
    (m0 : m ∅ P0 = 0)
    (PU : ∀ {f : ℕ → set α}, (∀ (i : ℕ), P (f i)) → P (set.Union fun (i : ℕ) => f i))
    (mU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), P (f i)),
        pairwise (disjoint on f) →
          m (set.Union fun (i : ℕ) => f i) (PU hm) = tsum fun (i : ℕ) => m (f i) (hm i))
    {β : Type u_2} [encodable β] {f : β → set α} (hd : pairwise (disjoint on f))
    (hm : ∀ (i : β), P (f i)) :
    extend m (set.Union fun (i : β) => f i) = tsum fun (i : β) => extend m (f i) :=
  sorry

theorem extend_union {α : Type u_1} {P : set α → Prop} {m : (s : set α) → P s → ennreal} (P0 : P ∅)
    (m0 : m ∅ P0 = 0)
    (PU : ∀ {f : ℕ → set α}, (∀ (i : ℕ), P (f i)) → P (set.Union fun (i : ℕ) => f i))
    (mU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), P (f i)),
        pairwise (disjoint on f) →
          m (set.Union fun (i : ℕ) => f i) (PU hm) = tsum fun (i : ℕ) => m (f i) (hm i))
    {s₁ : set α} {s₂ : set α} (hd : disjoint s₁ s₂) (h₁ : P s₁) (h₂ : P s₂) :
    extend m (s₁ ∪ s₂) = extend m s₁ + extend m s₂ :=
  sorry

/-- Given an arbitrary function on a subset of sets, we can define the outer measure corresponding
  to it (this is the unique maximal outer measure that is at most `m` on the domain of `m`). -/
def induced_outer_measure {α : Type u_1} {P : set α → Prop} (m : (s : set α) → P s → ennreal)
    (P0 : P ∅) (m0 : m ∅ P0 = 0) : outer_measure α :=
  outer_measure.of_function (extend m) sorry

theorem induced_outer_measure_eq_extend' {α : Type u_1} {P : set α → Prop}
    {m : (s : set α) → P s → ennreal} {P0 : P ∅} {m0 : m ∅ P0 = 0}
    (PU : ∀ {f : ℕ → set α}, (∀ (i : ℕ), P (f i)) → P (set.Union fun (i : ℕ) => f i))
    (msU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), P (f i)),
        m (set.Union fun (i : ℕ) => f i) (PU hm) ≤ tsum fun (i : ℕ) => m (f i) (hm i))
    (m_mono : ∀ {s₁ s₂ : set α} (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)
    {s : set α} (hs : P s) : coe_fn (induced_outer_measure m P0 m0) s = extend m s :=
  outer_measure.of_function_eq s (fun (t : set α) => extend_mono' m_mono hs)
    (extend_Union_le_tsum_nat' PU msU)

theorem induced_outer_measure_eq' {α : Type u_1} {P : set α → Prop}
    {m : (s : set α) → P s → ennreal} {P0 : P ∅} {m0 : m ∅ P0 = 0}
    (PU : ∀ {f : ℕ → set α}, (∀ (i : ℕ), P (f i)) → P (set.Union fun (i : ℕ) => f i))
    (msU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), P (f i)),
        m (set.Union fun (i : ℕ) => f i) (PU hm) ≤ tsum fun (i : ℕ) => m (f i) (hm i))
    (m_mono : ∀ {s₁ s₂ : set α} (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)
    {s : set α} (hs : P s) : coe_fn (induced_outer_measure m P0 m0) s = m s hs :=
  Eq.trans (induced_outer_measure_eq_extend' PU msU m_mono hs) (extend_eq m hs)

theorem induced_outer_measure_eq_infi {α : Type u_1} {P : set α → Prop}
    {m : (s : set α) → P s → ennreal} {P0 : P ∅} {m0 : m ∅ P0 = 0}
    (PU : ∀ {f : ℕ → set α}, (∀ (i : ℕ), P (f i)) → P (set.Union fun (i : ℕ) => f i))
    (msU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), P (f i)),
        m (set.Union fun (i : ℕ) => f i) (PU hm) ≤ tsum fun (i : ℕ) => m (f i) (hm i))
    (m_mono : ∀ {s₁ s₂ : set α} (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)
    (s : set α) :
    coe_fn (induced_outer_measure m P0 m0) s =
        infi fun (t : set α) => infi fun (ht : P t) => infi fun (h : s ⊆ t) => m t ht :=
  sorry

theorem induced_outer_measure_preimage {α : Type u_1} {P : set α → Prop}
    {m : (s : set α) → P s → ennreal} {P0 : P ∅} {m0 : m ∅ P0 = 0}
    (PU : ∀ {f : ℕ → set α}, (∀ (i : ℕ), P (f i)) → P (set.Union fun (i : ℕ) => f i))
    (msU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), P (f i)),
        m (set.Union fun (i : ℕ) => f i) (PU hm) ≤ tsum fun (i : ℕ) => m (f i) (hm i))
    (m_mono : ∀ {s₁ s₂ : set α} (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)
    (f : α ≃ α) (Pm : ∀ (s : set α), P (⇑f ⁻¹' s) ↔ P s)
    (mm : ∀ (s : set α) (hs : P s), m (⇑f ⁻¹' s) (iff.mpr (Pm s) hs) = m s hs) {A : set α} :
    coe_fn (induced_outer_measure m P0 m0) (⇑f ⁻¹' A) = coe_fn (induced_outer_measure m P0 m0) A :=
  sorry

theorem induced_outer_measure_exists_set {α : Type u_1} {P : set α → Prop}
    {m : (s : set α) → P s → ennreal} {P0 : P ∅} {m0 : m ∅ P0 = 0}
    (PU : ∀ {f : ℕ → set α}, (∀ (i : ℕ), P (f i)) → P (set.Union fun (i : ℕ) => f i))
    (msU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), P (f i)),
        m (set.Union fun (i : ℕ) => f i) (PU hm) ≤ tsum fun (i : ℕ) => m (f i) (hm i))
    (m_mono : ∀ {s₁ s₂ : set α} (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)
    {s : set α} (hs : coe_fn (induced_outer_measure m P0 m0) s < ⊤) {ε : nnreal} (hε : 0 < ε) :
    ∃ (t : set α),
        ∃ (ht : P t),
          s ⊆ t ∧
            coe_fn (induced_outer_measure m P0 m0) t ≤
              coe_fn (induced_outer_measure m P0 m0) s + ↑ε :=
  sorry

/-- To test whether `s` is Carathéodory-measurable we only need to check the sets `t` for which
  `P t` holds. See `of_function_caratheodory` for another way to show the Carathéodory-measurability
  of `s`.
-/
theorem induced_outer_measure_caratheodory {α : Type u_1} {P : set α → Prop}
    {m : (s : set α) → P s → ennreal} {P0 : P ∅} {m0 : m ∅ P0 = 0}
    (PU : ∀ {f : ℕ → set α}, (∀ (i : ℕ), P (f i)) → P (set.Union fun (i : ℕ) => f i))
    (msU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), P (f i)),
        m (set.Union fun (i : ℕ) => f i) (PU hm) ≤ tsum fun (i : ℕ) => m (f i) (hm i))
    (m_mono : ∀ {s₁ s₂ : set α} (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)
    (s : set α) :
    measurable_space.is_measurable' (outer_measure.caratheodory (induced_outer_measure m P0 m0)) s ↔
        ∀ (t : set α),
          P t →
            coe_fn (induced_outer_measure m P0 m0) (t ∩ s) +
                coe_fn (induced_outer_measure m P0 m0) (t \ s) ≤
              coe_fn (induced_outer_measure m P0 m0) t :=
  sorry

/-! If `P` is `is_measurable` for some measurable space, then we can remove some hypotheses of the
  above lemmas. -/

theorem extend_mono {α : Type u_1} [measurable_space α]
    {m : (s : set α) → is_measurable s → ennreal} (m0 : m ∅ is_measurable.empty = 0)
    (mU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), is_measurable (f i)),
        pairwise (disjoint on f) →
          m (set.Union fun (i : ℕ) => f i) (is_measurable.Union hm) =
            tsum fun (i : ℕ) => m (f i) (hm i))
    {s₁ : set α} {s₂ : set α} (h₁ : is_measurable s₁) (hs : s₁ ⊆ s₂) : extend m s₁ ≤ extend m s₂ :=
  sorry

theorem extend_Union_le_tsum_nat {α : Type u_1} [measurable_space α]
    {m : (s : set α) → is_measurable s → ennreal} (m0 : m ∅ is_measurable.empty = 0)
    (mU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), is_measurable (f i)),
        pairwise (disjoint on f) →
          m (set.Union fun (i : ℕ) => f i) (is_measurable.Union hm) =
            tsum fun (i : ℕ) => m (f i) (hm i))
    (s : ℕ → set α) :
    extend m (set.Union fun (i : ℕ) => s i) ≤ tsum fun (i : ℕ) => extend m (s i) :=
  sorry

theorem induced_outer_measure_eq_extend {α : Type u_1} [measurable_space α]
    {m : (s : set α) → is_measurable s → ennreal} (m0 : m ∅ is_measurable.empty = 0)
    (mU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), is_measurable (f i)),
        pairwise (disjoint on f) →
          m (set.Union fun (i : ℕ) => f i) (is_measurable.Union hm) =
            tsum fun (i : ℕ) => m (f i) (hm i))
    {s : set α} (hs : is_measurable s) :
    coe_fn (induced_outer_measure m is_measurable.empty m0) s = extend m s :=
  outer_measure.of_function_eq s (fun (t : set α) => extend_mono m0 mU hs)
    (extend_Union_le_tsum_nat m0 mU)

theorem induced_outer_measure_eq {α : Type u_1} [measurable_space α]
    {m : (s : set α) → is_measurable s → ennreal} (m0 : m ∅ is_measurable.empty = 0)
    (mU :
      ∀ {f : ℕ → set α} (hm : ∀ (i : ℕ), is_measurable (f i)),
        pairwise (disjoint on f) →
          m (set.Union fun (i : ℕ) => f i) (is_measurable.Union hm) =
            tsum fun (i : ℕ) => m (f i) (hm i))
    {s : set α} (hs : is_measurable s) :
    coe_fn (induced_outer_measure m is_measurable.empty m0) s = m s hs :=
  Eq.trans (induced_outer_measure_eq_extend m0 mU hs) (extend_eq m hs)

namespace outer_measure


/-- Given an outer measure `m` we can forget its value on non-measurable sets, and then consider
  `m.trim`, the unique maximal outer measure less than that function. -/
def trim {α : Type u_1} [measurable_space α] (m : outer_measure α) : outer_measure α :=
  induced_outer_measure (fun (s : set α) (_x : is_measurable s) => coe_fn m s) is_measurable.empty
    (empty m)

theorem le_trim {α : Type u_1} [measurable_space α] (m : outer_measure α) : m ≤ trim m :=
  iff.mpr le_of_function
    fun (s : set α) => le_infi fun (_x : is_measurable s) => le_refl (coe_fn m s)

theorem trim_eq {α : Type u_1} [measurable_space α] (m : outer_measure α) {s : set α}
    (hs : is_measurable s) : coe_fn (trim m) s = coe_fn m s :=
  sorry

theorem trim_congr {α : Type u_1} [measurable_space α] {m₁ : outer_measure α} {m₂ : outer_measure α}
    (H : ∀ {s : set α}, is_measurable s → coe_fn m₁ s = coe_fn m₂ s) : trim m₁ = trim m₂ :=
  sorry

theorem trim_le_trim {α : Type u_1} [measurable_space α] {m₁ : outer_measure α}
    {m₂ : outer_measure α} (H : m₁ ≤ m₂) : trim m₁ ≤ trim m₂ :=
  sorry

theorem le_trim_iff {α : Type u_1} [measurable_space α] {m₁ : outer_measure α}
    {m₂ : outer_measure α} :
    m₁ ≤ trim m₂ ↔ ∀ (s : set α), is_measurable s → coe_fn m₁ s ≤ coe_fn m₂ s :=
  iff.trans le_of_function (forall_congr fun (s : set α) => le_infi_iff)

theorem trim_eq_infi {α : Type u_1} [measurable_space α] (m : outer_measure α) (s : set α) :
    coe_fn (trim m) s =
        infi
          fun (t : set α) =>
            infi fun (st : s ⊆ t) => infi fun (ht : is_measurable t) => coe_fn m t :=
  sorry

theorem trim_eq_infi' {α : Type u_1} [measurable_space α] (m : outer_measure α) (s : set α) :
    coe_fn (trim m) s =
        infi fun (t : Subtype fun (t : set α) => s ⊆ t ∧ is_measurable t) => coe_fn m ↑t :=
  sorry

theorem trim_trim {α : Type u_1} [measurable_space α] (m : outer_measure α) :
    trim (trim m) = trim m :=
  sorry

@[simp] theorem trim_zero {α : Type u_1} [measurable_space α] : trim 0 = 0 := sorry

theorem trim_add {α : Type u_1} [measurable_space α] (m₁ : outer_measure α) (m₂ : outer_measure α) :
    trim (m₁ + m₂) = trim m₁ + trim m₂ :=
  sorry

theorem trim_sum_ge {α : Type u_1} [measurable_space α] {ι : Type u_2} (m : ι → outer_measure α) :
    (sum fun (i : ι) => trim (m i)) ≤ trim (sum m) :=
  sorry

theorem exists_is_measurable_superset_eq_trim {α : Type u_1} [measurable_space α]
    (m : outer_measure α) (s : set α) :
    ∃ (t : set α), s ⊆ t ∧ is_measurable t ∧ coe_fn m t = coe_fn (trim m) s :=
  sorry

theorem exists_is_measurable_superset_of_trim_eq_zero {α : Type u_1} [measurable_space α]
    {m : outer_measure α} {s : set α} (h : coe_fn (trim m) s = 0) :
    ∃ (t : set α), s ⊆ t ∧ is_measurable t ∧ coe_fn m t = 0 :=
  sorry

theorem trim_smul {α : Type u_1} [measurable_space α] (c : ennreal) (m : outer_measure α) :
    trim (c • m) = c • trim m :=
  sorry

/-- The trimmed property of a measure μ states that `μ.to_outer_measure.trim = μ.to_outer_measure`.
This theorem shows that a restricted trimmed outer measure is a trimmed outer measure. -/
theorem restrict_trim {α : Type u_1} [measurable_space α] {μ : outer_measure α} {s : set α}
    (hs : is_measurable s) : trim (coe_fn (restrict s) μ) = coe_fn (restrict s) (trim μ) :=
  sorry

end Mathlib