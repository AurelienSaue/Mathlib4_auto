/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.big_operators.intervals
import Mathlib.topology.instances.real
import Mathlib.topology.algebra.module
import Mathlib.data.indicator_function
import Mathlib.data.equiv.encodable.lattice
import Mathlib.order.filter.at_top_bot
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 u_6 

namespace Mathlib

/-!
# Infinite sum over a topological monoid

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `has_sum.tendsto_sum_nat`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/

/-- Infinite sum on a topological monoid

The `at_top` filter on `finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition or many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant.
-/
def has_sum {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] (f : β → α) (a : α) :=
  filter.tendsto (fun (s : finset β) => finset.sum s fun (b : β) => f b) filter.at_top (nhds a)

/-- `summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def summable {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] (f : β → α) :=
  ∃ (a : α), has_sum f a

/-- `∑' i, f i` is the sum of `f` it exists, or 0 otherwise -/
def tsum {α : Type u_1} [add_comm_monoid α] [topological_space α] {β : Type u_2} (f : β → α) : α :=
  dite (summable f) (fun (h : summable f) => classical.some h) fun (h : ¬summable f) => 0

-- see Note [operator precedence of big operators]

theorem summable.has_sum {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} (ha : summable f) : has_sum f (tsum fun (b : β) => f b) := sorry

theorem has_sum.summable {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} (h : has_sum f a) : summable f :=
  Exists.intro a h

/-- Constant zero function has sum `0` -/
theorem has_sum_zero {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] : has_sum (fun (b : β) => 0) 0 := sorry

theorem summable_zero {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] : summable fun (b : β) => 0 :=
  has_sum.summable has_sum_zero

theorem tsum_eq_zero_of_not_summable {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} (h : ¬summable f) : (tsum fun (b : β) => f b) = 0 := sorry

theorem has_sum.has_sum_of_sum_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} {g : γ → α} (h_eq : ∀ (u : finset γ),
  ∃ (v : finset β),
    ∀ (v' : finset β),
      v ⊆ v' → ∃ (u' : finset γ), u ⊆ u' ∧ (finset.sum u' fun (x : γ) => g x) = finset.sum v' fun (b : β) => f b) (hf : has_sum g a) : has_sum f a :=
  le_trans (filter.map_at_top_finset_sum_le_of_sum_eq h_eq) hf

theorem has_sum_iff_has_sum {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} {g : γ → α} (h₁ : ∀ (u : finset γ),
  ∃ (v : finset β),
    ∀ (v' : finset β),
      v ⊆ v' → ∃ (u' : finset γ), u ⊆ u' ∧ (finset.sum u' fun (x : γ) => g x) = finset.sum v' fun (b : β) => f b) (h₂ : ∀ (v : finset β),
  ∃ (u : finset γ),
    ∀ (u' : finset γ),
      u ⊆ u' → ∃ (v' : finset β), v ⊆ v' ∧ (finset.sum v' fun (b : β) => f b) = finset.sum u' fun (x : γ) => g x) : has_sum f a ↔ has_sum g a :=
  { mp := has_sum.has_sum_of_sum_eq h₂, mpr := has_sum.has_sum_of_sum_eq h₁ }

theorem function.injective.has_sum_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} {g : γ → β} (hg : function.injective g) (hf : ∀ (x : β), ¬x ∈ set.range g → f x = 0) : has_sum (f ∘ g) a ↔ has_sum f a := sorry

theorem function.injective.summable_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β → α} {g : γ → β} (hg : function.injective g) (hf : ∀ (x : β), ¬x ∈ set.range g → f x = 0) : summable (f ∘ g) ↔ summable f :=
  exists_congr fun (_x : α) => function.injective.has_sum_iff hg hf

theorem has_sum_subtype_iff_of_support_subset {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} {s : set β} (hf : function.support f ⊆ s) : has_sum (f ∘ coe) a ↔ has_sum f a := sorry

theorem has_sum_subtype_iff_indicator {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} {s : set β} : has_sum (f ∘ coe) a ↔ has_sum (set.indicator s f) a := sorry

@[simp] theorem has_sum_subtype_support {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} : has_sum (f ∘ coe) a ↔ has_sum f a :=
  has_sum_subtype_iff_of_support_subset (set.subset.refl (function.support f))

theorem has_sum_fintype {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [fintype β] (f : β → α) : has_sum f (finset.sum finset.univ fun (b : β) => f b) :=
  order_top.tendsto_at_top_nhds fun (s : finset β) => finset.sum s fun (b : β) => f b

protected theorem finset.has_sum {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] (s : finset β) (f : β → α) : has_sum (f ∘ coe) (finset.sum s fun (b : β) => f b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (has_sum (f ∘ coe) (finset.sum s fun (b : β) => f b))) (Eq.symm finset.sum_attach)))
    (has_sum_fintype (f ∘ coe))

protected theorem finset.summable {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] (s : finset β) (f : β → α) : summable (f ∘ coe) :=
  has_sum.summable (finset.has_sum s f)

protected theorem set.finite.summable {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {s : set β} (hs : set.finite s) (f : β → α) : summable (f ∘ coe) := sorry

/-- If a function `f` vanishes outside of a finite set `s`, then it `has_sum` `∑ b in s, f b`. -/
theorem has_sum_sum_of_ne_finset_zero {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} {s : finset β} (hf : ∀ (b : β), ¬b ∈ s → f b = 0) : has_sum f (finset.sum s fun (b : β) => f b) :=
  iff.mp (has_sum_subtype_iff_of_support_subset (iff.mpr function.support_subset_iff' hf)) (finset.has_sum s f)

theorem summable_of_ne_finset_zero {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} {s : finset β} (hf : ∀ (b : β), ¬b ∈ s → f b = 0) : summable f :=
  has_sum.summable (has_sum_sum_of_ne_finset_zero hf)

theorem has_sum_single {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} (b : β) (hf : ∀ (b' : β), b' ≠ b → f b' = 0) : has_sum f (f b) := sorry

theorem has_sum_ite_eq {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] (b : β) (a : α) : has_sum (fun (b' : β) => ite (b' = b) a 0) a := sorry

theorem equiv.has_sum_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} (e : γ ≃ β) : has_sum (f ∘ ⇑e) a ↔ has_sum f a := sorry

theorem equiv.summable_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β → α} (e : γ ≃ β) : summable (f ∘ ⇑e) ↔ summable f :=
  exists_congr fun (a : α) => equiv.has_sum_iff e

theorem summable.prod_symm {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β × γ → α} (hf : summable f) : summable fun (p : γ × β) => f (prod.swap p) :=
  iff.mpr (equiv.summable_iff (equiv.prod_comm γ β)) hf

theorem equiv.has_sum_iff_of_support {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} {g : γ → α} (e : ↥(function.support f) ≃ ↥(function.support g)) (he : ∀ (x : ↥(function.support f)), g ↑(coe_fn e x) = f ↑x) : has_sum f a ↔ has_sum g a := sorry

theorem has_sum_iff_has_sum_of_ne_zero_bij {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} {g : γ → α} (i : ↥(function.support g) → β) (hi : ∀ {x y : ↥(function.support g)}, i x = i y → ↑x = ↑y) (hf : function.support f ⊆ set.range i) (hfg : ∀ (x : ↥(function.support g)), f (i x) = g ↑x) : has_sum f a ↔ has_sum g a := sorry

theorem equiv.summable_iff_of_support {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β → α} {g : γ → α} (e : ↥(function.support f) ≃ ↥(function.support g)) (he : ∀ (x : ↥(function.support f)), g ↑(coe_fn e x) = f ↑x) : summable f ↔ summable g :=
  exists_congr fun (_x : α) => equiv.has_sum_iff_of_support e he

protected theorem has_sum.map {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} [add_comm_monoid γ] [topological_space γ] (hf : has_sum f a) (g : α →+ γ) (hg : continuous ⇑g) : has_sum (⇑g ∘ f) (coe_fn g a) := sorry

protected theorem summable.map {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {f : β → α} [add_comm_monoid γ] [topological_space γ] (hf : summable f) (g : α →+ γ) (hg : continuous ⇑g) : summable (⇑g ∘ f) :=
  has_sum.summable (has_sum.map (summable.has_sum hf) g hg)

/-- If `f : ℕ → α` has sum `a`, then the partial sums `∑_{i=0}^{n-1} f i` converge to `a`. -/
theorem has_sum.tendsto_sum_nat {α : Type u_1} [add_comm_monoid α] [topological_space α] {a : α} {f : ℕ → α} (h : has_sum f a) : filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => f i) filter.at_top (nhds a) :=
  filter.tendsto.comp h filter.tendsto_finset_range

theorem has_sum.unique {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} {a₁ : α} {a₂ : α} [t2_space α] : has_sum f a₁ → has_sum f a₂ → a₁ = a₂ :=
  tendsto_nhds_unique

theorem summable.has_sum_iff_tendsto_nat {α : Type u_1} [add_comm_monoid α] [topological_space α] [t2_space α] {f : ℕ → α} {a : α} (hf : summable f) : has_sum f a ↔ filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => f i) filter.at_top (nhds a) := sorry

theorem equiv.summable_iff_of_has_sum_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] {α' : Type u_4} [add_comm_monoid α'] [topological_space α'] (e : α' ≃ α) {f : β → α} {g : γ → α'} (he : ∀ {a : α'}, has_sum f (coe_fn e a) ↔ has_sum g a) : summable f ↔ summable g := sorry

theorem has_sum.add {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} {g : β → α} {a : α} {b : α} [has_continuous_add α] (hf : has_sum f a) (hg : has_sum g b) : has_sum (fun (b : β) => f b + g b) (a + b) := sorry

theorem summable.add {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} {g : β → α} [has_continuous_add α] (hf : summable f) (hg : summable g) : summable fun (b : β) => f b + g b :=
  has_sum.summable (has_sum.add (summable.has_sum hf) (summable.has_sum hg))

theorem has_sum_sum {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [has_continuous_add α] {f : γ → β → α} {a : γ → α} {s : finset γ} : (∀ (i : γ), i ∈ s → has_sum (f i) (a i)) →
  has_sum (fun (b : β) => finset.sum s fun (i : γ) => f i b) (finset.sum s fun (i : γ) => a i) := sorry

theorem summable_sum {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [has_continuous_add α] {f : γ → β → α} {s : finset γ} (hf : ∀ (i : γ), i ∈ s → summable (f i)) : summable fun (b : β) => finset.sum s fun (i : γ) => f i b :=
  has_sum.summable (has_sum_sum fun (i : γ) (hi : i ∈ s) => summable.has_sum (hf i hi))

theorem has_sum.add_compl {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} {b : α} [has_continuous_add α] {s : set β} (ha : has_sum (f ∘ coe) a) (hb : has_sum (f ∘ coe) b) : has_sum f (a + b) := sorry

theorem summable.add_compl {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} [has_continuous_add α] {s : set β} (hs : summable (f ∘ coe)) (hsc : summable (f ∘ coe)) : summable f :=
  has_sum.summable (has_sum.add_compl (summable.has_sum hs) (summable.has_sum hsc))

theorem has_sum.compl_add {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} {a : α} {b : α} [has_continuous_add α] {s : set β} (ha : has_sum (f ∘ coe) a) (hb : has_sum (f ∘ coe) b) : has_sum f (a + b) := sorry

theorem summable.compl_add {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] {f : β → α} [has_continuous_add α] {s : set β} (hs : summable (f ∘ coe)) (hsc : summable (f ∘ coe)) : summable f :=
  has_sum.summable (has_sum.compl_add (summable.has_sum hs) (summable.has_sum hsc))

theorem has_sum.sigma {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [has_continuous_add α] [regular_space α] {γ : β → Type u_3} {f : (sigma fun (b : β) => γ b) → α} {g : β → α} {a : α} (ha : has_sum f a) (hf : ∀ (b : β), has_sum (fun (c : γ b) => f (sigma.mk b c)) (g b)) : has_sum g a := sorry

/-- If a series `f` on `β × γ` has sum `a` and for each `b` the restriction of `f` to `{b} × γ`
has sum `g b`, then the series `g` has sum `a`. -/
theorem has_sum.prod_fiberwise {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [has_continuous_add α] [regular_space α] {f : β × γ → α} {g : β → α} {a : α} (ha : has_sum f a) (hf : ∀ (b : β), has_sum (fun (c : γ) => f (b, c)) (g b)) : has_sum g a :=
  has_sum.sigma (iff.mpr (equiv.has_sum_iff (equiv.sigma_equiv_prod β γ)) ha) hf

theorem summable.sigma' {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [has_continuous_add α] [regular_space α] {γ : β → Type u_3} {f : (sigma fun (b : β) => γ b) → α} (ha : summable f) (hf : ∀ (b : β), summable fun (c : γ b) => f (sigma.mk b c)) : summable fun (b : β) => tsum fun (c : γ b) => f (sigma.mk b c) :=
  has_sum.summable (has_sum.sigma (summable.has_sum ha) fun (b : β) => summable.has_sum (hf b))

theorem has_sum.sigma_of_has_sum {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [has_continuous_add α] [regular_space α] {γ : β → Type u_3} {f : (sigma fun (b : β) => γ b) → α} {g : β → α} {a : α} (ha : has_sum g a) (hf : ∀ (b : β), has_sum (fun (c : γ b) => f (sigma.mk b c)) (g b)) (hf' : summable f) : has_sum f a := sorry

theorem has_sum.tsum_eq {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] {f : β → α} {a : α} (ha : has_sum f a) : (tsum fun (b : β) => f b) = a :=
  has_sum.unique (summable.has_sum (Exists.intro a ha)) ha

theorem summable.has_sum_iff {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] {f : β → α} {a : α} (h : summable f) : has_sum f a ↔ (tsum fun (b : β) => f b) = a :=
  { mp := has_sum.tsum_eq, mpr := fun (eq : (tsum fun (b : β) => f b) = a) => eq ▸ summable.has_sum h }

@[simp] theorem tsum_zero {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] : (tsum fun (b : β) => 0) = 0 :=
  has_sum.tsum_eq has_sum_zero

theorem tsum_eq_sum {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] {f : β → α} {s : finset β} (hf : ∀ (b : β), ¬b ∈ s → f b = 0) : (tsum fun (b : β) => f b) = finset.sum s fun (b : β) => f b :=
  has_sum.tsum_eq (has_sum_sum_of_ne_finset_zero hf)

theorem tsum_fintype {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] [fintype β] (f : β → α) : (tsum fun (b : β) => f b) = finset.sum finset.univ fun (b : β) => f b :=
  has_sum.tsum_eq (has_sum_fintype f)

@[simp] theorem finset.tsum_subtype {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] (s : finset β) (f : β → α) : (tsum fun (x : Subtype fun (x : β) => x ∈ s) => f ↑x) = finset.sum s fun (x : β) => f x :=
  has_sum.tsum_eq (finset.has_sum s f)

@[simp] theorem finset.tsum_subtype' {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] (s : finset β) (f : β → α) : (tsum fun (x : ↥↑s) => f ↑x) = finset.sum s fun (x : β) => f x :=
  finset.tsum_subtype s f

theorem tsum_eq_single {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] {f : β → α} (b : β) (hf : ∀ (b' : β), b' ≠ b → f b' = 0) : (tsum fun (b : β) => f b) = f b :=
  has_sum.tsum_eq (has_sum_single b hf)

@[simp] theorem tsum_ite_eq {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] (b : β) (a : α) : (tsum fun (b' : β) => ite (b' = b) a 0) = a :=
  has_sum.tsum_eq (has_sum_ite_eq b a)

theorem equiv.tsum_eq_tsum_of_has_sum_iff_has_sum {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [t2_space α] {α' : Type u_4} [add_comm_monoid α'] [topological_space α'] (e : α' ≃ α) (h0 : coe_fn e 0 = 0) {f : β → α} {g : γ → α'} (h : ∀ {a : α'}, has_sum f (coe_fn e a) ↔ has_sum g a) : (tsum fun (b : β) => f b) = coe_fn e (tsum fun (c : γ) => g c) := sorry

theorem tsum_eq_tsum_of_has_sum_iff_has_sum {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [t2_space α] {f : β → α} {g : γ → α} (h : ∀ {a : α}, has_sum f a ↔ has_sum g a) : (tsum fun (b : β) => f b) = tsum fun (c : γ) => g c :=
  equiv.tsum_eq_tsum_of_has_sum_iff_has_sum (equiv.refl α) rfl h

theorem equiv.tsum_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [t2_space α] (j : γ ≃ β) (f : β → α) : (tsum fun (c : γ) => f (coe_fn j c)) = tsum fun (b : β) => f b :=
  tsum_eq_tsum_of_has_sum_iff_has_sum fun (a : α) => equiv.has_sum_iff j

theorem equiv.tsum_eq_tsum_of_support {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [t2_space α] {f : β → α} {g : γ → α} (e : ↥(function.support f) ≃ ↥(function.support g)) (he : ∀ (x : ↥(function.support f)), g ↑(coe_fn e x) = f ↑x) : (tsum fun (x : β) => f x) = tsum fun (y : γ) => g y :=
  tsum_eq_tsum_of_has_sum_iff_has_sum fun (_x : α) => equiv.has_sum_iff_of_support e he

theorem tsum_eq_tsum_of_ne_zero_bij {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [t2_space α] {f : β → α} {g : γ → α} (i : ↥(function.support g) → β) (hi : ∀ {x y : ↥(function.support g)}, i x = i y → ↑x = ↑y) (hf : function.support f ⊆ set.range i) (hfg : ∀ (x : ↥(function.support g)), f (i x) = g ↑x) : (tsum fun (x : β) => f x) = tsum fun (y : γ) => g y :=
  tsum_eq_tsum_of_has_sum_iff_has_sum fun (_x : α) => has_sum_iff_has_sum_of_ne_zero_bij i hi hf hfg

theorem tsum_subtype {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] (s : set β) (f : β → α) : (tsum fun (x : ↥s) => f ↑x) = tsum fun (x : β) => set.indicator s f x :=
  tsum_eq_tsum_of_has_sum_iff_has_sum fun (_x : α) => has_sum_subtype_iff_indicator

theorem tsum_add {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] {f : β → α} {g : β → α} [has_continuous_add α] (hf : summable f) (hg : summable g) : (tsum fun (b : β) => f b + g b) = (tsum fun (b : β) => f b) + tsum fun (b : β) => g b :=
  has_sum.tsum_eq (has_sum.add (summable.has_sum hf) (summable.has_sum hg))

theorem tsum_sum {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [t2_space α] [has_continuous_add α] {f : γ → β → α} {s : finset γ} (hf : ∀ (i : γ), i ∈ s → summable (f i)) : (tsum fun (b : β) => finset.sum s fun (i : γ) => f i b) = finset.sum s fun (i : γ) => tsum fun (b : β) => f i b :=
  has_sum.tsum_eq (has_sum_sum fun (i : γ) (hi : i ∈ s) => summable.has_sum (hf i hi))

theorem tsum_sigma' {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] [has_continuous_add α] [regular_space α] {γ : β → Type u_3} {f : (sigma fun (b : β) => γ b) → α} (h₁ : ∀ (b : β), summable fun (c : γ b) => f (sigma.mk b c)) (h₂ : summable f) : (tsum fun (p : sigma fun (b : β) => γ b) => f p) = tsum fun (b : β) => tsum fun (c : γ b) => f (sigma.mk b c) :=
  Eq.symm (has_sum.tsum_eq (has_sum.sigma (summable.has_sum h₂) fun (b : β) => summable.has_sum (h₁ b)))

theorem tsum_prod' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [t2_space α] [has_continuous_add α] [regular_space α] {f : β × γ → α} (h : summable f) (h₁ : ∀ (b : β), summable fun (c : γ) => f (b, c)) : (tsum fun (p : β × γ) => f p) = tsum fun (b : β) => tsum fun (c : γ) => f (b, c) :=
  Eq.symm (has_sum.tsum_eq (has_sum.prod_fiberwise (summable.has_sum h) fun (b : β) => summable.has_sum (h₁ b)))

theorem tsum_comm' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [t2_space α] [has_continuous_add α] [regular_space α] {f : β → γ → α} (h : summable (function.uncurry f)) (h₁ : ∀ (b : β), summable (f b)) (h₂ : ∀ (c : γ), summable fun (b : β) => f b c) : (tsum fun (c : γ) => tsum fun (b : β) => f b c) = tsum fun (b : β) => tsum fun (c : γ) => f b c := sorry

/-- You can compute a sum over an encodably type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
theorem tsum_supr_decode2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [t2_space α] [encodable γ] [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0) (s : γ → β) : (tsum fun (i : ℕ) => m (supr fun (b : γ) => supr fun (H : b ∈ encodable.decode2 γ i) => s b)) =
  tsum fun (b : γ) => m (s b) := sorry

/-- `tsum_supr_decode2` specialized to the complete lattice of sets. -/
theorem tsum_Union_decode2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [t2_space α] [encodable γ] (m : set β → α) (m0 : m ∅ = 0) (s : γ → set β) : (tsum fun (i : ℕ) => m (set.Union fun (b : γ) => set.Union fun (H : b ∈ encodable.decode2 γ i) => s b)) =
  tsum fun (b : γ) => m (s b) :=
  tsum_supr_decode2 m m0 s

/-! Some properties about measure-like functions.
  These could also be functions defined on complete sublattices of sets, with the property
  that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/

/-- If a function is countably sub-additive then it is sub-additive on encodable types -/
theorem rel_supr_tsum {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid α] [topological_space α] [t2_space α] [encodable γ] [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop) (m_supr : ∀ (s : ℕ → β), R (m (supr fun (i : ℕ) => s i)) (tsum fun (i : ℕ) => m (s i))) (s : γ → β) : R (m (supr fun (b : γ) => s b)) (tsum fun (b : γ) => m (s b)) := sorry

/-- If a function is countably sub-additive then it is sub-additive on finite sets -/
theorem rel_supr_sum {α : Type u_1} {β : Type u_2} {δ : Type u_4} [add_comm_monoid α] [topological_space α] [t2_space α] [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop) (m_supr : ∀ (s : ℕ → β), R (m (supr fun (i : ℕ) => s i)) (tsum fun (i : ℕ) => m (s i))) (s : δ → β) (t : finset δ) : R (m (supr fun (d : δ) => supr fun (H : d ∈ t) => s d)) (finset.sum t fun (d : δ) => m (s d)) := sorry

/-- If a function is countably sub-additive then it is binary sub-additive -/
theorem rel_sup_add {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [topological_space α] [t2_space α] [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop) (m_supr : ∀ (s : ℕ → β), R (m (supr fun (i : ℕ) => s i)) (tsum fun (i : ℕ) => m (s i))) (s₁ : β) (s₂ : β) : R (m (s₁ ⊔ s₂)) (m s₁ + m s₂) := sorry

theorem pi.has_sum {α : Type u_1} {ι : Type u_5} {π : α → Type u_6} [(x : α) → add_comm_monoid (π x)] [(x : α) → topological_space (π x)] {f : ι → (x : α) → π x} {g : (x : α) → π x} : has_sum f g ↔ ∀ (x : α), has_sum (fun (i : ι) => f i x) (g x) := sorry

theorem pi.summable {α : Type u_1} {ι : Type u_5} {π : α → Type u_6} [(x : α) → add_comm_monoid (π x)] [(x : α) → topological_space (π x)] {f : ι → (x : α) → π x} : summable f ↔ ∀ (x : α), summable fun (i : ι) => f i x := sorry

theorem tsum_apply {α : Type u_1} {ι : Type u_5} {π : α → Type u_6} [(x : α) → add_comm_monoid (π x)] [(x : α) → topological_space (π x)] [∀ (x : α), t2_space (π x)] {f : ι → (x : α) → π x} {x : α} (hf : summable f) : tsum (fun (i : ι) => f i) x = tsum fun (i : ι) => f i x :=
  Eq.symm (has_sum.tsum_eq (iff.mp pi.has_sum (summable.has_sum hf) x))

-- `by simpa using` speeds up elaboration. Why?

theorem has_sum.neg {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} {a : α} (h : has_sum f a) : has_sum (fun (b : β) => -f b) (-a) :=
  eq.mpr (id (Eq.refl (has_sum (fun (b : β) => -f b) (-a))))
    (eq.mp (Eq.refl (has_sum (⇑(-add_monoid_hom.id α) ∘ f) (coe_fn (-add_monoid_hom.id α) a)))
      (has_sum.map h (-add_monoid_hom.id α) continuous_neg))

theorem summable.neg {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} (hf : summable f) : summable fun (b : β) => -f b :=
  has_sum.summable (has_sum.neg (summable.has_sum hf))

theorem summable.of_neg {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} (hf : summable fun (b : β) => -f b) : summable f := sorry

theorem summable_neg_iff {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} : (summable fun (b : β) => -f b) ↔ summable f :=
  { mp := summable.of_neg, mpr := summable.neg }

theorem has_sum.sub {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} {g : β → α} {a₁ : α} {a₂ : α} (hf : has_sum f a₁) (hg : has_sum g a₂) : has_sum (fun (b : β) => f b - g b) (a₁ - a₂) := sorry

theorem summable.sub {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} {g : β → α} (hf : summable f) (hg : summable g) : summable fun (b : β) => f b - g b :=
  has_sum.summable (has_sum.sub (summable.has_sum hf) (summable.has_sum hg))

theorem has_sum.has_sum_compl_iff {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} {a₁ : α} {a₂ : α} {s : set β} (hf : has_sum (f ∘ coe) a₁) : has_sum (f ∘ coe) a₂ ↔ has_sum f (a₁ + a₂) := sorry

theorem has_sum.has_sum_iff_compl {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} {a₁ : α} {a₂ : α} {s : set β} (hf : has_sum (f ∘ coe) a₁) : has_sum f a₂ ↔ has_sum (f ∘ coe) (a₂ - a₁) := sorry

theorem summable.summable_compl_iff {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} {s : set β} (hf : summable (f ∘ coe)) : summable (f ∘ coe) ↔ summable f := sorry

protected theorem finset.has_sum_compl_iff {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} {a : α} (s : finset β) : has_sum (fun (x : Subtype fun (x : β) => ¬x ∈ s) => f ↑x) a ↔ has_sum f (a + finset.sum s fun (i : β) => f i) := sorry

protected theorem finset.has_sum_iff_compl {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} {a : α} (s : finset β) : has_sum f a ↔ has_sum (fun (x : Subtype fun (x : β) => ¬x ∈ s) => f ↑x) (a - finset.sum s fun (i : β) => f i) :=
  has_sum.has_sum_iff_compl (finset.has_sum s f)

protected theorem finset.summable_compl_iff {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} (s : finset β) : (summable fun (x : Subtype fun (x : β) => ¬x ∈ s) => f ↑x) ↔ summable f :=
  summable.summable_compl_iff (finset.summable s f)

theorem set.finite.summable_compl_iff {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} {s : set β} (hs : set.finite s) : summable (f ∘ coe) ↔ summable f :=
  summable.summable_compl_iff (set.finite.summable hs f)

theorem tsum_neg {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} [t2_space α] (hf : summable f) : (tsum fun (b : β) => -f b) = -tsum fun (b : β) => f b :=
  has_sum.tsum_eq (has_sum.neg (summable.has_sum hf))

theorem tsum_sub {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} {g : β → α} [t2_space α] (hf : summable f) (hg : summable g) : (tsum fun (b : β) => f b - g b) = (tsum fun (b : β) => f b) - tsum fun (b : β) => g b :=
  has_sum.tsum_eq (has_sum.sub (summable.has_sum hf) (summable.has_sum hg))

theorem tsum_add_tsum_compl {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} [t2_space α] {s : set β} (hs : summable (f ∘ coe)) (hsc : summable (f ∘ coe)) : ((tsum fun (x : ↥s) => f ↑x) + tsum fun (x : ↥(sᶜ)) => f ↑x) = tsum fun (x : β) => f x :=
  Eq.symm (has_sum.tsum_eq (has_sum.add_compl (summable.has_sum hs) (summable.has_sum hsc)))

theorem sum_add_tsum_compl {α : Type u_1} {β : Type u_2} [add_comm_group α] [topological_space α] [topological_add_group α] {f : β → α} [t2_space α] {s : finset β} (hf : summable f) : ((finset.sum s fun (x : β) => f x) + tsum fun (x : ↥(↑sᶜ)) => f ↑x) = tsum fun (x : β) => f x :=
  Eq.symm
    (has_sum.tsum_eq
      (has_sum.add_compl (finset.has_sum s f) (summable.has_sum (iff.mpr (finset.summable_compl_iff s) hf))))

/-!
### Sums on subtypes

If `s` is a finset of `α`, we show that the summability of `f` in the whole space and on the subtype
`univ - s` are equivalent, and relate their sums. For a function defined on `ℕ`, we deduce the
formula `(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)`, in `sum_add_tsum_nat_add`.
-/

theorem has_sum_nat_add_iff {α : Type u_1} [add_comm_group α] [topological_space α] [topological_add_group α] {f : ℕ → α} (k : ℕ) {a : α} : has_sum (fun (n : ℕ) => f (n + k)) a ↔ has_sum f (a + finset.sum (finset.range k) fun (i : ℕ) => f i) := sorry

theorem summable_nat_add_iff {α : Type u_1} [add_comm_group α] [topological_space α] [topological_add_group α] {f : ℕ → α} (k : ℕ) : (summable fun (n : ℕ) => f (n + k)) ↔ summable f :=
  iff.symm
    (equiv.summable_iff_of_has_sum_iff (equiv.add_right (finset.sum (finset.range k) fun (i : ℕ) => f i))
      fun (a : α) => iff.symm (has_sum_nat_add_iff k))

theorem has_sum_nat_add_iff' {α : Type u_1} [add_comm_group α] [topological_space α] [topological_add_group α] {f : ℕ → α} (k : ℕ) {a : α} : has_sum (fun (n : ℕ) => f (n + k)) (a - finset.sum (finset.range k) fun (i : ℕ) => f i) ↔ has_sum f a := sorry

theorem sum_add_tsum_nat_add {α : Type u_1} [add_comm_group α] [topological_space α] [topological_add_group α] [t2_space α] {f : ℕ → α} (k : ℕ) (h : summable f) : ((finset.sum (finset.range k) fun (i : ℕ) => f i) + tsum fun (i : ℕ) => f (i + k)) = tsum fun (i : ℕ) => f i := sorry

theorem tsum_eq_zero_add {α : Type u_1} [add_comm_group α] [topological_space α] [topological_add_group α] [t2_space α] {f : ℕ → α} (hf : summable f) : (tsum fun (b : ℕ) => f b) = f 0 + tsum fun (b : ℕ) => f (b + 1) := sorry

/-- For `f : ℕ → α`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add {α : Type u_1} [add_comm_group α] [topological_space α] [topological_add_group α] [t2_space α] (f : ℕ → α) : filter.tendsto (fun (i : ℕ) => tsum fun (k : ℕ) => f (k + i)) filter.at_top (nhds 0) := sorry

theorem has_sum.mul_left {α : Type u_1} {β : Type u_2} [semiring α] [topological_space α] [topological_semiring α] {f : β → α} {a₁ : α} (a₂ : α) (h : has_sum f a₁) : has_sum (fun (b : β) => a₂ * f b) (a₂ * a₁) :=
  eq.mpr (id (Eq.refl (has_sum (fun (b : β) => a₂ * f b) (a₂ * a₁))))
    (eq.mp (Eq.refl (has_sum (⇑(add_monoid_hom.mul_left a₂) ∘ f) (coe_fn (add_monoid_hom.mul_left a₂) a₁)))
      (has_sum.map h (add_monoid_hom.mul_left a₂) (continuous.mul continuous_const continuous_id)))

theorem has_sum.mul_right {α : Type u_1} {β : Type u_2} [semiring α] [topological_space α] [topological_semiring α] {f : β → α} {a₁ : α} (a₂ : α) (hf : has_sum f a₁) : has_sum (fun (b : β) => f b * a₂) (a₁ * a₂) :=
  eq.mpr (id (Eq.refl (has_sum (fun (b : β) => f b * a₂) (a₁ * a₂))))
    (eq.mp (Eq.refl (has_sum (⇑(add_monoid_hom.mul_right a₂) ∘ f) (coe_fn (add_monoid_hom.mul_right a₂) a₁)))
      (has_sum.map hf (add_monoid_hom.mul_right a₂) (continuous.mul continuous_id continuous_const)))

theorem summable.mul_left {α : Type u_1} {β : Type u_2} [semiring α] [topological_space α] [topological_semiring α] {f : β → α} (a : α) (hf : summable f) : summable fun (b : β) => a * f b :=
  has_sum.summable (has_sum.mul_left a (summable.has_sum hf))

theorem summable.mul_right {α : Type u_1} {β : Type u_2} [semiring α] [topological_space α] [topological_semiring α] {f : β → α} (a : α) (hf : summable f) : summable fun (b : β) => f b * a :=
  has_sum.summable (has_sum.mul_right a (summable.has_sum hf))

theorem summable.tsum_mul_left {α : Type u_1} {β : Type u_2} [semiring α] [topological_space α] [topological_semiring α] {f : β → α} [t2_space α] (a : α) (hf : summable f) : (tsum fun (b : β) => a * f b) = a * tsum fun (b : β) => f b :=
  has_sum.tsum_eq (has_sum.mul_left a (summable.has_sum hf))

theorem summable.tsum_mul_right {α : Type u_1} {β : Type u_2} [semiring α] [topological_space α] [topological_semiring α] {f : β → α} [t2_space α] (a : α) (hf : summable f) : (tsum fun (b : β) => f b * a) = (tsum fun (b : β) => f b) * a :=
  has_sum.tsum_eq (has_sum.mul_right a (summable.has_sum hf))

theorem has_sum.smul {α : Type u_1} {β : Type u_2} {R : Type u_5} [semiring R] [topological_space R] [topological_space α] [add_comm_monoid α] [semimodule R α] [topological_semimodule R α] {f : β → α} {a : α} {r : R} (hf : has_sum f a) : has_sum (fun (z : β) => r • f z) (r • a) :=
  has_sum.map hf (const_smul_hom α r) (continuous.smul continuous_const continuous_id)

theorem summable.smul {α : Type u_1} {β : Type u_2} {R : Type u_5} [semiring R] [topological_space R] [topological_space α] [add_comm_monoid α] [semimodule R α] [topological_semimodule R α] {f : β → α} {r : R} (hf : summable f) : summable fun (z : β) => r • f z :=
  has_sum.summable (has_sum.smul (summable.has_sum hf))

theorem tsum_smul {α : Type u_1} {β : Type u_2} {R : Type u_5} [semiring R] [topological_space R] [topological_space α] [add_comm_monoid α] [semimodule R α] [topological_semimodule R α] {f : β → α} [t2_space α] {r : R} (hf : summable f) : (tsum fun (z : β) => r • f z) = r • tsum fun (z : β) => f z :=
  has_sum.tsum_eq (has_sum.smul (summable.has_sum hf))

theorem has_sum.div_const {α : Type u_1} {β : Type u_2} [division_ring α] [topological_space α] [topological_semiring α] {f : β → α} {a : α} (h : has_sum f a) (b : α) : has_sum (fun (x : β) => f x / b) (a / b) := sorry

theorem has_sum_mul_left_iff {α : Type u_1} {β : Type u_2} [division_ring α] [topological_space α] [topological_semiring α] {f : β → α} {a₁ : α} {a₂ : α} (h : a₂ ≠ 0) : has_sum f a₁ ↔ has_sum (fun (b : β) => a₂ * f b) (a₂ * a₁) := sorry

theorem has_sum_mul_right_iff {α : Type u_1} {β : Type u_2} [division_ring α] [topological_space α] [topological_semiring α] {f : β → α} {a₁ : α} {a₂ : α} (h : a₂ ≠ 0) : has_sum f a₁ ↔ has_sum (fun (b : β) => f b * a₂) (a₁ * a₂) := sorry

theorem summable_mul_left_iff {α : Type u_1} {β : Type u_2} [division_ring α] [topological_space α] [topological_semiring α] {f : β → α} {a : α} (h : a ≠ 0) : summable f ↔ summable fun (b : β) => a * f b := sorry

theorem summable_mul_right_iff {α : Type u_1} {β : Type u_2} [division_ring α] [topological_space α] [topological_semiring α] {f : β → α} {a : α} (h : a ≠ 0) : summable f ↔ summable fun (b : β) => f b * a := sorry

theorem tsum_mul_left {α : Type u_1} {β : Type u_2} [division_ring α] [topological_space α] [topological_semiring α] {f : β → α} {a : α} [t2_space α] : (tsum fun (x : β) => a * f x) = a * tsum fun (x : β) => f x := sorry

theorem tsum_mul_right {α : Type u_1} {β : Type u_2} [division_ring α] [topological_space α] [topological_semiring α] {f : β → α} {a : α} [t2_space α] : (tsum fun (x : β) => f x * a) = (tsum fun (x : β) => f x) * a := sorry

theorem has_sum_le {α : Type u_1} {β : Type u_2} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} {g : β → α} {a₁ : α} {a₂ : α} (h : ∀ (b : β), f b ≤ g b) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto' hf hg fun (s : finset β) => finset.sum_le_sum fun (b : β) (_x : b ∈ s) => h b

theorem has_sum_le_inj {α : Type u_1} {β : Type u_2} {γ : Type u_3} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} {a₁ : α} {a₂ : α} {g : γ → α} (i : β → γ) (hi : function.injective i) (hs : ∀ (c : γ), ¬c ∈ set.range i → 0 ≤ g c) (h : ∀ (b : β), f b ≤ g (i b)) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ ≤ a₂ := sorry

theorem tsum_le_tsum_of_inj {α : Type u_1} {β : Type u_2} {γ : Type u_3} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} {g : γ → α} (i : β → γ) (hi : function.injective i) (hs : ∀ (c : γ), ¬c ∈ set.range i → 0 ≤ g c) (h : ∀ (b : β), f b ≤ g (i b)) (hf : summable f) (hg : summable g) : tsum f ≤ tsum g :=
  has_sum_le_inj i hi hs h (summable.has_sum hf) (summable.has_sum hg)

theorem sum_le_has_sum {α : Type u_1} {β : Type u_2} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {a : α} {f : β → α} (s : finset β) (hs : ∀ (b : β), ¬b ∈ s → 0 ≤ f b) (hf : has_sum f a) : (finset.sum s fun (b : β) => f b) ≤ a := sorry

theorem le_has_sum {α : Type u_1} {β : Type u_2} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} {a : α} (hf : has_sum f a) (b : β) (hb : ∀ (b' : β), b' ≠ b → 0 ≤ f b') : f b ≤ a := sorry

theorem sum_le_tsum {α : Type u_1} {β : Type u_2} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} (s : finset β) (hs : ∀ (b : β), ¬b ∈ s → 0 ≤ f b) (hf : summable f) : (finset.sum s fun (b : β) => f b) ≤ tsum f :=
  sum_le_has_sum s hs (summable.has_sum hf)

theorem le_tsum {α : Type u_1} {β : Type u_2} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} (hf : summable f) (b : β) (hb : ∀ (b' : β), b' ≠ b → 0 ≤ f b') : f b ≤ tsum fun (b : β) => f b :=
  le_has_sum (summable.has_sum hf) b hb

theorem tsum_le_tsum {α : Type u_1} {β : Type u_2} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} {g : β → α} (h : ∀ (b : β), f b ≤ g b) (hf : summable f) (hg : summable g) : (tsum fun (b : β) => f b) ≤ tsum fun (b : β) => g b :=
  has_sum_le h (summable.has_sum hf) (summable.has_sum hg)

theorem has_sum.nonneg {α : Type u_1} {β : Type u_2} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {g : β → α} {a : α} (h : ∀ (b : β), 0 ≤ g b) (ha : has_sum g a) : 0 ≤ a :=
  has_sum_le h has_sum_zero ha

theorem has_sum.nonpos {α : Type u_1} {β : Type u_2} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {g : β → α} {a : α} (h : ∀ (b : β), g b ≤ 0) (ha : has_sum g a) : a ≤ 0 :=
  has_sum_le h ha has_sum_zero

theorem tsum_nonneg {α : Type u_1} {β : Type u_2} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {g : β → α} (h : ∀ (b : β), 0 ≤ g b) : 0 ≤ tsum fun (b : β) => g b := sorry

theorem tsum_nonpos {α : Type u_1} {β : Type u_2} [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} (h : ∀ (b : β), f b ≤ 0) : (tsum fun (b : β) => f b) ≤ 0 := sorry

theorem le_has_sum' {α : Type u_1} {β : Type u_2} [canonically_ordered_add_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} {a : α} (hf : has_sum f a) (b : β) : f b ≤ a :=
  le_has_sum hf b fun (_x : β) (_x_1 : _x ≠ b) => zero_le (f _x)

theorem le_tsum' {α : Type u_1} {β : Type u_2} [canonically_ordered_add_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} (hf : summable f) (b : β) : f b ≤ tsum fun (b : β) => f b :=
  le_tsum hf b fun (_x : β) (_x_1 : _x ≠ b) => zero_le (f _x)

theorem has_sum_zero_iff {α : Type u_1} {β : Type u_2} [canonically_ordered_add_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} : has_sum f 0 ↔ ∀ (x : β), f x = 0 := sorry

theorem tsum_eq_zero_iff {α : Type u_1} {β : Type u_2} [canonically_ordered_add_monoid α] [topological_space α] [order_closed_topology α] {f : β → α} (hf : summable f) : (tsum fun (i : β) => f i) = 0 ↔ ∀ (x : β), f x = 0 := sorry

theorem summable_iff_cauchy_seq_finset {α : Type u_1} {β : Type u_2} [add_comm_group α] [uniform_space α] [complete_space α] {f : β → α} : summable f ↔ cauchy_seq fun (s : finset β) => finset.sum s fun (b : β) => f b :=
  iff.symm cauchy_map_iff_exists_tendsto

theorem cauchy_seq_finset_iff_vanishing {α : Type u_1} {β : Type u_2} [add_comm_group α] [uniform_space α] [uniform_add_group α] {f : β → α} : (cauchy_seq fun (s : finset β) => finset.sum s fun (b : β) => f b) ↔
  ∀ (e : set α), e ∈ nhds 0 → ∃ (s : finset β), ∀ (t : finset β), disjoint t s → (finset.sum t fun (b : β) => f b) ∈ e := sorry

theorem summable_iff_vanishing {α : Type u_1} {β : Type u_2} [add_comm_group α] [uniform_space α] [uniform_add_group α] {f : β → α} [complete_space α] : summable f ↔
  ∀ (e : set α), e ∈ nhds 0 → ∃ (s : finset β), ∀ (t : finset β), disjoint t s → (finset.sum t fun (b : β) => f b) ∈ e := sorry

/- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a` -/

theorem summable.summable_of_eq_zero_or_self {α : Type u_1} {β : Type u_2} [add_comm_group α] [uniform_space α] [uniform_add_group α] {f : β → α} {g : β → α} [complete_space α] (hf : summable f) (h : ∀ (b : β), g b = 0 ∨ g b = f b) : summable g := sorry

protected theorem summable.indicator {α : Type u_1} {β : Type u_2} [add_comm_group α] [uniform_space α] [uniform_add_group α] {f : β → α} [complete_space α] (hf : summable f) (s : set β) : summable (set.indicator s f) :=
  summable.summable_of_eq_zero_or_self hf (set.indicator_eq_zero_or_self s f)

theorem summable.comp_injective {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α] [uniform_space α] [uniform_add_group α] {f : β → α} [complete_space α] {i : γ → β} (hf : summable f) (hi : function.injective i) : summable (f ∘ i) := sorry

theorem summable.subtype {α : Type u_1} {β : Type u_2} [add_comm_group α] [uniform_space α] [uniform_add_group α] {f : β → α} [complete_space α] (hf : summable f) (s : set β) : summable (f ∘ coe) :=
  summable.comp_injective hf subtype.coe_injective

theorem summable_subtype_and_compl {α : Type u_1} {β : Type u_2} [add_comm_group α] [uniform_space α] [uniform_add_group α] {f : β → α} [complete_space α] {s : set β} : ((summable fun (x : ↥s) => f ↑x) ∧ summable fun (x : ↥(sᶜ)) => f ↑x) ↔ summable f :=
  { mp := iff.mpr and_imp summable.add_compl,
    mpr := fun (h : summable f) => { left := summable.subtype h s, right := summable.subtype h (sᶜ) } }

theorem summable.sigma_factor {α : Type u_1} {β : Type u_2} [add_comm_group α] [uniform_space α] [uniform_add_group α] [complete_space α] {γ : β → Type u_3} {f : (sigma fun (b : β) => γ b) → α} (ha : summable f) (b : β) : summable fun (c : γ b) => f (sigma.mk b c) :=
  summable.comp_injective ha sigma_mk_injective

theorem summable.sigma {α : Type u_1} {β : Type u_2} [add_comm_group α] [uniform_space α] [uniform_add_group α] [complete_space α] [regular_space α] {γ : β → Type u_3} {f : (sigma fun (b : β) => γ b) → α} (ha : summable f) : summable fun (b : β) => tsum fun (c : γ b) => f (sigma.mk b c) :=
  summable.sigma' ha fun (b : β) => summable.sigma_factor ha b

theorem summable.prod_factor {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α] [uniform_space α] [uniform_add_group α] [complete_space α] {f : β × γ → α} (h : summable f) (b : β) : summable fun (c : γ) => f (b, c) :=
  summable.comp_injective h
    fun (c₁ c₂ : γ) (h : (fun (c : γ) => (b, c)) c₁ = (fun (c : γ) => (b, c)) c₂) => and.right (iff.mp prod.ext_iff h)

theorem tsum_sigma {α : Type u_1} {β : Type u_2} [add_comm_group α] [uniform_space α] [uniform_add_group α] [complete_space α] [regular_space α] {γ : β → Type u_3} {f : (sigma fun (b : β) => γ b) → α} (ha : summable f) : (tsum fun (p : sigma fun (b : β) => γ b) => f p) = tsum fun (b : β) => tsum fun (c : γ b) => f (sigma.mk b c) :=
  tsum_sigma' (fun (b : β) => summable.sigma_factor ha b) ha

theorem tsum_prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α] [uniform_space α] [uniform_add_group α] [complete_space α] [regular_space α] {f : β × γ → α} (h : summable f) : (tsum fun (p : β × γ) => f p) = tsum fun (b : β) => tsum fun (c : γ) => f (b, c) :=
  tsum_prod' h (summable.prod_factor h)

theorem tsum_comm {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_group α] [uniform_space α] [uniform_add_group α] [complete_space α] [regular_space α] {f : β → γ → α} (h : summable (function.uncurry f)) : (tsum fun (c : γ) => tsum fun (b : β) => f b c) = tsum fun (b : β) => tsum fun (c : γ) => f b c :=
  tsum_comm' h (summable.prod_factor h) (summable.prod_factor (summable.prod_symm h))

theorem summable.vanishing {α : Type u_1} {G : Type u_5} [topological_space G] [add_comm_group G] [topological_add_group G] {f : α → G} (hf : summable f) {e : set G} (he : e ∈ nhds 0) : ∃ (s : finset α), ∀ (t : finset α), disjoint t s → (finset.sum t fun (k : α) => f k) ∈ e := sorry

/-- Series divergence test: if `f` is a convergent series, then `f x` tends to zero along
`cofinite`. -/
theorem summable.tendsto_cofinite_zero {α : Type u_1} {G : Type u_5} [topological_space G] [add_comm_group G] [topological_add_group G] {f : α → G} (hf : summable f) : filter.tendsto f filter.cofinite (nhds 0) := sorry

theorem summable_abs_iff {α : Type u_1} {β : Type u_2} [linear_ordered_add_comm_group β] [uniform_space β] [uniform_add_group β] [complete_space β] {f : α → β} : (summable fun (x : α) => abs (f x)) ↔ summable f := sorry

theorem summable.of_abs {α : Type u_1} {β : Type u_2} [linear_ordered_add_comm_group β] [uniform_space β] [uniform_add_group β] [complete_space β] {f : α → β} : (summable fun (x : α) => abs (f x)) → summable f :=
  iff.mp summable_abs_iff

/-- If the extended distance between consequent points of a sequence is estimated
by a summable series of `nnreal`s, then the original sequence is a Cauchy sequence. -/
theorem cauchy_seq_of_edist_le_of_summable {α : Type u_1} [emetric_space α] {f : ℕ → α} (d : ℕ → nnreal) (hf : ∀ (n : ℕ), edist (f n) (f (Nat.succ n)) ≤ ↑(d n)) (hd : summable d) : cauchy_seq f := sorry

/-- If the distance between consequent points of a sequence is estimated by a summable series,
then the original sequence is a Cauchy sequence. -/
theorem cauchy_seq_of_dist_le_of_summable {α : Type u_1} [metric_space α] {f : ℕ → α} (d : ℕ → ℝ) (hf : ∀ (n : ℕ), dist (f n) (f (Nat.succ n)) ≤ d n) (hd : summable d) : cauchy_seq f := sorry

theorem cauchy_seq_of_summable_dist {α : Type u_1} [metric_space α] {f : ℕ → α} (h : summable fun (n : ℕ) => dist (f n) (f (Nat.succ n))) : cauchy_seq f :=
  cauchy_seq_of_dist_le_of_summable (fun (n : ℕ) => dist (f n) (f (Nat.succ n)))
    (fun (_x : ℕ) => le_refl (dist (f _x) (f (Nat.succ _x)))) h

theorem dist_le_tsum_of_dist_le_of_tendsto {α : Type u_1} [metric_space α] {f : ℕ → α} (d : ℕ → ℝ) (hf : ∀ (n : ℕ), dist (f n) (f (Nat.succ n)) ≤ d n) (hd : summable d) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) (n : ℕ) : dist (f n) a ≤ tsum fun (m : ℕ) => d (n + m) := sorry

theorem dist_le_tsum_of_dist_le_of_tendsto₀ {α : Type u_1} [metric_space α] {f : ℕ → α} (d : ℕ → ℝ) (hf : ∀ (n : ℕ), dist (f n) (f (Nat.succ n)) ≤ d n) (hd : summable d) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) : dist (f 0) a ≤ tsum d := sorry

theorem dist_le_tsum_dist_of_tendsto {α : Type u_1} [metric_space α] {f : ℕ → α} (h : summable fun (n : ℕ) => dist (f n) (f (Nat.succ n))) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) (n : ℕ) : dist (f n) a ≤ tsum fun (m : ℕ) => dist (f (n + m)) (f (Nat.succ (n + m))) :=
  (fun (this : dist (f n) a ≤ tsum fun (m : ℕ) => (fun (n : ℕ) => dist (f n) (f (Nat.succ n))) (n + m)) => this)
    (dist_le_tsum_of_dist_le_of_tendsto (fun (n : ℕ) => dist (f n) (f (Nat.succ n)))
      (fun (_x : ℕ) => le_refl (dist (f _x) (f (Nat.succ _x)))) h ha n)

theorem dist_le_tsum_dist_of_tendsto₀ {α : Type u_1} [metric_space α] {f : ℕ → α} (h : summable fun (n : ℕ) => dist (f n) (f (Nat.succ n))) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) : dist (f 0) a ≤ tsum fun (n : ℕ) => dist (f n) (f (Nat.succ n)) := sorry

