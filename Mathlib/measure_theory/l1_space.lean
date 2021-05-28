/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.ae_eq_fun
import Mathlib.PostPort

universes u_1 u_2 u_3 u_5 u_4 u_6 

namespace Mathlib

/-!
# Integrable functions and `L¹` space

In the first part of this file, the predicate `integrable` is defined and basic properties of
integrable functions are proved.

In the second part, the space `L¹` of equivalence classes of integrable functions under the relation
of being almost everywhere equal is defined as a subspace of the space `L⁰`. See the file
`src/measure_theory/ae_eq_fun.lean` for information on `L⁰` space.

## Notation

* `α →₁ β` is the type of `L¹` space, where `α` is a `measure_space` and `β` is a `normed_group`
  with a `second_countable_topology`. `f : α →ₘ β` is a "function" in `L¹`. In comments, `[f]` is
  also used to denote an `L¹` function.

  `₁` can be typed as `\1`.

## Main definitions

* Let `f : α → β` be a function, where `α` is a `measure_space` and `β` a `normed_group`.
  Then `has_finite_integral f` means `(∫⁻ a, nnnorm (f a)) < ⊤`.

* If `β` is moreover a `measurable_space` then `f` is called `integrable` if
  `f` is `measurable` and `has_finite_integral f` holds.

* The space `L¹` is defined as a subspace of `L⁰` :
  An `ae_eq_fun` `[f] : α →ₘ β` is in the space `L¹` if `edist [f] 0 < ⊤`, which means
  `(∫⁻ a, edist (f a) 0) < ⊤` if we expand the definition of `edist` in `L⁰`.

## Main statements

`L¹`, as a subspace, inherits most of the structures of `L⁰`.

## Implementation notes

Maybe `integrable f` should be mean `(∫⁻ a, edist (f a) 0) < ⊤`, so that `integrable` and
`ae_eq_fun.integrable` are more aligned. But in the end one can use the lemma
`lintegral_nnnorm_eq_lintegral_edist : (∫⁻ a, nnnorm (f a)) = (∫⁻ a, edist (f a) 0)` to switch the
two forms.

To prove something for an arbitrary integrable function, a useful theorem is
`integrable.induction` in the file `set_integral`.

## Tags

integrable, function space, l1

-/

namespace measure_theory


/-! ### Some results about the Lebesgue integral involving a normed group -/

theorem lintegral_nnnorm_eq_lintegral_edist {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] (f : α → β) : (lintegral μ fun (a : α) => ↑(nnnorm (f a))) = lintegral μ fun (a : α) => edist (f a) 0 := sorry

theorem lintegral_norm_eq_lintegral_edist {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] (f : α → β) : (lintegral μ fun (a : α) => ennreal.of_real (norm (f a))) = lintegral μ fun (a : α) => edist (f a) 0 := sorry

theorem lintegral_edist_triangle {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [topological_space.second_countable_topology β] [measurable_space β] [opens_measurable_space β] {f : α → β} {g : α → β} {h : α → β} (hf : ae_measurable f) (hg : ae_measurable g) (hh : ae_measurable h) : (lintegral μ fun (a : α) => edist (f a) (g a)) ≤
  (lintegral μ fun (a : α) => edist (f a) (h a)) + lintegral μ fun (a : α) => edist (g a) (h a) := sorry

theorem lintegral_nnnorm_zero {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] : (lintegral μ fun (a : α) => ↑(nnnorm 0)) = 0 := sorry

theorem lintegral_nnnorm_add {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [normed_group β] [normed_group γ] [measurable_space β] [opens_measurable_space β] [measurable_space γ] [opens_measurable_space γ] {f : α → β} {g : α → γ} (hf : ae_measurable f) (hg : ae_measurable g) : (lintegral μ fun (a : α) => ↑(nnnorm (f a)) + ↑(nnnorm (g a))) =
  (lintegral μ fun (a : α) => ↑(nnnorm (f a))) + lintegral μ fun (a : α) => ↑(nnnorm (g a)) :=
  lintegral_add' (ae_measurable.ennnorm hf) (ae_measurable.ennnorm hg)

theorem lintegral_nnnorm_neg {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {f : α → β} : (lintegral μ fun (a : α) => ↑(nnnorm (Neg.neg f a))) = lintegral μ fun (a : α) => ↑(nnnorm (f a)) := sorry

/-! ### The predicate `has_finite_integral` -/

/-- `has_finite_integral f μ` means that the integral `∫⁻ a, ∥f a∥ ∂μ` is finite.
  `has_finite_integral f` means `has_finite_integral f volume`. -/
def has_finite_integral {α : Type u_1} {β : Type u_2} [measurable_space α] [normed_group β] (f : α → β) (μ : autoParam (measure α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.measure_theory.volume_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory") "volume_tac")
    []))  :=
  (lintegral μ fun (a : α) => ↑(nnnorm (f a))) < ⊤

theorem has_finite_integral_iff_norm {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] (f : α → β) : has_finite_integral f ↔ (lintegral μ fun (a : α) => ennreal.of_real (norm (f a))) < ⊤ := sorry

theorem has_finite_integral_iff_edist {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] (f : α → β) : has_finite_integral f ↔ (lintegral μ fun (a : α) => edist (f a) 0) < ⊤ := sorry

theorem has_finite_integral_iff_of_real {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ} (h : filter.eventually_le (measure.ae μ) 0 f) : has_finite_integral f ↔ (lintegral μ fun (a : α) => ennreal.of_real (f a)) < ⊤ := sorry

theorem has_finite_integral.mono {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [normed_group β] [normed_group γ] {f : α → β} {g : α → γ} (hg : has_finite_integral g) (h : filter.eventually (fun (a : α) => norm (f a) ≤ norm (g a)) (measure.ae μ)) : has_finite_integral f := sorry

theorem has_finite_integral.mono' {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {f : α → β} {g : α → ℝ} (hg : has_finite_integral g) (h : filter.eventually (fun (a : α) => norm (f a) ≤ g a) (measure.ae μ)) : has_finite_integral f :=
  has_finite_integral.mono hg
    (filter.eventually.mono h fun (x : α) (hx : norm (f x) ≤ g x) => le_trans hx (le_abs_self (g x)))

theorem has_finite_integral.congr' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [normed_group β] [normed_group γ] {f : α → β} {g : α → γ} (hf : has_finite_integral f) (h : filter.eventually (fun (a : α) => norm (f a) = norm (g a)) (measure.ae μ)) : has_finite_integral g :=
  has_finite_integral.mono hf (filter.eventually_eq.le (filter.eventually_eq.symm h))

theorem has_finite_integral_congr' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [normed_group β] [normed_group γ] {f : α → β} {g : α → γ} (h : filter.eventually (fun (a : α) => norm (f a) = norm (g a)) (measure.ae μ)) : has_finite_integral f ↔ has_finite_integral g :=
  { mp := fun (hf : has_finite_integral f) => has_finite_integral.congr' hf h,
    mpr := fun (hg : has_finite_integral g) => has_finite_integral.congr' hg (filter.eventually_eq.symm h) }

theorem has_finite_integral.congr {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {f : α → β} {g : α → β} (hf : has_finite_integral f) (h : filter.eventually_eq (measure.ae μ) f g) : has_finite_integral g :=
  has_finite_integral.congr' hf (filter.eventually_eq.fun_comp h norm)

theorem has_finite_integral_congr {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {f : α → β} {g : α → β} (h : filter.eventually_eq (measure.ae μ) f g) : has_finite_integral f ↔ has_finite_integral g :=
  has_finite_integral_congr' (filter.eventually_eq.fun_comp h norm)

theorem has_finite_integral_const_iff {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {c : β} : (has_finite_integral fun (x : α) => c) ↔ c = 0 ∨ coe_fn μ set.univ < ⊤ := sorry

theorem has_finite_integral_const {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [finite_measure μ] (c : β) : has_finite_integral fun (x : α) => c :=
  iff.mpr has_finite_integral_const_iff (Or.inr (measure_lt_top μ set.univ))

theorem has_finite_integral_of_bounded {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [finite_measure μ] {f : α → β} {C : ℝ} (hC : filter.eventually (fun (a : α) => norm (f a) ≤ C) (measure.ae μ)) : has_finite_integral f :=
  has_finite_integral.mono' (has_finite_integral_const C) hC

theorem has_finite_integral.mono_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} {ν : measure α} [normed_group β] {f : α → β} (h : has_finite_integral f) (hμ : μ ≤ ν) : has_finite_integral f :=
  lt_of_le_of_lt (lintegral_mono' hμ (le_refl fun (a : α) => ↑(nnnorm (f a)))) h

theorem has_finite_integral.add_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} {ν : measure α} [normed_group β] {f : α → β} (hμ : has_finite_integral f) (hν : has_finite_integral f) : has_finite_integral f := sorry

theorem has_finite_integral.left_of_add_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} {ν : measure α} [normed_group β] {f : α → β} (h : has_finite_integral f) : has_finite_integral f :=
  has_finite_integral.mono_measure h (measure.le_add_right (le_refl μ))

theorem has_finite_integral.right_of_add_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} {ν : measure α} [normed_group β] {f : α → β} (h : has_finite_integral f) : has_finite_integral f :=
  has_finite_integral.mono_measure h (measure.le_add_left (le_refl ν))

@[simp] theorem has_finite_integral_add_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} {ν : measure α} [normed_group β] {f : α → β} : has_finite_integral f ↔ has_finite_integral f ∧ has_finite_integral f := sorry

theorem has_finite_integral.smul_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {f : α → β} (h : has_finite_integral f) {c : ennreal} (hc : c < ⊤) : has_finite_integral f := sorry

@[simp] theorem has_finite_integral_zero_measure {α : Type u_1} {β : Type u_2} [measurable_space α] [normed_group β] (f : α → β) : has_finite_integral f := sorry

@[simp] theorem has_finite_integral_zero (α : Type u_1) (β : Type u_2) [measurable_space α] (μ : measure α) [normed_group β] : has_finite_integral fun (a : α) => 0 := sorry

theorem has_finite_integral.neg {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {f : α → β} (hfi : has_finite_integral f) : has_finite_integral (-f) := sorry

@[simp] theorem has_finite_integral_neg_iff {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {f : α → β} : has_finite_integral (-f) ↔ has_finite_integral f :=
  { mp := fun (h : has_finite_integral (-f)) => neg_neg f ▸ has_finite_integral.neg h, mpr := has_finite_integral.neg }

theorem has_finite_integral.norm {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {f : α → β} (hfi : has_finite_integral f) : has_finite_integral fun (a : α) => norm (f a) := sorry

theorem has_finite_integral_norm_iff {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] (f : α → β) : (has_finite_integral fun (a : α) => norm (f a)) ↔ has_finite_integral f :=
  has_finite_integral_congr' (filter.eventually_of_forall fun (x : α) => norm_norm (f x))

theorem all_ae_of_real_F_le_bound {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {F : ℕ → α → β} {bound : α → ℝ} (h : ∀ (n : ℕ), filter.eventually (fun (a : α) => norm (F n a) ≤ bound a) (measure.ae μ)) (n : ℕ) : filter.eventually (fun (a : α) => ennreal.of_real (norm (F n a)) ≤ ennreal.of_real (bound a)) (measure.ae μ) :=
  filter.eventually.mono (h n) fun (a : α) (h : norm (F n a) ≤ bound a) => ennreal.of_real_le_of_real h

theorem all_ae_tendsto_of_real_norm {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {F : ℕ → α → β} {f : α → β} (h : filter.eventually (fun (a : α) => filter.tendsto (fun (n : ℕ) => F n a) filter.at_top (nhds (f a))) (measure.ae μ)) : filter.eventually
  (fun (a : α) =>
    filter.tendsto (fun (n : ℕ) => ennreal.of_real (norm (F n a))) filter.at_top (nhds (ennreal.of_real (norm (f a)))))
  (measure.ae μ) :=
  filter.eventually.mono h
    fun (a : α) (h : filter.tendsto (fun (n : ℕ) => F n a) filter.at_top (nhds (f a))) =>
      ennreal.tendsto_of_real (filter.tendsto.comp (continuous.tendsto continuous_norm (f a)) h)

theorem all_ae_of_real_f_le_bound {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {F : ℕ → α → β} {f : α → β} {bound : α → ℝ} (h_bound : ∀ (n : ℕ), filter.eventually (fun (a : α) => norm (F n a) ≤ bound a) (measure.ae μ)) (h_lim : filter.eventually (fun (a : α) => filter.tendsto (fun (n : ℕ) => F n a) filter.at_top (nhds (f a))) (measure.ae μ)) : filter.eventually (fun (a : α) => ennreal.of_real (norm (f a)) ≤ ennreal.of_real (bound a)) (measure.ae μ) := sorry

theorem has_finite_integral_of_dominated_convergence {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {F : ℕ → α → β} {f : α → β} {bound : α → ℝ} (bound_has_finite_integral : has_finite_integral bound) (h_bound : ∀ (n : ℕ), filter.eventually (fun (a : α) => norm (F n a) ≤ bound a) (measure.ae μ)) (h_lim : filter.eventually (fun (a : α) => filter.tendsto (fun (n : ℕ) => F n a) filter.at_top (nhds (f a))) (measure.ae μ)) : has_finite_integral f := sorry

/- `∥F n a∥ ≤ bound a` and `∥F n a∥ --> ∥f a∥` implies `∥f a∥ ≤ bound a`,
  and so `∫ ∥f∥ ≤ ∫ bound < ⊤` since `bound` is has_finite_integral -/

theorem tendsto_lintegral_norm_of_dominated_convergence {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [borel_space β] [topological_space.second_countable_topology β] {F : ℕ → α → β} {f : α → β} {bound : α → ℝ} (F_measurable : ∀ (n : ℕ), ae_measurable (F n)) (f_measurable : ae_measurable f) (bound_has_finite_integral : has_finite_integral bound) (h_bound : ∀ (n : ℕ), filter.eventually (fun (a : α) => norm (F n a) ≤ bound a) (measure.ae μ)) (h_lim : filter.eventually (fun (a : α) => filter.tendsto (fun (n : ℕ) => F n a) filter.at_top (nhds (f a))) (measure.ae μ)) : filter.tendsto (fun (n : ℕ) => lintegral μ fun (a : α) => ennreal.of_real (norm (F n a - f a))) filter.at_top (nhds 0) := sorry

/- `∥F n a∥ ≤ bound a` and `F n a --> f a` implies `∥f a∥ ≤ bound a`, and thus by the
  triangle inequality, have `∥F n a - f a∥ ≤ 2 * (bound a). -/

/- On the other hand, `F n a --> f a` implies that `∥F n a - f a∥ --> 0`  -/

/- Therefore, by the dominated convergence theorem for nonnegative integration, have
  ` ∫ ∥f a - F n a∥ --> 0 ` -/

/-! Lemmas used for defining the positive part of a `L¹` function -/

theorem has_finite_integral.max_zero {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ} (hf : has_finite_integral f) : has_finite_integral fun (a : α) => max (f a) 0 := sorry

theorem has_finite_integral.min_zero {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ} (hf : has_finite_integral f) : has_finite_integral fun (a : α) => min (f a) 0 := sorry

theorem has_finite_integral.smul {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {𝕜 : Type u_5} [normed_field 𝕜] [normed_space 𝕜 β] (c : 𝕜) {f : α → β} : has_finite_integral f → has_finite_integral (c • f) := sorry

theorem has_finite_integral_smul_iff {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] {𝕜 : Type u_5} [normed_field 𝕜] [normed_space 𝕜 β] {c : 𝕜} (hc : c ≠ 0) (f : α → β) : has_finite_integral (c • f) ↔ has_finite_integral f := sorry

theorem has_finite_integral.const_mul {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ} (h : has_finite_integral f) (c : ℝ) : has_finite_integral fun (x : α) => c * f x :=
  has_finite_integral.smul c h

theorem has_finite_integral.mul_const {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ} (h : has_finite_integral f) (c : ℝ) : has_finite_integral fun (x : α) => f x * c := sorry

/-! ### The predicate `integrable` -/

/-- `integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ∥f a∥ ∂μ` is finite.
  `integrable f` means `integrable f volume`. -/
def integrable {α : Type u_1} {β : Type u_2} [measurable_space α] [normed_group β] [measurable_space β] (f : α → β) (μ : autoParam (measure α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.measure_theory.volume_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory") "volume_tac")
    []))  :=
  ae_measurable f ∧ has_finite_integral f

theorem integrable.ae_measurable {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] {f : α → β} (hf : integrable f) : ae_measurable f :=
  and.left hf

theorem integrable.has_finite_integral {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] {f : α → β} (hf : integrable f) : has_finite_integral f :=
  and.right hf

theorem integrable.mono {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [normed_group β] [normed_group γ] [measurable_space β] [measurable_space γ] {f : α → β} {g : α → γ} (hg : integrable g) (hf : ae_measurable f) (h : filter.eventually (fun (a : α) => norm (f a) ≤ norm (g a)) (measure.ae μ)) : integrable f :=
  { left := hf, right := has_finite_integral.mono (integrable.has_finite_integral hg) h }

theorem integrable.mono' {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] {f : α → β} {g : α → ℝ} (hg : integrable g) (hf : ae_measurable f) (h : filter.eventually (fun (a : α) => norm (f a) ≤ g a) (measure.ae μ)) : integrable f :=
  { left := hf, right := has_finite_integral.mono' (integrable.has_finite_integral hg) h }

theorem integrable.congr' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [normed_group β] [normed_group γ] [measurable_space β] [measurable_space γ] {f : α → β} {g : α → γ} (hf : integrable f) (hg : ae_measurable g) (h : filter.eventually (fun (a : α) => norm (f a) = norm (g a)) (measure.ae μ)) : integrable g :=
  { left := hg, right := has_finite_integral.congr' (integrable.has_finite_integral hf) h }

theorem integrable_congr' {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [normed_group β] [normed_group γ] [measurable_space β] [measurable_space γ] {f : α → β} {g : α → γ} (hf : ae_measurable f) (hg : ae_measurable g) (h : filter.eventually (fun (a : α) => norm (f a) = norm (g a)) (measure.ae μ)) : integrable f ↔ integrable g :=
  { mp := fun (h2f : integrable f) => integrable.congr' h2f hg h,
    mpr := fun (h2g : integrable g) => integrable.congr' h2g hf (filter.eventually_eq.symm h) }

theorem integrable.congr {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] {f : α → β} {g : α → β} (hf : integrable f) (h : filter.eventually_eq (measure.ae μ) f g) : integrable g :=
  { left := ae_measurable.congr (and.left hf) h, right := has_finite_integral.congr (and.right hf) h }

theorem integrable_congr {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] {f : α → β} {g : α → β} (h : filter.eventually_eq (measure.ae μ) f g) : integrable f ↔ integrable g :=
  { mp := fun (hf : integrable f) => integrable.congr hf h,
    mpr := fun (hg : integrable g) => integrable.congr hg (filter.eventually_eq.symm h) }

theorem integrable_const_iff {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] {c : β} : (integrable fun (x : α) => c) ↔ c = 0 ∨ coe_fn μ set.univ < ⊤ := sorry

theorem integrable_const {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [finite_measure μ] (c : β) : integrable fun (x : α) => c :=
  iff.mpr integrable_const_iff (Or.inr (measure_lt_top μ set.univ))

theorem integrable.mono_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} {ν : measure α} [normed_group β] [measurable_space β] {f : α → β} (h : integrable f) (hμ : μ ≤ ν) : integrable f :=
  { left := ae_measurable.mono_measure (integrable.ae_measurable h) hμ,
    right := has_finite_integral.mono_measure (integrable.has_finite_integral h) hμ }

theorem integrable.add_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} {ν : measure α} [normed_group β] [measurable_space β] {f : α → β} (hμ : integrable f) (hν : integrable f) : integrable f :=
  { left := ae_measurable.add_measure (integrable.ae_measurable hμ) (integrable.ae_measurable hν),
    right := has_finite_integral.add_measure (integrable.has_finite_integral hμ) (integrable.has_finite_integral hν) }

theorem integrable.left_of_add_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} {ν : measure α} [normed_group β] [measurable_space β] {f : α → β} (h : integrable f) : integrable f :=
  integrable.mono_measure h (measure.le_add_right (le_refl μ))

theorem integrable.right_of_add_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} {ν : measure α} [normed_group β] [measurable_space β] {f : α → β} (h : integrable f) : integrable f :=
  integrable.mono_measure h (measure.le_add_left (le_refl ν))

@[simp] theorem integrable_add_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} {ν : measure α} [normed_group β] [measurable_space β] {f : α → β} : integrable f ↔ integrable f ∧ integrable f :=
  { mp :=
      fun (h : integrable f) => { left := integrable.left_of_add_measure h, right := integrable.right_of_add_measure h },
    mpr := fun (h : integrable f ∧ integrable f) => integrable.add_measure (and.left h) (and.right h) }

theorem integrable.smul_measure {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] {f : α → β} (h : integrable f) {c : ennreal} (hc : c < ⊤) : integrable f :=
  { left := ae_measurable.smul_measure (integrable.ae_measurable h) c,
    right := has_finite_integral.smul_measure (integrable.has_finite_integral h) hc }

theorem integrable_map_measure {α : Type u_1} {β : Type u_2} {δ : Type u_4} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [measurable_space δ] [opens_measurable_space β] {f : α → δ} {g : δ → β} (hg : ae_measurable g) (hf : measurable f) : integrable g ↔ integrable (g ∘ f) := sorry

theorem lintegral_edist_lt_top {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] {f : α → β} {g : α → β} (hf : integrable f) (hg : integrable g) : (lintegral μ fun (a : α) => edist (f a) (g a)) < ⊤ := sorry

@[simp] theorem integrable_zero (α : Type u_1) (β : Type u_2) [measurable_space α] (μ : measure α) [normed_group β] [measurable_space β] : integrable fun (_x : α) => 0 := sorry

theorem integrable.add' {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [opens_measurable_space β] {f : α → β} {g : α → β} (hf : integrable f) (hg : integrable g) : has_finite_integral (f + g) := sorry

theorem integrable.add {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [borel_space β] [topological_space.second_countable_topology β] {f : α → β} {g : α → β} (hf : integrable f) (hg : integrable g) : integrable (f + g) :=
  { left := ae_measurable.add (integrable.ae_measurable hf) (integrable.ae_measurable hg),
    right := integrable.add' hf hg }

theorem integrable_finset_sum {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] {ι : Type u_3} [borel_space β] [topological_space.second_countable_topology β] (s : finset ι) {f : ι → α → β} (hf : ∀ (i : ι), integrable (f i)) : integrable fun (a : α) => finset.sum s fun (i : ι) => f i a := sorry

theorem integrable.neg {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [borel_space β] {f : α → β} (hf : integrable f) : integrable (-f) :=
  { left := ae_measurable.neg (integrable.ae_measurable hf),
    right := has_finite_integral.neg (integrable.has_finite_integral hf) }

@[simp] theorem integrable_neg_iff {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [borel_space β] {f : α → β} : integrable (-f) ↔ integrable f :=
  { mp := fun (h : integrable (-f)) => neg_neg f ▸ integrable.neg h, mpr := integrable.neg }

theorem integrable.sub' {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [opens_measurable_space β] {f : α → β} {g : α → β} (hf : integrable f) (hg : integrable g) : has_finite_integral (f - g) := sorry

theorem integrable.sub {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [borel_space β] [topological_space.second_countable_topology β] {f : α → β} {g : α → β} (hf : integrable f) (hg : integrable g) : integrable (f - g) := sorry

theorem integrable.norm {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [opens_measurable_space β] {f : α → β} (hf : integrable f) : integrable fun (a : α) => norm (f a) :=
  { left := ae_measurable.norm (integrable.ae_measurable hf),
    right := has_finite_integral.norm (integrable.has_finite_integral hf) }

theorem integrable_norm_iff {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [opens_measurable_space β] {f : α → β} (hf : ae_measurable f) : (integrable fun (a : α) => norm (f a)) ↔ integrable f := sorry

theorem integrable.prod_mk {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] {μ : measure α} [normed_group β] [normed_group γ] [measurable_space β] [measurable_space γ] [opens_measurable_space β] [opens_measurable_space γ] {f : α → β} {g : α → γ} (hf : integrable f) (hg : integrable g) : integrable fun (x : α) => (f x, g x) := sorry

/-! ### Lemmas used for defining the positive part of a `L¹` function -/

theorem integrable.max_zero {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ} (hf : integrable f) : integrable fun (a : α) => max (f a) 0 :=
  { left := ae_measurable.max (integrable.ae_measurable hf) (measurable.ae_measurable measurable_const),
    right := has_finite_integral.max_zero (integrable.has_finite_integral hf) }

theorem integrable.min_zero {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ} (hf : integrable f) : integrable fun (a : α) => min (f a) 0 :=
  { left := ae_measurable.min (integrable.ae_measurable hf) (measurable.ae_measurable measurable_const),
    right := has_finite_integral.min_zero (integrable.has_finite_integral hf) }

theorem integrable.smul {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] {𝕜 : Type u_5} [normed_field 𝕜] [normed_space 𝕜 β] [borel_space β] (c : 𝕜) {f : α → β} (hf : integrable f) : integrable (c • f) :=
  { left := ae_measurable.const_smul (integrable.ae_measurable hf) c,
    right := has_finite_integral.smul c (integrable.has_finite_integral hf) }

theorem integrable_smul_iff {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] {𝕜 : Type u_5} [normed_field 𝕜] [normed_space 𝕜 β] [borel_space β] {c : 𝕜} (hc : c ≠ 0) (f : α → β) : integrable (c • f) ↔ integrable f :=
  and_congr (ae_measurable_const_smul_iff hc) (has_finite_integral_smul_iff hc f)

theorem integrable.const_mul {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ} (h : integrable f) (c : ℝ) : integrable fun (x : α) => c * f x :=
  integrable.smul c h

theorem integrable.mul_const {α : Type u_1} [measurable_space α] {μ : measure α} {f : α → ℝ} (h : integrable f) (c : ℝ) : integrable fun (x : α) => f x * c := sorry

theorem integrable_smul_const {α : Type u_1} [measurable_space α] {μ : measure α} {𝕜 : Type u_5} [nondiscrete_normed_field 𝕜] [complete_space 𝕜] [measurable_space 𝕜] [borel_space 𝕜] {E : Type u_6} [normed_group E] [normed_space 𝕜 E] [measurable_space E] [borel_space E] {f : α → 𝕜} {c : E} (hc : c ≠ 0) : (integrable fun (x : α) => f x • c) ↔ integrable f := sorry

/-! ### The predicate `integrable` on measurable functions modulo a.e.-equality -/

namespace ae_eq_fun


/-- A class of almost everywhere equal functions is `integrable` if it has a finite distance to
  the origin. It means the same thing as the predicate `integrable` over functions. -/
def integrable {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] (f : ae_eq_fun α β μ)  :=
  f ∈ emetric.ball 0 ⊤

theorem integrable_mk {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] {f : α → β} (hf : ae_measurable f) : integrable (mk f hf) ↔ integrable f := sorry

theorem integrable_coe_fn {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] {f : ae_eq_fun α β μ} : integrable ⇑f ↔ integrable f := sorry

theorem integrable_zero {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] : integrable 0 :=
  emetric.mem_ball_self ennreal.coe_lt_top

theorem integrable.add {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] {f : ae_eq_fun α β μ} {g : ae_eq_fun α β μ} : integrable f → integrable g → integrable (f + g) := sorry

theorem integrable.neg {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] {f : ae_eq_fun α β μ} : integrable f → integrable (-f) := sorry

theorem integrable.sub {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] {f : ae_eq_fun α β μ} {g : ae_eq_fun α β μ} (hf : integrable f) (hg : integrable g) : integrable (f - g) :=
  integrable.add hf (integrable.neg hg)

protected theorem is_add_subgroup {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] : is_add_subgroup (emetric.ball 0 ⊤) :=
  is_add_subgroup.mk fun (_x : ae_eq_fun α β μ) => integrable.neg

theorem integrable.smul {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] {𝕜 : Type u_5} [normed_field 𝕜] [normed_space 𝕜 β] {c : 𝕜} {f : ae_eq_fun α β μ} : integrable f → integrable (c • f) := sorry

end ae_eq_fun


/-! ### The `L¹` space of functions -/

/-- The space of equivalence classes of integrable (and measurable) functions, where two integrable
    functions are equivalent if they agree almost everywhere, i.e., they differ on a set of measure
    `0`. -/
def l1 (α : Type u_1) (β : Type u_2) [measurable_space α] [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] (μ : measure α)  :=
  Subtype fun (f : ae_eq_fun α β μ) => ae_eq_fun.integrable f

namespace l1


protected instance measure_theory.ae_eq_fun.has_coe {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] : has_coe (l1 α β μ) (ae_eq_fun α β μ) :=
  Mathlib.coe_subtype

protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] : has_coe_to_fun (l1 α β μ) :=
  has_coe_to_fun.mk (fun (f : l1 α β μ) => α → β) fun (f : l1 α β μ) => ⇑↑f

@[simp] theorem coe_coe {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] (f : l1 α β μ) : ⇑↑f = ⇑f :=
  rfl

protected theorem eq {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] {f : l1 α β μ} {g : l1 α β μ} : ↑f = ↑g → f = g :=
  subtype.eq

protected theorem eq_iff {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] {f : l1 α β μ} {g : l1 α β μ} : ↑f = ↑g ↔ f = g :=
  { mp := l1.eq, mpr := congr_arg coe }

/- TODO : order structure of l1-/

/-- `L¹` space forms a `emetric_space`, with the emetric being inherited from almost everywhere
  functions, i.e., `edist f g = ∫⁻ a, edist (f a) (g a)`. -/
protected instance emetric_space {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] : emetric_space (l1 α β μ) :=
  subtype.emetric_space

/-- `L¹` space forms a `metric_space`, with the metric being inherited from almost everywhere
  functions, i.e., `edist f g = ennreal.to_real (∫⁻ a, edist (f a) (g a))`. -/
protected instance metric_space {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [opens_measurable_space β] : metric_space (l1 α β μ) :=
  metric_space_emetric_ball 0 ⊤

protected instance add_comm_group {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] : add_comm_group (l1 α β μ) :=
  subtype.add_comm_group

protected instance inhabited {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] : Inhabited (l1 α β μ) :=
  { default := 0 }

@[simp] theorem coe_zero {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] : ↑0 = 0 :=
  rfl

@[simp] theorem coe_add {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) (g : l1 α β μ) : ↑(f + g) = ↑f + ↑g :=
  rfl

@[simp] theorem coe_neg {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : ↑(-f) = -↑f :=
  rfl

@[simp] theorem coe_sub {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) (g : l1 α β μ) : ↑(f - g) = ↑f - ↑g :=
  rfl

@[simp] theorem edist_eq {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) (g : l1 α β μ) : edist f g = edist ↑f ↑g :=
  rfl

theorem dist_eq {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) (g : l1 α β μ) : dist f g = ennreal.to_real (edist ↑f ↑g) :=
  rfl

/-- The norm on `L¹` space is defined to be `∥f∥ = ∫⁻ a, edist (f a) 0`. -/
protected instance has_norm {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] : has_norm (l1 α β μ) :=
  has_norm.mk fun (f : l1 α β μ) => dist f 0

theorem norm_eq {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : norm f = ennreal.to_real (edist (↑f) 0) :=
  rfl

protected instance normed_group {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] : normed_group (l1 α β μ) :=
  normed_group.of_add_dist sorry sorry

protected instance has_scalar {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] {𝕜 : Type u_5} [normed_field 𝕜] [normed_space 𝕜 β] : has_scalar 𝕜 (l1 α β μ) :=
  has_scalar.mk fun (x : 𝕜) (f : l1 α β μ) => { val := x • ↑f, property := sorry }

@[simp] theorem coe_smul {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] {𝕜 : Type u_5} [normed_field 𝕜] [normed_space 𝕜 β] (c : 𝕜) (f : l1 α β μ) : ↑(c • f) = c • ↑f :=
  rfl

protected instance semimodule {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] {𝕜 : Type u_5} [normed_field 𝕜] [normed_space 𝕜 β] : semimodule 𝕜 (l1 α β μ) :=
  semimodule.mk sorry sorry

protected instance normed_space {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] {𝕜 : Type u_5} [normed_field 𝕜] [normed_space 𝕜 β] : normed_space 𝕜 (l1 α β μ) :=
  normed_space.mk sorry

/-- Construct the equivalence class `[f]` of an integrable function `f`. -/
def of_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : α → β) (hf : integrable f) : l1 α β μ :=
  { val := ae_eq_fun.mk f (integrable.ae_measurable hf), property := sorry }

@[simp] theorem of_fun_eq_mk {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : α → β) (hf : integrable f) : ↑(of_fun f hf) = ae_eq_fun.mk f (integrable.ae_measurable hf) :=
  rfl

theorem of_fun_eq_of_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : α → β) (g : α → β) (hf : integrable f) (hg : integrable g) : of_fun f hf = of_fun g hg ↔ filter.eventually_eq (measure.ae μ) f g := sorry

theorem of_fun_zero {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] : of_fun (fun (_x : α) => 0) (integrable_zero α β μ) = 0 :=
  rfl

theorem of_fun_add {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : α → β) (g : α → β) (hf : integrable f) (hg : integrable g) : of_fun (f + g) (integrable.add hf hg) = of_fun f hf + of_fun g hg :=
  rfl

theorem of_fun_neg {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : α → β) (hf : integrable f) : of_fun (-f) (integrable.neg hf) = -of_fun f hf :=
  rfl

theorem of_fun_sub {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : α → β) (g : α → β) (hf : integrable f) (hg : integrable g) : of_fun (f - g) (integrable.sub hf hg) = of_fun f hf - of_fun g hg := sorry

theorem norm_of_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : α → β) (hf : integrable f) : norm (of_fun f hf) = ennreal.to_real (lintegral μ fun (a : α) => edist (f a) 0) :=
  rfl

theorem norm_of_fun_eq_lintegral_norm {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : α → β) (hf : integrable f) : norm (of_fun f hf) = ennreal.to_real (lintegral μ fun (a : α) => ennreal.of_real (norm (f a))) := sorry

theorem of_fun_smul {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] {𝕜 : Type u_5} [normed_field 𝕜] [normed_space 𝕜 β] (f : α → β) (hf : integrable f) (k : 𝕜) : of_fun (fun (a : α) => k • f a) (integrable.smul k hf) = k • of_fun f hf :=
  rfl

protected theorem measurable {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : measurable ⇑f :=
  ae_eq_fun.measurable (subtype.val f)

protected theorem ae_measurable {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : ae_measurable ⇑f :=
  ae_eq_fun.ae_measurable (subtype.val f)

theorem measurable_norm {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : measurable fun (a : α) => norm (coe_fn f a) :=
  measurable.norm (l1.measurable f)

protected theorem integrable {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : integrable ⇑f :=
  iff.mpr ae_eq_fun.integrable_coe_fn (subtype.property f)

protected theorem has_finite_integral {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : has_finite_integral ⇑f :=
  integrable.has_finite_integral (l1.integrable f)

theorem integrable_norm {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : integrable fun (a : α) => norm (coe_fn f a) :=
  iff.mpr (integrable_norm_iff (l1.ae_measurable f)) (l1.integrable f)

theorem of_fun_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : of_fun (⇑f) (l1.integrable f) = f :=
  subtype.ext (ae_eq_fun.mk_coe_fn ↑f)

theorem mk_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : ae_eq_fun.mk (⇑f) (l1.ae_measurable f) = ↑f := sorry

theorem to_fun_of_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : α → β) (hf : integrable f) : filter.eventually_eq (measure.ae μ) (⇑(of_fun f hf)) f :=
  ae_eq_fun.coe_fn_mk f (integrable.ae_measurable hf)

theorem zero_to_fun (α : Type u_1) (β : Type u_2) [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] : filter.eventually_eq (measure.ae μ) (⇑0) 0 :=
  ae_eq_fun.coe_fn_zero

theorem add_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) (g : l1 α β μ) : filter.eventually_eq (measure.ae μ) (⇑(f + g)) (⇑f + ⇑g) :=
  ae_eq_fun.coe_fn_add ↑f ↑g

theorem neg_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : filter.eventually_eq (measure.ae μ) (⇑(-f)) (-⇑f) :=
  ae_eq_fun.coe_fn_neg ↑f

theorem sub_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) (g : l1 α β μ) : filter.eventually_eq (measure.ae μ) (⇑(f - g)) (⇑f - ⇑g) :=
  ae_eq_fun.coe_fn_sub ↑f ↑g

theorem dist_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) (g : l1 α β μ) : dist f g = ennreal.to_real (lintegral μ fun (x : α) => edist (coe_fn f x) (coe_fn g x)) := sorry

theorem norm_eq_nnnorm_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : norm f = ennreal.to_real (lintegral μ fun (a : α) => ↑(nnnorm (coe_fn f a))) := sorry

theorem norm_eq_norm_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : norm f = ennreal.to_real (lintegral μ fun (a : α) => ennreal.of_real (norm (coe_fn f a))) := sorry

theorem lintegral_edist_to_fun_lt_top {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) (g : l1 α β μ) : (lintegral μ fun (a : α) => edist (coe_fn f a) (coe_fn g a)) < ⊤ :=
  lintegral_edist_lt_top (l1.integrable f) (l1.integrable g)

theorem smul_to_fun {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] {𝕜 : Type u_5} [normed_field 𝕜] [normed_space 𝕜 β] (c : 𝕜) (f : l1 α β μ) : filter.eventually_eq (measure.ae μ) (⇑(c • f)) (c • ⇑f) :=
  ae_eq_fun.coe_fn_smul c ↑f

theorem norm_eq_lintegral {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : norm f = ennreal.to_real (lintegral μ fun (x : α) => ↑(nnnorm (coe_fn f x))) := sorry

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `norm_eq_lintegral` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
theorem norm_sub_eq_lintegral {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) (g : l1 α β μ) : norm (f - g) = ennreal.to_real (lintegral μ fun (x : α) => ↑(nnnorm (coe_fn f x - coe_fn g x))) := sorry

theorem of_real_norm_eq_lintegral {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) : ennreal.of_real (norm f) = lintegral μ fun (x : α) => ↑(nnnorm (coe_fn f x)) := sorry

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `of_real_norm_eq_lintegral` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
theorem of_real_norm_sub_eq_lintegral {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] (f : l1 α β μ) (g : l1 α β μ) : ennreal.of_real (norm (f - g)) = lintegral μ fun (x : α) => ↑(nnnorm (coe_fn f x - coe_fn g x)) := sorry

/-- Positive part of a function in `L¹` space. -/
def pos_part {α : Type u_1} [measurable_space α] {μ : measure α} (f : l1 α ℝ μ) : l1 α ℝ μ :=
  { val := ae_eq_fun.pos_part ↑f, property := sorry }

/-- Negative part of a function in `L¹` space. -/
def neg_part {α : Type u_1} [measurable_space α] {μ : measure α} (f : l1 α ℝ μ) : l1 α ℝ μ :=
  pos_part (-f)

theorem coe_pos_part {α : Type u_1} [measurable_space α] {μ : measure α} (f : l1 α ℝ μ) : ↑(pos_part f) = ae_eq_fun.pos_part ↑f :=
  rfl

theorem pos_part_to_fun {α : Type u_1} [measurable_space α] {μ : measure α} (f : l1 α ℝ μ) : filter.eventually_eq (measure.ae μ) ⇑(pos_part f) fun (a : α) => max (coe_fn f a) 0 :=
  ae_eq_fun.coe_fn_pos_part ↑f

theorem neg_part_to_fun_eq_max {α : Type u_1} [measurable_space α] {μ : measure α} (f : l1 α ℝ μ) : filter.eventually (fun (a : α) => coe_fn (neg_part f) a = max (-coe_fn f a) 0) (measure.ae μ) := sorry

theorem neg_part_to_fun_eq_min {α : Type u_1} [measurable_space α] {μ : measure α} (f : l1 α ℝ μ) : filter.eventually (fun (a : α) => coe_fn (neg_part f) a = -min (coe_fn f a) 0) (measure.ae μ) := sorry

theorem norm_le_norm_of_ae_le {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure α} [normed_group β] [measurable_space β] [topological_space.second_countable_topology β] [borel_space β] {f : l1 α β μ} {g : l1 α β μ} (h : filter.eventually (fun (a : α) => norm (coe_fn f a) ≤ norm (coe_fn g a)) (measure.ae μ)) : norm f ≤ norm g := sorry

theorem continuous_pos_part {α : Type u_1} [measurable_space α] {μ : measure α} : continuous fun (f : l1 α ℝ μ) => pos_part f := sorry

theorem continuous_neg_part {α : Type u_1} [measurable_space α] {μ : measure α} : continuous fun (f : l1 α ℝ μ) => neg_part f := sorry

/- TODO: l1 is a complete space -/

end l1


end measure_theory


theorem integrable_zero_measure {α : Type u_1} {β : Type u_2} [measurable_space α] [normed_group β] [measurable_space β] {f : α → β} : measure_theory.integrable f :=
  measure_theory.integrable.congr (measure_theory.integrable_zero α β 0)
    (id (Eq.refl (coe_fn 0 (set_of fun (x : α) => 0 ≠ f x))))

