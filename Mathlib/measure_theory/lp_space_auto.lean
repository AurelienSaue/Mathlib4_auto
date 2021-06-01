/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.ess_sup
import Mathlib.measure_theory.l1_space
import Mathlib.analysis.mean_inequalities
import Mathlib.PostPort

universes u_1 u_3 u_2 u_4 

namespace Mathlib

/-!
# ℒp space and Lp space

This file describes properties of almost everywhere measurable functions with finite seminorm,
denoted by `snorm f p μ` and defined for `p:ennreal` as `0` if `p=0`, `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for
`0 < p < ∞` and `ess_sup ∥f∥ μ` for `p=∞`.

The Prop-valued `mem_ℒp f p μ` states that a function `f : α → E` has finite seminorm.
The space `Lp α E p μ` is the subtype of elements of `α →ₘ[μ] E` (see ae_eq_fun) such that
`snorm f p μ` is finite. For `1 ≤ p`, `snorm` defines a norm and Lp is a metric space.

TODO: prove that Lp is complete.

## Main definitions

* `snorm' f p μ` : `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a  measurable
  space and `F` is a normed group.
* `snorm_ess_sup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `ess_sup ∥f∥ μ`.
* `snorm f p μ` : for `p : ennreal`, seminorm in `ℒp`, equal to `0` for `p=0`, to `snorm' f p μ`
  for `0 < p < ∞` and to `snorm_ess_sup f μ` for `p = ∞`.

* `mem_ℒp f p μ` : property that the function `f` is almost everywhere measurable and has finite
  p-seminorm for measure `μ` (`snorm f p μ < ∞`)
* `Lp E p μ` : elements of `α →ₘ[μ] E` (see ae_eq_fun) such that `snorm f p μ` is finite. Defined
  as an `add_subgroup` of `α →ₘ[μ] E`.

-/

namespace measure_theory


/-- `(∫ ∥f a∥^p ∂μ) ^ (1/p)`, which is a seminorm on the space of measurable functions for which
this quantity is finite -/
def snorm' {α : Type u_1} {F : Type u_3} [measurable_space α] [normed_group F] (f : α → F) (p : ℝ)
    (μ : measure α) : ennreal :=
  (lintegral μ fun (a : α) => ↑(nnnorm (f a)) ^ p) ^ (1 / p)

/-- seminorm for `ℒ∞`, equal to the essential supremum of `∥f∥`. -/
def snorm_ess_sup {α : Type u_1} {F : Type u_3} [measurable_space α] [normed_group F] (f : α → F)
    (μ : measure α) : ennreal :=
  ess_sup (fun (x : α) => ↑(nnnorm (f x))) μ

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`ess_sup ∥f∥ μ` for `p = ∞`. -/
def snorm {α : Type u_1} {F : Type u_3} [measurable_space α] [normed_group F] (f : α → F)
    (q : ennreal) (μ : measure α) : ennreal :=
  ite (q = 0) 0 (ite (q = ⊤) (snorm_ess_sup f μ) (snorm' f (ennreal.to_real q) μ))

theorem snorm_eq_snorm' {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {q : ennreal} (hq_ne_zero : q ≠ 0) (hq_ne_top : q ≠ ⊤) {f : α → F} :
    snorm f q μ = snorm' f (ennreal.to_real q) μ :=
  sorry

@[simp] theorem snorm_exponent_top {α : Type u_1} {F : Type u_3} [measurable_space α]
    {μ : measure α} [normed_group F] {f : α → F} : snorm f ⊤ μ = snorm_ess_sup f μ :=
  sorry

/-- The property that `f:α→E` is ae_measurable and `(∫ ∥f a∥^p ∂μ)^(1/p)` is finite -/
def mem_ℒp {α : Type u_1} {E : Type u_2} [measurable_space α] [measurable_space E] [normed_group E]
    (f : α → E) (p : ennreal) (μ : measure α) :=
  ae_measurable f ∧ snorm f p μ < ⊤

theorem lintegral_rpow_nnnorm_eq_rpow_snorm' {α : Type u_1} {F : Type u_3} [measurable_space α]
    {μ : measure α} [normed_group F] {p : ℝ} {f : α → F} (hp0_lt : 0 < p) :
    (lintegral μ fun (a : α) => ↑(nnnorm (f a)) ^ p) = snorm' f p μ ^ p :=
  sorry

theorem mem_ℒp_one_iff_integrable {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {f : α → E} : mem_ℒp f 1 μ ↔ integrable f :=
  sorry

theorem mem_ℒp.snorm_lt_top {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} {f : α → E} (hfp : mem_ℒp f q μ) :
    snorm f q μ < ⊤ :=
  and.right hfp

theorem mem_ℒp.snorm_ne_top {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} {f : α → E} (hfp : mem_ℒp f q μ) :
    snorm f q μ ≠ ⊤ :=
  ne_of_lt (and.right hfp)

theorem lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top {α : Type u_1} {F : Type u_3}
    [measurable_space α] {μ : measure α} [normed_group F] {p : ℝ} {f : α → F} (hp0_lt : 0 < p)
    (hfp : snorm' f p μ < ⊤) : (lintegral μ fun (a : α) => ↑(nnnorm (f a)) ^ p) < ⊤ :=
  sorry

@[simp] theorem snorm'_exponent_zero {α : Type u_1} {F : Type u_3} [measurable_space α]
    {μ : measure α} [normed_group F] {f : α → F} : snorm' f 0 μ = 1 :=
  sorry

@[simp] theorem snorm_exponent_zero {α : Type u_1} {F : Type u_3} [measurable_space α]
    {μ : measure α} [normed_group F] {f : α → F} : snorm f 0 μ = 0 :=
  sorry

theorem mem_ℒp_zero_iff_ae_measurable {α : Type u_1} {E : Type u_2} [measurable_space α]
    {μ : measure α} [measurable_space E] [normed_group E] {f : α → E} :
    mem_ℒp f 0 μ ↔ ae_measurable f :=
  sorry

@[simp] theorem snorm'_zero {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {p : ℝ} (hp0_lt : 0 < p) : snorm' 0 p μ = 0 :=
  sorry

@[simp] theorem snorm'_zero' {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {p : ℝ} (hp0_ne : p ≠ 0) (hμ : μ ≠ 0) : snorm' 0 p μ = 0 :=
  sorry

@[simp] theorem snorm_ess_sup_zero {α : Type u_1} {F : Type u_3} [measurable_space α]
    {μ : measure α} [normed_group F] : snorm_ess_sup 0 μ = 0 :=
  sorry

@[simp] theorem snorm_zero {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {q : ennreal} : snorm 0 q μ = 0 :=
  sorry

theorem zero_mem_ℒp {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} : mem_ℒp 0 q μ :=
  { left := measurable.ae_measurable measurable_zero,
    right := eq.mpr (id (Eq._oldrec (Eq.refl (snorm 0 q μ < ⊤)) snorm_zero)) ennreal.coe_lt_top }

theorem snorm'_measure_zero_of_pos {α : Type u_1} {F : Type u_3} [measurable_space α]
    [normed_group F] {p : ℝ} {f : α → F} (hp_pos : 0 < p) : snorm' f p 0 = 0 :=
  sorry

theorem snorm'_measure_zero_of_exponent_zero {α : Type u_1} {F : Type u_3} [measurable_space α]
    [normed_group F] {f : α → F} : snorm' f 0 0 = 1 :=
  sorry

theorem snorm'_measure_zero_of_neg {α : Type u_1} {F : Type u_3} [measurable_space α]
    [normed_group F] {p : ℝ} {f : α → F} (hp_neg : p < 0) : snorm' f p 0 = ⊤ :=
  sorry

@[simp] theorem snorm_ess_sup_measure_zero {α : Type u_1} {F : Type u_3} [measurable_space α]
    [normed_group F] {f : α → F} : snorm_ess_sup f 0 = 0 :=
  sorry

@[simp] theorem snorm_measure_zero {α : Type u_1} {F : Type u_3} [measurable_space α]
    [normed_group F] {q : ennreal} {f : α → F} : snorm f q 0 = 0 :=
  sorry

theorem snorm'_const {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {p : ℝ} (c : F) (hp_pos : 0 < p) :
    snorm' (fun (x : α) => c) p μ = ↑(nnnorm c) * coe_fn μ set.univ ^ (1 / p) :=
  sorry

theorem snorm'_const' {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {p : ℝ} [finite_measure μ] (c : F) (hc_ne_zero : c ≠ 0) (hp_ne_zero : p ≠ 0) :
    snorm' (fun (x : α) => c) p μ = ↑(nnnorm c) * coe_fn μ set.univ ^ (1 / p) :=
  sorry

theorem snorm_ess_sup_const {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] (c : F) (hμ : μ ≠ 0) : snorm_ess_sup (fun (x : α) => c) μ = ↑(nnnorm c) :=
  sorry

theorem snorm'_const_of_probability_measure {α : Type u_1} {F : Type u_3} [measurable_space α]
    {μ : measure α} [normed_group F] {p : ℝ} (c : F) (hp_pos : 0 < p) [probability_measure μ] :
    snorm' (fun (x : α) => c) p μ = ↑(nnnorm c) :=
  sorry

theorem snorm_const {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {q : ennreal} (c : F) (h0 : q ≠ 0) (hμ : μ ≠ 0) :
    snorm (fun (x : α) => c) q μ = ↑(nnnorm c) * coe_fn μ set.univ ^ (1 / ennreal.to_real q) :=
  sorry

theorem snorm_const' {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {q : ennreal} (c : F) (h0 : q ≠ 0) (h_top : q ≠ ⊤) :
    snorm (fun (x : α) => c) q μ = ↑(nnnorm c) * coe_fn μ set.univ ^ (1 / ennreal.to_real q) :=
  sorry

theorem mem_ℒp_const {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} (c : E) [finite_measure μ] :
    mem_ℒp (fun (a : α) => c) q μ :=
  sorry

theorem snorm'_congr_ae {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {p : ℝ} {f : α → F} {g : α → F}
    (hfg : filter.eventually_eq (measure.ae μ) f g) : snorm' f p μ = snorm' g p μ :=
  sorry

theorem snorm_ess_sup_congr_ae {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {f : α → F} {g : α → F} (hfg : filter.eventually_eq (measure.ae μ) f g) :
    snorm_ess_sup f μ = snorm_ess_sup g μ :=
  sorry

theorem snorm_congr_ae {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {q : ennreal} {f : α → F} {g : α → F}
    (hfg : filter.eventually_eq (measure.ae μ) f g) : snorm f q μ = snorm g q μ :=
  sorry

theorem mem_ℒp.ae_eq {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} {f : α → E} {g : α → E}
    (hfg : filter.eventually_eq (measure.ae μ) f g) (hf_Lp : mem_ℒp f q μ) : mem_ℒp g q μ :=
  sorry

theorem mem_ℒp_congr_ae {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} {f : α → E} {g : α → E}
    (hfg : filter.eventually_eq (measure.ae μ) f g) : mem_ℒp f q μ ↔ mem_ℒp g q μ :=
  { mp := fun (h : mem_ℒp f q μ) => mem_ℒp.ae_eq hfg h,
    mpr := fun (h : mem_ℒp g q μ) => mem_ℒp.ae_eq (filter.eventually_eq.symm hfg) h }

theorem snorm'_eq_zero_of_ae_zero {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {p : ℝ} {f : α → F} (hp0_lt : 0 < p)
    (hf_zero : filter.eventually_eq (measure.ae μ) f 0) : snorm' f p μ = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (snorm' f p μ = 0)) (snorm'_congr_ae hf_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (snorm' 0 p μ = 0)) (snorm'_zero hp0_lt))) (Eq.refl 0))

theorem snorm'_eq_zero_of_ae_zero' {α : Type u_1} {F : Type u_3} [measurable_space α]
    {μ : measure α} [normed_group F] {p : ℝ} (hp0_ne : p ≠ 0) (hμ : μ ≠ 0) {f : α → F}
    (hf_zero : filter.eventually_eq (measure.ae μ) f 0) : snorm' f p μ = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (snorm' f p μ = 0)) (snorm'_congr_ae hf_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (snorm' 0 p μ = 0)) (snorm'_zero' hp0_ne hμ))) (Eq.refl 0))

theorem ae_eq_zero_of_snorm'_eq_zero {α : Type u_1} {E : Type u_2} [measurable_space α]
    {μ : measure α} [measurable_space E] [normed_group E] {p : ℝ} [opens_measurable_space E]
    {f : α → E} (hp0 : 0 ≤ p) (hf : ae_measurable f) (h : snorm' f p μ = 0) :
    filter.eventually_eq (measure.ae μ) f 0 :=
  sorry

theorem snorm'_eq_zero_iff {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {p : ℝ} [opens_measurable_space E] (hp0_lt : 0 < p)
    {f : α → E} (hf : ae_measurable f) :
    snorm' f p μ = 0 ↔ filter.eventually_eq (measure.ae μ) f 0 :=
  { mp := ae_eq_zero_of_snorm'_eq_zero (le_of_lt hp0_lt) hf,
    mpr := snorm'_eq_zero_of_ae_zero hp0_lt }

theorem coe_nnnorm_ae_le_snorm_ess_sup {α : Type u_1} {F : Type u_3} [measurable_space α]
    [normed_group F] (f : α → F) (μ : measure α) :
    filter.eventually (fun (x : α) => ↑(nnnorm (f x)) ≤ snorm_ess_sup f μ) (measure.ae μ) :=
  ennreal.ae_le_ess_sup fun (x : α) => ↑(nnnorm (f x))

theorem snorm_ess_sup_eq_zero_iff {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {f : α → F} :
    snorm_ess_sup f μ = 0 ↔ filter.eventually_eq (measure.ae μ) f 0 :=
  sorry

theorem snorm_eq_zero_iff {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} [opens_measurable_space E] {f : α → E}
    (hf : ae_measurable f) (h0 : q ≠ 0) :
    snorm f q μ = 0 ↔ filter.eventually_eq (measure.ae μ) f 0 :=
  sorry

@[simp] theorem snorm'_neg {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {p : ℝ} {f : α → F} : snorm' (-f) p μ = snorm' f p μ :=
  sorry

@[simp] theorem snorm_neg {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {q : ennreal} {f : α → F} : snorm (-f) q μ = snorm f q μ :=
  sorry

theorem mem_ℒp.neg {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} [borel_space E] {f : α → E}
    (hf : mem_ℒp f q μ) : mem_ℒp (-f) q μ :=
  sorry

theorem snorm'_le_snorm'_mul_rpow_measure_univ {α : Type u_1} {E : Type u_2} [measurable_space α]
    {μ : measure α} [measurable_space E] [normed_group E] [borel_space E] {p : ℝ} {q : ℝ}
    (hp0_lt : 0 < p) (hpq : p ≤ q) {f : α → E} (hf : ae_measurable f) :
    snorm' f p μ ≤ snorm' f q μ * coe_fn μ set.univ ^ (1 / p - 1 / q) :=
  sorry

theorem snorm'_le_snorm_ess_sup_mul_rpow_measure_univ {α : Type u_1} {F : Type u_3}
    [measurable_space α] {μ : measure α} [normed_group F] {p : ℝ} (hp_pos : 0 < p) {f : α → F} :
    snorm' f p μ ≤ snorm_ess_sup f μ * coe_fn μ set.univ ^ (1 / p) :=
  sorry

theorem snorm'_le_snorm'_of_exponent_le {α : Type u_1} {E : Type u_2} [measurable_space α]
    [measurable_space E] [normed_group E] [borel_space E] {p : ℝ} {q : ℝ} (hp0_lt : 0 < p)
    (hpq : p ≤ q) (μ : measure α) [probability_measure μ] {f : α → E} (hf : ae_measurable f) :
    snorm' f p μ ≤ snorm' f q μ :=
  sorry

theorem snorm'_le_snorm_ess_sup {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {p : ℝ} (hp_pos : 0 < p) {f : α → F} [probability_measure μ] :
    snorm' f p μ ≤ snorm_ess_sup f μ :=
  sorry

theorem snorm_le_snorm_of_exponent_le {α : Type u_1} {E : Type u_2} [measurable_space α]
    {μ : measure α} [measurable_space E] [normed_group E] [borel_space E] {p : ennreal}
    {q : ennreal} (hpq : p ≤ q) [probability_measure μ] {f : α → E} (hf : ae_measurable f) :
    snorm f p μ ≤ snorm f q μ :=
  sorry

theorem snorm'_lt_top_of_snorm'_lt_top_of_exponent_le {α : Type u_1} {E : Type u_2}
    [measurable_space α] {μ : measure α} [measurable_space E] [normed_group E] [borel_space E]
    {p : ℝ} {q : ℝ} [finite_measure μ] {f : α → E} (hf : ae_measurable f)
    (hfq_lt_top : snorm' f q μ < ⊤) (hp_nonneg : 0 ≤ p) (hpq : p ≤ q) : snorm' f p μ < ⊤ :=
  sorry

theorem mem_ℒp.mem_ℒp_of_exponent_le {α : Type u_1} {E : Type u_2} [measurable_space α]
    {μ : measure α} [measurable_space E] [normed_group E] [borel_space E] {p : ennreal}
    {q : ennreal} [finite_measure μ] {f : α → E} (hfq : mem_ℒp f q μ) (hpq : p ≤ q) :
    mem_ℒp f p μ :=
  sorry

theorem mem_ℒp.integrable {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} [borel_space E] (hq1 : 1 ≤ q) {f : α → E}
    [finite_measure μ] (hfq : mem_ℒp f q μ) : integrable f :=
  iff.mp mem_ℒp_one_iff_integrable (mem_ℒp.mem_ℒp_of_exponent_le hfq hq1)

theorem snorm'_add_le {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {p : ℝ} [borel_space E] {f : α → E} {g : α → E}
    (hf : ae_measurable f) (hg : ae_measurable g) (hp1 : 1 ≤ p) :
    snorm' (f + g) p μ ≤ snorm' f p μ + snorm' g p μ :=
  sorry

theorem snorm_ess_sup_add_le {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {f : α → F} {g : α → F} :
    snorm_ess_sup (f + g) μ ≤ snorm_ess_sup f μ + snorm_ess_sup g μ :=
  sorry

theorem snorm_add_le {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} [borel_space E] {f : α → E} {g : α → E}
    (hf : ae_measurable f) (hg : ae_measurable g) (hq1 : 1 ≤ q) :
    snorm (f + g) q μ ≤ snorm f q μ + snorm g q μ :=
  sorry

theorem snorm_add_lt_top_of_one_le {α : Type u_1} {E : Type u_2} [measurable_space α]
    {μ : measure α} [measurable_space E] [normed_group E] {q : ennreal} [borel_space E] {f : α → E}
    {g : α → E} (hf : mem_ℒp f q μ) (hg : mem_ℒp g q μ) (hq1 : 1 ≤ q) : snorm (f + g) q μ < ⊤ :=
  lt_of_le_of_lt (snorm_add_le (and.left hf) (and.left hg) hq1)
    (iff.mpr ennreal.add_lt_top { left := and.right hf, right := and.right hg })

theorem snorm'_add_lt_top_of_le_one {α : Type u_1} {E : Type u_2} [measurable_space α]
    {μ : measure α} [measurable_space E] [normed_group E] {p : ℝ} [borel_space E] {f : α → E}
    {g : α → E} (hf : ae_measurable f) (hg : ae_measurable g) (hf_snorm : snorm' f p μ < ⊤)
    (hg_snorm : snorm' g p μ < ⊤) (hp_pos : 0 < p) (hp1 : p ≤ 1) : snorm' (f + g) p μ < ⊤ :=
  sorry

theorem snorm_add_lt_top {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} [borel_space E] {f : α → E} {g : α → E}
    (hf : mem_ℒp f q μ) (hg : mem_ℒp g q μ) : snorm (f + g) q μ < ⊤ :=
  sorry

theorem mem_ℒp.add {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} [borel_space E]
    [topological_space.second_countable_topology E] {f : α → E} {g : α → E} (hf : mem_ℒp f q μ)
    (hg : mem_ℒp g q μ) : mem_ℒp (f + g) q μ :=
  { left := ae_measurable.add (and.left hf) (and.left hg), right := snorm_add_lt_top hf hg }

theorem mem_ℒp.sub {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} [borel_space E]
    [topological_space.second_countable_topology E] {f : α → E} {g : α → E} (hf : mem_ℒp f q μ)
    (hg : mem_ℒp g q μ) : mem_ℒp (f - g) q μ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (mem_ℒp (f - g) q μ)) (sub_eq_add_neg f g)))
    (mem_ℒp.add hf (mem_ℒp.neg hg))

theorem snorm'_const_smul {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {p : ℝ} {𝕜 : Type u_4} [normed_field 𝕜] [normed_space 𝕜 F] {f : α → F} (c : 𝕜)
    (hp0_lt : 0 < p) : snorm' (c • f) p μ = ↑(nnnorm c) * snorm' f p μ :=
  sorry

theorem snorm_ess_sup_const_smul {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {𝕜 : Type u_4} [normed_field 𝕜] [normed_space 𝕜 F] {f : α → F} (c : 𝕜) :
    snorm_ess_sup (c • f) μ = ↑(nnnorm c) * snorm_ess_sup f μ :=
  sorry

theorem snorm_const_smul {α : Type u_1} {F : Type u_3} [measurable_space α] {μ : measure α}
    [normed_group F] {q : ennreal} {𝕜 : Type u_4} [normed_field 𝕜] [normed_space 𝕜 F] {f : α → F}
    (c : 𝕜) : snorm (c • f) q μ = ↑(nnnorm c) * snorm f q μ :=
  sorry

theorem mem_ℒp.const_smul {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {q : ennreal} {𝕜 : Type u_4} [normed_field 𝕜]
    [normed_space 𝕜 E] [borel_space E] {f : α → E} (hf : mem_ℒp f q μ) (c : 𝕜) :
    mem_ℒp (c • f) q μ :=
  { left := ae_measurable.const_smul (and.left hf) c,
    right :=
      lt_of_le_of_lt (le_of_eq (snorm_const_smul c))
        (ennreal.mul_lt_top ennreal.coe_lt_top (and.right hf)) }

theorem snorm'_smul_le_mul_snorm' {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {p : ℝ} {𝕜 : Type u_4} [normed_field 𝕜] [normed_space 𝕜 E]
    [opens_measurable_space E] [measurable_space 𝕜] [opens_measurable_space 𝕜] {q : ℝ} {r : ℝ}
    {f : α → E} (hf : ae_measurable f) {φ : α → 𝕜} (hφ : ae_measurable φ) (hp0_lt : 0 < p)
    (hpq : p < q) (hpqr : 1 / p = 1 / q + 1 / r) :
    snorm' (φ • f) p μ ≤ snorm' φ q μ * snorm' f r μ :=
  sorry

/-! ### Lp space

The space of equivalence classes of measurable functions for which `snorm f p μ < ⊤`.
-/

@[simp] theorem snorm_ae_eq_fun {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {p : ennreal} {f : α → E} (hf : ae_measurable f) :
    snorm (⇑(ae_eq_fun.mk f hf)) p μ = snorm f p μ :=
  snorm_congr_ae (ae_eq_fun.coe_fn_mk f hf)

theorem mem_ℒp.snorm_mk_lt_top {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] {p : ennreal} {f : α → E} (hfp : mem_ℒp f p μ) :
    snorm (⇑(ae_eq_fun.mk f (and.left hfp))) p μ < ⊤ :=
  sorry

/-- Lp space -/
def Lp {α : Type u_1} (E : Type u_2) [measurable_space α] [measurable_space E] [normed_group E]
    [borel_space E] [topological_space.second_countable_topology E] (p : ennreal) (μ : measure α) :
    add_subgroup (ae_eq_fun α E μ) :=
  add_subgroup.mk (set_of fun (f : ae_eq_fun α E μ) => snorm (⇑f) p μ < ⊤) sorry sorry sorry

/-- make an element of Lp from a function verifying `mem_ℒp` -/
def mem_ℒp.to_Lp {α : Type u_1} {E : Type u_2} [measurable_space α] [measurable_space E]
    [normed_group E] [borel_space E] [topological_space.second_countable_topology E] (f : α → E)
    {p : ennreal} {μ : measure α} (h_mem_ℒp : mem_ℒp f p μ) : ↥(Lp E p μ) :=
  { val := ae_eq_fun.mk f sorry, property := mem_ℒp.snorm_mk_lt_top h_mem_ℒp }

theorem mem_ℒp.coe_fn_to_Lp {α : Type u_1} {E : Type u_2} [measurable_space α] [measurable_space E]
    [normed_group E] [borel_space E] [topological_space.second_countable_topology E] {μ : measure α}
    {p : ennreal} {f : α → E} (hf : mem_ℒp f p μ) :
    filter.eventually_eq (measure.ae μ) (⇑(mem_ℒp.to_Lp f hf)) f :=
  ae_eq_fun.coe_fn_mk f (mem_ℒp.to_Lp._proof_1 f hf)

namespace Lp


theorem mem_Lp_iff_snorm_lt_top {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {f : ae_eq_fun α E μ} :
    f ∈ Lp E p μ ↔ snorm (⇑f) p μ < ⊤ :=
  iff.refl (f ∈ Lp E p μ)

theorem antimono {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] [finite_measure μ] {p : ennreal} {q : ennreal}
    (hpq : p ≤ q) : Lp E q μ ≤ Lp E p μ :=
  fun (f : ae_eq_fun α E μ) (hf : f ∈ Lp E q μ) =>
    and.right (mem_ℒp.mem_ℒp_of_exponent_le { left := ae_eq_fun.ae_measurable f, right := hf } hpq)

theorem coe_fn_mk {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {f : ae_eq_fun α E μ}
    (hf : snorm (⇑f) p μ < ⊤) :
    filter.eventually_eq (measure.ae μ) ⇑{ val := f, property := hf } ⇑f :=
  sorry

theorem snorm_lt_top {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} (f : ↥(Lp E p μ)) :
    snorm (⇑f) p μ < ⊤ :=
  subtype.prop f

theorem snorm_ne_top {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} (f : ↥(Lp E p μ)) :
    snorm (⇑f) p μ ≠ ⊤ :=
  has_lt.lt.ne (snorm_lt_top f)

theorem measurable {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} (f : ↥(Lp E p μ)) :
    measurable ⇑f :=
  ae_eq_fun.measurable (subtype.val f)

theorem ae_measurable {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} (f : ↥(Lp E p μ)) :
    ae_measurable ⇑f :=
  ae_eq_fun.ae_measurable (subtype.val f)

theorem mem_ℒp {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} (f : ↥(Lp E p μ)) :
    mem_ℒp (⇑f) p μ :=
  { left := ae_measurable f, right := subtype.prop f }

theorem coe_fn_zero {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} :
    filter.eventually_eq (measure.ae μ) (⇑0) 0 :=
  ae_eq_fun.coe_fn_zero

theorem coe_fn_neg {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {f : ↥(Lp E p μ)} :
    filter.eventually_eq (measure.ae μ) (⇑(-f)) (-⇑f) :=
  ae_eq_fun.coe_fn_neg ↑f

theorem coe_fn_add {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {f : ↥(Lp E p μ)}
    {g : ↥(Lp E p μ)} : filter.eventually_eq (measure.ae μ) (⇑(f + g)) (⇑f + ⇑g) :=
  ae_eq_fun.coe_fn_add (subtype.val f) (subtype.val g)

theorem coe_fn_sub {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {f : ↥(Lp E p μ)}
    {g : ↥(Lp E p μ)} : filter.eventually_eq (measure.ae μ) (⇑(f - g)) (⇑f - ⇑g) :=
  ae_eq_fun.coe_fn_sub ↑f ↑g

theorem mem_Lp_const {E : Type u_2} [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} (α : Type u_1)
    [measurable_space α] (μ : measure α) (c : E) [finite_measure μ] :
    ae_eq_fun.const α c ∈ Lp E p μ :=
  mem_ℒp.snorm_mk_lt_top (mem_ℒp_const c)

protected instance has_norm {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} : has_norm ↥(Lp E p μ) :=
  has_norm.mk fun (f : ↥(Lp E p μ)) => ennreal.to_real (snorm (⇑f) p μ)

theorem norm_def {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} (f : ↥(Lp E p μ)) :
    norm f = ennreal.to_real (snorm (⇑f) p μ) :=
  rfl

@[simp] theorem norm_zero {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} : norm 0 = 0 :=
  sorry

theorem norm_eq_zero_iff {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {f : ↥(Lp E p μ)} (hp : 0 < p) :
    norm f = 0 ↔ f = 0 :=
  sorry

@[simp] theorem norm_neg {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {f : ↥(Lp E p μ)} :
    norm (-f) = norm f :=
  sorry

protected instance normed_group {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} [hp : fact (1 ≤ p)] :
    normed_group ↥(Lp E p μ) :=
  normed_group.of_core ↥(Lp E p μ) sorry

theorem mem_Lp_const_smul {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {𝕜 : Type u_4} [normed_field 𝕜]
    [normed_space 𝕜 E] (c : 𝕜) (f : ↥(Lp E p μ)) : c • ↑f ∈ Lp E p μ :=
  sorry

protected instance has_scalar {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {𝕜 : Type u_4} [normed_field 𝕜]
    [normed_space 𝕜 E] : has_scalar 𝕜 ↥(Lp E p μ) :=
  has_scalar.mk
    fun (c : 𝕜) (f : ↥(Lp E p μ)) => { val := c • ↑f, property := mem_Lp_const_smul c f }

theorem coe_fn_smul {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {𝕜 : Type u_4} [normed_field 𝕜]
    [normed_space 𝕜 E] {f : ↥(Lp E p μ)} {c : 𝕜} :
    filter.eventually_eq (measure.ae μ) (⇑(c • f)) (c • ⇑f) :=
  ae_eq_fun.coe_fn_smul c ↑f

protected instance semimodule {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {𝕜 : Type u_4} [normed_field 𝕜]
    [normed_space 𝕜 E] : semimodule 𝕜 ↥(Lp E p μ) :=
  semimodule.mk sorry sorry

theorem norm_const_smul {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {𝕜 : Type u_4} [normed_field 𝕜]
    [normed_space 𝕜 E] (c : 𝕜) (f : ↥(Lp E p μ)) : norm (c • f) = norm c * norm f :=
  sorry

protected instance normed_space {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure α}
    [measurable_space E] [normed_group E] [borel_space E]
    [topological_space.second_countable_topology E] {p : ennreal} {𝕜 : Type u_4} [normed_field 𝕜]
    [normed_space 𝕜 E] [fact (1 ≤ p)] : normed_space 𝕜 ↥(Lp E p μ) :=
  normed_space.mk sorry

end Mathlib