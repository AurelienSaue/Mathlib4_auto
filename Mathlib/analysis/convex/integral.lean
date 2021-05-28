/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.convex.basic
import Mathlib.measure_theory.set_integral
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Jensen's inequality for integrals

In this file we prove four theorems:

* `convex.smul_integral_mem`: if `μ` is a non-zero finite measure on `α`, `s` is a convex closed set
  in `E`, and `f` is an integrable function sending `μ`-a.e. points to `s`, then the average value
  of `f` belongs to `s`: `(μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s`. See also `convex.center_mass_mem`
  for a finite sum version of this lemma.

* `convex.integral_mem`: if `μ` is a probability measure on `α`, `s` is a convex closed set in `E`,
  and `f` is an integrable function sending `μ`-a.e. points to `s`, then the expected value of `f`
  belongs to `s`: `∫ x, f x ∂μ ∈ s`. See also `convex.sum_mem` for a finite sum version of this
  lemma.

* `convex_on.map_smul_integral_le`: Jensen's inequality: if a function `g : E → ℝ` is convex and
  continuous on a convex closed set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is
  a function sending `μ`-a.e. points to `s`, then the value of `g` at the average value of `f` is
  less than or equal to the average value of `g ∘ f` provided that both `f` and `g ∘ f` are
  integrable. See also `convex.map_center_mass_le` for a finite sum version of this lemma.

* `convex_on.map_integral_le`: Jensen's inequality: if a function `g : E → ℝ` is convex and
  continuous on a convex closed set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a
  function sending `μ`-a.e. points to `s`, then the value of `g` at the expected value of `f` is
  less than or equal to the expected value of `g ∘ f` provided that both `f` and `g ∘ f` are
  integrable. See also `convex.map_sum_le` for a finite sum version of this lemma.

## Tags

convex, integral, center mass, Jensen's inequality
-/

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s`. See also `convex.center_mass_mem` for a finite sum version
of this lemma. -/
theorem convex.smul_integral_mem {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [normed_group E] [normed_space ℝ E] [complete_space E] [topological_space.second_countable_topology E] [measurable_space E] [borel_space E] [measure_theory.finite_measure μ] {s : set E} (hs : convex s) (hsc : is_closed s) (hμ : μ ≠ 0) {f : α → E} (hfs : filter.eventually (fun (x : α) => f x ∈ s) (measure_theory.measure.ae μ)) (hfi : measure_theory.integrable f) : (ennreal.to_real (coe_fn μ set.univ)⁻¹ • measure_theory.integral μ fun (x : α) => f x) ∈ s := sorry

/-- If `μ` is a probability measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the expected value of `f` belongs to `s`:
`∫ x, f x ∂μ ∈ s`. See also `convex.sum_mem` for a finite sum version of this lemma. -/
theorem convex.integral_mem {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [normed_group E] [normed_space ℝ E] [complete_space E] [topological_space.second_countable_topology E] [measurable_space E] [borel_space E] [measure_theory.probability_measure μ] {s : set E} (hs : convex s) (hsc : is_closed s) {f : α → E} (hf : filter.eventually (fun (x : α) => f x ∈ s) (measure_theory.measure.ae μ)) (hfi : measure_theory.integrable f) : (measure_theory.integral μ fun (x : α) => f x) ∈ s := sorry

/-- Jensen's inequality: if a function `g : E → ℝ` is convex and continuous on a convex closed set
`s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending `μ`-a.e. points
to `s`, then the value of `g` at the average value of `f` is less than or equal to the average value
of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also `convex.map_center_mass_le`
for a finite sum version of this lemma. -/
theorem convex_on.map_smul_integral_le {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [normed_group E] [normed_space ℝ E] [complete_space E] [topological_space.second_countable_topology E] [measurable_space E] [borel_space E] [measure_theory.finite_measure μ] {s : set E} {g : E → ℝ} (hg : convex_on s g) (hgc : continuous_on g s) (hsc : is_closed s) (hμ : μ ≠ 0) {f : α → E} (hfs : filter.eventually (fun (x : α) => f x ∈ s) (measure_theory.measure.ae μ)) (hfi : measure_theory.integrable f) (hgi : measure_theory.integrable (g ∘ f)) : g (ennreal.to_real (coe_fn μ set.univ)⁻¹ • measure_theory.integral μ fun (x : α) => f x) ≤
  ennreal.to_real (coe_fn μ set.univ)⁻¹ • measure_theory.integral μ fun (x : α) => g (f x) := sorry

/-- Jensen's inequality: if a function `g : E → ℝ` is convex and continuous on a convex closed set
`s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e. points to
`s`, then the value of `g` at the expected value of `f` is less than or equal to the expected value
of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also `convex.map_sum_le` for a
finite sum version of this lemma. -/
theorem convex_on.map_integral_le {α : Type u_1} {E : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [normed_group E] [normed_space ℝ E] [complete_space E] [topological_space.second_countable_topology E] [measurable_space E] [borel_space E] [measure_theory.probability_measure μ] {s : set E} {g : E → ℝ} (hg : convex_on s g) (hgc : continuous_on g s) (hsc : is_closed s) {f : α → E} (hfs : filter.eventually (fun (x : α) => f x ∈ s) (measure_theory.measure.ae μ)) (hfi : measure_theory.integrable f) (hgi : measure_theory.integrable (g ∘ f)) : g (measure_theory.integral μ fun (x : α) => f x) ≤ measure_theory.integral μ fun (x : α) => g (f x) := sorry

