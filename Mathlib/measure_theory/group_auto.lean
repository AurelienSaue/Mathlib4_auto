/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.integration
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: left and right invariant measures.
* We define the measure `μ.inv : A ↦ μ(A⁻¹)` and show that it is right invariant iff
  `μ` is left invariant.
-/

namespace measure_theory


/-- A measure `μ` on a topological group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself.
  To left translate sets we use preimage under left multiplication,
  since preimages are nicer to work with than images. -/
def is_add_left_invariant {G : Type u_1} [measurable_space G] [Add G] (μ : set G → ennreal) :=
  ∀ (g : G) {A : set G} (h : is_measurable A), μ ((fun (h : G) => g + h) ⁻¹' A) = μ A

/-- A measure `μ` on a topological group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself.
  To right translate sets we use preimage under right multiplication,
  since preimages are nicer to work with than images. -/
def is_add_right_invariant {G : Type u_1} [measurable_space G] [Add G] (μ : set G → ennreal) :=
  ∀ (g : G) {A : set G} (h : is_measurable A), μ ((fun (h : G) => h + g) ⁻¹' A) = μ A

namespace measure


theorem map_mul_left_eq_self {G : Type u_1} [measurable_space G] [topological_space G] [Mul G]
    [has_continuous_mul G] [borel_space G] {μ : measure G} :
    (∀ (g : G), coe_fn (map (Mul.mul g)) μ = μ) ↔ is_mul_left_invariant ⇑μ :=
  sorry

theorem map_mul_right_eq_self {G : Type u_1} [measurable_space G] [topological_space G] [Mul G]
    [has_continuous_mul G] [borel_space G] {μ : measure G} :
    (∀ (g : G), coe_fn (map fun (h : G) => h * g) μ = μ) ↔ is_mul_right_invariant ⇑μ :=
  sorry

/-- The measure `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
protected def neg {G : Type u_1} [measurable_space G] [Neg G] (μ : measure G) : measure G :=
  coe_fn (map Neg.neg) μ

theorem neg_apply {G : Type u_1} [measurable_space G] [add_group G] [topological_space G]
    [topological_add_group G] [borel_space G] (μ : measure G) {s : set G} (hs : is_measurable s) :
    coe_fn (measure.neg μ) s = coe_fn μ (-s) :=
  sorry

@[simp] protected theorem neg_neg {G : Type u_1} [measurable_space G] [add_group G]
    [topological_space G] [topological_add_group G] [borel_space G] (μ : measure G) :
    measure.neg (measure.neg μ) = μ :=
  sorry

theorem regular.neg {G : Type u_1} [measurable_space G] [add_group G] [topological_space G]
    [topological_add_group G] [borel_space G] {μ : measure G} [t2_space G] (hμ : regular μ) :
    regular (measure.neg μ) :=
  regular.map hμ (homeomorph.neg G)

end measure


@[simp] theorem regular_inv_iff {G : Type u_1} [measurable_space G] [group G] [topological_space G]
    [topological_group G] [borel_space G] {μ : measure G} [t2_space G] :
    measure.regular (measure.inv μ) ↔ measure.regular μ :=
  sorry

theorem is_add_left_invariant.neg {G : Type u_1} [measurable_space G] [add_group G]
    [topological_space G] [topological_add_group G] [borel_space G] {μ : measure G}
    (h : is_add_left_invariant ⇑μ) : is_add_right_invariant ⇑(measure.neg μ) :=
  sorry

theorem is_mul_right_invariant.inv {G : Type u_1} [measurable_space G] [group G]
    [topological_space G] [topological_group G] [borel_space G] {μ : measure G}
    (h : is_mul_right_invariant ⇑μ) : is_mul_left_invariant ⇑(measure.inv μ) :=
  sorry

@[simp] theorem is_mul_right_invariant_inv {G : Type u_1} [measurable_space G] [group G]
    [topological_space G] [topological_group G] [borel_space G] {μ : measure G} :
    is_mul_right_invariant ⇑(measure.inv μ) ↔ is_mul_left_invariant ⇑μ :=
  sorry

@[simp] theorem is_add_left_invariant_neg {G : Type u_1} [measurable_space G] [add_group G]
    [topological_space G] [topological_add_group G] [borel_space G] {μ : measure G} :
    is_add_left_invariant ⇑(measure.neg μ) ↔ is_add_right_invariant ⇑μ :=
  sorry

/-! Properties of regular left invariant measures -/

theorem is_mul_left_invariant.null_iff_empty {G : Type u_1} [measurable_space G]
    [topological_space G] [borel_space G] {μ : measure G} [group G] [topological_group G]
    (hμ : measure.regular μ) (h2μ : is_mul_left_invariant ⇑μ) (h3μ : μ ≠ 0) {s : set G}
    (hs : is_open s) : coe_fn μ s = 0 ↔ s = ∅ :=
  sorry

theorem is_mul_left_invariant.null_iff {G : Type u_1} [measurable_space G] [topological_space G]
    [borel_space G] {μ : measure G} [group G] [topological_group G] (hμ : measure.regular μ)
    (h2μ : is_mul_left_invariant ⇑μ) {s : set G} (hs : is_open s) :
    coe_fn μ s = 0 ↔ s = ∅ ∨ μ = 0 :=
  sorry

theorem is_mul_left_invariant.measure_ne_zero_iff_nonempty {G : Type u_1} [measurable_space G]
    [topological_space G] [borel_space G] {μ : measure G} [group G] [topological_group G]
    (hμ : measure.regular μ) (h2μ : is_mul_left_invariant ⇑μ) (h3μ : μ ≠ 0) {s : set G}
    (hs : is_open s) : coe_fn μ s ≠ 0 ↔ set.nonempty s :=
  sorry

/-- For nonzero regular left invariant measures, the integral of a continuous nonnegative function
  `f` is 0 iff `f` is 0. -/
-- @[to_additive] (fails for now)

theorem lintegral_eq_zero_of_is_mul_left_invariant {G : Type u_1} [measurable_space G]
    [topological_space G] [borel_space G] {μ : measure G} [group G] [topological_group G]
    (hμ : measure.regular μ) (h2μ : is_mul_left_invariant ⇑μ) (h3μ : μ ≠ 0) {f : G → ennreal}
    (hf : continuous f) : (lintegral μ fun (x : G) => f x) = 0 ↔ f = 0 :=
  sorry

end Mathlib