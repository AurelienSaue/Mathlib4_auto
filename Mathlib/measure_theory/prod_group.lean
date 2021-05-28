/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.prod
import Mathlib.measure_theory.group
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Measure theory in the product of groups

In this file we show properties about measure theory in products of topological groups
and properties of iterated integrals in topological groups.

These lemmas show the uniqueness of left invariant measures on locally compact groups, up to
scaling. In this file we follow the proof and refer to the book *Measure Theory* by Paul Halmos.

The idea of the proof is to use the translation invariance of measures to prove `μ(F) = c * μ(E)`
for two sets `E` and `F`, where `c` is a constant that does not depend on `μ`. Let `e` and `f` be
the characteristic functions of `E` and `F`.
Assume that `μ` and `ν` are left-invariant measures. Then the map `(x, y) ↦ (y * x, x⁻¹)`
preserves the measure `μ.prod ν`, which means that
```
  ∫ x, ∫ y, h x y ∂ν ∂μ = ∫ x, ∫ y, h (y * x) x⁻¹ ∂ν ∂μ
```
If we apply this to `h x y := e x * f y⁻¹ / ν ((λ h, h * y⁻¹) ⁻¹' E)`, we can rewrite the RHS to
`μ(F)`, and the LHS to `c * μ(E)`, where `c = c(ν)` does not depend on `μ`.
Applying this to `μ` and to `ν` gives `μ (F) / μ (E) = ν (F) / ν (E)`, which is the uniqueness up to
scalar multiplication.

The proof in [Halmos] seems to contain an omission in §60 Th. A, see
`measure_theory.measure_lintegral_div_measure` and
https://math.stackexchange.com/questions/3974485/does-right-translation-preserve-finiteness-for-a-left-invariant-measure
-/

namespace measure_theory


/-- This condition is part of the definition of a measurable group in [Halmos, §59].
  There, the map in this lemma is called `S`. -/
theorem map_prod_mul_eq {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} {ν : measure G} [sigma_finite ν] [sigma_finite μ] (hν : is_mul_left_invariant ⇑ν) : coe_fn (measure.map fun (z : G × G) => (prod.fst z, prod.fst z * prod.snd z)) (measure.prod μ ν) = measure.prod μ ν := sorry

/-- The function we are mapping along is `SR` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
theorem map_prod_mul_eq_swap {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} {ν : measure G} [sigma_finite ν] [sigma_finite μ] (hμ : is_mul_left_invariant ⇑μ) : coe_fn (measure.map fun (z : G × G) => (prod.snd z, prod.snd z * prod.fst z)) (measure.prod μ ν) = measure.prod ν μ := sorry

/-- The function we are mapping along is `S⁻¹` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq`. -/
theorem map_prod_inv_mul_eq {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} {ν : measure G} [sigma_finite ν] [sigma_finite μ] (hν : is_mul_left_invariant ⇑ν) : coe_fn (measure.map fun (z : G × G) => (prod.fst z, prod.fst z⁻¹ * prod.snd z)) (measure.prod μ ν) = measure.prod μ ν :=
  iff.mp
    (measurable_equiv.map_apply_eq_iff_map_symm_apply_eq (homeomorph.to_measurable_equiv (homeomorph.shear_mul_right G)))
    (map_prod_mul_eq hν)

/-- The function we are mapping along is `S⁻¹R` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
theorem map_prod_inv_mul_eq_swap {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} {ν : measure G} [sigma_finite ν] [sigma_finite μ] (hμ : is_mul_left_invariant ⇑μ) : coe_fn (measure.map fun (z : G × G) => (prod.snd z, prod.snd z⁻¹ * prod.fst z)) (measure.prod μ ν) = measure.prod ν μ := sorry

/-- The function we are mapping along is `S⁻¹RSR` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
theorem map_prod_mul_inv_eq {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} {ν : measure G} [sigma_finite ν] [sigma_finite μ] (hμ : is_mul_left_invariant ⇑μ) (hν : is_mul_left_invariant ⇑ν) : coe_fn (measure.map fun (z : G × G) => (prod.snd z * prod.fst z, prod.fst z⁻¹)) (measure.prod μ ν) = measure.prod μ ν := sorry

theorem measure_null_of_measure_inv_null {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} [sigma_finite μ] (hμ : is_mul_left_invariant ⇑μ) {E : set G} (hE : is_measurable E) (h2E : coe_fn μ ((fun (x : G) => x⁻¹) ⁻¹' E) = 0) : coe_fn μ E = 0 := sorry

theorem measure_inv_null {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} [sigma_finite μ] (hμ : is_mul_left_invariant ⇑μ) {E : set G} (hE : is_measurable E) : coe_fn μ ((fun (x : G) => x⁻¹) ⁻¹' E) = 0 ↔ coe_fn μ E = 0 := sorry

theorem measurable_measure_mul_right {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} [sigma_finite μ] {E : set G} (hE : is_measurable E) : measurable fun (x : G) => coe_fn μ ((fun (y : G) => y * x) ⁻¹' E) := sorry

theorem lintegral_lintegral_mul_inv {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} {ν : measure G} [sigma_finite ν] [sigma_finite μ] (hμ : is_mul_left_invariant ⇑μ) (hν : is_mul_left_invariant ⇑ν) (f : G → G → ennreal) (hf : measurable (function.uncurry f)) : (lintegral μ fun (x : G) => lintegral ν fun (y : G) => f (y * x) (x⁻¹)) =
  lintegral μ fun (x : G) => lintegral ν fun (y : G) => f x y := sorry

theorem measure_mul_right_null {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} [sigma_finite μ] (hμ : is_mul_left_invariant ⇑μ) {E : set G} (hE : is_measurable E) (y : G) : coe_fn μ ((fun (x : G) => x * y) ⁻¹' E) = 0 ↔ coe_fn μ E = 0 := sorry

theorem measure_mul_right_ne_zero {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} [sigma_finite μ] (hμ : is_mul_left_invariant ⇑μ) {E : set G} (hE : is_measurable E) (h2E : coe_fn μ E ≠ 0) (y : G) : coe_fn μ ((fun (x : G) => x * y) ⁻¹' E) ≠ 0 :=
  iff.mpr (not_iff_not_of_iff (measure_mul_right_null hμ hE y)) h2E

/-- A technical lemma relating two different measures. This is basically [Halmos, §60 Th. A].
  Note that if `f` is the characteristic function of a measurable set `F` this states that
  `μ F = c * μ E` for a constant `c` that does not depend on `μ`.
  There seems to be a gap in the last step of the proof in [Halmos].
  In the last line, the equality `g(x⁻¹)ν(Ex⁻¹) = f(x)` holds if we can prove that
  `0 < ν(Ex⁻¹) < ∞`. The first inequality follows from §59, Th. D, but I couldn't find the second
  inequality. For this reason, we use a compact `E` instead of a measurable `E` as in [Halmos], and
  additionally assume that `ν` is a regular measure (we only need that it is finite on compact
  sets). -/
theorem measure_lintegral_div_measure {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} {ν : measure G} [sigma_finite ν] [sigma_finite μ] [t2_space G] (hμ : is_mul_left_invariant ⇑μ) (hν : is_mul_left_invariant ⇑ν) (h2ν : measure.regular ν) {E : set G} (hE : is_compact E) (h2E : coe_fn ν E ≠ 0) (f : G → ennreal) (hf : measurable f) : (coe_fn μ E * lintegral ν fun (y : G) => f (y⁻¹) / coe_fn ν ((fun (h : G) => h * (y⁻¹)) ⁻¹' E)) =
  lintegral μ fun (x : G) => f x := sorry

/-- This is roughly the uniqueness (up to a scalar) of left invariant Borel measures on a second
  countable locally compact group. The uniqueness of Haar measure is proven from this in
  `measure_theory.measure.haar_measure_unique` -/
theorem measure_mul_measure_eq {G : Type u_1} [topological_space G] [measurable_space G] [topological_space.second_countable_topology G] [borel_space G] [group G] [topological_group G] {μ : measure G} {ν : measure G} [sigma_finite ν] [sigma_finite μ] [t2_space G] (hμ : is_mul_left_invariant ⇑μ) (hν : is_mul_left_invariant ⇑ν) (h2ν : measure.regular ν) {E : set G} {F : set G} (hE : is_compact E) (hF : is_measurable F) (h2E : coe_fn ν E ≠ 0) : coe_fn μ E * coe_fn ν F = coe_fn ν E * coe_fn μ F := sorry

