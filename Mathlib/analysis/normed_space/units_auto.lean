/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.specific_limits
import Mathlib.analysis.asymptotics
import PostPort

universes u_1 

namespace Mathlib

/-!
# The group of units of a complete normed ring

This file contains the basic theory for the group of units (invertible elements) of a complete
normed ring (Banach algebras being a notable special case).

## Main results

The constructions `one_sub`, `add` and `unit_of_nearby` state, in varying forms, that perturbations
of a unit are units.  The latter two are not stated in their optimal form; more precise versions
would use the spectral radius.

The first main result is `is_open`:  the group of units of a complete normed ring is an open subset
of the ring.

The function `inverse` (defined in `algebra.ring`), for a ring `R`, sends `a : R` to `a⁻¹` if `a` is
a unit and 0 if not.  The other major results of this file (notably `inverse_add`,
`inverse_add_norm` and `inverse_add_norm_diff_nth_order`) cover the asymptotic properties of
`inverse (x + t)` as `t → 0`.

-/

namespace units


/-- In a complete normed ring, a perturbation of `1` by an element `t` of distance less than `1`
from `1` is a unit.  Here we construct its `units` structure.  -/
def one_sub {R : Type u_1} [normed_ring R] [complete_space R] (t : R) (h : norm t < 1) : units R :=
  mk (1 - t) (tsum fun (n : ℕ) => t ^ n) (mul_neg_geom_series t h) (geom_series_mul_neg t h)

@[simp] theorem one_sub_coe {R : Type u_1} [normed_ring R] [complete_space R] (t : R) (h : norm t < 1) : ↑(one_sub t h) = 1 - t :=
  rfl

/-- In a complete normed ring, a perturbation of a unit `x` by an element `t` of distance less than
`∥x⁻¹∥⁻¹` from `x` is a unit.  Here we construct its `units` structure. -/
def add {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) (t : R) (h : norm t < (norm ↑(x⁻¹)⁻¹)) : units R :=
  x * one_sub (-(↑(x⁻¹) * t)) sorry

@[simp] theorem add_coe {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) (t : R) (h : norm t < (norm ↑(x⁻¹)⁻¹)) : ↑(add x t h) = ↑x + t := sorry

/-- In a complete normed ring, an element `y` of distance less than `∥x⁻¹∥⁻¹` from `x` is a unit.
Here we construct its `units` structure. -/
def unit_of_nearby {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) (y : R) (h : norm (y - ↑x) < (norm ↑(x⁻¹)⁻¹)) : units R :=
  add x (y - ↑x) h

@[simp] theorem unit_of_nearby_coe {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) (y : R) (h : norm (y - ↑x) < (norm ↑(x⁻¹)⁻¹)) : ↑(unit_of_nearby x y h) = y := sorry

/-- The group of units of a complete normed ring is an open subset of the ring. -/
theorem is_open {R : Type u_1} [normed_ring R] [complete_space R] : is_open (set_of fun (x : R) => is_unit x) := sorry

theorem nhds {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) : (set_of fun (x : R) => is_unit x) ∈ nhds ↑x :=
  mem_nhds_sets is_open
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑x ∈ set_of fun (x : R) => is_unit x)) set.mem_set_of_eq)) (is_unit_unit x))

end units


namespace normed_ring


theorem inverse_one_sub {R : Type u_1} [normed_ring R] [complete_space R] (t : R) (h : norm t < 1) : ring.inverse (1 - t) = ↑(units.one_sub t h⁻¹) := sorry

/-- The formula `inverse (x + t) = inverse (1 + x⁻¹ * t) * x⁻¹` holds for `t` sufficiently small. -/
theorem inverse_add {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) : filter.eventually (fun (t : R) => ring.inverse (↑x + t) = ring.inverse (1 + ↑(x⁻¹) * t) * ↑(x⁻¹)) (nhds 0) := sorry

theorem inverse_one_sub_nth_order {R : Type u_1} [normed_ring R] [complete_space R] (n : ℕ) : filter.eventually
  (fun (t : R) =>
    ring.inverse (1 - t) = (finset.sum (finset.range n) fun (i : ℕ) => t ^ i) + t ^ n * ring.inverse (1 - t))
  (nhds 0) := sorry

/-- The formula
`inverse (x + t) = (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹ + (- x⁻¹ * t) ^ n * inverse (x + t)`
holds for `t` sufficiently small. -/
theorem inverse_add_nth_order {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) (n : ℕ) : filter.eventually
  (fun (t : R) =>
    ring.inverse (↑x + t) =
      (finset.sum (finset.range n) fun (i : ℕ) => (-↑(x⁻¹) * t) ^ i) * ↑(x⁻¹) +
        (-↑(x⁻¹) * t) ^ n * ring.inverse (↑x + t))
  (nhds 0) := sorry

theorem inverse_one_sub_norm {R : Type u_1} [normed_ring R] [complete_space R] : asymptotics.is_O (fun (t : R) => ring.inverse (1 - t)) (fun (t : R) => 1) (nhds 0) := sorry

/-- The function `λ t, inverse (x + t)` is O(1) as `t → 0`. -/
theorem inverse_add_norm {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) : asymptotics.is_O (fun (t : R) => ring.inverse (↑x + t)) (fun (t : R) => 1) (nhds 0) := sorry

/-- The function
`λ t, inverse (x + t) - (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹`
is `O(t ^ n)` as `t → 0`. -/
theorem inverse_add_norm_diff_nth_order {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) (n : ℕ) : asymptotics.is_O
  (fun (t : R) => ring.inverse (↑x + t) - (finset.sum (finset.range n) fun (i : ℕ) => (-↑(x⁻¹) * t) ^ i) * ↑(x⁻¹))
  (fun (t : R) => norm t ^ n) (nhds 0) := sorry

/-- The function `λ t, inverse (x + t) - x⁻¹` is `O(t)` as `t → 0`. -/
theorem inverse_add_norm_diff_first_order {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) : asymptotics.is_O (fun (t : R) => ring.inverse (↑x + t) - ↑(x⁻¹)) (fun (t : R) => norm t) (nhds 0) := sorry

/-- The function
`λ t, inverse (x + t) - x⁻¹ + x⁻¹ * t * x⁻¹`
is `O(t ^ 2)` as `t → 0`. -/
theorem inverse_add_norm_diff_second_order {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) : asymptotics.is_O (fun (t : R) => ring.inverse (↑x + t) - ↑(x⁻¹) + ↑(x⁻¹) * t * ↑(x⁻¹)) (fun (t : R) => norm t ^ bit0 1)
  (nhds 0) := sorry

/-- The function `inverse` is continuous at each unit of `R`. -/
theorem inverse_continuous_at {R : Type u_1} [normed_ring R] [complete_space R] (x : units R) : continuous_at ring.inverse ↑x := sorry

