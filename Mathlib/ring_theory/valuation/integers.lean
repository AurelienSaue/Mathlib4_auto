/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.valuation.basic
import Mathlib.PostPort

universes u v w l 

namespace Mathlib

/-!
# Ring of integers under a given valuation

The elements with valuation less than or equal to 1.

TODO: Define characteristic predicate.
-/

namespace valuation


/-- The ring of integers under a given valuation is the subring of elements with valuation ≤ 1. -/
def integer {R : Type u} {Γ₀ : Type v} [ring R] [linear_ordered_comm_group_with_zero Γ₀] (v : valuation R Γ₀) : subring R :=
  subring.mk (set_of fun (x : R) => coe_fn v x ≤ 1) sorry sorry sorry sorry sorry

/-- Given a valuation v : R → Γ₀ and a ring homomorphism O →+* R, we say that O is the integers of v
if f is injective, and its range is exactly `v.integer`. -/
structure integers {R : Type u} {Γ₀ : Type v} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀] (v : valuation R Γ₀) (O : Type w) [comm_ring O] [algebra O R] 
where
  hom_inj : function.injective ⇑(algebra_map O R)
  map_le_one : ∀ (x : O), coe_fn v (coe_fn (algebra_map O R) x) ≤ 1
  exists_of_le_one : ∀ {r : R}, coe_fn v r ≤ 1 → ∃ (x : O), coe_fn (algebra_map O R) x = r

-- typeclass shortcut

protected instance algebra {R : Type u} {Γ₀ : Type v} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀] (v : valuation R Γ₀) : algebra (↥(integer v)) R :=
  algebra.of_subring (integer v)

theorem integer.integers {R : Type u} {Γ₀ : Type v} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀] (v : valuation R Γ₀) : integers v ↥(integer v) :=
  integers.mk subtype.coe_injective (fun (r : ↥(integer v)) => subtype.property r)
    fun (r : R) (hr : coe_fn v r ≤ 1) => Exists.intro { val := r, property := hr } rfl

namespace integers


theorem one_of_is_unit {R : Type u} {Γ₀ : Type v} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀] {v : valuation R Γ₀} {O : Type w} [comm_ring O] [algebra O R] (hv : integers v O) {x : O} (hx : is_unit x) : coe_fn v (coe_fn (algebra_map O R) x) = 1 := sorry

theorem is_unit_of_one {R : Type u} {Γ₀ : Type v} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀] {v : valuation R Γ₀} {O : Type w} [comm_ring O] [algebra O R] (hv : integers v O) {x : O} (hx : is_unit (coe_fn (algebra_map O R) x)) (hvx : coe_fn v (coe_fn (algebra_map O R) x) = 1) : is_unit x := sorry

theorem le_of_dvd {R : Type u} {Γ₀ : Type v} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀] {v : valuation R Γ₀} {O : Type w} [comm_ring O] [algebra O R] (hv : integers v O) {x : O} {y : O} (h : x ∣ y) : coe_fn v (coe_fn (algebra_map O R) y) ≤ coe_fn v (coe_fn (algebra_map O R) x) := sorry

end integers


namespace integers


theorem dvd_of_le {F : Type u} {Γ₀ : Type v} [field F] [linear_ordered_comm_group_with_zero Γ₀] {v : valuation F Γ₀} {O : Type w} [comm_ring O] [algebra O F] (hv : integers v O) {x : O} {y : O} (h : coe_fn v (coe_fn (algebra_map O F) x) ≤ coe_fn v (coe_fn (algebra_map O F) y)) : y ∣ x := sorry

theorem dvd_iff_le {F : Type u} {Γ₀ : Type v} [field F] [linear_ordered_comm_group_with_zero Γ₀] {v : valuation F Γ₀} {O : Type w} [comm_ring O] [algebra O F] (hv : integers v O) {x : O} {y : O} : x ∣ y ↔ coe_fn v (coe_fn (algebra_map O F) y) ≤ coe_fn v (coe_fn (algebra_map O F) x) :=
  { mp := le_of_dvd hv, mpr := dvd_of_le hv }

theorem le_iff_dvd {F : Type u} {Γ₀ : Type v} [field F] [linear_ordered_comm_group_with_zero Γ₀] {v : valuation F Γ₀} {O : Type w} [comm_ring O] [algebra O F] (hv : integers v O) {x : O} {y : O} : coe_fn v (coe_fn (algebra_map O F) x) ≤ coe_fn v (coe_fn (algebra_map O F) y) ↔ y ∣ x :=
  { mp := dvd_of_le hv, mpr := le_of_dvd hv }

