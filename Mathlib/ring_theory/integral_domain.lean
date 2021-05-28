/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.card
import Mathlib.data.polynomial.ring_division
import Mathlib.group_theory.order_of_element
import Mathlib.algebra.geom_sum
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Integral domains

Assorted theorems about integral domains.

## Main theorems

* `is_cyclic_of_subgroup_integral_domain` : A finite subgroup of the units of an integral domain
                                            is cyclic.
* `field_of_integral_domain`              : A finite integral domain is a field.

## Tags

integral domain, finite integral domain, finite field
-/

theorem card_nth_roots_subgroup_units {R : Type u_1} {G : Type u_2} [integral_domain R] [group G] [fintype G] (f : G →* R) (hf : function.injective ⇑f) {n : ℕ} (hn : 0 < n) (g₀ : G) : finset.card (has_sep.sep (fun (g : G) => g ^ n = g₀) finset.univ) ≤
  coe_fn multiset.card (polynomial.nth_roots n (coe_fn f g₀)) := sorry

/-- A finite subgroup of the unit group of an integral domain is cyclic. -/
theorem is_cyclic_of_subgroup_integral_domain {R : Type u_1} {G : Type u_2} [integral_domain R] [group G] [fintype G] (f : G →* R) (hf : function.injective ⇑f) : is_cyclic G := sorry

/-- The unit group of a finite integral domain is cyclic. -/
protected instance units.is_cyclic {R : Type u_1} [integral_domain R] [fintype R] : is_cyclic (units R) :=
  is_cyclic_of_subgroup_integral_domain (units.coe_hom R) units.ext

/-- Every finite integral domain is a field. -/
def field_of_integral_domain {R : Type u_1} [integral_domain R] [DecidableEq R] [fintype R] : field R :=
  field.mk integral_domain.add sorry integral_domain.zero sorry sorry integral_domain.neg integral_domain.sub sorry sorry
    integral_domain.mul sorry integral_domain.one sorry sorry sorry sorry sorry
    (fun (a : R) => dite (a = 0) (fun (h : a = 0) => 0) fun (h : ¬a = 0) => fintype.bij_inv sorry 1) sorry sorry sorry

/-- A finite subgroup of the units of an integral domain is cyclic. -/
protected instance subgroup_units_cyclic {R : Type u_1} [integral_domain R] (S : set (units R)) [is_subgroup S] [fintype ↥S] : is_cyclic ↥S := sorry

theorem card_fiber_eq_of_mem_range {G : Type u_2} [group G] [fintype G] {H : Type u_1} [group H] [DecidableEq H] (f : G →* H) {x : H} {y : H} (hx : x ∈ set.range ⇑f) (hy : y ∈ set.range ⇑f) : finset.card (finset.filter (fun (g : G) => coe_fn f g = x) finset.univ) =
  finset.card (finset.filter (fun (g : G) => coe_fn f g = y) finset.univ) := sorry

/-- In an integral domain, a sum indexed by a nontrivial homomorphism from a finite group is zero. -/
theorem sum_hom_units_eq_zero {R : Type u_1} {G : Type u_2} [integral_domain R] [group G] [fintype G] (f : G →* R) (hf : f ≠ 1) : (finset.sum finset.univ fun (g : G) => coe_fn f g) = 0 := sorry

/-- In an integral domain, a sum indexed by a homomorphism from a finite group is zero,
unless the homomorphism is trivial, in which case the sum is equal to the cardinality of the group. -/
theorem sum_hom_units {R : Type u_1} {G : Type u_2} [integral_domain R] [group G] [fintype G] (f : G →* R) [Decidable (f = 1)] : (finset.sum finset.univ fun (g : G) => coe_fn f g) = ite (f = 1) (↑(fintype.card G)) 0 := sorry

