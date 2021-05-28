/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.module.pi
import Mathlib.algebra.ordered_pi
import Mathlib.algebra.module.prod
import Mathlib.algebra.ordered_field
import Mathlib.PostPort

universes u_1 u_2 l u_3 

namespace Mathlib

/-!
# Ordered semimodules

In this file we define

* `ordered_semimodule R M` : an ordered additive commutative monoid `M` is an `ordered_semimodule`
  over an `ordered_semiring` `R` if the scalar product respects the order relation on the
  monoid and on the ring. There is a correspondence between this structure and convex cones,
  which is proven in `analysis/convex/cone.lean`.

## Implementation notes

* We choose to define `ordered_semimodule` as a `Prop`-valued mixin, so that it can be
  used for both modules and algebras
  (the axioms for an "ordered algebra" are exactly that the algebra is ordered as a module).
* To get ordered modules and ordered vector spaces, it suffices to the replace the
  `order_add_comm_monoid` and the `ordered_semiring` as desired.

## References

* https://en.wikipedia.org/wiki/Ordered_vector_space

## Tags

ordered semimodule, ordered module, ordered vector space
-/

/--
An ordered semimodule is an ordered additive commutative monoid
with a partial order in which the scalar multiplication is compatible with the order.
-/
class ordered_semimodule (R : Type u_1) (M : Type u_2) [ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M] 
where
  smul_lt_smul_of_pos : ∀ {a b : M} {c : R}, a < b → 0 < c → c • a < c • b
  lt_of_smul_lt_smul_of_pos : ∀ {a b : M} {c : R}, c • a < c • b → 0 < c → a < b

theorem smul_lt_smul_of_pos {R : Type u_1} {M : Type u_2} [ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M] [ordered_semimodule R M] {a : M} {b : M} {c : R} : a < b → 0 < c → c • a < c • b :=
  ordered_semimodule.smul_lt_smul_of_pos

theorem smul_le_smul_of_nonneg {R : Type u_1} {M : Type u_2} [ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M] [ordered_semimodule R M] {a : M} {b : M} {c : R} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c • a ≤ c • b := sorry

theorem eq_of_smul_eq_smul_of_pos_of_le {R : Type u_1} {M : Type u_2} [ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M] [ordered_semimodule R M] {a : M} {b : M} {c : R} (h₁ : c • a = c • b) (hc : 0 < c) (hle : a ≤ b) : a = b :=
  or.resolve_left (has_le.le.lt_or_eq hle) fun (hlt : a < b) => has_lt.lt.ne (smul_lt_smul_of_pos hlt hc) h₁

theorem lt_of_smul_lt_smul_of_nonneg {R : Type u_1} {M : Type u_2} [ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M] [ordered_semimodule R M] {a : M} {b : M} {c : R} (h : c • a < c • b) (hc : 0 ≤ c) : a < b := sorry

theorem smul_lt_smul_iff_of_pos {R : Type u_1} {M : Type u_2} [ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M] [ordered_semimodule R M] {a : M} {b : M} {c : R} (hc : 0 < c) : c • a < c • b ↔ a < b :=
  { mp := fun (h : c • a < c • b) => lt_of_smul_lt_smul_of_nonneg h (has_lt.lt.le hc),
    mpr := fun (h : a < b) => smul_lt_smul_of_pos h hc }

theorem smul_pos_iff_of_pos {R : Type u_1} {M : Type u_2} [ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M] [ordered_semimodule R M] {a : M} {c : R} (hc : 0 < c) : 0 < c • a ↔ 0 < a :=
  iff.trans (eq.mpr (id (Eq._oldrec (Eq.refl (0 < c • a ↔ c • 0 < c • a)) (smul_zero c))) (iff.refl (0 < c • a)))
    (smul_lt_smul_iff_of_pos hc)

/-- If `R` is a linear ordered semifield, then it suffices to verify only the first axiom of
`ordered_semimodule`. Moreover, it suffices to verify that `a < b` and `0 < c` imply
`c • a ≤ c • b`. We have no semifields in `mathlib`, so we use the assumption `∀ c ≠ 0, is_unit c`
instead. -/
theorem ordered_semimodule.mk'' {R : Type u_1} {M : Type u_2} [linear_ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M] (hR : ∀ {c : R}, c ≠ 0 → is_unit c) (hlt : ∀ {a b : M} {c : R}, a < b → 0 < c → c • a ≤ c • b) : ordered_semimodule R M := sorry

/-- If `R` is a linear ordered field, then it suffices to verify only the first axiom of
`ordered_semimodule`. -/
theorem ordered_semimodule.mk' {k : Type u_1} {M : Type u_2} [linear_ordered_field k] [ordered_add_comm_monoid M] [semimodule k M] (hlt : ∀ {a b : M} {c : k}, a < b → 0 < c → c • a ≤ c • b) : ordered_semimodule k M :=
  ordered_semimodule.mk'' (fun (c : k) (hc : c ≠ 0) => is_unit.mk0 c hc) hlt

protected instance linear_ordered_semiring.to_ordered_semimodule {R : Type u_1} [linear_ordered_semiring R] : ordered_semimodule R R :=
  ordered_semimodule.mk ordered_semiring.mul_lt_mul_of_pos_left
    fun (_x _x_1 _x_2 : R) (h : _x_2 • _x < _x_2 • _x_1) (hc : 0 < _x_2) => lt_of_mul_lt_mul_left h (has_lt.lt.le hc)

theorem smul_le_smul_iff_of_pos {k : Type u_1} {M : Type u_2} [linear_ordered_field k] [ordered_add_comm_group M] [semimodule k M] [ordered_semimodule k M] {a : M} {b : M} {c : k} (hc : 0 < c) : c • a ≤ c • b ↔ a ≤ b := sorry

theorem smul_le_smul_iff_of_neg {k : Type u_1} {M : Type u_2} [linear_ordered_field k] [ordered_add_comm_group M] [semimodule k M] [ordered_semimodule k M] {a : M} {b : M} {c : k} (hc : c < 0) : c • a ≤ c • b ↔ b ≤ a := sorry

theorem smul_lt_iff_of_pos {k : Type u_1} {M : Type u_2} [linear_ordered_field k] [ordered_add_comm_group M] [semimodule k M] [ordered_semimodule k M] {a : M} {b : M} {c : k} (hc : 0 < c) : c • a < b ↔ a < c⁻¹ • b := sorry

theorem smul_le_iff_of_pos {k : Type u_1} {M : Type u_2} [linear_ordered_field k] [ordered_add_comm_group M] [semimodule k M] [ordered_semimodule k M] {a : M} {b : M} {c : k} (hc : 0 < c) : c • a ≤ b ↔ a ≤ c⁻¹ • b := sorry

theorem le_smul_iff_of_pos {k : Type u_1} {M : Type u_2} [linear_ordered_field k] [ordered_add_comm_group M] [semimodule k M] [ordered_semimodule k M] {a : M} {b : M} {c : k} (hc : 0 < c) : a ≤ c • b ↔ c⁻¹ • a ≤ b := sorry

protected instance prod.ordered_semimodule {k : Type u_1} {M : Type u_2} {N : Type u_3} [linear_ordered_field k] [ordered_add_comm_group M] [semimodule k M] [ordered_semimodule k M] [ordered_add_comm_group N] [semimodule k N] [ordered_semimodule k N] : ordered_semimodule k (M × N) :=
  ordered_semimodule.mk'
    fun (v u : M × N) (c : k) (h : v < u) (hc : 0 < c) =>
      { left := smul_le_smul_of_nonneg (and.left (and.left h)) (has_lt.lt.le hc),
        right := smul_le_smul_of_nonneg (and.right (and.left h)) (has_lt.lt.le hc) }

protected instance pi.ordered_semimodule {k : Type u_1} [linear_ordered_field k] {ι : Type u_2} {M : ι → Type u_3} [(i : ι) → ordered_add_comm_group (M i)] [(i : ι) → semimodule k (M i)] [∀ (i : ι), ordered_semimodule k (M i)] : ordered_semimodule k ((i : ι) → M i) :=
  ordered_semimodule.mk'
    fun (v u : (i : ι) → M i) (c : k) (h : v < u) (hc : 0 < c) (i : ι) =>
      id (smul_le_smul_of_nonneg (has_lt.lt.le h i) (has_lt.lt.le hc))

-- Sometimes Lean fails to apply the dependent version to non-dependent functions,

-- so we define another instance

protected instance pi.ordered_semimodule' {k : Type u_1} [linear_ordered_field k] {ι : Type u_2} {M : Type u_3} [ordered_add_comm_group M] [semimodule k M] [ordered_semimodule k M] : ordered_semimodule k (ι → M) :=
  pi.ordered_semimodule

protected instance order_dual.has_scalar {R : Type u_1} {M : Type u_2} [semiring R] [ordered_add_comm_monoid M] [semimodule R M] : has_scalar R (order_dual M) :=
  has_scalar.mk has_scalar.smul

protected instance order_dual.mul_action {R : Type u_1} {M : Type u_2} [semiring R] [ordered_add_comm_monoid M] [semimodule R M] : mul_action R (order_dual M) :=
  mul_action.mk sorry sorry

protected instance order_dual.distrib_mul_action {R : Type u_1} {M : Type u_2} [semiring R] [ordered_add_comm_monoid M] [semimodule R M] : distrib_mul_action R (order_dual M) :=
  distrib_mul_action.mk sorry sorry

protected instance order_dual.semimodule {R : Type u_1} {M : Type u_2} [semiring R] [ordered_add_comm_monoid M] [semimodule R M] : semimodule R (order_dual M) :=
  semimodule.mk sorry sorry

protected instance order_dual.ordered_semimodule {R : Type u_1} {M : Type u_2} [ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M] [ordered_semimodule R M] : ordered_semimodule R (order_dual M) :=
  ordered_semimodule.mk (fun (a b : order_dual M) => ordered_semimodule.smul_lt_smul_of_pos)
    fun (a b : order_dual M) => ordered_semimodule.lt_of_smul_lt_smul_of_pos

