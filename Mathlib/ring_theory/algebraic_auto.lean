/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.finite_dimensional
import Mathlib.ring_theory.integral_closure
import Mathlib.data.polynomial.integral_normalization
import Mathlib.PostPort

universes u v u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/

/-- An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial. -/
def is_algebraic (R : Type u) {A : Type v} [comm_ring R] [ring A] [algebra R A] (x : A) :=
  ∃ (p : polynomial R), p ≠ 0 ∧ coe_fn (polynomial.aeval x) p = 0

/-- A subalgebra is algebraic if all its elements are algebraic. -/
def subalgebra.is_algebraic {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
    (S : subalgebra R A) :=
  ∀ (x : A), x ∈ S → is_algebraic R x

/-- An algebra is algebraic if all its elements are algebraic. -/
def algebra.is_algebraic (R : Type u) (A : Type v) [comm_ring R] [ring A] [algebra R A] :=
  ∀ (x : A), is_algebraic R x

/-- A subalgebra is algebraic if and only if it is algebraic an algebra. -/
theorem subalgebra.is_algebraic_iff {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
    (S : subalgebra R A) : subalgebra.is_algebraic S ↔ algebra.is_algebraic R ↥S :=
  sorry

/-- An algebra is algebraic if and only if it is algebraic as a subalgebra. -/
theorem algebra.is_algebraic_iff {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] :
    algebra.is_algebraic R A ↔ subalgebra.is_algebraic ⊤ :=
  sorry

/-- An integral element of an algebra is algebraic.-/
theorem is_integral.is_algebraic (R : Type u) {A : Type v} [comm_ring R] [nontrivial R] [ring A]
    [algebra R A] {x : A} (h : is_integral R x) : is_algebraic R x :=
  sorry

/-- An element of an algebra over a field is algebraic if and only if it is integral.-/
theorem is_algebraic_iff_is_integral (K : Type u) {A : Type v} [field K] [ring A] [algebra K A]
    {x : A} : is_algebraic K x ↔ is_integral K x :=
  sorry

theorem is_algebraic_iff_is_integral' (K : Type u) {A : Type v} [field K] [ring A] [algebra K A] :
    algebra.is_algebraic K A ↔ algebra.is_integral K A :=
  { mp :=
      fun (h : algebra.is_algebraic K A) (x : A) => iff.mp (is_algebraic_iff_is_integral K) (h x),
    mpr :=
      fun (h : algebra.is_integral K A) (x : A) => iff.mpr (is_algebraic_iff_is_integral K) (h x) }

namespace algebra


/-- If L is an algebraic field extension of K and A is an algebraic algebra over L,
then A is algebraic over K. -/
theorem is_algebraic_trans {K : Type u_1} {L : Type u_2} {A : Type u_3} [field K] [field L]
    [comm_ring A] [algebra K L] [algebra L A] [algebra K A] [is_scalar_tower K L A]
    (L_alg : is_algebraic K L) (A_alg : is_algebraic L A) : is_algebraic K A :=
  sorry

/-- A field extension is algebraic if it is finite. -/
theorem is_algebraic_of_finite {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L]
    [finite : finite_dimensional K L] : is_algebraic K L :=
  fun (x : L) =>
    iff.mpr (is_algebraic_iff_is_integral K)
      (is_integral_of_submodule_noetherian ⊤
        (is_noetherian_of_submodule_of_noetherian K L (↑⊤) finite) x mem_top)

end algebra


theorem exists_integral_multiple {R : Type u_1} {S : Type u_2} [integral_domain R] [comm_ring S]
    [algebra R S] {z : S} (hz : is_algebraic R z)
    (inj : ∀ (x : R), coe_fn (algebra_map R S) x = 0 → x = 0) :
    ∃ (x : ↥(integral_closure R S)), ∃ (y : ↥(integral_closure R S)), ∃ (H : y ≠ 0), z * ↑y = ↑x :=
  sorry

theorem inv_eq_of_aeval_div_X_ne_zero {K : Type u_3} {L : Type u_4} [field K] [field L]
    [algebra K L] {x : L} {p : polynomial K}
    (aeval_ne : coe_fn (polynomial.aeval x) (polynomial.div_X p) ≠ 0) :
    x⁻¹ =
        coe_fn (polynomial.aeval x) (polynomial.div_X p) /
          (coe_fn (polynomial.aeval x) p - coe_fn (algebra_map K L) (polynomial.coeff p 0)) :=
  sorry

theorem inv_eq_of_root_of_coeff_zero_ne_zero {K : Type u_3} {L : Type u_4} [field K] [field L]
    [algebra K L] {x : L} {p : polynomial K} (aeval_eq : coe_fn (polynomial.aeval x) p = 0)
    (coeff_zero_ne : polynomial.coeff p 0 ≠ 0) :
    x⁻¹ =
        -(coe_fn (polynomial.aeval x) (polynomial.div_X p) /
            coe_fn (algebra_map K L) (polynomial.coeff p 0)) :=
  sorry

theorem subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero {K : Type u_3} {L : Type u_4} [field K]
    [field L] [algebra K L] (A : subalgebra K L) {x : ↥A} {p : polynomial K}
    (aeval_eq : coe_fn (polynomial.aeval x) p = 0) (coeff_zero_ne : polynomial.coeff p 0 ≠ 0) :
    ↑x⁻¹ ∈ A :=
  sorry

theorem subalgebra.inv_mem_of_algebraic {K : Type u_3} {L : Type u_4} [field K] [field L]
    [algebra K L] (A : subalgebra K L) {x : ↥A} (hx : is_algebraic K ↑x) : ↑x⁻¹ ∈ A :=
  sorry

/-- In an algebraic extension L/K, an intermediate subalgebra is a field. -/
theorem subalgebra.is_field_of_algebraic {K : Type u_3} {L : Type u_4} [field K] [field L]
    [algebra K L] (A : subalgebra K L) (hKL : algebra.is_algebraic K L) : is_field ↥A :=
  sorry

end Mathlib