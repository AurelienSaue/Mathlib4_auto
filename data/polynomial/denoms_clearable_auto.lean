/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.polynomial.erase_lead
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Denominators of evaluation of polynomials at ratios

Let `i : R → K` be a homomorphism of semirings.  Assume that `K` is commutative.  If `a` and
`b` are elements of `R` such that `i b ∈ K` is invertible, then for any polynomial
`f ∈ polynomial R` the "mathematical" expression `b ^ f.nat_degree * f (a / b) ∈ K` is in
the image of the homomorphism `i`.
-/

-- TODO: use hypothesis (ub : is_unit (i b)) to work with localizations.

/-- `denoms_clearable` formalizes the property that `b ^ N * f (a / b)`
does not have denominators, if the inequality `f.nat_degree ≤ N` holds.

In the implementation, we also use provide an inverse in the existential.
-/
def denoms_clearable {R : Type u_1} {K : Type u_2} [semiring R] [comm_semiring K] (a : R) (b : R) (N : ℕ) (f : polynomial R) (i : R →+* K)  :=
  ∃ (D : R),
    ∃ (bi : K), bi * coe_fn i b = 1 ∧ coe_fn i D = coe_fn i b ^ N * polynomial.eval (coe_fn i a * bi) (polynomial.map i f)

theorem denoms_clearable_zero {R : Type u_1} {K : Type u_2} [semiring R] [comm_semiring K] {i : R →+* K} {b : R} {bi : K} (N : ℕ) (a : R) (bu : bi * coe_fn i b = 1) : denoms_clearable a b N 0 i := sorry

theorem denoms_clearable_C_mul_X_pow {R : Type u_1} {K : Type u_2} [semiring R] [comm_semiring K] {i : R →+* K} {b : R} {bi : K} {N : ℕ} (a : R) (bu : bi * coe_fn i b = 1) {n : ℕ} (r : R) (nN : n ≤ N) : denoms_clearable a b N (coe_fn polynomial.C r * polynomial.X ^ n) i := sorry

theorem denoms_clearable.add {R : Type u_1} {K : Type u_2} [semiring R] [comm_semiring K] {i : R →+* K} {a : R} {b : R} {N : ℕ} {f : polynomial R} {g : polynomial R} : denoms_clearable a b N f i → denoms_clearable a b N g i → denoms_clearable a b N (f + g) i := sorry

theorem denoms_clearable_of_nat_degree_le {R : Type u_1} {K : Type u_2} [semiring R] [comm_semiring K] {i : R →+* K} {b : R} {bi : K} (N : ℕ) (a : R) (bu : bi * coe_fn i b = 1) (f : polynomial R) : polynomial.nat_degree f ≤ N → denoms_clearable a b N f i := sorry

/-- If `i : R → K` is a ring homomorphism, `f` is a polynomial with coefficients in `R`,
`a, b` are elements of `R`, with `i b` invertible, then there is a `D ∈ R` such that
`b ^ f.nat_degree * f (a / b)` equals `i D`. -/
theorem denoms_clearable_nat_degree {R : Type u_1} {K : Type u_2} [semiring R] [comm_semiring K] {b : R} {bi : K} (i : R →+* K) (f : polynomial R) (a : R) (bu : bi * coe_fn i b = 1) : denoms_clearable a b (polynomial.nat_degree f) f i :=
  denoms_clearable_of_nat_degree_le (polynomial.nat_degree f) a bu f le_rfl

