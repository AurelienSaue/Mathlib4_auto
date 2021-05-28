/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.monic
import Mathlib.tactic.linarith.default
import Mathlib.PostPort

universes u w 

namespace Mathlib

/-!
# Polynomials

Lemmas for the interaction between polynomials and ∑ and ∏.

## Main results

- `nat_degree_prod_of_monic` : the degree of a product of monic polynomials is the product of
    degrees. We prove this only for [comm_semiring R],
    but it ought to be true for [semiring R] and list.prod.
- `nat_degree_prod` : for polynomials over an integral domain,
    the degree of the product is the sum of degrees
- `leading_coeff_prod` : for polynomials over an integral domain,
    the leading coefficient is the product of leading coefficients
- `prod_X_sub_C_coeff_card_pred` carries most of the content for computing
    the second coefficient of the characteristic polynomial.
-/

namespace polynomial


theorem nat_degree_prod_le {R : Type u} {ι : Type w} (s : finset ι) [comm_semiring R] (f : ι → polynomial R) : nat_degree (finset.prod s fun (i : ι) => f i) ≤ finset.sum s fun (i : ι) => nat_degree (f i) := sorry

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `leading_coeff_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem leading_coeff_prod' {R : Type u} {ι : Type w} (s : finset ι) [comm_semiring R] (f : ι → polynomial R) (h : (finset.prod s fun (i : ι) => leading_coeff (f i)) ≠ 0) : leading_coeff (finset.prod s fun (i : ι) => f i) = finset.prod s fun (i : ι) => leading_coeff (f i) := sorry

/--
The degree of a product of polynomials is equal to
the product of the degrees, provided that the product of leading coefficients is nonzero.

See `nat_degree_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
theorem nat_degree_prod' {R : Type u} {ι : Type w} (s : finset ι) [comm_semiring R] (f : ι → polynomial R) (h : (finset.prod s fun (i : ι) => leading_coeff (f i)) ≠ 0) : nat_degree (finset.prod s fun (i : ι) => f i) = finset.sum s fun (i : ι) => nat_degree (f i) := sorry

theorem nat_degree_prod_of_monic {R : Type u} {ι : Type w} (s : finset ι) [comm_semiring R] (f : ι → polynomial R) [nontrivial R] (h : ∀ (i : ι), i ∈ s → monic (f i)) : nat_degree (finset.prod s fun (i : ι) => f i) = finset.sum s fun (i : ι) => nat_degree (f i) := sorry

theorem coeff_zero_prod {R : Type u} {ι : Type w} (s : finset ι) [comm_semiring R] (f : ι → polynomial R) : coeff (finset.prod s fun (i : ι) => f i) 0 = finset.prod s fun (i : ι) => coeff (f i) 0 := sorry

-- Eventually this can be generalized with Vieta's formulas

-- plus the connection between roots and factorization.

theorem prod_X_sub_C_next_coeff {R : Type u} {ι : Type w} [comm_ring R] [nontrivial R] {s : finset ι} (f : ι → R) : next_coeff (finset.prod s fun (i : ι) => X - coe_fn C (f i)) = -finset.sum s fun (i : ι) => f i := sorry

theorem prod_X_sub_C_coeff_card_pred {R : Type u} {ι : Type w} [comm_ring R] [nontrivial R] (s : finset ι) (f : ι → R) (hs : 0 < finset.card s) : coeff (finset.prod s fun (i : ι) => X - coe_fn C (f i)) (finset.card s - 1) = -finset.sum s fun (i : ι) => f i := sorry

theorem nat_degree_prod {R : Type u} {ι : Type w} (s : finset ι) [comm_ring R] [no_zero_divisors R] (f : ι → polynomial R) [nontrivial R] (h : ∀ (i : ι), i ∈ s → f i ≠ 0) : nat_degree (finset.prod s fun (i : ι) => f i) = finset.sum s fun (i : ι) => nat_degree (f i) := sorry

theorem leading_coeff_prod {R : Type u} {ι : Type w} (s : finset ι) [comm_ring R] [no_zero_divisors R] (f : ι → polynomial R) : leading_coeff (finset.prod s fun (i : ι) => f i) = finset.prod s fun (i : ι) => leading_coeff (f i) := sorry

