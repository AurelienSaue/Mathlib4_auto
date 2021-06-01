/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.apply_fun
import Mathlib.data.equiv.ring
import Mathlib.data.zmod.basic
import Mathlib.linear_algebra.basis
import Mathlib.ring_theory.integral_domain
import Mathlib.field_theory.separable
import Mathlib.PostPort

universes u_2 u_1 

namespace Mathlib

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

See `ring_theory.integral_domain` for the fact that the unit group of a finite field is a
cyclic group, as well as the fact that every finite integral domain is a field (`field_of_integral_domain`).

## Main results

1. `card_units`: The unit group of a finite field is has cardinality `q - 1`.
2. `sum_pow_units`: The sum of `x^i`, where `x` ranges over the units of `K`, is
   - `q-1` if `q-1 ∣ i`
   - `0`   otherwise
3. `finite_field.card`: The cardinality `q` is a power of the characteristic of `K`.
   See `card'` for a variant.

## Notation

Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

-/

namespace finite_field


/-- The cardinality of a field is at most `n` times the cardinality of the image of a degree `n`
  polynomial -/
theorem card_image_polynomial_eval {R : Type u_2} [integral_domain R] [DecidableEq R] [fintype R]
    {p : polynomial R} (hp : 0 < polynomial.degree p) :
    fintype.card R ≤
        polynomial.nat_degree p *
          finset.card (finset.image (fun (x : R) => polynomial.eval x p) finset.univ) :=
  sorry

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
theorem exists_root_sum_quadratic {R : Type u_2} [integral_domain R] [fintype R] {f : polynomial R}
    {g : polynomial R} (hf2 : polynomial.degree f = bit0 1) (hg2 : polynomial.degree g = bit0 1)
    (hR : fintype.card R % bit0 1 = 1) :
    ∃ (a : R), ∃ (b : R), polynomial.eval a f + polynomial.eval b g = 0 :=
  sorry

theorem card_units {K : Type u_1} [field K] [fintype K] :
    fintype.card (units K) = fintype.card K - 1 :=
  sorry

theorem prod_univ_units_id_eq_neg_one {K : Type u_1} [field K] [fintype K] :
    (finset.prod finset.univ fun (x : units K) => x) = -1 :=
  sorry

theorem pow_card_sub_one_eq_one {K : Type u_1} [field K] [fintype K] (a : K) (ha : a ≠ 0) :
    a ^ (fintype.card K - 1) = 1 :=
  sorry

theorem pow_card {K : Type u_1} [field K] [fintype K] (a : K) : a ^ fintype.card K = a := sorry

theorem card (K : Type u_1) [field K] [fintype K] (p : ℕ) [char_p K p] :
    ∃ (n : ℕ+), nat.prime p ∧ fintype.card K = p ^ ↑n :=
  sorry

theorem card' {K : Type u_1} [field K] [fintype K] :
    ∃ (p : ℕ), ∃ (n : ℕ+), nat.prime p ∧ fintype.card K = p ^ ↑n :=
  sorry

@[simp] theorem cast_card_eq_zero (K : Type u_1) [field K] [fintype K] : ↑(fintype.card K) = 0 :=
  sorry

theorem forall_pow_eq_one_iff (K : Type u_1) [field K] [fintype K] (i : ℕ) :
    (∀ (x : units K), x ^ i = 1) ↔ fintype.card K - 1 ∣ i :=
  sorry

/-- The sum of `x ^ i` as `x` ranges over the units of a finite field of cardinality `q`
is equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`. -/
theorem sum_pow_units (K : Type u_1) [field K] [fintype K] (i : ℕ) :
    (finset.sum finset.univ fun (x : units K) => ↑x ^ i) = ite (fintype.card K - 1 ∣ i) (-1) 0 :=
  sorry

/-- The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q - 1`. -/
theorem sum_pow_lt_card_sub_one {K : Type u_1} [field K] [fintype K] (i : ℕ)
    (h : i < fintype.card K - 1) : (finset.sum finset.univ fun (x : K) => x ^ i) = 0 :=
  sorry

theorem frobenius_pow {K : Type u_1} [field K] [fintype K] {p : ℕ} [fact (nat.prime p)] [char_p K p]
    {n : ℕ} (hcard : fintype.card K = p ^ n) : frobenius K p ^ n = 1 :=
  sorry

theorem expand_card {K : Type u_1} [field K] [fintype K] (f : polynomial K) :
    coe_fn (polynomial.expand K (fintype.card K)) f = f ^ fintype.card K :=
  sorry

end finite_field


namespace zmod


theorem sum_two_squares (p : ℕ) [hp : fact (nat.prime p)] (x : zmod p) :
    ∃ (a : zmod p), ∃ (b : zmod p), a ^ bit0 1 + b ^ bit0 1 = x :=
  sorry

end zmod


namespace char_p


theorem sum_two_squares (R : Type u_1) [integral_domain R] (p : ℕ) [fact (0 < p)] [char_p R p]
    (x : ℤ) : ∃ (a : ℕ), ∃ (b : ℕ), ↑a ^ bit0 1 + ↑b ^ bit0 1 = ↑x :=
  sorry

end char_p


/-- The Fermat-Euler totient theorem. `nat.modeq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp] theorem zmod.pow_totient {n : ℕ} [fact (0 < n)] (x : units (zmod n)) :
    x ^ nat.totient n = 1 :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (x ^ nat.totient n = 1)) (Eq.symm (zmod.card_units_eq_totient n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x ^ fintype.card (units (zmod n)) = 1)) (pow_card_eq_one x)))
      (Eq.refl 1))

/-- The Fermat-Euler totient theorem. `zmod.pow_totient` is an alternative statement
  of the same theorem. -/
theorem nat.modeq.pow_totient {x : ℕ} {n : ℕ} (h : nat.coprime x n) :
    nat.modeq n (x ^ nat.totient n) 1 :=
  sorry

namespace zmod


/-- A variation on Fermat's little theorem. See `zmod.pow_card_sub_one_eq_one` -/
@[simp] theorem pow_card {p : ℕ} [fact (nat.prime p)] (x : zmod p) : x ^ p = x :=
  eq.mp (Eq._oldrec (Eq.refl (x ^ fintype.card (zmod p) = x)) (card p)) (finite_field.pow_card x)

@[simp] theorem frobenius_zmod (p : ℕ) [hp : fact (nat.prime p)] :
    frobenius (zmod p) p = ring_hom.id (zmod p) :=
  sorry

@[simp] theorem card_units (p : ℕ) [fact (nat.prime p)] : fintype.card (units (zmod p)) = p - 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (fintype.card (units (zmod p)) = p - 1)) finite_field.card_units))
    (eq.mpr (id (Eq._oldrec (Eq.refl (fintype.card (zmod p) - 1 = p - 1)) (card p)))
      (Eq.refl (p - 1)))

/-- Fermat's Little Theorem: for every unit `a` of `zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem units_pow_card_sub_one_eq_one (p : ℕ) [fact (nat.prime p)] (a : units (zmod p)) :
    a ^ (p - 1) = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (p - 1) = 1)) (Eq.symm (card_units p))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ fintype.card (units (zmod p)) = 1)) (pow_card_eq_one a)))
      (Eq.refl 1))

/-- Fermat's Little Theorem: for all nonzero `a : zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem pow_card_sub_one_eq_one {p : ℕ} [fact (nat.prime p)] {a : zmod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 :=
  eq.mp (Eq._oldrec (Eq.refl (a ^ (fintype.card (zmod p) - 1) = 1)) (card p))
    (finite_field.pow_card_sub_one_eq_one a ha)

theorem expand_card {p : ℕ} [fact (nat.prime p)] (f : polynomial (zmod p)) :
    coe_fn (polynomial.expand (zmod p) p) f = f ^ p :=
  sorry

end Mathlib