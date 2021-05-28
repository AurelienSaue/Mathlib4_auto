/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.ring_theory.int.basic
import Mathlib.algebra.field_power
import Mathlib.ring_theory.multiplicity
import Mathlib.data.real.cau_seq
import Mathlib.tactic.ring_exp
import Mathlib.tactic.basic
import PostPort

namespace Mathlib

/-!
# p-adic norm

This file defines the p-adic valuation and the p-adic norm on ℚ.

The p-adic valuation on ℚ is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on p.

The valuation induces a norm on ℚ. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

## Notations

This file uses the local notation `/.` for `rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (prime p)]` as a type class argument.

## References

* [F. Q. Gouêva, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/

/--
For `p ≠ 1`, the p-adic valuation of an integer `z ≠ 0` is the largest natural number `n` such that
p^n divides z.

`padic_val_rat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.denom`.
If `q = 0` or `p = 1`, then `padic_val_rat p q` defaults to 0.
-/
def padic_val_rat (p : ℕ) (q : ℚ) : ℤ :=
  dite (q ≠ 0 ∧ p ≠ 1)
    (fun (h : q ≠ 0 ∧ p ≠ 1) =>
      ↑(roption.get (multiplicity (↑p) (rat.num q)) sorry) - ↑(roption.get (multiplicity ↑p ↑(rat.denom q)) sorry))
    fun (h : ¬(q ≠ 0 ∧ p ≠ 1)) => 0

/--
A simplification of the definition of `padic_val_rat p q` when `q ≠ 0` and `p` is prime.
-/
theorem padic_val_rat_def (p : ℕ) [hp : fact (nat.prime p)] {q : ℚ} (hq : q ≠ 0) : padic_val_rat p q =
  ↑(roption.get (multiplicity (↑p) (rat.num q))
        (iff.mpr multiplicity.finite_int_iff { left := nat.prime.ne_one hp, right := rat.num_ne_zero_of_ne_zero hq })) -
    ↑(roption.get (multiplicity ↑p ↑(rat.denom q))
        (iff.mpr multiplicity.finite_int_iff
          { left := nat.prime.ne_one hp,
            right :=
              eq.mpr
                (id
                  (Eq.trans
                    ((fun (a a_1 : ℤ) (e_1 : a = a_1) (b b_1 : ℤ) (e_2 : b = b_1) => congr (congr_arg ne e_1) e_2)
                      (↑(rat.denom q)) (↑(rat.denom q)) (Eq.refl ↑(rat.denom q)) 0 (↑0) (Eq.symm int.coe_nat_zero))
                    (Eq.trans (propext (ne_from_not_eq ↑(rat.denom q) ↑0))
                      ((fun (a a_1 : Prop) (e_1 : a = a_1) => congr_arg Not e_1) (↑(rat.denom q) = ↑0) (rat.denom q = 0)
                        (propext int.coe_nat_inj')))))
                (eq.mp (propext (ne_from_not_eq (rat.denom q) 0)) (rat.denom_ne_zero q)) })) :=
  dif_pos { left := hq, right := nat.prime.ne_one hp }

namespace padic_val_rat


/--
`padic_val_rat p q` is symmetric in `q`.
-/
@[simp] protected theorem neg {p : ℕ} (q : ℚ) : padic_val_rat p (-q) = padic_val_rat p q := sorry

/--
`padic_val_rat p 1` is 0 for any `p`.
-/
@[simp] protected theorem one {p : ℕ} : padic_val_rat p 1 = 0 := sorry

/--
For `p ≠ 0, p ≠ 1, `padic_val_rat p p` is 1.
-/
@[simp] theorem padic_val_rat_self {p : ℕ} (hp : 1 < p) : padic_val_rat p ↑p = 1 := sorry

/--
The p-adic value of an integer `z ≠ 0` is the multiplicity of `p` in `z`.
-/
theorem padic_val_rat_of_int {p : ℕ} (z : ℤ) (hp : p ≠ 1) (hz : z ≠ 0) : padic_val_rat p ↑z =
  ↑(roption.get (multiplicity (↑p) z) (iff.mpr multiplicity.finite_int_iff { left := hp, right := hz })) := sorry

end padic_val_rat


/--
A convenience function for the case of `padic_val_rat` when both inputs are natural numbers.
-/
def padic_val_nat (p : ℕ) (n : ℕ) : ℕ :=
  int.to_nat (padic_val_rat p ↑n)

/--
`padic_val_nat` is defined as an `int.to_nat` cast; this lemma ensures that the cast is well-behaved.
-/
theorem zero_le_padic_val_rat_of_nat (p : ℕ) (n : ℕ) : 0 ≤ padic_val_rat p ↑n := sorry

/--
`padic_val_rat` coincides with `padic_val_nat`.
-/
@[simp] theorem padic_val_rat_of_nat (p : ℕ) (n : ℕ) : ↑(padic_val_nat p n) = padic_val_rat p ↑n := sorry

/--
A simplification of `padic_val_nat` when one input is prime, by analogy with `padic_val_rat_def`.
-/
theorem padic_val_nat_def {p : ℕ} [hp : fact (nat.prime p)] {n : ℕ} (hn : n ≠ 0) : padic_val_nat p n =
  roption.get (multiplicity p n)
    (iff.mpr multiplicity.finite_nat_iff { left := nat.prime.ne_one hp, right := iff.mpr bot_lt_iff_ne_bot hn }) := sorry

theorem one_le_padic_val_nat_of_dvd {n : ℕ} {p : ℕ} [prime : fact (nat.prime p)] (nonzero : n ≠ 0) (div : p ∣ n) : 1 ≤ padic_val_nat p n := sorry

@[simp] theorem padic_val_nat_zero (m : ℕ) : padic_val_nat m 0 = 0 :=
  eq.mpr (id (Eq.refl (padic_val_nat m 0 = 0))) (Eq.refl (padic_val_nat m 0))

@[simp] theorem padic_val_nat_one (m : ℕ) : padic_val_nat m 1 = 0 := sorry

namespace padic_val_rat


/--
The multiplicity of `p : ℕ` in `a : ℤ` is finite exactly when `a ≠ 0`.
-/
theorem finite_int_prime_iff {p : ℕ} [p_prime : fact (nat.prime p)] {a : ℤ} : multiplicity.finite (↑p) a ↔ a ≠ 0 := sorry

/--
A rewrite lemma for `padic_val_rat p q` when `q` is expressed in terms of `rat.mk`.
-/
protected theorem defn (p : ℕ) [p_prime : fact (nat.prime p)] {q : ℚ} {n : ℤ} {d : ℤ} (hqz : q ≠ 0) (qdf : q = rat.mk n d) : padic_val_rat p q =
  ↑(roption.get (multiplicity (↑p) n)
        (iff.mpr multiplicity.finite_int_iff
          { left := ne.symm (ne_of_lt (nat.prime.one_lt p_prime)),
            right :=
              fun (hn : n = 0) =>
                False._oldrec
                  (eq.mp
                    (Eq.trans
                      ((fun (a a_1 : ℚ) (e_1 : a = a_1) (ᾰ ᾰ_1 : ℚ) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2) q q
                        (Eq.refl q) (rat.mk n d) 0
                        (Eq.trans
                          ((fun (ᾰ ᾰ_1 : ℤ) (e_1 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℤ) (e_2 : ᾰ_2 = ᾰ_3) =>
                              congr (congr_arg rat.mk e_1) e_2)
                            n 0 hn d d (Eq.refl d))
                          (rat.zero_mk d)))
                      (propext (iff_false_intro hqz)))
                    qdf) })) -
    ↑(roption.get (multiplicity (↑p) d)
        (iff.mpr multiplicity.finite_int_iff
          { left := ne.symm (ne_of_lt (nat.prime.one_lt p_prime)),
            right :=
              fun (hd : d = 0) =>
                False._oldrec
                  (eq.mp
                    (Eq.trans
                      ((fun (a a_1 : ℚ) (e_1 : a = a_1) (ᾰ ᾰ_1 : ℚ) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2) q q
                        (Eq.refl q) (rat.mk n d) 0
                        (Eq.trans
                          ((fun (ᾰ ᾰ_1 : ℤ) (e_1 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℤ) (e_2 : ᾰ_2 = ᾰ_3) =>
                              congr (congr_arg rat.mk e_1) e_2)
                            n n (Eq.refl n) d 0 hd)
                          (rat.mk_zero n)))
                      (propext (iff_false_intro hqz)))
                    qdf) })) := sorry

/--
A rewrite lemma for `padic_val_rat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`.
-/
protected theorem mul (p : ℕ) [p_prime : fact (nat.prime p)] {q : ℚ} {r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : padic_val_rat p (q * r) = padic_val_rat p q + padic_val_rat p r := sorry

/--
A rewrite lemma for `padic_val_rat p (q^k) with condition `q ≠ 0`.
-/
protected theorem pow (p : ℕ) [p_prime : fact (nat.prime p)] {q : ℚ} (hq : q ≠ 0) {k : ℕ} : padic_val_rat p (q ^ k) = ↑k * padic_val_rat p q := sorry

/--
A rewrite lemma for `padic_val_rat p (q⁻¹)` with condition `q ≠ 0`.
-/
protected theorem inv (p : ℕ) [p_prime : fact (nat.prime p)] {q : ℚ} (hq : q ≠ 0) : padic_val_rat p (q⁻¹) = -padic_val_rat p q := sorry

/--
A rewrite lemma for `padic_val_rat p (q / r)` with conditions `q ≠ 0`, `r ≠ 0`.
-/
protected theorem div (p : ℕ) [p_prime : fact (nat.prime p)] {q : ℚ} {r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : padic_val_rat p (q / r) = padic_val_rat p q - padic_val_rat p r := sorry

/--
A condition for `padic_val_rat p (n₁ / d₁) ≤ padic_val_rat p (n₂ / d₂),
in terms of divisibility by `p^n`.
-/
theorem padic_val_rat_le_padic_val_rat_iff (p : ℕ) [p_prime : fact (nat.prime p)] {n₁ : ℤ} {n₂ : ℤ} {d₁ : ℤ} {d₂ : ℤ} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) : padic_val_rat p (rat.mk n₁ d₁) ≤ padic_val_rat p (rat.mk n₂ d₂) ↔ ∀ (n : ℕ), ↑p ^ n ∣ n₁ * d₂ → ↑p ^ n ∣ n₂ * d₁ := sorry

/--
Sufficient conditions to show that the p-adic valuation of `q` is less than or equal to the
p-adic vlauation of `q + r`.
-/
theorem le_padic_val_rat_add_of_le (p : ℕ) [p_prime : fact (nat.prime p)] {q : ℚ} {r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0) (h : padic_val_rat p q ≤ padic_val_rat p r) : padic_val_rat p q ≤ padic_val_rat p (q + r) := sorry

/--
The minimum of the valuations of `q` and `r` is less than or equal to the valuation of `q + r`.
-/
theorem min_le_padic_val_rat_add (p : ℕ) [p_prime : fact (nat.prime p)] {q : ℚ} {r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0) : min (padic_val_rat p q) (padic_val_rat p r) ≤ padic_val_rat p (q + r) := sorry

/-- A finite sum of rationals with positive p-adic valuation has positive p-adic valuation
  (if the sum is non-zero). -/
theorem sum_pos_of_pos (p : ℕ) [p_prime : fact (nat.prime p)] {n : ℕ} {F : ℕ → ℚ} (hF : ∀ (i : ℕ), i < n → 0 < padic_val_rat p (F i)) (hn0 : (finset.sum (finset.range n) fun (i : ℕ) => F i) ≠ 0) : 0 < padic_val_rat p (finset.sum (finset.range n) fun (i : ℕ) => F i) := sorry

end padic_val_rat


namespace padic_val_nat


/--
A rewrite lemma for `padic_val_nat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`.
-/
protected theorem mul (p : ℕ) [p_prime : fact (nat.prime p)] {q : ℕ} {r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) : padic_val_nat p (q * r) = padic_val_nat p q + padic_val_nat p r := sorry

/--
Dividing out by a prime factor reduces the padic_val_nat by 1.
-/
protected theorem div {p : ℕ} [p_prime : fact (nat.prime p)] {b : ℕ} (dvd : p ∣ b) : padic_val_nat p (b / p) = padic_val_nat p b - 1 := sorry

end padic_val_nat


/--
If a prime doesn't appear in `n`, `padic_val_nat p n` is `0`.
-/
theorem padic_val_nat_of_not_dvd {p : ℕ} [fact (nat.prime p)] {n : ℕ} (not_dvd : ¬p ∣ n) : padic_val_nat p n = 0 := sorry

theorem dvd_of_one_le_padic_val_nat {n : ℕ} {p : ℕ} [prime : fact (nat.prime p)] (hp : 1 ≤ padic_val_nat p n) : p ∣ n := sorry

theorem padic_val_nat_primes {p : ℕ} {q : ℕ} [p_prime : fact (nat.prime p)] [q_prime : fact (nat.prime q)] (neq : p ≠ q) : padic_val_nat p q = 0 :=
  padic_val_nat_of_not_dvd (iff.mp (not_congr (iff.symm (nat.prime_dvd_prime_iff_eq p_prime q_prime))) neq)

protected theorem padic_val_nat.div' {p : ℕ} [p_prime : fact (nat.prime p)] {m : ℕ} (cpm : nat.coprime p m) {b : ℕ} (dvd : m ∣ b) : padic_val_nat p (b / m) = padic_val_nat p b := sorry

theorem padic_val_nat_eq_factors_count (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) : padic_val_nat p n = list.count p (nat.factors n) := sorry

theorem prod_pow_prime_padic_val_nat (n : ℕ) (hn : n ≠ 0) (m : ℕ) (pr : n < m) : (finset.prod (finset.filter nat.prime (finset.range m)) fun (p : ℕ) => p ^ padic_val_nat p n) = n := sorry

/--
If `q ≠ 0`, the p-adic norm of a rational `q` is `p ^ (-(padic_val_rat p q))`.
If `q = 0`, the p-adic norm of `q` is 0.
-/
def padic_norm (p : ℕ) (q : ℚ) : ℚ :=
  ite (q = 0) 0 (↑p ^ (-padic_val_rat p q))

namespace padic_norm


/--
Unfolds the definition of the p-adic norm of `q` when `q ≠ 0`.
-/
@[simp] protected theorem eq_fpow_of_nonzero (p : ℕ) {q : ℚ} (hq : q ≠ 0) : padic_norm p q = ↑p ^ (-padic_val_rat p q) := sorry

/--
The p-adic norm is nonnegative.
-/
protected theorem nonneg (p : ℕ) (q : ℚ) : 0 ≤ padic_norm p q := sorry

/--
The p-adic norm of 0 is 0.
-/
@[simp] protected theorem zero (p : ℕ) : padic_norm p 0 = 0 := sorry

/--
The p-adic norm of 1 is 1.
-/
@[simp] protected theorem one (p : ℕ) : padic_norm p 1 = 1 := sorry

/--
The p-adic norm of `p` is `1/p` if `p > 1`.

See also `padic_norm.padic_norm_p_of_prime` for a version that assumes `p` is prime.
-/
theorem padic_norm_p {p : ℕ} (hp : 1 < p) : padic_norm p ↑p = 1 / ↑p := sorry

/--
The p-adic norm of `p` is `1/p` if `p` is prime.

See also `padic_norm.padic_norm_p` for a version that assumes `1 < p`.
-/
@[simp] theorem padic_norm_p_of_prime (p : ℕ) [fact (nat.prime p)] : padic_norm p ↑p = 1 / ↑p :=
  padic_norm_p (nat.prime.one_lt _inst_1)

/--
The p-adic norm of `p` is less than 1 if `1 < p`.

See also `padic_norm.padic_norm_p_lt_one_of_prime` for a version assuming `prime p`.
-/
theorem padic_norm_p_lt_one {p : ℕ} (hp : 1 < p) : padic_norm p ↑p < 1 := sorry

/--
The p-adic norm of `p` is less than 1 if `p` is prime.

See also `padic_norm.padic_norm_p_lt_one` for a version assuming `1 < p`.
-/
theorem padic_norm_p_lt_one_of_prime (p : ℕ) [fact (nat.prime p)] : padic_norm p ↑p < 1 :=
  padic_norm_p_lt_one (nat.prime.one_lt _inst_1)

/--
`padic_norm p q` takes discrete values `p ^ -z` for `z : ℤ`.
-/
protected theorem values_discrete (p : ℕ) {q : ℚ} (hq : q ≠ 0) : ∃ (z : ℤ), padic_norm p q = ↑p ^ (-z) := sorry

/--
`padic_norm p` is symmetric.
-/
@[simp] protected theorem neg (p : ℕ) (q : ℚ) : padic_norm p (-q) = padic_norm p q := sorry

/--
If `q ≠ 0`, then `padic_norm p q ≠ 0`.
-/
protected theorem nonzero (p : ℕ) [hp : fact (nat.prime p)] {q : ℚ} (hq : q ≠ 0) : padic_norm p q ≠ 0 := sorry

/--
If the p-adic norm of `q` is 0, then `q` is 0.
-/
theorem zero_of_padic_norm_eq_zero (p : ℕ) [hp : fact (nat.prime p)] {q : ℚ} (h : padic_norm p q = 0) : q = 0 := sorry

/--
The p-adic norm is multiplicative.
-/
@[simp] protected theorem mul (p : ℕ) [hp : fact (nat.prime p)] (q : ℚ) (r : ℚ) : padic_norm p (q * r) = padic_norm p q * padic_norm p r := sorry

/--
The p-adic norm respects division.
-/
@[simp] protected theorem div (p : ℕ) [hp : fact (nat.prime p)] (q : ℚ) (r : ℚ) : padic_norm p (q / r) = padic_norm p q / padic_norm p r := sorry

/--
The p-adic norm of an integer is at most 1.
-/
protected theorem of_int (p : ℕ) [hp : fact (nat.prime p)] (z : ℤ) : padic_norm p ↑z ≤ 1 := sorry

/--
The p-adic norm is nonarchimedean: the norm of `p + q` is at most the max of the norm of `p` and
the norm of `q`.
-/
protected theorem nonarchimedean (p : ℕ) [hp : fact (nat.prime p)] {q : ℚ} {r : ℚ} : padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) := sorry

/--
The p-adic norm respects the triangle inequality: the norm of `p + q` is at most the norm of `p`
plus the norm of `q`.
-/
theorem triangle_ineq (p : ℕ) [hp : fact (nat.prime p)] (q : ℚ) (r : ℚ) : padic_norm p (q + r) ≤ padic_norm p q + padic_norm p r :=
  le_trans (padic_norm.nonarchimedean p) (max_le_add_of_nonneg (padic_norm.nonneg p q) (padic_norm.nonneg p r))

/--
The p-adic norm of a difference is at most the max of each component. Restates the archimedean
property of the p-adic norm.
-/
protected theorem sub (p : ℕ) [hp : fact (nat.prime p)] {q : ℚ} {r : ℚ} : padic_norm p (q - r) ≤ max (padic_norm p q) (padic_norm p r) := sorry

/--
If the p-adic norms of `q` and `r` are different, then the norm of `q + r` is equal to the max of
the norms of `q` and `r`.
-/
theorem add_eq_max_of_ne (p : ℕ) [hp : fact (nat.prime p)] {q : ℚ} {r : ℚ} (hne : padic_norm p q ≠ padic_norm p r) : padic_norm p (q + r) = max (padic_norm p q) (padic_norm p r) := sorry

/--
The p-adic norm is an absolute value: positive-definite and multiplicative, satisfying the triangle
inequality.
-/
protected instance is_absolute_value (p : ℕ) [hp : fact (nat.prime p)] : is_absolute_value (padic_norm p) :=
  is_absolute_value.mk (padic_norm.nonneg p)
    (fun (x : ℚ) =>
      { mp := fun (ᾰ : padic_norm p x = 0) => zero_of_padic_norm_eq_zero p ᾰ,
        mpr :=
          fun (ᾰ : x = 0) =>
            eq.mpr
              (id
                (Eq.trans
                  ((fun (a a_1 : ℚ) (e_1 : a = a_1) (ᾰ ᾰ_1 : ℚ) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
                    (padic_norm p x) 0
                    (Eq.trans
                      ((fun (p p_1 : ℕ) (e_1 : p = p_1) (q q_1 : ℚ) (e_2 : q = q_1) =>
                          congr (congr_arg padic_norm e_1) e_2)
                        p p (Eq.refl p) x 0 ᾰ)
                      (padic_norm.zero p))
                    0 0 (Eq.refl 0))
                  (propext (eq_self_iff_true 0))))
              trivial })
    (triangle_ineq p) (padic_norm.mul p)

theorem dvd_iff_norm_le {p : ℕ} [hp : fact (nat.prime p)] {n : ℕ} {z : ℤ} : ↑(p ^ n) ∣ z ↔ padic_norm p ↑z ≤ ↑p ^ (-↑n) := sorry

