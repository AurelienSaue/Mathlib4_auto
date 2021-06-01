/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.field_theory.finite.basic
import Mathlib.data.zmod.basic
import Mathlib.data.nat.parity
import Mathlib.PostPort

namespace Mathlib

/-!
# Quadratic reciprocity.

This file contains results about quadratic residues modulo a prime number.

The main results are the law of quadratic reciprocity, `quadratic_reciprocity`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`exists_pow_two_eq_prime_iff_of_mod_four_eq_one`, and
`exists_pow_two_eq_prime_iff_of_mod_four_eq_three`.

Also proven are conditions for `-1` and `2` to be a square modulo a prime,
`exists_pow_two_eq_neg_one_iff_mod_four_ne_three` and
`exists_pow_two_eq_two_iff`

## Implementation notes

The proof of quadratic reciprocity implemented uses Gauss' lemma and Eisenstein's lemma
-/

namespace zmod


/-- Euler's Criterion: A unit `x` of `zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
theorem euler_criterion_units (p : ℕ) [fact (nat.prime p)] (x : units (zmod p)) :
    (∃ (y : units (zmod p)), y ^ bit0 1 = x) ↔ x ^ (p / bit0 1) = 1 :=
  sorry

/-- Euler's Criterion: a nonzero `a : zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
theorem euler_criterion (p : ℕ) [fact (nat.prime p)] {a : zmod p} (ha : a ≠ 0) :
    (∃ (y : zmod p), y ^ bit0 1 = a) ↔ a ^ (p / bit0 1) = 1 :=
  sorry

theorem exists_pow_two_eq_neg_one_iff_mod_four_ne_three (p : ℕ) [fact (nat.prime p)] :
    (∃ (y : zmod p), y ^ bit0 1 = -1) ↔ p % bit0 (bit0 1) ≠ bit1 1 :=
  sorry

theorem pow_div_two_eq_neg_one_or_one (p : ℕ) [fact (nat.prime p)] {a : zmod p} (ha : a ≠ 0) :
    a ^ (p / bit0 1) = 1 ∨ a ^ (p / bit0 1) = -1 :=
  sorry

/-- Wilson's Lemma: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
@[simp] theorem wilsons_lemma (p : ℕ) [fact (nat.prime p)] : ↑(nat.factorial (p - 1)) = -1 := sorry

@[simp] theorem prod_Ico_one_prime (p : ℕ) [fact (nat.prime p)] :
    (finset.prod (finset.Ico 1 p) fun (x : ℕ) => ↑x) = -1 :=
  sorry

end zmod


/-- The image of the map sending a non zero natural number `x ≤ p / 2` to the absolute value
  of the element of interger in the interval `(-p/2, p/2]` congruent to `a * x` mod p is the set
  of non zero natural numbers `x` such that `x ≤ p / 2` -/
theorem Ico_map_val_min_abs_nat_abs_eq_Ico_map_id (p : ℕ) [hp : fact (nat.prime p)] (a : zmod p)
    (hap : a ≠ 0) :
    multiset.map (fun (x : ℕ) => int.nat_abs (zmod.val_min_abs (a * ↑x)))
          (finset.val (finset.Ico 1 (Nat.succ (p / bit0 1)))) =
        multiset.map (fun (a : ℕ) => a) (finset.val (finset.Ico 1 (Nat.succ (p / bit0 1)))) :=
  sorry

theorem div_eq_filter_card {a : ℕ} {b : ℕ} {c : ℕ} (hb0 : 0 < b) (hc : a / b ≤ c) :
    a / b = finset.card (finset.filter (fun (x : ℕ) => x * b ≤ a) (finset.Ico 1 (Nat.succ c))) :=
  sorry

/-- The given sum is the number of integer points in the triangle formed by the diagonal of the
  rectangle `(0, p/2) × (0, q/2)`  -/
/-- Each of the sums in this lemma is the cardinality of the set integer points in each of the
  two triangles formed by the diagonal of the rectangle `(0, p/2) × (0, q/2)`. Adding them
  gives the number of points in the rectangle. -/
namespace zmod


/-- The Legendre symbol of `a` and `p` is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a ^ (p / 2)` is `1` modulo `p`
   (by `euler_criterion` this is equivalent to “`a` is a square modulo `p`”);
* `-1` otherwise.

-/
def legendre_sym (a : ℕ) (p : ℕ) : ℤ := ite (↑a = 0) 0 (ite (↑a ^ (p / bit0 1) = 1) 1 (-1))

theorem legendre_sym_eq_pow (a : ℕ) (p : ℕ) [hp : fact (nat.prime p)] :
    ↑(legendre_sym a p) = ↑a ^ (p / bit0 1) :=
  sorry

theorem legendre_sym_eq_one_or_neg_one (a : ℕ) (p : ℕ) (ha : ↑a ≠ 0) :
    legendre_sym a p = -1 ∨ legendre_sym a p = 1 :=
  sorry

theorem legendre_sym_eq_zero_iff (a : ℕ) (p : ℕ) : legendre_sym a p = 0 ↔ ↑a = 0 := sorry

/-- Gauss' lemma. The legendre symbol can be computed by considering the number of naturals less
  than `p/2` such that `(a * x) % p > p / 2` -/
theorem gauss_lemma (p : ℕ) [fact (nat.prime p)] {a : ℕ} [hp1 : fact (p % bit0 1 = 1)]
    (ha0 : ↑a ≠ 0) :
    legendre_sym a p =
        (-1) ^
          finset.card
            (finset.filter (fun (x : ℕ) => p / bit0 1 < val (↑a * ↑x))
              (finset.Ico 1 (Nat.succ (p / bit0 1)))) :=
  sorry

theorem legendre_sym_eq_one_iff (p : ℕ) [fact (nat.prime p)] {a : ℕ} (ha0 : ↑a ≠ 0) :
    legendre_sym a p = 1 ↔ ∃ (b : zmod p), b ^ bit0 1 = ↑a :=
  sorry

theorem eisenstein_lemma (p : ℕ) [fact (nat.prime p)] [hp1 : fact (p % bit0 1 = 1)] {a : ℕ}
    (ha1 : a % bit0 1 = 1) (ha0 : ↑a ≠ 0) :
    legendre_sym a p =
        (-1) ^ finset.sum (finset.Ico 1 (Nat.succ (p / bit0 1))) fun (x : ℕ) => x * a / p :=
  sorry

theorem quadratic_reciprocity (p : ℕ) (q : ℕ) [fact (nat.prime p)] [fact (nat.prime q)]
    [hp1 : fact (p % bit0 1 = 1)] [hq1 : fact (q % bit0 1 = 1)] (hpq : p ≠ q) :
    legendre_sym p q * legendre_sym q p = (-1) ^ (p / bit0 1 * (q / bit0 1)) :=
  sorry

-- move this

protected instance fact_prime_two : fact (nat.prime (bit0 1)) := nat.prime_two

theorem legendre_sym_two (p : ℕ) [fact (nat.prime p)] [hp1 : fact (p % bit0 1 = 1)] :
    legendre_sym (bit0 1) p = (-1) ^ (p / bit0 (bit0 1) + p / bit0 1) :=
  sorry

theorem exists_pow_two_eq_two_iff (p : ℕ) [fact (nat.prime p)] [hp1 : fact (p % bit0 1 = 1)] :
    (∃ (a : zmod p), a ^ bit0 1 = bit0 1) ↔
        p % bit0 (bit0 (bit0 1)) = 1 ∨ p % bit0 (bit0 (bit0 1)) = bit1 (bit1 1) :=
  sorry

theorem exists_pow_two_eq_prime_iff_of_mod_four_eq_one (p : ℕ) (q : ℕ) [fact (nat.prime p)]
    [fact (nat.prime q)] (hp1 : p % bit0 (bit0 1) = 1) [hq1 : fact (q % bit0 1 = 1)] :
    (∃ (a : zmod p), a ^ bit0 1 = ↑q) ↔ ∃ (b : zmod q), b ^ bit0 1 = ↑p :=
  sorry

theorem exists_pow_two_eq_prime_iff_of_mod_four_eq_three (p : ℕ) (q : ℕ) [fact (nat.prime p)]
    [fact (nat.prime q)] (hp3 : p % bit0 (bit0 1) = bit1 1) (hq3 : q % bit0 (bit0 1) = bit1 1)
    (hpq : p ≠ q) : (∃ (a : zmod p), a ^ bit0 1 = ↑q) ↔ ¬∃ (b : zmod q), b ^ bit0 1 = ↑p :=
  sorry

end Mathlib