/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.unique_factorization_domain
import Mathlib.ring_theory.int.basic
import Mathlib.number_theory.divisors
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Squarefree elements of monoids
An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

## Main Definitions
 - `squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
 - `multiplicity.squarefree_iff_multiplicity_le_one`: `x` is `squarefree` iff for every `y`, either
  `multiplicity y x ≤ 1` or `is_unit y`.
 - `unique_factorization_monoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
 factorization monoid is squarefree iff `factors x` has no duplicate factors.
 - `nat.squarefree_iff_nodup_factors`: A positive natural number `x` is squarefree iff
  the list `factors x` has no duplicate factors.
## Tags
squarefree, multiplicity

-/

/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
def squarefree {R : Type u_1} [monoid R] (r : R) := ∀ (x : R), x * x ∣ r → is_unit x

@[simp] theorem is_unit.squarefree {R : Type u_1} [comm_monoid R] {x : R} (h : is_unit x) :
    squarefree x :=
  fun (y : R) (hdvd : y * y ∣ x) => is_unit_of_mul_is_unit_left (is_unit_of_dvd_unit hdvd h)

@[simp] theorem squarefree_one {R : Type u_1} [comm_monoid R] : squarefree 1 :=
  is_unit.squarefree is_unit_one

@[simp] theorem not_squarefree_zero {R : Type u_1} [monoid_with_zero R] [nontrivial R] :
    ¬squarefree 0 :=
  sorry

@[simp] theorem irreducible.squarefree {R : Type u_1} [comm_monoid R] {x : R} (h : irreducible x) :
    squarefree x :=
  sorry

@[simp] theorem prime.squarefree {R : Type u_1} [comm_cancel_monoid_with_zero R] {x : R}
    (h : prime x) : squarefree x :=
  irreducible.squarefree (irreducible_of_prime h)

theorem squarefree_of_dvd_of_squarefree {R : Type u_1} [comm_monoid R] {x : R} {y : R}
    (hdvd : x ∣ y) (hsq : squarefree y) : squarefree x :=
  fun (a : R) (h : a * a ∣ x) => hsq a (dvd.trans h hdvd)

namespace multiplicity


theorem squarefree_iff_multiplicity_le_one {R : Type u_1} [comm_monoid R] [DecidableRel has_dvd.dvd]
    (r : R) : squarefree r ↔ ∀ (x : R), multiplicity x r ≤ 1 ∨ is_unit x :=
  sorry

end multiplicity


namespace unique_factorization_monoid


theorem squarefree_iff_nodup_factors {R : Type u_1} [comm_cancel_monoid_with_zero R] [nontrivial R]
    [unique_factorization_monoid R] [normalization_monoid R] [DecidableEq R] {x : R} (x0 : x ≠ 0) :
    squarefree x ↔ multiset.nodup (factors x) :=
  sorry

theorem dvd_pow_iff_dvd_of_squarefree {R : Type u_1} [comm_cancel_monoid_with_zero R] [nontrivial R]
    [unique_factorization_monoid R] [normalization_monoid R] {x : R} {y : R} {n : ℕ}
    (hsq : squarefree x) (h0 : n ≠ 0) : x ∣ y ^ n ↔ x ∣ y :=
  sorry

end unique_factorization_monoid


namespace nat


theorem squarefree_iff_nodup_factors {n : ℕ} (h0 : n ≠ 0) : squarefree n ↔ list.nodup (factors n) :=
  sorry

protected instance squarefree.decidable_pred : decidable_pred squarefree := sorry

theorem divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) :
    finset.val (finset.filter squarefree (divisors n)) =
        multiset.map (fun (x : finset ℕ) => multiset.prod (finset.val x))
          (finset.val
            (finset.powerset (multiset.to_finset (unique_factorization_monoid.factors n)))) :=
  sorry

theorem sum_divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) {α : Type u_1} [add_comm_monoid α]
    {f : ℕ → α} :
    (finset.sum (finset.filter squarefree (divisors n)) fun (i : ℕ) => f i) =
        finset.sum (finset.powerset (multiset.to_finset (unique_factorization_monoid.factors n)))
          fun (i : finset ℕ) => f (multiset.prod (finset.val i)) :=
  sorry

end Mathlib