/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.associated
import Mathlib.algebra.big_operators.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Prime elements in rings
This file contains lemmas about prime elements of commutative rings.
-/

/-- If `x * y = a * ∏ i in s, p i` where `p i` is always prime, then
  `x` and `y` can both be written as a divisor of `a` multiplied by
  a product over a subset of `s`  -/
theorem mul_eq_mul_prime_prod {R : Type u_1} [comm_cancel_monoid_with_zero R] {α : Type u_2}
    [DecidableEq α] {x : R} {y : R} {a : R} {s : finset α} {p : α → R}
    (hp : ∀ (i : α), i ∈ s → prime (p i)) (hx : x * y = a * finset.prod s fun (i : α) => p i) :
    ∃ (t : finset α),
        ∃ (u : finset α),
          ∃ (b : R),
            ∃ (c : R),
              t ∪ u = s ∧
                disjoint t u ∧
                  a = b * c ∧
                    (x = b * finset.prod t fun (i : α) => p i) ∧
                      y = c * finset.prod u fun (i : α) => p i :=
  sorry

/-- If ` x * y = a * p ^ n` where `p` is prime, then `x` and `y` can both be written
  as the product of a power of `p` and a divisor of `a`. -/
theorem mul_eq_mul_prime_pow {R : Type u_1} [comm_cancel_monoid_with_zero R] {x : R} {y : R} {a : R}
    {p : R} {n : ℕ} (hp : prime p) (hx : x * y = a * p ^ n) :
    ∃ (i : ℕ),
        ∃ (j : ℕ), ∃ (b : R), ∃ (c : R), i + j = n ∧ a = b * c ∧ x = b * p ^ i ∧ y = c * p ^ j :=
  sorry

end Mathlib