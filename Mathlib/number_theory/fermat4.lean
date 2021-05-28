/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Paul van Wamelen.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.number_theory.pythagorean_triples
import Mathlib.ring_theory.coprime
import Mathlib.PostPort

namespace Mathlib

/-!
# Fermat's Last Theorem for the case n = 4
There are no non-zero integers `a`, `b` and `c` such that `a ^ 4 + b ^ 4 = c ^ 4`.
-/

/-- Shorthand for three non-zero integers `a`, `b`, and `c` satisfying `a ^ 4 + b ^ 4 = c ^ 2`.
We will show that no integers satisfy this equation. Clearly Fermat's Last theorem for n = 4
follows. -/
def fermat_42 (a : ℤ) (b : ℤ) (c : ℤ)  :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ^ bit0 (bit0 1) + b ^ bit0 (bit0 1) = c ^ bit0 1

namespace fermat_42


theorem comm {a : ℤ} {b : ℤ} {c : ℤ} : fermat_42 a b c ↔ fermat_42 b a c := sorry

theorem mul {a : ℤ} {b : ℤ} {c : ℤ} {k : ℤ} (hk0 : k ≠ 0) : fermat_42 a b c ↔ fermat_42 (k * a) (k * b) (k ^ bit0 1 * c) := sorry

theorem ne_zero {a : ℤ} {b : ℤ} {c : ℤ} (h : fermat_42 a b c) : c ≠ 0 := sorry

/-- We say a solution to `a ^ 4 + b ^ 4 = c ^ 2` is minimal if there is no other solution with
a smaller `c` (in absolute value). -/
def minimal (a : ℤ) (b : ℤ) (c : ℤ)  :=
  fermat_42 a b c ∧ ∀ (a1 b1 c1 : ℤ), fermat_42 a1 b1 c1 → int.nat_abs c ≤ int.nat_abs c1

/-- if we have a solution to `a ^ 4 + b ^ 4 = c ^ 2` then there must be a minimal one. -/
theorem exists_minimal {a : ℤ} {b : ℤ} {c : ℤ} (h : fermat_42 a b c) : ∃ (a0 : ℤ), ∃ (b0 : ℤ), ∃ (c0 : ℤ), minimal a0 b0 c0 := sorry

/-- a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` must have `a` and `b` coprime. -/
theorem coprime_of_minimal {a : ℤ} {b : ℤ} {c : ℤ} (h : minimal a b c) : is_coprime a b := sorry

/-- We can swap `a` and `b` in a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2`. -/
theorem minimal_comm {a : ℤ} {b : ℤ} {c : ℤ} : minimal a b c → minimal b a c := sorry

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has positive `c`. -/
theorem neg_of_minimal {a : ℤ} {b : ℤ} {c : ℤ} : minimal a b c → minimal a b (-c) := sorry

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has `a` odd. -/
theorem exists_odd_minimal {a : ℤ} {b : ℤ} {c : ℤ} (h : fermat_42 a b c) : ∃ (a0 : ℤ), ∃ (b0 : ℤ), ∃ (c0 : ℤ), minimal a0 b0 c0 ∧ a0 % bit0 1 = 1 := sorry

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has
`a` odd and `c` positive. -/
theorem exists_pos_odd_minimal {a : ℤ} {b : ℤ} {c : ℤ} (h : fermat_42 a b c) : ∃ (a0 : ℤ), ∃ (b0 : ℤ), ∃ (c0 : ℤ), minimal a0 b0 c0 ∧ a0 % bit0 1 = 1 ∧ 0 < c0 := sorry

end fermat_42


theorem int.coprime_of_sqr_sum {r : ℤ} {s : ℤ} (h2 : is_coprime s r) : is_coprime (r ^ bit0 1 + s ^ bit0 1) r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime (r ^ bit0 1 + s ^ bit0 1) r)) (pow_two r)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime (r * r + s ^ bit0 1) r)) (pow_two s)))
      (is_coprime.mul_add_left_left (is_coprime.mul_left h2 h2) r))

theorem int.coprime_of_sqr_sum' {r : ℤ} {s : ℤ} (h : is_coprime r s) : is_coprime (r ^ bit0 1 + s ^ bit0 1) (r * s) :=
  is_coprime.mul_right (int.coprime_of_sqr_sum (iff.mp is_coprime_comm h))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime (r ^ bit0 1 + s ^ bit0 1) s)) (add_comm (r ^ bit0 1) (s ^ bit0 1))))
      (int.coprime_of_sqr_sum h))

namespace fermat_42


-- If we have a solution to a ^ 4 + b ^ 4 = c ^ 2, we can construct a smaller one. This

-- implies there can't be a smallest solution.

theorem not_minimal {a : ℤ} {b : ℤ} {c : ℤ} (h : minimal a b c) (ha2 : a % bit0 1 = 1) (hc : 0 < c) : False := sorry

end fermat_42


theorem not_fermat_42 {a : ℤ} {b : ℤ} {c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : a ^ bit0 (bit0 1) + b ^ bit0 (bit0 1) ≠ c ^ bit0 1 := sorry

theorem not_fermat_4 {a : ℤ} {b : ℤ} {c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : a ^ bit0 (bit0 1) + b ^ bit0 (bit0 1) ≠ c ^ bit0 (bit0 1) := sorry

