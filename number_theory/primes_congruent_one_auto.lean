/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Riccardo Brasca
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.ring_theory.polynomial.cyclotomic
import Mathlib.topology.algebra.polynomial
import Mathlib.field_theory.finite.basic
import PostPort

namespace Mathlib

/-!
# Primes congruent to one

We prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that
`p ≡ 1 [MOD k]`.
-/

namespace nat


/-- For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. -/
theorem exists_prime_ge_modeq_one (k : ℕ) (n : ℕ) (hpos : 0 < k) : ∃ (p : ℕ), prime p ∧ n ≤ p ∧ modeq k p 1 := sorry

theorem frequently_at_top_modeq_one (k : ℕ) (hpos : 0 < k) : filter.frequently (fun (p : ℕ) => prime p ∧ modeq k p 1) filter.at_top := sorry

theorem infinite_set_of_prime_modeq_one (k : ℕ) (hpos : 0 < k) : set.infinite (set_of fun (p : ℕ) => prime p ∧ modeq k p 1) :=
  iff.mp frequently_at_top_iff_infinite (frequently_at_top_modeq_one k hpos)

