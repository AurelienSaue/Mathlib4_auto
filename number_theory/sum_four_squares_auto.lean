/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

## Lagrange's four square theorem

The main result in this file is `sum_four_squares`,
a proof that every natural number is the sum of four square numbers.

# Implementation Notes

The proof used is close to Lagrange's original proof.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group_power.identities
import Mathlib.data.zmod.basic
import Mathlib.field_theory.finite.basic
import Mathlib.data.int.parity
import Mathlib.data.fintype.card
import PostPort

namespace Mathlib

namespace int


theorem sum_two_squares_of_two_mul_sum_two_squares {m : ℤ} {x : ℤ} {y : ℤ} (h : bit0 1 * m = x ^ bit0 1 + y ^ bit0 1) : m = ((x - y) / bit0 1) ^ bit0 1 + ((x + y) / bit0 1) ^ bit0 1 := sorry

theorem exists_sum_two_squares_add_one_eq_k (p : ℕ) [hp : fact (nat.prime p)] : ∃ (a : ℤ), ∃ (b : ℤ), ∃ (k : ℕ), a ^ bit0 1 + b ^ bit0 1 + 1 = ↑k * ↑p ∧ k < p := sorry

end int


namespace nat


theorem sum_four_squares (n : ℕ) : ∃ (a : ℕ), ∃ (b : ℕ), ∃ (c : ℕ), ∃ (d : ℕ), a ^ bit0 1 + b ^ bit0 1 + c ^ bit0 1 + d ^ bit0 1 = n := sorry

