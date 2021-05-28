/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.roots_of_unity
import Mathlib.analysis.special_functions.trigonometric
import Mathlib.analysis.special_functions.pow
import Mathlib.PostPort

namespace Mathlib

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `e ^ (2 * real.pi * complex.I * (i / n))` for `i ∈ finset.range n`.

## Main declarations

* `complex.mem_roots_of_unity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`.
* `complex.card_roots_of_unity`: the number of `n`-th roots of unity is exactly `n`.

-/

namespace complex


theorem is_primitive_root_exp_of_coprime (i : ℕ) (n : ℕ) (h0 : n ≠ 0) (hi : nat.coprime i n) : is_primitive_root (exp (bit0 1 * ↑real.pi * I * (↑i / ↑n))) n := sorry

theorem is_primitive_root_exp (n : ℕ) (h0 : n ≠ 0) : is_primitive_root (exp (bit0 1 * ↑real.pi * I / ↑n)) n := sorry

theorem is_primitive_root_iff (ζ : ℂ) (n : ℕ) (hn : n ≠ 0) : is_primitive_root ζ n ↔ ∃ (i : ℕ), ∃ (H : i < n), ∃ (hi : nat.coprime i n), exp (bit0 1 * ↑real.pi * I * (↑i / ↑n)) = ζ := sorry

/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`. -/
theorem mem_roots_of_unity (n : ℕ+) (x : units ℂ) : x ∈ roots_of_unity n ℂ ↔ ∃ (i : ℕ), ∃ (H : i < ↑n), exp (bit0 1 * ↑real.pi * I * (↑i / ↑n)) = ↑x := sorry

theorem card_roots_of_unity (n : ℕ+) : fintype.card ↥(roots_of_unity n ℂ) = ↑n :=
  is_primitive_root.card_roots_of_unity (is_primitive_root_exp (↑n) (pnat.ne_zero n))

theorem card_primitive_roots (k : ℕ) (h : k ≠ 0) : finset.card (primitive_roots k ℂ) = nat.totient k :=
  is_primitive_root.card_primitive_roots (is_primitive_root_exp k h) (nat.pos_of_ne_zero h)

