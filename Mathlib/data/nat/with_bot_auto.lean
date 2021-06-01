/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.basic
import Mathlib.algebra.ordered_group
import Mathlib.PostPort

namespace Mathlib

/-!
# `with_bot ℕ`

Lemmas about the type of natural numbers with a bottom element adjoined.
-/

namespace nat


theorem with_bot.add_eq_zero_iff {n : with_bot ℕ} {m : with_bot ℕ} : n + m = 0 ↔ n = 0 ∧ m = 0 :=
  sorry

theorem with_bot.add_eq_one_iff {n : with_bot ℕ} {m : with_bot ℕ} :
    n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0 :=
  sorry

@[simp] theorem with_bot.coe_nonneg {n : ℕ} : 0 ≤ ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ ↑n)) (Eq.symm with_bot.coe_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑0 ≤ ↑n)) (propext with_bot.coe_le_coe))) (zero_le n))

@[simp] theorem with_bot.lt_zero_iff (n : with_bot ℕ) : n < 0 ↔ n = ⊥ := sorry

end Mathlib