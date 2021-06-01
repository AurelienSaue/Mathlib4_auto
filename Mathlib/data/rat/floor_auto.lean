/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Kappelmann
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.floor
import Mathlib.tactic.field_simp
import Mathlib.PostPort

namespace Mathlib

/-!
# Floor Function for Rational Numbers

## Summary

We define the `floor` function and the `floor_ring` instance on `ℚ`. Some technical lemmas relating
`floor` to integer division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/

namespace rat


/-- `floor q` is the largest integer `z` such that `z ≤ q` -/
protected def floor : ℚ → ℤ := sorry

protected theorem le_floor {z : ℤ} {r : ℚ} : z ≤ rat.floor r ↔ ↑z ≤ r := sorry

protected instance floor_ring : floor_ring ℚ := floor_ring.mk rat.floor rat.le_floor

protected theorem floor_def {q : ℚ} : floor q = num q / ↑(denom q) :=
  cases_on q
    fun (q_num : ℤ) (q_denom : ℕ) (q_pos : 0 < q_denom)
      (q_cop : nat.coprime (int.nat_abs q_num) q_denom) =>
      Eq.refl (floor (mk' q_num q_denom q_pos q_cop))

theorem floor_int_div_nat_eq_div {n : ℤ} {d : ℕ} : floor (↑n / ↑d) = n / ↑d := sorry

end rat


theorem int.mod_nat_eq_sub_mul_floor_rat_div {n : ℤ} {d : ℕ} : n % ↑d = n - ↑d * floor (↑n / ↑d) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (n % ↑d = n - ↑d * floor (↑n / ↑d)))
        (eq_sub_of_add_eq (int.mod_add_div n ↑d))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (n - ↑d * (n / ↑d) = n - ↑d * floor (↑n / ↑d)))
          rat.floor_int_div_nat_eq_div))
      (Eq.refl (n - ↑d * (n / ↑d))))

theorem nat.coprime_sub_mul_floor_rat_div_of_coprime {n : ℕ} {d : ℕ}
    (n_coprime_d : nat.coprime n d) : nat.coprime (int.nat_abs (↑n - ↑d * floor (↑n / ↑d))) d :=
  sorry

namespace rat


theorem num_lt_succ_floor_mul_denom (q : ℚ) : num q < (floor q + 1) * ↑(denom q) := sorry

theorem fract_inv_num_lt_num_of_pos {q : ℚ} (q_pos : 0 < q) : num (fract (q⁻¹)) < num q := sorry

end Mathlib