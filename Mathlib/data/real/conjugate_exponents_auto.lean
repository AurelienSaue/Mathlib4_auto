/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.real.ennreal
import Mathlib.PostPort

universes l 

namespace Mathlib

/-!
# Real conjugate exponents

`p.is_conjugate_exponent q` registers the fact that the real numbers `p` and `q` are `> 1` and
satisfy `1/p + 1/q = 1`. This property shows up often in analysis, especially when dealing with
`L^p` spaces.

We make several basic facts available through dot notation in this situation.

We also introduce `p.conjugate_exponent` for `p / (p-1)`. When `p > 1`, it is conjugate to `p`.
-/

namespace real


/-- Two real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
structure is_conjugate_exponent (p : ℝ) (q : ℝ) where
  one_lt : 1 < p
  inv_add_inv_conj : 1 / p + 1 / q = 1

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `1/p + 1/q = 1`. -/
def conjugate_exponent (p : ℝ) : ℝ := p / (p - 1)

namespace is_conjugate_exponent


/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/

theorem pos {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : 0 < p :=
  lt_trans zero_lt_one (one_lt h)

theorem nonneg {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : 0 ≤ p := le_of_lt (pos h)

theorem ne_zero {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : p ≠ 0 := ne_of_gt (pos h)

theorem sub_one_pos {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : 0 < p - 1 :=
  iff.mpr sub_pos (one_lt h)

theorem sub_one_ne_zero {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : p - 1 ≠ 0 :=
  ne_of_gt (sub_one_pos h)

theorem one_div_pos {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : 0 < 1 / p :=
  iff.mpr one_div_pos (pos h)

theorem one_div_nonneg {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : 0 ≤ 1 / p :=
  le_of_lt (one_div_pos h)

theorem one_div_ne_zero {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : 1 / p ≠ 0 :=
  ne_of_gt (one_div_pos h)

theorem conj_eq {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : q = p / (p - 1) := sorry

theorem conjugate_eq {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : conjugate_exponent p = q :=
  Eq.symm (conj_eq h)

theorem sub_one_mul_conj {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ iff.mp (eq_div_iff (sub_one_ne_zero h)) (conj_eq h)

theorem mul_eq_add {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : p * q = p + q := sorry

protected theorem symm {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) :
    is_conjugate_exponent q p :=
  sorry

theorem one_lt_nnreal {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) : 1 < nnreal.of_real p :=
  sorry

theorem inv_add_inv_conj_nnreal {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) :
    1 / nnreal.of_real p + 1 / nnreal.of_real q = 1 :=
  sorry

theorem inv_add_inv_conj_ennreal {p : ℝ} {q : ℝ} (h : is_conjugate_exponent p q) :
    1 / ennreal.of_real p + 1 / ennreal.of_real q = 1 :=
  sorry

end is_conjugate_exponent


theorem is_conjugate_exponent_iff {p : ℝ} {q : ℝ} (h : 1 < p) :
    is_conjugate_exponent p q ↔ q = p / (p - 1) :=
  sorry

theorem is_conjugate_exponent_conjugate_exponent {p : ℝ} (h : 1 < p) :
    is_conjugate_exponent p (conjugate_exponent p) :=
  iff.mpr (is_conjugate_exponent_iff h) rfl

end Mathlib