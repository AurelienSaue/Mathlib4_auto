/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Yury Kudryashov.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.real.sqrt
import Mathlib.data.rat.sqrt
import Mathlib.ring_theory.int.basic
import Mathlib.data.polynomial.eval
import Mathlib.data.polynomial.degree.default
import Mathlib.tactic.interval_cases
import Mathlib.PostPort

namespace Mathlib

/-!
# Irrational real numbers

In this file we define a predicate `irrational` on `ℝ`, prove that the `n`-th root of an integer
number is irrational if it is not integer, and that `sqrt q` is irrational if and only if
`rat.sqrt q * rat.sqrt q ≠ q ∧ 0 ≤ q`.

We also provide dot-style constructors like `irrational.add_rat`, `irrational.rat_sub` etc.
-/

/-- A real number is irrational if it is not equal to any rational number. -/
def irrational (x : ℝ)  :=
  ¬x ∈ set.range coe

theorem irrational_iff_ne_rational (x : ℝ) : irrational x ↔ ∀ (a b : ℤ), x ≠ ↑a / ↑b := sorry

/-!
### Irrationality of roots of integer and rational numbers
-/

/-- If `x^n`, `n > 0`, is integer and is not the `n`-th power of an integer, then
`x` is irrational. -/
theorem irrational_nrt_of_notint_nrt {x : ℝ} (n : ℕ) (m : ℤ) (hxr : x ^ n = ↑m) (hv : ¬∃ (y : ℤ), x = ↑y) (hnpos : 0 < n) : irrational x := sorry

/-- If `x^n = m` is an integer and `n` does not divide the `multiplicity p m`, then `x`
is irrational. -/
theorem irrational_nrt_of_n_not_dvd_multiplicity {x : ℝ} (n : ℕ) {m : ℤ} (hm : m ≠ 0) (p : ℕ) [hp : fact (nat.prime p)] (hxr : x ^ n = ↑m) (hv : roption.get (multiplicity (↑p) m) (iff.mpr multiplicity.finite_int_iff { left := nat.prime.ne_one hp, right := hm }) %
    n ≠
  0) : irrational x := sorry

theorem irrational_sqrt_of_multiplicity_odd (m : ℤ) (hm : 0 < m) (p : ℕ) [hp : fact (nat.prime p)] (Hpv : roption.get (multiplicity (↑p) m)
      (iff.mpr multiplicity.finite_int_iff { left := nat.prime.ne_one hp, right := ne.symm (ne_of_lt hm) }) %
    bit0 1 =
  1) : irrational (real.sqrt ↑m) := sorry

theorem nat.prime.irrational_sqrt {p : ℕ} (hp : nat.prime p) : irrational (real.sqrt ↑p) := sorry

theorem irrational_sqrt_two : irrational (real.sqrt (bit0 1)) := sorry

theorem irrational_sqrt_rat_iff (q : ℚ) : irrational (real.sqrt ↑q) ↔ rat.sqrt q * rat.sqrt q ≠ q ∧ 0 ≤ q := sorry

protected instance irrational.decidable (q : ℚ) : Decidable (irrational (real.sqrt ↑q)) :=
  decidable_of_iff' (rat.sqrt q * rat.sqrt q ≠ q ∧ 0 ≤ q) (irrational_sqrt_rat_iff q)

/-!
### Adding/subtracting/multiplying by rational numbers
-/

theorem rat.not_irrational (q : ℚ) : ¬irrational ↑q :=
  fun (h : irrational ↑q) => h (Exists.intro q rfl)

namespace irrational


theorem add_cases {x : ℝ} {y : ℝ} : irrational (x + y) → irrational x ∨ irrational y := sorry

theorem of_rat_add (q : ℚ) {x : ℝ} (h : irrational (↑q + x)) : irrational x :=
  or.elim (add_cases h) (fun (h : irrational ↑q) => absurd h (rat.not_irrational q)) id

theorem rat_add (q : ℚ) {x : ℝ} (h : irrational x) : irrational (↑q + x) :=
  of_rat_add (-q)
    (eq.mpr (id (Eq._oldrec (Eq.refl (irrational (↑(-q) + (↑q + x)))) (rat.cast_neg q)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (irrational (-↑q + (↑q + x)))) (neg_add_cancel_left (↑q) x))) h))

theorem of_add_rat (q : ℚ) {x : ℝ} : irrational (x + ↑q) → irrational x :=
  add_comm (↑q) x ▸ of_rat_add q

theorem add_rat (q : ℚ) {x : ℝ} (h : irrational x) : irrational (x + ↑q) :=
  add_comm (↑q) x ▸ rat_add q h

theorem of_neg {x : ℝ} (h : irrational (-x)) : irrational x := sorry

protected theorem neg {x : ℝ} (h : irrational x) : irrational (-x) :=
  of_neg (eq.mpr (id (Eq._oldrec (Eq.refl (irrational ( --x))) (neg_neg x))) h)

theorem sub_rat (q : ℚ) {x : ℝ} (h : irrational x) : irrational (x - ↑q) := sorry

theorem rat_sub (q : ℚ) {x : ℝ} (h : irrational x) : irrational (↑q - x) :=
  eq.mpr (id ((fun (x x_1 : ℝ) (e_1 : x = x_1) => congr_arg irrational e_1) (↑q - x) (↑q + -x) (sub_eq_add_neg (↑q) x)))
    (eq.mp (Eq.refl (irrational (↑q + -x))) (rat_add q (irrational.neg h)))

theorem of_sub_rat (q : ℚ) {x : ℝ} (h : irrational (x - ↑q)) : irrational x := sorry

theorem of_rat_sub (q : ℚ) {x : ℝ} (h : irrational (↑q - x)) : irrational x := sorry

theorem mul_cases {x : ℝ} {y : ℝ} : irrational (x * y) → irrational x ∨ irrational y := sorry

theorem of_mul_rat (q : ℚ) {x : ℝ} (h : irrational (x * ↑q)) : irrational x :=
  or.elim (mul_cases h) id fun (h : irrational ↑q) => absurd h (rat.not_irrational q)

theorem mul_rat {x : ℝ} (h : irrational x) {q : ℚ} (hq : q ≠ 0) : irrational (x * ↑q) := sorry

theorem of_rat_mul (q : ℚ) {x : ℝ} : irrational (↑q * x) → irrational x :=
  mul_comm x ↑q ▸ of_mul_rat q

theorem rat_mul {x : ℝ} (h : irrational x) {q : ℚ} (hq : q ≠ 0) : irrational (↑q * x) :=
  mul_comm x ↑q ▸ mul_rat h hq

theorem of_mul_self {x : ℝ} (h : irrational (x * x)) : irrational x :=
  or.elim (mul_cases h) id id

theorem of_inv {x : ℝ} (h : irrational (x⁻¹)) : irrational x := sorry

protected theorem inv {x : ℝ} (h : irrational x) : irrational (x⁻¹) :=
  of_inv (eq.mpr (id (Eq._oldrec (Eq.refl (irrational (x⁻¹⁻¹))) (inv_inv' x))) h)

theorem div_cases {x : ℝ} {y : ℝ} (h : irrational (x / y)) : irrational x ∨ irrational y :=
  or.imp id of_inv (mul_cases h)

theorem of_rat_div (q : ℚ) {x : ℝ} (h : irrational (↑q / x)) : irrational x :=
  of_inv (of_rat_mul q h)

theorem of_one_div {x : ℝ} (h : irrational (1 / x)) : irrational x :=
  of_rat_div 1 (eq.mpr (id (Eq._oldrec (Eq.refl (irrational (↑1 / x))) rat.cast_one)) h)

theorem of_pow {x : ℝ} (n : ℕ) : irrational (x ^ n) → irrational x := sorry

theorem of_fpow {x : ℝ} (m : ℤ) : irrational (x ^ m) → irrational x := sorry

end irrational


theorem one_lt_nat_degree_of_irrational_root (x : ℝ) (p : polynomial ℤ) (hx : irrational x) (p_nonzero : p ≠ 0) (x_is_root : coe_fn (polynomial.aeval x) p = 0) : 1 < polynomial.nat_degree p := sorry

@[simp] theorem irrational_rat_add_iff {q : ℚ} {x : ℝ} : irrational (↑q + x) ↔ irrational x :=
  { mp := irrational.of_rat_add q, mpr := irrational.rat_add q }

@[simp] theorem irrational_add_rat_iff {q : ℚ} {x : ℝ} : irrational (x + ↑q) ↔ irrational x :=
  { mp := irrational.of_add_rat q, mpr := irrational.add_rat q }

@[simp] theorem irrational_rat_sub_iff {q : ℚ} {x : ℝ} : irrational (↑q - x) ↔ irrational x :=
  { mp := irrational.of_rat_sub q, mpr := irrational.rat_sub q }

@[simp] theorem irrational_sub_rat_iff {q : ℚ} {x : ℝ} : irrational (x - ↑q) ↔ irrational x :=
  { mp := irrational.of_sub_rat q, mpr := irrational.sub_rat q }

@[simp] theorem irrational_neg_iff {x : ℝ} : irrational (-x) ↔ irrational x :=
  { mp := irrational.of_neg, mpr := irrational.neg }

@[simp] theorem irrational_inv_iff {x : ℝ} : irrational (x⁻¹) ↔ irrational x :=
  { mp := irrational.of_inv, mpr := irrational.inv }

