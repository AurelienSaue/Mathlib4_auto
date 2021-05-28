/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Paul van Wamelen.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.field
import Mathlib.ring_theory.int.basic
import Mathlib.algebra.group_with_zero.power
import Mathlib.tactic.ring
import Mathlib.tactic.ring_exp
import Mathlib.tactic.field_simp
import PostPort

universes u_1 

namespace Mathlib

/-!
# Pythagorean Triples
The main result is the classification of pythagorean triples. The final result is for general
pythagorean triples. It follows from the more interesting relatively prime case. We use the
"rational parametrization of the circle" method for the proof. The parametrization maps the point
`(x / z, y / z)` to the slope of the line through `(-1 , 0)` and `(x / z, y / z)`. This quickly
shows that `(x / z, y / z) = (2 * m * n / (m ^ 2 + n ^ 2), (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2))` where
`m / n` is the slope. In order to identify numerators and denominators we now need results showing
that these are coprime. This is easy except for the prime 2. In order to deal with that we have to
analyze the parity of `x`, `y`, `m` and `n` and eliminate all the impossible cases. This takes up
the bulk of the proof below.
-/

/-- Three integers `x`, `y`, and `z` form a Pythagorean triple if `x * x + y * y = z * z`. -/
def pythagorean_triple (x : ℤ) (y : ℤ) (z : ℤ)  :=
  x * x + y * y = z * z

/-- Pythagorean triples are interchangable, i.e `x * x + y * y = y * y + x * x = z * z`.
This comes from additive commutativity. -/
theorem pythagorean_triple_comm {x : ℤ} {y : ℤ} {z : ℤ} : pythagorean_triple x y z ↔ pythagorean_triple y x z :=
  id
    (eq.mpr (id (Eq._oldrec (Eq.refl (x * x + y * y = z * z ↔ y * y + x * x = z * z)) (add_comm (x * x) (y * y))))
      (iff.refl (y * y + x * x = z * z)))

/-- The zeroth Pythagorean triple is all zeros. -/
theorem pythagorean_triple.zero : pythagorean_triple 0 0 0 := sorry

namespace pythagorean_triple


theorem eq {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) : x * x + y * y = z * z :=
  h

theorem symm {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) : pythagorean_triple y x z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (pythagorean_triple y x z)) (propext pythagorean_triple_comm))) h

/-- A triple is still a triple if you multiply `x`, `y` and `z`
by a constant `k`. -/
theorem mul {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (k : ℤ) : pythagorean_triple (k * x) (k * y) (k * z) := sorry

/-- `(k*x, k*y, k*z)` is a Pythagorean triple if and only if
`(x, y, z)` is also a triple. -/
theorem mul_iff {x : ℤ} {y : ℤ} {z : ℤ} (k : ℤ) (hk : k ≠ 0) : pythagorean_triple (k * x) (k * y) (k * z) ↔ pythagorean_triple x y z := sorry

/-- A pythogorean triple `x, y, z` is “classified” if there exist integers `k, m, n` such that either
 * `x = k * (m ^ 2 - n ^ 2)` and `y = k * (2 * m * n)`, or
 * `x = k * (2 * m * n)` and `y = k * (m ^ 2 - n ^ 2)`. -/
def is_classified {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z)  :=
  ∃ (k : ℤ),
    ∃ (m : ℤ),
      ∃ (n : ℤ),
        (x = k * (m ^ bit0 1 - n ^ bit0 1) ∧ y = k * (bit0 1 * m * n) ∨
            x = k * (bit0 1 * m * n) ∧ y = k * (m ^ bit0 1 - n ^ bit0 1)) ∧
          int.gcd m n = 1

/-- A primitive pythogorean triple `x, y, z` is a pythagorean triple with `x` and `y` coprime.
 Such a triple is “primitively classified” if there exist coprime integers `m, n` such that either
 * `x = m ^ 2 - n ^ 2` and `y = 2 * m * n`, or
 * `x = 2 * m * n` and `y = m ^ 2 - n ^ 2`.
-/
def is_primitive_classified {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z)  :=
  ∃ (m : ℤ),
    ∃ (n : ℤ),
      (x = m ^ bit0 1 - n ^ bit0 1 ∧ y = bit0 1 * m * n ∨ x = bit0 1 * m * n ∧ y = m ^ bit0 1 - n ^ bit0 1) ∧
        int.gcd m n = 1 ∧ (m % bit0 1 = 0 ∧ n % bit0 1 = 1 ∨ m % bit0 1 = 1 ∧ n % bit0 1 = 0)

theorem mul_is_classified {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (k : ℤ) (hc : is_classified h) : is_classified (mul h k) := sorry

theorem even_odd_of_coprime {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (hc : int.gcd x y = 1) : x % bit0 1 = 0 ∧ y % bit0 1 = 1 ∨ x % bit0 1 = 1 ∧ y % bit0 1 = 0 := sorry

theorem gcd_dvd {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) : ↑(int.gcd x y) ∣ z := sorry

theorem normalize {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) : pythagorean_triple (x / ↑(int.gcd x y)) (y / ↑(int.gcd x y)) (z / ↑(int.gcd x y)) := sorry

theorem is_classified_of_is_primitive_classified {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (hp : is_primitive_classified h) : is_classified h := sorry

theorem is_classified_of_normalize_is_primitive_classified {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (hc : is_primitive_classified (normalize h)) : is_classified h := sorry

theorem ne_zero_of_coprime {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (hc : int.gcd x y = 1) : z ≠ 0 := sorry

theorem is_primitive_classified_of_coprime_of_zero_left {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (hc : int.gcd x y = 1) (hx : x = 0) : is_primitive_classified h := sorry

theorem coprime_of_coprime {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (hc : int.gcd x y = 1) : int.gcd y z = 1 := sorry

end pythagorean_triple


/-!
### A parametrization of the unit circle

For the classification of pythogorean triples, we will use a parametrization of the unit circle.
-/

/--  A parameterization of the unit circle that is useful for classifying Pythagorean triples.
 (To be applied in the case where `K = ℚ`.) -/
def circle_equiv_gen {K : Type u_1} [field K] (hk : ∀ (x : K), 1 + x ^ bit0 1 ≠ 0) : K ≃ Subtype fun (p : K × K) => prod.fst p ^ bit0 1 + prod.snd p ^ bit0 1 = 1 ∧ prod.snd p ≠ -1 :=
  equiv.mk
    (fun (x : K) => { val := (bit0 1 * x / (1 + x ^ bit0 1), (1 - x ^ bit0 1) / (1 + x ^ bit0 1)), property := sorry })
    (fun (p : Subtype fun (p : K × K) => prod.fst p ^ bit0 1 + prod.snd p ^ bit0 1 = 1 ∧ prod.snd p ≠ -1) =>
      prod.fst ↑p / (prod.snd ↑p + 1))
    sorry sorry

@[simp] theorem circle_equiv_apply {K : Type u_1} [field K] (hk : ∀ (x : K), 1 + x ^ bit0 1 ≠ 0) (x : K) : ↑(coe_fn (circle_equiv_gen hk) x) = (bit0 1 * x / (1 + x ^ bit0 1), (1 - x ^ bit0 1) / (1 + x ^ bit0 1)) :=
  rfl

@[simp] theorem circle_equiv_symm_apply {K : Type u_1} [field K] (hk : ∀ (x : K), 1 + x ^ bit0 1 ≠ 0) (v : Subtype fun (p : K × K) => prod.fst p ^ bit0 1 + prod.snd p ^ bit0 1 = 1 ∧ prod.snd p ≠ -1) : coe_fn (equiv.symm (circle_equiv_gen hk)) v = prod.fst ↑v / (prod.snd ↑v + 1) :=
  rfl

namespace pythagorean_triple


theorem is_primitive_classified_aux {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (hc : int.gcd x y = 1) (hzpos : 0 < z) {m : ℤ} {n : ℤ} (hm2n2 : 0 < m ^ bit0 1 + n ^ bit0 1) (hv2 : ↑x / ↑z = bit0 1 * ↑m * ↑n / (↑m ^ bit0 1 + ↑n ^ bit0 1)) (hw2 : ↑y / ↑z = (↑m ^ bit0 1 - ↑n ^ bit0 1) / (↑m ^ bit0 1 + ↑n ^ bit0 1)) (H : int.gcd (m ^ bit0 1 - n ^ bit0 1) (m ^ bit0 1 + n ^ bit0 1) = 1) (co : int.gcd m n = 1) (pp : m % bit0 1 = 0 ∧ n % bit0 1 = 1 ∨ m % bit0 1 = 1 ∧ n % bit0 1 = 0) : is_primitive_classified h := sorry

theorem is_primitive_classified_of_coprime_of_odd_of_pos {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (hc : int.gcd x y = 1) (hyo : y % bit0 1 = 1) (hzpos : 0 < z) : is_primitive_classified h := sorry

theorem is_primitive_classified_of_coprime_of_pos {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (hc : int.gcd x y = 1) (hzpos : 0 < z) : is_primitive_classified h := sorry

theorem is_primitive_classified_of_coprime {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (hc : int.gcd x y = 1) : is_primitive_classified h := sorry

theorem classified {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) : is_classified h := sorry

theorem coprime_classification {x : ℤ} {y : ℤ} {z : ℤ} : pythagorean_triple x y z ∧ int.gcd x y = 1 ↔
  ∃ (m : ℤ),
    ∃ (n : ℤ),
      (x = m ^ bit0 1 - n ^ bit0 1 ∧ y = bit0 1 * m * n ∨ x = bit0 1 * m * n ∧ y = m ^ bit0 1 - n ^ bit0 1) ∧
        (z = m ^ bit0 1 + n ^ bit0 1 ∨ z = -(m ^ bit0 1 + n ^ bit0 1)) ∧
          int.gcd m n = 1 ∧ (m % bit0 1 = 0 ∧ n % bit0 1 = 1 ∨ m % bit0 1 = 1 ∧ n % bit0 1 = 0) := sorry

/-- by assuming `x` is odd and `z` is positive we get a slightly more precise classification of
the pythagorean triple `x ^ 2 + y ^ 2 = z ^ 2`-/
theorem coprime_classification' {x : ℤ} {y : ℤ} {z : ℤ} (h : pythagorean_triple x y z) (h_coprime : int.gcd x y = 1) (h_parity : x % bit0 1 = 1) (h_pos : 0 < z) : ∃ (m : ℤ),
  ∃ (n : ℤ),
    x = m ^ bit0 1 - n ^ bit0 1 ∧
      y = bit0 1 * m * n ∧
        z = m ^ bit0 1 + n ^ bit0 1 ∧
          int.gcd m n = 1 ∧ (m % bit0 1 = 0 ∧ n % bit0 1 = 1 ∨ m % bit0 1 = 1 ∧ n % bit0 1 = 0) ∧ 0 ≤ m := sorry

theorem classification {x : ℤ} {y : ℤ} {z : ℤ} : pythagorean_triple x y z ↔
  ∃ (k : ℤ),
    ∃ (m : ℤ),
      ∃ (n : ℤ),
        (x = k * (m ^ bit0 1 - n ^ bit0 1) ∧ y = k * (bit0 1 * m * n) ∨
            x = k * (bit0 1 * m * n) ∧ y = k * (m ^ bit0 1 - n ^ bit0 1)) ∧
          (z = k * (m ^ bit0 1 + n ^ bit0 1) ∨ z = -k * (m ^ bit0 1 + n ^ bit0 1)) := sorry

