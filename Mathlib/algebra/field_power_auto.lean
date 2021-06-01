/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Integer power operation on fields.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group_with_zero.power
import Mathlib.tactic.linarith.default
import Mathlib.PostPort

universes u_1 u_2 u 

namespace Mathlib

@[simp] theorem ring_hom.map_fpow {K : Type u_1} {L : Type u_2} [division_ring K] [division_ring L]
    (f : K →+* L) (a : K) (n : ℤ) : coe_fn f (a ^ n) = coe_fn f a ^ n :=
  monoid_with_zero_hom.map_fpow (ring_hom.to_monoid_with_zero_hom f)

@[simp] theorem neg_fpow_bit0 {K : Type u_1} [division_ring K] (x : K) (n : ℤ) :
    (-x) ^ bit0 n = x ^ bit0 n :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((-x) ^ bit0 n = x ^ bit0 n)) (fpow_bit0' (-x) n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((-x * -x) ^ n = x ^ bit0 n)) (fpow_bit0' x n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl ((-x * -x) ^ n = (x * x) ^ n)) (neg_mul_neg x x)))
        (Eq.refl ((x * x) ^ n))))

@[simp] theorem neg_fpow_bit1 {K : Type u_1} [division_ring K] (x : K) (n : ℤ) :
    (-x) ^ bit1 n = -x ^ bit1 n :=
  sorry

theorem fpow_nonneg_of_nonneg {K : Type u} [linear_ordered_field K] {a : K} (ha : 0 ≤ a) (z : ℤ) :
    0 ≤ a ^ z :=
  int.cases_on z (fun (z : ℕ) => idRhs (0 ≤ a ^ z) (pow_nonneg ha z))
    fun (z : ℕ) => idRhs (0 ≤ (a ^ Nat.succ z⁻¹)) (iff.mpr inv_nonneg (pow_nonneg ha (Nat.succ z)))

theorem fpow_pos_of_pos {K : Type u} [linear_ordered_field K] {a : K} (ha : 0 < a) (z : ℤ) :
    0 < a ^ z :=
  int.cases_on z (fun (z : ℕ) => idRhs (0 < a ^ z) (pow_pos ha z))
    fun (z : ℕ) => idRhs (0 < (a ^ Nat.succ z⁻¹)) (iff.mpr inv_pos (pow_pos ha (Nat.succ z)))

theorem fpow_le_of_le {K : Type u} [linear_ordered_field K] {x : K} (hx : 1 ≤ x) {a : ℤ} {b : ℤ}
    (h : a ≤ b) : x ^ a ≤ x ^ b :=
  sorry

theorem pow_le_max_of_min_le {K : Type u} [linear_ordered_field K] {x : K} (hx : 1 ≤ x) {a : ℤ}
    {b : ℤ} {c : ℤ} (h : min a b ≤ c) : x ^ (-c) ≤ max (x ^ (-a)) (x ^ (-b)) :=
  sorry

theorem fpow_le_one_of_nonpos {K : Type u} [linear_ordered_field K] {p : K} (hp : 1 ≤ p) {z : ℤ}
    (hz : z ≤ 0) : p ^ z ≤ 1 :=
  sorry

theorem one_le_fpow_of_nonneg {K : Type u} [linear_ordered_field K] {p : K} (hp : 1 ≤ p) {z : ℤ}
    (hz : 0 ≤ z) : 1 ≤ p ^ z :=
  sorry

theorem one_lt_pow {K : Type u_1} [linear_ordered_semiring K] {p : K} (hp : 1 < p) {n : ℕ} :
    1 ≤ n → 1 < p ^ n :=
  sorry

theorem one_lt_fpow {K : Type u_1} [linear_ordered_field K] {p : K} (hp : 1 < p) (z : ℤ) :
    0 < z → 1 < p ^ z :=
  sorry

theorem nat.fpow_pos_of_pos {K : Type u_1} [linear_ordered_field K] {p : ℕ} (h : 0 < p) (n : ℤ) :
    0 < ↑p ^ n :=
  sorry

theorem nat.fpow_ne_zero_of_pos {K : Type u_1} [linear_ordered_field K] {p : ℕ} (h : 0 < p)
    (n : ℤ) : ↑p ^ n ≠ 0 :=
  ne_of_gt (nat.fpow_pos_of_pos h n)

theorem fpow_strict_mono {K : Type u_1} [linear_ordered_field K] {x : K} (hx : 1 < x) :
    strict_mono fun (n : ℤ) => x ^ n :=
  sorry

@[simp] theorem fpow_lt_iff_lt {K : Type u_1} [linear_ordered_field K] {x : K} (hx : 1 < x) {m : ℤ}
    {n : ℤ} : x ^ m < x ^ n ↔ m < n :=
  strict_mono.lt_iff_lt (fpow_strict_mono hx)

@[simp] theorem fpow_le_iff_le {K : Type u_1} [linear_ordered_field K] {x : K} (hx : 1 < x) {m : ℤ}
    {n : ℤ} : x ^ m ≤ x ^ n ↔ m ≤ n :=
  strict_mono.le_iff_le (fpow_strict_mono hx)

@[simp] theorem pos_div_pow_pos {K : Type u_1} [linear_ordered_field K] {a : K} {b : K} (ha : 0 < a)
    (hb : 0 < b) (k : ℕ) : 0 < a / b ^ k :=
  div_pos ha (pow_pos hb k)

@[simp] theorem div_pow_le {K : Type u_1} [linear_ordered_field K] {a : K} {b : K} (ha : 0 < a)
    (hb : 1 ≤ b) (k : ℕ) : a / b ^ k ≤ a :=
  iff.mpr (div_le_iff (pow_pos (lt_of_lt_of_le zero_lt_one hb) k))
    (trans_rel_right LessEq (Eq.symm (mul_one a))
      (iff.mpr (mul_le_mul_left ha) (one_le_pow_of_one_le hb k)))

theorem fpow_injective {K : Type u_1} [linear_ordered_field K] {x : K} (h₀ : 0 < x) (h₁ : x ≠ 1) :
    function.injective (pow x) :=
  sorry

@[simp] theorem fpow_inj {K : Type u_1} [linear_ordered_field K] {x : K} (h₀ : 0 < x) (h₁ : x ≠ 1)
    {m : ℤ} {n : ℤ} : x ^ m = x ^ n ↔ m = n :=
  function.injective.eq_iff (fpow_injective h₀ h₁)

@[simp] theorem rat.cast_fpow {K : Type u_1} [field K] [char_zero K] (q : ℚ) (n : ℤ) :
    ↑(q ^ n) = ↑q ^ n :=
  ring_hom.map_fpow (rat.cast_hom K) q n

end Mathlib