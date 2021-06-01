/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.prime
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Extended GCD and divisibility over ℤ

## Main definitions

* Given `x y : ℕ`, `xgcd x y` computes the pair of integers `(a, b)` such that
  `gcd x y = x * a + y * b`. `gcd_a x y` and `gcd_b x y` are defined to be `a` and `b`,
  respectively.

## Main statements

* `gcd_eq_gcd_ab`: Bézout's lemma, given `x y : ℕ`, `gcd x y = x * gcd_a x y + y * gcd_b x y`.

-/

/-! ### Extended Euclidean algorithm -/

namespace nat


/-- Helper function for the extended GCD algorithm (`nat.xgcd`). -/
def xgcd_aux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ := sorry

@[simp] theorem xgcd_zero_left {s : ℤ} {t : ℤ} {r' : ℕ} {s' : ℤ} {t' : ℤ} :
    xgcd_aux 0 s t r' s' t' = (r', s', t') :=
  sorry

theorem xgcd_aux_rec {r : ℕ} {s : ℤ} {t : ℤ} {r' : ℕ} {s' : ℤ} {t' : ℤ} (h : 0 < r) :
    xgcd_aux r s t r' s' t' = xgcd_aux (r' % r) (s' - ↑r' / ↑r * s) (t' - ↑r' / ↑r * t) r s t :=
  sorry

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x : ℕ) (y : ℕ) : ℤ × ℤ := prod.snd (xgcd_aux x 1 0 y 0 1)

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_a (x : ℕ) (y : ℕ) : ℤ := prod.fst (xgcd x y)

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_b (x : ℕ) (y : ℕ) : ℤ := prod.snd (xgcd x y)

@[simp] theorem gcd_a_zero_left {s : ℕ} : gcd_a 0 s = 0 := sorry

@[simp] theorem gcd_b_zero_left {s : ℕ} : gcd_b 0 s = 1 := sorry

@[simp] theorem gcd_a_zero_right {s : ℕ} (h : s ≠ 0) : gcd_a s 0 = 1 := sorry

@[simp] theorem gcd_b_zero_right {s : ℕ} (h : s ≠ 0) : gcd_b s 0 = 0 := sorry

@[simp] theorem xgcd_aux_fst (x : ℕ) (y : ℕ) (s : ℤ) (t : ℤ) (s' : ℤ) (t' : ℤ) :
    prod.fst (xgcd_aux x s t y s' t') = gcd x y :=
  sorry

theorem xgcd_aux_val (x : ℕ) (y : ℕ) : xgcd_aux x 1 0 y 0 1 = (gcd x y, xgcd x y) := sorry

theorem xgcd_val (x : ℕ) (y : ℕ) : xgcd x y = (gcd_a x y, gcd_b x y) := sorry

theorem xgcd_aux_P (x : ℕ) (y : ℕ) {r : ℕ} {r' : ℕ} {s : ℤ} {t : ℤ} {s' : ℤ} {t' : ℤ} :
    P x y (r, s, t) → P x y (r', s', t') → P x y (xgcd_aux r s t r' s' t') :=
  sorry

/-- Bézout's lemma: given `x y : ℕ`, `gcd x y = x * a + y * b`, where `a = gcd_a x y` and
`b = gcd_b x y` are computed by the extended Euclidean algorithm.
-/
theorem gcd_eq_gcd_ab (x : ℕ) (y : ℕ) : ↑(gcd x y) = ↑x * gcd_a x y + ↑y * gcd_b x y := sorry

end nat


/-! ### Divisibility over ℤ -/

namespace int


theorem nat_abs_div (a : ℤ) (b : ℤ) (H : b ∣ a) : nat_abs (a / b) = nat_abs a / nat_abs b := sorry

theorem nat_abs_dvd_abs_iff {i : ℤ} {j : ℤ} : nat_abs i ∣ nat_abs j ↔ i ∣ j :=
  { mp :=
      fun (H : nat_abs i ∣ nat_abs j) =>
        iff.mp dvd_nat_abs (iff.mp nat_abs_dvd (iff.mpr coe_nat_dvd H)),
    mpr := fun (H : i ∣ j) => iff.mp coe_nat_dvd (iff.mpr dvd_nat_abs (iff.mpr nat_abs_dvd H)) }

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : nat.prime p) {m : ℤ} {n : ℤ}
    {k : ℕ} {l : ℕ} (hpm : ↑(p ^ k) ∣ m) (hpn : ↑(p ^ l) ∣ n) (hpmn : ↑(p ^ (k + l + 1)) ∣ m * n) :
    ↑(p ^ (k + 1)) ∣ m ∨ ↑(p ^ (l + 1)) ∣ n :=
  sorry

theorem dvd_of_mul_dvd_mul_left {i : ℤ} {j : ℤ} {k : ℤ} (k_non_zero : k ≠ 0) (H : k * i ∣ k * j) :
    i ∣ j :=
  dvd.elim H
    fun (l : ℤ) (H1 : k * j = k * i * l) =>
      Exists.intro l
        (mul_left_cancel' k_non_zero
          (eq.mp (Eq._oldrec (Eq.refl (k * j = k * i * l)) (mul_assoc k i l)) H1))

theorem dvd_of_mul_dvd_mul_right {i : ℤ} {j : ℤ} {k : ℤ} (k_non_zero : k ≠ 0) (H : i * k ∣ j * k) :
    i ∣ j :=
  dvd_of_mul_dvd_mul_left k_non_zero
    (eq.mp (Eq._oldrec (Eq.refl (k * i ∣ j * k)) (mul_comm j k))
      (eq.mp (Eq._oldrec (Eq.refl (i * k ∣ j * k)) (mul_comm i k)) H))

theorem prime.dvd_nat_abs_of_coe_dvd_pow_two {p : ℕ} (hp : nat.prime p) (k : ℤ)
    (h : ↑p ∣ k ^ bit0 1) : p ∣ nat_abs k :=
  sorry

/-- ℤ specific version of least common multiple. -/
def lcm (i : ℤ) (j : ℤ) : ℕ := nat.lcm (nat_abs i) (nat_abs j)

theorem lcm_def (i : ℤ) (j : ℤ) : lcm i j = nat.lcm (nat_abs i) (nat_abs j) := rfl

theorem gcd_dvd_left (i : ℤ) (j : ℤ) : ↑(gcd i j) ∣ i :=
  iff.mp dvd_nat_abs (iff.mpr coe_nat_dvd (nat.gcd_dvd_left (nat_abs i) (nat_abs j)))

theorem gcd_dvd_right (i : ℤ) (j : ℤ) : ↑(gcd i j) ∣ j :=
  iff.mp dvd_nat_abs (iff.mpr coe_nat_dvd (nat.gcd_dvd_right (nat_abs i) (nat_abs j)))

theorem dvd_gcd {i : ℤ} {j : ℤ} {k : ℤ} (h1 : k ∣ i) (h2 : k ∣ j) : k ∣ ↑(gcd i j) :=
  iff.mp nat_abs_dvd
    (iff.mpr coe_nat_dvd
      (nat.dvd_gcd (iff.mpr nat_abs_dvd_abs_iff h1) (iff.mpr nat_abs_dvd_abs_iff h2)))

theorem gcd_mul_lcm (i : ℤ) (j : ℤ) : gcd i j * lcm i j = nat_abs (i * j) := sorry

theorem gcd_comm (i : ℤ) (j : ℤ) : gcd i j = gcd j i := nat.gcd_comm (nat_abs i) (nat_abs j)

theorem gcd_assoc (i : ℤ) (j : ℤ) (k : ℤ) : gcd (↑(gcd i j)) k = gcd i ↑(gcd j k) :=
  nat.gcd_assoc (nat_abs i) (nat_abs j) (nat_abs k)

@[simp] theorem gcd_self (i : ℤ) : gcd i i = nat_abs i := sorry

@[simp] theorem gcd_zero_left (i : ℤ) : gcd 0 i = nat_abs i := sorry

@[simp] theorem gcd_zero_right (i : ℤ) : gcd i 0 = nat_abs i := sorry

@[simp] theorem gcd_one_left (i : ℤ) : gcd 1 i = 1 := nat.gcd_one_left (nat_abs i)

@[simp] theorem gcd_one_right (i : ℤ) : gcd i 1 = 1 := nat.gcd_one_right (nat_abs i)

theorem gcd_mul_left (i : ℤ) (j : ℤ) (k : ℤ) : gcd (i * j) (i * k) = nat_abs i * gcd j k := sorry

theorem gcd_mul_right (i : ℤ) (j : ℤ) (k : ℤ) : gcd (i * j) (k * j) = gcd i k * nat_abs j := sorry

theorem gcd_pos_of_non_zero_left {i : ℤ} (j : ℤ) (i_non_zero : i ≠ 0) : 0 < gcd i j :=
  nat.gcd_pos_of_pos_left (nat_abs j) (nat_abs_pos_of_ne_zero i_non_zero)

theorem gcd_pos_of_non_zero_right (i : ℤ) {j : ℤ} (j_non_zero : j ≠ 0) : 0 < gcd i j :=
  nat.gcd_pos_of_pos_right (nat_abs i) (nat_abs_pos_of_ne_zero j_non_zero)

theorem gcd_eq_zero_iff {i : ℤ} {j : ℤ} : gcd i j = 0 ↔ i = 0 ∧ j = 0 := sorry

theorem gcd_div {i : ℤ} {j : ℤ} {k : ℤ} (H1 : k ∣ i) (H2 : k ∣ j) :
    gcd (i / k) (j / k) = gcd i j / nat_abs k :=
  sorry

theorem gcd_div_gcd_div_gcd {i : ℤ} {j : ℤ} (H : 0 < gcd i j) :
    gcd (i / ↑(gcd i j)) (j / ↑(gcd i j)) = 1 :=
  sorry

theorem gcd_dvd_gcd_of_dvd_left {i : ℤ} {k : ℤ} (j : ℤ) (H : i ∣ k) : gcd i j ∣ gcd k j :=
  iff.mp coe_nat_dvd (dvd_gcd (dvd.trans (gcd_dvd_left i j) H) (gcd_dvd_right i j))

theorem gcd_dvd_gcd_of_dvd_right {i : ℤ} {k : ℤ} (j : ℤ) (H : i ∣ k) : gcd j i ∣ gcd j k :=
  iff.mp coe_nat_dvd (dvd_gcd (gcd_dvd_left j i) (dvd.trans (gcd_dvd_right j i) H))

theorem gcd_dvd_gcd_mul_left (i : ℤ) (j : ℤ) (k : ℤ) : gcd i j ∣ gcd (k * i) j :=
  gcd_dvd_gcd_of_dvd_left j (dvd_mul_left i k)

theorem gcd_dvd_gcd_mul_right (i : ℤ) (j : ℤ) (k : ℤ) : gcd i j ∣ gcd (i * k) j :=
  gcd_dvd_gcd_of_dvd_left j (dvd_mul_right i k)

theorem gcd_dvd_gcd_mul_left_right (i : ℤ) (j : ℤ) (k : ℤ) : gcd i j ∣ gcd i (k * j) :=
  gcd_dvd_gcd_of_dvd_right i (dvd_mul_left j k)

theorem gcd_dvd_gcd_mul_right_right (i : ℤ) (j : ℤ) (k : ℤ) : gcd i j ∣ gcd i (j * k) :=
  gcd_dvd_gcd_of_dvd_right i (dvd_mul_right j k)

theorem gcd_eq_left {i : ℤ} {j : ℤ} (H : i ∣ j) : gcd i j = nat_abs i := sorry

theorem gcd_eq_right {i : ℤ} {j : ℤ} (H : j ∣ i) : gcd i j = nat_abs j :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd i j = nat_abs j)) (gcd_comm i j)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd j i = nat_abs j)) (gcd_eq_left H))) (Eq.refl (nat_abs j)))

theorem ne_zero_of_gcd {x : ℤ} {y : ℤ} (hc : gcd x y ≠ 0) : x ≠ 0 ∨ y ≠ 0 := sorry

theorem exists_gcd_one {m : ℤ} {n : ℤ} (H : 0 < gcd m n) :
    ∃ (m' : ℤ), ∃ (n' : ℤ), gcd m' n' = 1 ∧ m = m' * ↑(gcd m n) ∧ n = n' * ↑(gcd m n) :=
  sorry

theorem exists_gcd_one' {m : ℤ} {n : ℤ} (H : 0 < gcd m n) :
    ∃ (g : ℕ), ∃ (m' : ℤ), ∃ (n' : ℤ), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * ↑g ∧ n = n' * ↑g :=
  sorry

theorem pow_dvd_pow_iff {m : ℤ} {n : ℤ} {k : ℕ} (k0 : 0 < k) : m ^ k ∣ n ^ k ↔ m ∣ n := sorry

/-! ### lcm -/

theorem lcm_comm (i : ℤ) (j : ℤ) : lcm i j = lcm j i :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lcm i j = lcm j i)) (lcm.equations._eqn_1 i j)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (nat.lcm (nat_abs i) (nat_abs j) = lcm j i))
          (lcm.equations._eqn_1 j i)))
      (nat.lcm_comm (nat_abs i) (nat_abs j)))

theorem lcm_assoc (i : ℤ) (j : ℤ) (k : ℤ) : lcm (↑(lcm i j)) k = lcm i ↑(lcm j k) := sorry

@[simp] theorem lcm_zero_left (i : ℤ) : lcm 0 i = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lcm 0 i = 0)) (lcm.equations._eqn_1 0 i)))
    (nat.lcm_zero_left (nat_abs i))

@[simp] theorem lcm_zero_right (i : ℤ) : lcm i 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lcm i 0 = 0)) (lcm.equations._eqn_1 i 0)))
    (nat.lcm_zero_right (nat_abs i))

@[simp] theorem lcm_one_left (i : ℤ) : lcm 1 i = nat_abs i :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lcm 1 i = nat_abs i)) (lcm.equations._eqn_1 1 i)))
    (nat.lcm_one_left (nat_abs i))

@[simp] theorem lcm_one_right (i : ℤ) : lcm i 1 = nat_abs i :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lcm i 1 = nat_abs i)) (lcm.equations._eqn_1 i 1)))
    (nat.lcm_one_right (nat_abs i))

@[simp] theorem lcm_self (i : ℤ) : lcm i i = nat_abs i :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lcm i i = nat_abs i)) (lcm.equations._eqn_1 i i)))
    (nat.lcm_self (nat_abs i))

theorem dvd_lcm_left (i : ℤ) (j : ℤ) : i ∣ ↑(lcm i j) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (i ∣ ↑(lcm i j))) (lcm.equations._eqn_1 i j)))
    (iff.mpr coe_nat_dvd_right (nat.dvd_lcm_left (nat_abs i) (nat_abs j)))

theorem dvd_lcm_right (i : ℤ) (j : ℤ) : j ∣ ↑(lcm i j) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (j ∣ ↑(lcm i j))) (lcm.equations._eqn_1 i j)))
    (iff.mpr coe_nat_dvd_right (nat.dvd_lcm_right (nat_abs i) (nat_abs j)))

theorem lcm_dvd {i : ℤ} {j : ℤ} {k : ℤ} : i ∣ k → j ∣ k → ↑(lcm i j) ∣ k :=
  eq.mpr (id (Eq._oldrec (Eq.refl (i ∣ k → j ∣ k → ↑(lcm i j) ∣ k)) (lcm.equations._eqn_1 i j)))
    fun (hi : i ∣ k) (hj : j ∣ k) =>
      iff.mpr coe_nat_dvd_left
        (nat.lcm_dvd (iff.mpr nat_abs_dvd_abs_iff hi) (iff.mpr nat_abs_dvd_abs_iff hj))

end int


theorem pow_gcd_eq_one {M : Type u_1} [monoid M] (x : M) {m : ℕ} {n : ℕ} (hm : x ^ m = 1)
    (hn : x ^ n = 1) : x ^ nat.gcd m n = 1 :=
  sorry

end Mathlib