/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.modeq
import Mathlib.data.zsqrtd.basic
import Mathlib.tactic.omega.default
import Mathlib.PostPort

namespace Mathlib

namespace pell


@[simp] theorem d_pos {a : ℕ} (a1 : 1 < a) : 0 < d a1 :=
  nat.sub_pos_of_lt (mul_lt_mul a1 (le_of_lt a1) (of_as_true trivial) (of_as_true trivial))

def pell {a : ℕ} (a1 : 1 < a) : ℕ → ℕ × ℕ :=
  fun (n : ℕ) =>
    nat.rec_on n (1, 0) fun (n : ℕ) (xy : ℕ × ℕ) => (prod.fst xy * a + d a1 * prod.snd xy, prod.fst xy + prod.snd xy * a)

def xn {a : ℕ} (a1 : 1 < a) (n : ℕ) : ℕ :=
  prod.fst (pell a1 n)

def yn {a : ℕ} (a1 : 1 < a) (n : ℕ) : ℕ :=
  prod.snd (pell a1 n)

@[simp] theorem pell_val {a : ℕ} (a1 : 1 < a) (n : ℕ) : pell a1 n = (xn a1 n, yn a1 n) :=
  (fun (this : pell a1 n = (prod.fst (pell a1 n), prod.snd (pell a1 n))) => this)
    ((fun (_a : ℕ × ℕ) => prod.cases_on _a fun (fst snd : ℕ) => idRhs ((fst, snd) = (fst, snd)) rfl) (pell a1 n))

@[simp] theorem xn_zero {a : ℕ} (a1 : 1 < a) : xn a1 0 = 1 :=
  rfl

@[simp] theorem yn_zero {a : ℕ} (a1 : 1 < a) : yn a1 0 = 0 :=
  rfl

@[simp] theorem xn_succ {a : ℕ} (a1 : 1 < a) (n : ℕ) : xn a1 (n + 1) = xn a1 n * a + d a1 * yn a1 n :=
  rfl

@[simp] theorem yn_succ {a : ℕ} (a1 : 1 < a) (n : ℕ) : yn a1 (n + 1) = xn a1 n + yn a1 n * a :=
  rfl

@[simp] theorem xn_one {a : ℕ} (a1 : 1 < a) : xn a1 1 = a := sorry

@[simp] theorem yn_one {a : ℕ} (a1 : 1 < a) : yn a1 1 = 1 := sorry

def xz {a : ℕ} (a1 : 1 < a) (n : ℕ) : ℤ :=
  ↑(xn a1 n)

def yz {a : ℕ} (a1 : 1 < a) (n : ℕ) : ℤ :=
  ↑(yn a1 n)

def az {a : ℕ} (a1 : 1 < a) : ℤ :=
  ↑a

theorem asq_pos {a : ℕ} (a1 : 1 < a) : 0 < a * a :=
  le_trans (le_of_lt a1) (eq.mp (Eq._oldrec (Eq.refl (a * 1 ≤ a * a)) (mul_one a)) (nat.mul_le_mul_left a (le_of_lt a1)))

theorem dz_val {a : ℕ} (a1 : 1 < a) : ↑(d a1) = az a1 * az a1 - 1 := sorry

@[simp] theorem xz_succ {a : ℕ} (a1 : 1 < a) (n : ℕ) : xz a1 (n + 1) = xz a1 n * az a1 + ↑(d a1) * yz a1 n :=
  rfl

@[simp] theorem yz_succ {a : ℕ} (a1 : 1 < a) (n : ℕ) : yz a1 (n + 1) = xz a1 n + yz a1 n * az a1 :=
  rfl

def pell_zd {a : ℕ} (a1 : 1 < a) (n : ℕ) : ℤ√↑(d a1) :=
  zsqrtd.mk ↑(xn a1 n) ↑(yn a1 n)

@[simp] theorem pell_zd_re {a : ℕ} (a1 : 1 < a) (n : ℕ) : zsqrtd.re (pell_zd a1 n) = ↑(xn a1 n) :=
  rfl

@[simp] theorem pell_zd_im {a : ℕ} (a1 : 1 < a) (n : ℕ) : zsqrtd.im (pell_zd a1 n) = ↑(yn a1 n) :=
  rfl

def is_pell {a : ℕ} (a1 : 1 < a) : ℤ√↑(d a1) → Prop :=
  sorry

theorem is_pell_nat {a : ℕ} (a1 : 1 < a) {x : ℕ} {y : ℕ} : is_pell a1 (zsqrtd.mk ↑x ↑y) ↔ x * x - d a1 * y * y = 1 := sorry

theorem is_pell_norm {a : ℕ} (a1 : 1 < a) {b : ℤ√↑(d a1)} : is_pell a1 b ↔ b * zsqrtd.conj b = 1 := sorry

theorem is_pell_mul {a : ℕ} (a1 : 1 < a) {b : ℤ√↑(d a1)} {c : ℤ√↑(d a1)} (hb : is_pell a1 b) (hc : is_pell a1 c) : is_pell a1 (b * c) := sorry

theorem is_pell_conj {a : ℕ} (a1 : 1 < a) {b : ℤ√↑(d a1)} : is_pell a1 b ↔ is_pell a1 (zsqrtd.conj b) := sorry

@[simp] theorem pell_zd_succ {a : ℕ} (a1 : 1 < a) (n : ℕ) : pell_zd a1 (n + 1) = pell_zd a1 n * zsqrtd.mk (↑a) 1 := sorry

theorem is_pell_one {a : ℕ} (a1 : 1 < a) : is_pell a1 (zsqrtd.mk (↑a) 1) := sorry

theorem is_pell_pell_zd {a : ℕ} (a1 : 1 < a) (n : ℕ) : is_pell a1 (pell_zd a1 n) := sorry

@[simp] theorem pell_eqz {a : ℕ} (a1 : 1 < a) (n : ℕ) : xz a1 n * xz a1 n - ↑(d a1) * yz a1 n * yz a1 n = 1 :=
  is_pell_pell_zd a1 n

@[simp] theorem pell_eq {a : ℕ} (a1 : 1 < a) (n : ℕ) : xn a1 n * xn a1 n - d a1 * yn a1 n * yn a1 n = 1 := sorry

protected instance dnsq {a : ℕ} (a1 : 1 < a) : zsqrtd.nonsquare (d a1) := sorry

theorem xn_ge_a_pow {a : ℕ} (a1 : 1 < a) (n : ℕ) : a ^ n ≤ xn a1 n := sorry

theorem n_lt_a_pow {a : ℕ} (a1 : 1 < a) (n : ℕ) : n < a ^ n := sorry

theorem n_lt_xn {a : ℕ} (a1 : 1 < a) (n : ℕ) : n < xn a1 n :=
  lt_of_lt_of_le (n_lt_a_pow a1 n) (xn_ge_a_pow a1 n)

theorem x_pos {a : ℕ} (a1 : 1 < a) (n : ℕ) : 0 < xn a1 n :=
  lt_of_le_of_lt (nat.zero_le n) (n_lt_xn a1 n)

theorem eq_pell_lem {a : ℕ} (a1 : 1 < a) (n : ℕ) (b : ℤ√↑(d a1)) : 1 ≤ b → is_pell a1 b → b ≤ pell_zd a1 n → ∃ (n : ℕ), b = pell_zd a1 n := sorry

theorem eq_pell_zd {a : ℕ} (a1 : 1 < a) (b : ℤ√↑(d a1)) (b1 : 1 ≤ b) (hp : is_pell a1 b) : ∃ (n : ℕ), b = pell_zd a1 n := sorry

theorem eq_pell {a : ℕ} (a1 : 1 < a) {x : ℕ} {y : ℕ} (hp : x * x - d a1 * y * y = 1) : ∃ (n : ℕ), x = xn a1 n ∧ y = yn a1 n := sorry

theorem pell_zd_add {a : ℕ} (a1 : 1 < a) (m : ℕ) (n : ℕ) : pell_zd a1 (m + n) = pell_zd a1 m * pell_zd a1 n := sorry

theorem xn_add {a : ℕ} (a1 : 1 < a) (m : ℕ) (n : ℕ) : xn a1 (m + n) = xn a1 m * xn a1 n + d a1 * yn a1 m * yn a1 n := sorry

theorem yn_add {a : ℕ} (a1 : 1 < a) (m : ℕ) (n : ℕ) : yn a1 (m + n) = xn a1 m * yn a1 n + yn a1 m * xn a1 n := sorry

theorem pell_zd_sub {a : ℕ} (a1 : 1 < a) {m : ℕ} {n : ℕ} (h : n ≤ m) : pell_zd a1 (m - n) = pell_zd a1 m * zsqrtd.conj (pell_zd a1 n) := sorry

theorem xz_sub {a : ℕ} (a1 : 1 < a) {m : ℕ} {n : ℕ} (h : n ≤ m) : xz a1 (m - n) = xz a1 m * xz a1 n - ↑(d a1) * yz a1 m * yz a1 n := sorry

theorem yz_sub {a : ℕ} (a1 : 1 < a) {m : ℕ} {n : ℕ} (h : n ≤ m) : yz a1 (m - n) = xz a1 n * yz a1 m - xz a1 m * yz a1 n := sorry

theorem xy_coprime {a : ℕ} (a1 : 1 < a) (n : ℕ) : nat.coprime (xn a1 n) (yn a1 n) := sorry

theorem y_increasing {a : ℕ} (a1 : 1 < a) {m : ℕ} {n : ℕ} : m < n → yn a1 m < yn a1 n := sorry

theorem x_increasing {a : ℕ} (a1 : 1 < a) {m : ℕ} {n : ℕ} : m < n → xn a1 m < xn a1 n := sorry

theorem yn_ge_n {a : ℕ} (a1 : 1 < a) (n : ℕ) : n ≤ yn a1 n := sorry

theorem y_mul_dvd {a : ℕ} (a1 : 1 < a) (n : ℕ) (k : ℕ) : yn a1 n ∣ yn a1 (n * k) := sorry

theorem y_dvd_iff {a : ℕ} (a1 : 1 < a) (m : ℕ) (n : ℕ) : yn a1 m ∣ yn a1 n ↔ m ∣ n := sorry

theorem xy_modeq_yn {a : ℕ} (a1 : 1 < a) (n : ℕ) (k : ℕ) : nat.modeq (yn a1 n ^ bit0 1) (xn a1 (n * k)) (xn a1 n ^ k) ∧
  nat.modeq (yn a1 n ^ bit1 1) (yn a1 (n * k)) (k * xn a1 n ^ (k - 1) * yn a1 n) := sorry

theorem ysq_dvd_yy {a : ℕ} (a1 : 1 < a) (n : ℕ) : yn a1 n * yn a1 n ∣ yn a1 (n * yn a1 n) := sorry

theorem dvd_of_ysq_dvd {a : ℕ} (a1 : 1 < a) {n : ℕ} {t : ℕ} (h : yn a1 n * yn a1 n ∣ yn a1 t) : yn a1 n ∣ t := sorry

theorem pell_zd_succ_succ {a : ℕ} (a1 : 1 < a) (n : ℕ) : pell_zd a1 (n + bit0 1) + pell_zd a1 n = ↑(bit0 1 * a) * pell_zd a1 (n + 1) := sorry

theorem xy_succ_succ {a : ℕ} (a1 : 1 < a) (n : ℕ) : xn a1 (n + bit0 1) + xn a1 n = bit0 1 * a * xn a1 (n + 1) ∧ yn a1 (n + bit0 1) + yn a1 n = bit0 1 * a * yn a1 (n + 1) := sorry

theorem xn_succ_succ {a : ℕ} (a1 : 1 < a) (n : ℕ) : xn a1 (n + bit0 1) + xn a1 n = bit0 1 * a * xn a1 (n + 1) :=
  and.left (xy_succ_succ a1 n)

theorem yn_succ_succ {a : ℕ} (a1 : 1 < a) (n : ℕ) : yn a1 (n + bit0 1) + yn a1 n = bit0 1 * a * yn a1 (n + 1) :=
  and.right (xy_succ_succ a1 n)

theorem xz_succ_succ {a : ℕ} (a1 : 1 < a) (n : ℕ) : xz a1 (n + bit0 1) = ↑(bit0 1 * a) * xz a1 (n + 1) - xz a1 n := sorry

theorem yz_succ_succ {a : ℕ} (a1 : 1 < a) (n : ℕ) : yz a1 (n + bit0 1) = ↑(bit0 1 * a) * yz a1 (n + 1) - yz a1 n := sorry

theorem yn_modeq_a_sub_one {a : ℕ} (a1 : 1 < a) (n : ℕ) : nat.modeq (a - 1) (yn a1 n) n := sorry

theorem yn_modeq_two {a : ℕ} (a1 : 1 < a) (n : ℕ) : nat.modeq (bit0 1) (yn a1 n) n := sorry

theorem x_sub_y_dvd_pow_lem {a : ℕ} (a1 : 1 < a) (y2 : ℤ) (y1 : ℤ) (y0 : ℤ) (yn1 : ℤ) (yn0 : ℤ) (xn1 : ℤ) (xn0 : ℤ) (ay : ℤ) (a2 : ℤ) : (a2 * yn1 - yn0) * ay + y2 - (a2 * xn1 - xn0) = y2 - a2 * y1 + y0 + a2 * (yn1 * ay + y1 - xn1) - (yn0 * ay + y0 - xn0) := sorry

theorem x_sub_y_dvd_pow {a : ℕ} (a1 : 1 < a) (y : ℕ) (n : ℕ) : bit0 1 * ↑a * ↑y - ↑y * ↑y - 1 ∣ yz a1 n * (↑a - ↑y) + ↑(y ^ n) - xz a1 n := sorry

theorem xn_modeq_x2n_add_lem {a : ℕ} (a1 : 1 < a) (n : ℕ) (j : ℕ) : xn a1 n ∣ d a1 * yn a1 n * (yn a1 n * xn a1 j) + xn a1 j := sorry

theorem xn_modeq_x2n_add {a : ℕ} (a1 : 1 < a) (n : ℕ) (j : ℕ) : nat.modeq (xn a1 n) (xn a1 (bit0 1 * n + j) + xn a1 j) 0 := sorry

theorem xn_modeq_x2n_sub_lem {a : ℕ} (a1 : 1 < a) {n : ℕ} {j : ℕ} (h : j ≤ n) : nat.modeq (xn a1 n) (xn a1 (bit0 1 * n - j) + xn a1 j) 0 := sorry

theorem xn_modeq_x2n_sub {a : ℕ} (a1 : 1 < a) {n : ℕ} {j : ℕ} (h : j ≤ bit0 1 * n) : nat.modeq (xn a1 n) (xn a1 (bit0 1 * n - j) + xn a1 j) 0 := sorry

theorem xn_modeq_x4n_add {a : ℕ} (a1 : 1 < a) (n : ℕ) (j : ℕ) : nat.modeq (xn a1 n) (xn a1 (bit0 (bit0 1) * n + j)) (xn a1 j) := sorry

theorem xn_modeq_x4n_sub {a : ℕ} (a1 : 1 < a) {n : ℕ} {j : ℕ} (h : j ≤ bit0 1 * n) : nat.modeq (xn a1 n) (xn a1 (bit0 (bit0 1) * n - j)) (xn a1 j) := sorry

theorem eq_of_xn_modeq_lem1 {a : ℕ} (a1 : 1 < a) {i : ℕ} {n : ℕ} {j : ℕ} : i < j → j < n → xn a1 i % xn a1 n < xn a1 j % xn a1 n := sorry

theorem eq_of_xn_modeq_lem2 {a : ℕ} (a1 : 1 < a) {n : ℕ} (h : bit0 1 * xn a1 n = xn a1 (n + 1)) : a = bit0 1 ∧ n = 0 := sorry

theorem eq_of_xn_modeq_lem3 {a : ℕ} (a1 : 1 < a) {i : ℕ} {n : ℕ} (npos : 0 < n) {j : ℕ} : i < j → j ≤ bit0 1 * n → j ≠ n → ¬(a = bit0 1 ∧ n = 1 ∧ i = 0 ∧ j = bit0 1) → xn a1 i % xn a1 n < xn a1 j % xn a1 n := sorry

theorem eq_of_xn_modeq_le {a : ℕ} (a1 : 1 < a) {i : ℕ} {j : ℕ} {n : ℕ} (npos : 0 < n) (ij : i ≤ j) (j2n : j ≤ bit0 1 * n) (h : nat.modeq (xn a1 n) (xn a1 i) (xn a1 j)) (ntriv : ¬(a = bit0 1 ∧ n = 1 ∧ i = 0 ∧ j = bit0 1)) : i = j := sorry

theorem eq_of_xn_modeq {a : ℕ} (a1 : 1 < a) {i : ℕ} {j : ℕ} {n : ℕ} (npos : 0 < n) (i2n : i ≤ bit0 1 * n) (j2n : j ≤ bit0 1 * n) (h : nat.modeq (xn a1 n) (xn a1 i) (xn a1 j)) (ntriv : a = bit0 1 → n = 1 → (i = 0 → j ≠ bit0 1) ∧ (i = bit0 1 → j ≠ 0)) : i = j := sorry

theorem eq_of_xn_modeq' {a : ℕ} (a1 : 1 < a) {i : ℕ} {j : ℕ} {n : ℕ} (ipos : 0 < i) (hin : i ≤ n) (j4n : j ≤ bit0 (bit0 1) * n) (h : nat.modeq (xn a1 n) (xn a1 j) (xn a1 i)) : j = i ∨ j + i = bit0 (bit0 1) * n := sorry

theorem modeq_of_xn_modeq {a : ℕ} (a1 : 1 < a) {i : ℕ} {j : ℕ} {n : ℕ} (ipos : 0 < i) (hin : i ≤ n) (h : nat.modeq (xn a1 n) (xn a1 j) (xn a1 i)) : nat.modeq (bit0 (bit0 1) * n) j i ∨ nat.modeq (bit0 (bit0 1) * n) (j + i) 0 := sorry

theorem xy_modeq_of_modeq {a : ℕ} {b : ℕ} {c : ℕ} (a1 : 1 < a) (b1 : 1 < b) (h : nat.modeq c a b) (n : ℕ) : nat.modeq c (xn a1 n) (xn b1 n) ∧ nat.modeq c (yn a1 n) (yn b1 n) := sorry

theorem matiyasevic {a : ℕ} {k : ℕ} {x : ℕ} {y : ℕ} : (∃ (a1 : 1 < a), xn a1 k = x ∧ yn a1 k = y) ↔
  1 < a ∧
    k ≤ y ∧
      (x = 1 ∧ y = 0 ∨
        ∃ (u : ℕ),
          ∃ (v : ℕ),
            ∃ (s : ℕ),
              ∃ (t : ℕ),
                ∃ (b : ℕ),
                  x * x - (a * a - 1) * y * y = 1 ∧
                    u * u - (a * a - 1) * v * v = 1 ∧
                      s * s - (b * b - 1) * t * t = 1 ∧
                        1 < b ∧
                          nat.modeq (bit0 (bit0 1) * y) b 1 ∧
                            nat.modeq u b a ∧ 0 < v ∧ y * y ∣ v ∧ nat.modeq u s x ∧ nat.modeq (bit0 (bit0 1) * y) t k) := sorry

theorem eq_pow_of_pell_lem {a : ℕ} {y : ℕ} {k : ℕ} (a1 : 1 < a) (ypos : 0 < y) : 0 < k → y ^ k < a → ↑(y ^ k) < bit0 1 * ↑a * ↑y - ↑y * ↑y - 1 := sorry

theorem eq_pow_of_pell {m : ℕ} {n : ℕ} {k : ℕ} : n ^ k = m ↔
  k = 0 ∧ m = 1 ∨
    0 < k ∧
      (n = 0 ∧ m = 0 ∨
        0 < n ∧
          ∃ (w : ℕ),
            ∃ (a : ℕ),
              ∃ (t : ℕ),
                ∃ (z : ℕ),
                  ∃ (a1 : 1 < a),
                    nat.modeq t (xn a1 k) (yn a1 k * (a - n) + m) ∧
                      bit0 1 * a * n = t + (n * n + 1) ∧
                        m < t ∧ n ≤ w ∧ k ≤ w ∧ a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1) := sorry

