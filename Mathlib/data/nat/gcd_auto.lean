/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# Definitions and properties of `gcd`, `lcm`, and `coprime`

-/

namespace nat


/-! ### `gcd` -/

theorem gcd_dvd (m : ℕ) (n : ℕ) : gcd m n ∣ m ∧ gcd m n ∣ n := sorry

theorem gcd_dvd_left (m : ℕ) (n : ℕ) : gcd m n ∣ m := and.left (gcd_dvd m n)

theorem gcd_dvd_right (m : ℕ) (n : ℕ) : gcd m n ∣ n := and.right (gcd_dvd m n)

theorem gcd_le_left {m : ℕ} (n : ℕ) (h : 0 < m) : gcd m n ≤ m := le_of_dvd h (gcd_dvd_left m n)

theorem gcd_le_right (m : ℕ) {n : ℕ} (h : 0 < n) : gcd m n ≤ n := le_of_dvd h (gcd_dvd_right m n)

theorem dvd_gcd {m : ℕ} {n : ℕ} {k : ℕ} : k ∣ m → k ∣ n → k ∣ gcd m n := sorry

theorem dvd_gcd_iff {m : ℕ} {n : ℕ} {k : ℕ} : k ∣ gcd m n ↔ k ∣ m ∧ k ∣ n := sorry

theorem gcd_comm (m : ℕ) (n : ℕ) : gcd m n = gcd n m :=
  dvd_antisymm (dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n))
    (dvd_gcd (gcd_dvd_right n m) (gcd_dvd_left n m))

theorem gcd_eq_left_iff_dvd {m : ℕ} {n : ℕ} : m ∣ n ↔ gcd m n = m := sorry

theorem gcd_eq_right_iff_dvd {m : ℕ} {n : ℕ} : m ∣ n ↔ gcd n m = m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m ∣ n ↔ gcd n m = m)) (gcd_comm n m))) gcd_eq_left_iff_dvd

theorem gcd_assoc (m : ℕ) (n : ℕ) (k : ℕ) : gcd (gcd m n) k = gcd m (gcd n k) := sorry

@[simp] theorem gcd_one_right (n : ℕ) : gcd n 1 = 1 := Eq.trans (gcd_comm n 1) (gcd_one_left n)

theorem gcd_mul_left (m : ℕ) (n : ℕ) (k : ℕ) : gcd (m * n) (m * k) = m * gcd n k := sorry

theorem gcd_mul_right (m : ℕ) (n : ℕ) (k : ℕ) : gcd (m * n) (k * n) = gcd m k * n := sorry

theorem gcd_pos_of_pos_left {m : ℕ} (n : ℕ) (mpos : 0 < m) : 0 < gcd m n :=
  pos_of_dvd_of_pos (gcd_dvd_left m n) mpos

theorem gcd_pos_of_pos_right (m : ℕ) {n : ℕ} (npos : 0 < n) : 0 < gcd m n :=
  pos_of_dvd_of_pos (gcd_dvd_right m n) npos

theorem eq_zero_of_gcd_eq_zero_left {m : ℕ} {n : ℕ} (H : gcd m n = 0) : m = 0 :=
  or.elim (eq_zero_or_pos m) id
    fun (H1 : 0 < m) => absurd (Eq.symm H) (ne_of_lt (gcd_pos_of_pos_left n H1))

theorem eq_zero_of_gcd_eq_zero_right {m : ℕ} {n : ℕ} (H : gcd m n = 0) : n = 0 :=
  eq_zero_of_gcd_eq_zero_left (eq.mp (Eq._oldrec (Eq.refl (gcd m n = 0)) (gcd_comm m n)) H)

theorem gcd_div {m : ℕ} {n : ℕ} {k : ℕ} (H1 : k ∣ m) (H2 : k ∣ n) :
    gcd (m / k) (n / k) = gcd m n / k :=
  sorry

theorem gcd_dvd_gcd_of_dvd_left {m : ℕ} {k : ℕ} (n : ℕ) (H : m ∣ k) : gcd m n ∣ gcd k n :=
  dvd_gcd (dvd.trans (gcd_dvd_left m n) H) (gcd_dvd_right m n)

theorem gcd_dvd_gcd_of_dvd_right {m : ℕ} {k : ℕ} (n : ℕ) (H : m ∣ k) : gcd n m ∣ gcd n k :=
  dvd_gcd (gcd_dvd_left n m) (dvd.trans (gcd_dvd_right n m) H)

theorem gcd_dvd_gcd_mul_left (m : ℕ) (n : ℕ) (k : ℕ) : gcd m n ∣ gcd (k * m) n :=
  gcd_dvd_gcd_of_dvd_left n (dvd_mul_left m k)

theorem gcd_dvd_gcd_mul_right (m : ℕ) (n : ℕ) (k : ℕ) : gcd m n ∣ gcd (m * k) n :=
  gcd_dvd_gcd_of_dvd_left n (dvd_mul_right m k)

theorem gcd_dvd_gcd_mul_left_right (m : ℕ) (n : ℕ) (k : ℕ) : gcd m n ∣ gcd m (k * n) :=
  gcd_dvd_gcd_of_dvd_right m (dvd_mul_left n k)

theorem gcd_dvd_gcd_mul_right_right (m : ℕ) (n : ℕ) (k : ℕ) : gcd m n ∣ gcd m (n * k) :=
  gcd_dvd_gcd_of_dvd_right m (dvd_mul_right n k)

theorem gcd_eq_left {m : ℕ} {n : ℕ} (H : m ∣ n) : gcd m n = m :=
  dvd_antisymm (gcd_dvd_left m n) (dvd_gcd (dvd_refl m) H)

theorem gcd_eq_right {m : ℕ} {n : ℕ} (H : n ∣ m) : gcd m n = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd m n = n)) (gcd_comm m n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd n m = n)) (gcd_eq_left H))) (Eq.refl n))

@[simp] theorem gcd_mul_left_left (m : ℕ) (n : ℕ) : gcd (m * n) n = n :=
  dvd_antisymm (gcd_dvd_right (m * n) n) (dvd_gcd (dvd_mul_left n m) (dvd_refl n))

@[simp] theorem gcd_mul_left_right (m : ℕ) (n : ℕ) : gcd n (m * n) = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd n (m * n) = n)) (gcd_comm n (m * n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd (m * n) n = n)) (gcd_mul_left_left m n))) (Eq.refl n))

@[simp] theorem gcd_mul_right_left (m : ℕ) (n : ℕ) : gcd (n * m) n = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd (n * m) n = n)) (mul_comm n m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd (m * n) n = n)) (gcd_mul_left_left m n))) (Eq.refl n))

@[simp] theorem gcd_mul_right_right (m : ℕ) (n : ℕ) : gcd n (n * m) = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd n (n * m) = n)) (gcd_comm n (n * m))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd (n * m) n = n)) (gcd_mul_right_left m n))) (Eq.refl n))

@[simp] theorem gcd_gcd_self_right_left (m : ℕ) (n : ℕ) : gcd m (gcd m n) = gcd m n :=
  dvd_antisymm (gcd_dvd_right m (gcd m n)) (dvd_gcd (gcd_dvd_left m n) (dvd_refl (gcd m n)))

@[simp] theorem gcd_gcd_self_right_right (m : ℕ) (n : ℕ) : gcd m (gcd n m) = gcd n m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd m (gcd n m) = gcd n m)) (gcd_comm n m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd m (gcd m n) = gcd m n)) (gcd_gcd_self_right_left m n)))
      (Eq.refl (gcd m n)))

@[simp] theorem gcd_gcd_self_left_right (m : ℕ) (n : ℕ) : gcd (gcd n m) m = gcd n m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd (gcd n m) m = gcd n m)) (gcd_comm (gcd n m) m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd m (gcd n m) = gcd n m)) (gcd_gcd_self_right_right m n)))
      (Eq.refl (gcd n m)))

@[simp] theorem gcd_gcd_self_left_left (m : ℕ) (n : ℕ) : gcd (gcd m n) m = gcd m n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd (gcd m n) m = gcd m n)) (gcd_comm m n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd (gcd n m) m = gcd n m)) (gcd_gcd_self_left_right m n)))
      (Eq.refl (gcd n m)))

theorem gcd_add_mul_self (m : ℕ) (n : ℕ) (k : ℕ) : gcd m (n + k * m) = gcd m n := sorry

theorem gcd_eq_zero_iff {i : ℕ} {j : ℕ} : gcd i j = 0 ↔ i = 0 ∧ j = 0 := sorry

/-! ### `lcm` -/

theorem lcm_comm (m : ℕ) (n : ℕ) : lcm m n = lcm n m :=
  id
    (eq.mpr (id (Eq._oldrec (Eq.refl (m * n / gcd m n = n * m / gcd n m)) (mul_comm m n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (n * m / gcd m n = n * m / gcd n m)) (gcd_comm m n)))
        (Eq.refl (n * m / gcd n m))))

@[simp] theorem lcm_zero_left (m : ℕ) : lcm 0 m = 0 :=
  id
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 * m / gcd 0 m = 0)) (zero_mul m)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 / gcd 0 m = 0)) (nat.zero_div (gcd 0 m)))) (Eq.refl 0)))

@[simp] theorem lcm_zero_right (m : ℕ) : lcm m 0 = 0 := lcm_comm 0 m ▸ lcm_zero_left m

@[simp] theorem lcm_one_left (m : ℕ) : lcm 1 m = m := sorry

@[simp] theorem lcm_one_right (m : ℕ) : lcm m 1 = m := lcm_comm 1 m ▸ lcm_one_left m

@[simp] theorem lcm_self (m : ℕ) : lcm m m = m := sorry

theorem dvd_lcm_left (m : ℕ) (n : ℕ) : m ∣ lcm m n :=
  dvd.intro (n / gcd m n) (Eq.symm (nat.mul_div_assoc m (gcd_dvd_right m n)))

theorem dvd_lcm_right (m : ℕ) (n : ℕ) : n ∣ lcm m n := lcm_comm n m ▸ dvd_lcm_left n m

theorem gcd_mul_lcm (m : ℕ) (n : ℕ) : gcd m n * lcm m n = m * n := sorry

theorem lcm_dvd {m : ℕ} {n : ℕ} {k : ℕ} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k := sorry

theorem lcm_assoc (m : ℕ) (n : ℕ) (k : ℕ) : lcm (lcm m n) k = lcm m (lcm n k) := sorry

theorem lcm_ne_zero {m : ℕ} {n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 := sorry

/-!
### `coprime`

See also `nat.coprime_of_dvd` and `nat.coprime_of_dvd'` to prove `nat.coprime m n`.
-/

protected instance coprime.decidable (m : ℕ) (n : ℕ) : Decidable (coprime m n) :=
  eq.mpr sorry (nat.decidable_eq (gcd m n) 1)

theorem coprime.gcd_eq_one {m : ℕ} {n : ℕ} : coprime m n → gcd m n = 1 := id

theorem coprime.symm {m : ℕ} {n : ℕ} : coprime n m → coprime m n := Eq.trans (gcd_comm m n)

theorem coprime.dvd_of_dvd_mul_right {m : ℕ} {n : ℕ} {k : ℕ} (H1 : coprime k n) (H2 : k ∣ m * n) :
    k ∣ m :=
  sorry

theorem coprime.dvd_of_dvd_mul_left {m : ℕ} {n : ℕ} {k : ℕ} (H1 : coprime k m) (H2 : k ∣ m * n) :
    k ∣ n :=
  coprime.dvd_of_dvd_mul_right H1 (eq.mp (Eq._oldrec (Eq.refl (k ∣ m * n)) (mul_comm m n)) H2)

theorem coprime.gcd_mul_left_cancel {k : ℕ} (m : ℕ) {n : ℕ} (H : coprime k n) :
    gcd (k * m) n = gcd m n :=
  sorry

theorem coprime.gcd_mul_right_cancel (m : ℕ) {k : ℕ} {n : ℕ} (H : coprime k n) :
    gcd (m * k) n = gcd m n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd (m * k) n = gcd m n)) (mul_comm m k)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd (k * m) n = gcd m n)) (coprime.gcd_mul_left_cancel m H)))
      (Eq.refl (gcd m n)))

theorem coprime.gcd_mul_left_cancel_right {k : ℕ} {m : ℕ} (n : ℕ) (H : coprime k m) :
    gcd m (k * n) = gcd m n :=
  sorry

theorem coprime.gcd_mul_right_cancel_right {k : ℕ} {m : ℕ} (n : ℕ) (H : coprime k m) :
    gcd m (n * k) = gcd m n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd m (n * k) = gcd m n)) (mul_comm n k)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (gcd m (k * n) = gcd m n)) (coprime.gcd_mul_left_cancel_right n H)))
      (Eq.refl (gcd m n)))

theorem coprime_div_gcd_div_gcd {m : ℕ} {n : ℕ} (H : 0 < gcd m n) :
    coprime (m / gcd m n) (n / gcd m n) :=
  sorry

theorem not_coprime_of_dvd_of_dvd {m : ℕ} {n : ℕ} {d : ℕ} (dgt1 : 1 < d) (Hm : d ∣ m) (Hn : d ∣ n) :
    ¬coprime m n :=
  fun (co : gcd m n = 1) =>
    not_lt_of_ge
      (le_of_dvd zero_lt_one
        (eq.mpr (id (Eq._oldrec (Eq.refl (d ∣ 1)) (Eq.symm co))) (dvd_gcd Hm Hn)))
      dgt1

theorem exists_coprime {m : ℕ} {n : ℕ} (H : 0 < gcd m n) :
    ∃ (m' : ℕ), ∃ (n' : ℕ), coprime m' n' ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
  sorry

theorem exists_coprime' {m : ℕ} {n : ℕ} (H : 0 < gcd m n) :
    ∃ (g : ℕ), ∃ (m' : ℕ), ∃ (n' : ℕ), 0 < g ∧ coprime m' n' ∧ m = m' * g ∧ n = n' * g :=
  sorry

theorem coprime.mul {m : ℕ} {n : ℕ} {k : ℕ} (H1 : coprime m k) (H2 : coprime n k) :
    coprime (m * n) k :=
  Eq.trans (coprime.gcd_mul_left_cancel n H1) H2

theorem coprime.mul_right {k : ℕ} {m : ℕ} {n : ℕ} (H1 : coprime k m) (H2 : coprime k n) :
    coprime k (m * n) :=
  coprime.symm (coprime.mul (coprime.symm H1) (coprime.symm H2))

theorem coprime.coprime_dvd_left {m : ℕ} {k : ℕ} {n : ℕ} (H1 : m ∣ k) (H2 : coprime k n) :
    coprime m n :=
  sorry

theorem coprime.coprime_dvd_right {m : ℕ} {k : ℕ} {n : ℕ} (H1 : n ∣ m) (H2 : coprime k m) :
    coprime k n :=
  coprime.symm (coprime.coprime_dvd_left H1 (coprime.symm H2))

theorem coprime.coprime_mul_left {k : ℕ} {m : ℕ} {n : ℕ} (H : coprime (k * m) n) : coprime m n :=
  coprime.coprime_dvd_left (dvd_mul_left m k) H

theorem coprime.coprime_mul_right {k : ℕ} {m : ℕ} {n : ℕ} (H : coprime (m * k) n) : coprime m n :=
  coprime.coprime_dvd_left (dvd_mul_right m k) H

theorem coprime.coprime_mul_left_right {k : ℕ} {m : ℕ} {n : ℕ} (H : coprime m (k * n)) :
    coprime m n :=
  coprime.coprime_dvd_right (dvd_mul_left n k) H

theorem coprime.coprime_mul_right_right {k : ℕ} {m : ℕ} {n : ℕ} (H : coprime m (n * k)) :
    coprime m n :=
  coprime.coprime_dvd_right (dvd_mul_right n k) H

theorem coprime.coprime_div_left {m : ℕ} {n : ℕ} {a : ℕ} (cmn : coprime m n) (dvd : a ∣ m) :
    coprime (m / a) n :=
  sorry

theorem coprime.coprime_div_right {m : ℕ} {n : ℕ} {a : ℕ} (cmn : coprime m n) (dvd : a ∣ n) :
    coprime m (n / a) :=
  coprime.symm (coprime.coprime_div_left (coprime.symm cmn) dvd)

theorem coprime_mul_iff_left {k : ℕ} {m : ℕ} {n : ℕ} :
    coprime (m * n) k ↔ coprime m k ∧ coprime n k :=
  sorry

theorem coprime_mul_iff_right {k : ℕ} {m : ℕ} {n : ℕ} :
    coprime k (m * n) ↔ coprime k m ∧ coprime k n :=
  sorry

theorem coprime.gcd_left (k : ℕ) {m : ℕ} {n : ℕ} (hmn : coprime m n) : coprime (gcd k m) n :=
  coprime.coprime_dvd_left (gcd_dvd_right k m) hmn

theorem coprime.gcd_right (k : ℕ) {m : ℕ} {n : ℕ} (hmn : coprime m n) : coprime m (gcd k n) :=
  coprime.coprime_dvd_right (gcd_dvd_right k n) hmn

theorem coprime.gcd_both (k : ℕ) (l : ℕ) {m : ℕ} {n : ℕ} (hmn : coprime m n) :
    coprime (gcd k m) (gcd l n) :=
  coprime.gcd_right l (coprime.gcd_left k hmn)

theorem coprime.mul_dvd_of_dvd_of_dvd {a : ℕ} {n : ℕ} {m : ℕ} (hmn : coprime m n) (hm : m ∣ a)
    (hn : n ∣ a) : m * n ∣ a :=
  sorry

theorem coprime_one_left (n : ℕ) : coprime 1 n := gcd_one_left

theorem coprime_one_right (n : ℕ) : coprime n 1 := gcd_one_right

theorem coprime.pow_left {m : ℕ} {k : ℕ} (n : ℕ) (H1 : coprime m k) : coprime (m ^ n) k :=
  nat.rec_on n (coprime_one_left k) fun (n : ℕ) (IH : coprime (m ^ n) k) => coprime.mul H1 IH

theorem coprime.pow_right {m : ℕ} {k : ℕ} (n : ℕ) (H1 : coprime k m) : coprime k (m ^ n) :=
  coprime.symm (coprime.pow_left n (coprime.symm H1))

theorem coprime.pow {k : ℕ} {l : ℕ} (m : ℕ) (n : ℕ) (H1 : coprime k l) : coprime (k ^ m) (l ^ n) :=
  coprime.pow_right n (coprime.pow_left m H1)

theorem coprime.eq_one_of_dvd {k : ℕ} {m : ℕ} (H : coprime k m) (d : k ∣ m) : k = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (k = 1)) (Eq.symm (coprime.gcd_eq_one H))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (k = gcd k m)) (gcd_eq_left d))) (Eq.refl k))

@[simp] theorem coprime_zero_left (n : ℕ) : coprime 0 n ↔ n = 1 := sorry

@[simp] theorem coprime_zero_right (n : ℕ) : coprime n 0 ↔ n = 1 := sorry

@[simp] theorem coprime_one_left_iff (n : ℕ) : coprime 1 n ↔ True := sorry

@[simp] theorem coprime_one_right_iff (n : ℕ) : coprime n 1 ↔ True := sorry

@[simp] theorem coprime_self (n : ℕ) : coprime n n ↔ n = 1 := sorry

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`. -/
def prod_dvd_and_dvd_of_dvd_prod {m : ℕ} {n : ℕ} {k : ℕ} (H : k ∣ m * n) :
    Subtype
        fun (d : (Subtype fun (m' : ℕ) => m' ∣ m) × Subtype fun (n' : ℕ) => n' ∣ n) =>
          k = ↑(prod.fst d) * ↑(prod.snd d) :=
  (fun (_x : ℕ) (h0 : gcd k m = _x) =>
      nat.cases_on _x
        (fun (h0 : gcd k m = 0) =>
          Eq._oldrec
            (fun (H : 0 ∣ m * n) (h0 : gcd 0 m = 0) =>
              Eq._oldrec
                (fun (H : 0 ∣ 0 * n) (h0 : gcd 0 0 = 0) =>
                  { val := ({ val := 0, property := sorry }, { val := n, property := dvd_refl n }),
                    property := sorry })
                sorry H h0)
            sorry H h0)
        (fun (n_1 : ℕ) (h0 : gcd k m = Nat.succ n_1) =>
          (fun (h0 : gcd k m = Nat.succ n_1) =>
              { val :=
                  ({ val := gcd k m, property := gcd_dvd_right k m },
                  { val := k / gcd k m, property := sorry }),
                property := sorry })
            h0)
        h0)
    (gcd k m) sorry

theorem gcd_mul_dvd_mul_gcd (k : ℕ) (m : ℕ) (n : ℕ) : gcd k (m * n) ∣ gcd k m * gcd k n := sorry

theorem coprime.gcd_mul (k : ℕ) {m : ℕ} {n : ℕ} (h : coprime m n) :
    gcd k (m * n) = gcd k m * gcd k n :=
  dvd_antisymm (gcd_mul_dvd_mul_gcd k m n)
    (coprime.mul_dvd_of_dvd_of_dvd (coprime.gcd_both k k h) (gcd_dvd_gcd_mul_right_right k m n)
      (gcd_dvd_gcd_mul_left_right k n m))

theorem pow_dvd_pow_iff {a : ℕ} {b : ℕ} {n : ℕ} (n0 : 0 < n) : a ^ n ∣ b ^ n ↔ a ∣ b := sorry

theorem gcd_mul_gcd_of_coprime_of_mul_eq_mul {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (cop : coprime c d)
    (h : a * b = c * d) : gcd a c * gcd b c = c :=
  sorry

end Mathlib