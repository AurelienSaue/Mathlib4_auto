/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.int.gcd
import Mathlib.tactic.abel
import Mathlib.data.list.rotate
import PostPort

universes u_1 

namespace Mathlib

/-
# Congruences modulo a natural number

This file defines the equivalence relation `a ≡ b [MOD n]` on the natural numbers,
and proves basic properties about it such as the Chinese Remainder Theorem
`modeq_and_modeq_iff_modeq_mul`.

## Notations

`a ≡ b [MOD n]` is notation for `modeq n a b`, which is defined to mean `a % n = b % n`.

## Tags

modeq, congruence, mod, MOD, modulo
-/

namespace nat


/-- Modular equality. `modeq n a b`, or `a ≡ b [MOD n]`, means
  that `a - b` is a multiple of `n`. -/
def modeq (n : ℕ) (a : ℕ) (b : ℕ)  :=
  a % n = b % n

namespace modeq


protected theorem refl {n : ℕ} (a : ℕ) : modeq n a a :=
  rfl

protected theorem symm {n : ℕ} {a : ℕ} {b : ℕ} : modeq n a b → modeq n b a :=
  Eq.symm

protected theorem trans {n : ℕ} {a : ℕ} {b : ℕ} {c : ℕ} : modeq n a b → modeq n b c → modeq n a c :=
  Eq.trans

protected theorem comm {n : ℕ} {a : ℕ} {b : ℕ} : modeq n a b ↔ modeq n b a :=
  { mp := modeq.symm, mpr := modeq.symm }

theorem modeq_zero_iff {n : ℕ} {a : ℕ} : modeq n a 0 ↔ n ∣ a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (modeq n a 0 ↔ n ∣ a)) (equations._eqn_1 n a 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a % n = 0 % n ↔ n ∣ a)) (zero_mod n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a % n = 0 ↔ n ∣ a)) (propext (dvd_iff_mod_eq_zero n a)))) (iff.refl (a % n = 0))))

theorem modeq_iff_dvd {n : ℕ} {a : ℕ} {b : ℕ} : modeq n a b ↔ ↑n ∣ ↑b - ↑a := sorry

theorem modeq_of_dvd {n : ℕ} {a : ℕ} {b : ℕ} : ↑n ∣ ↑b - ↑a → modeq n a b :=
  iff.mpr modeq_iff_dvd

theorem dvd_of_modeq {n : ℕ} {a : ℕ} {b : ℕ} : modeq n a b → ↑n ∣ ↑b - ↑a :=
  iff.mp modeq_iff_dvd

/-- A variant of `modeq_iff_dvd` with `nat` divisibility -/
theorem modeq_iff_dvd' {n : ℕ} {a : ℕ} {b : ℕ} (h : a ≤ b) : modeq n a b ↔ n ∣ b - a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (modeq n a b ↔ n ∣ b - a)) (propext modeq_iff_dvd)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n ∣ ↑b - ↑a ↔ n ∣ b - a)) (Eq.symm (propext int.coe_nat_dvd))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑n ∣ ↑b - ↑a ↔ ↑n ∣ ↑(b - a))) (int.coe_nat_sub h))) (iff.refl (↑n ∣ ↑b - ↑a))))

theorem mod_modeq (a : ℕ) (n : ℕ) : modeq n (a % n) a :=
  mod_mod a n

theorem modeq_of_dvd_of_modeq {n : ℕ} {m : ℕ} {a : ℕ} {b : ℕ} (d : m ∣ n) (h : modeq n a b) : modeq m a b :=
  modeq_of_dvd (dvd_trans (iff.mpr int.coe_nat_dvd d) (dvd_of_modeq h))

theorem modeq_mul_left' {n : ℕ} {a : ℕ} {b : ℕ} (c : ℕ) (h : modeq n a b) : modeq (c * n) (c * a) (c * b) := sorry

theorem modeq_mul_left {n : ℕ} {a : ℕ} {b : ℕ} (c : ℕ) (h : modeq n a b) : modeq n (c * a) (c * b) :=
  modeq_of_dvd_of_modeq (dvd_mul_left n c) (modeq_mul_left' c h)

theorem modeq_mul_right' {n : ℕ} {a : ℕ} {b : ℕ} (c : ℕ) (h : modeq n a b) : modeq (n * c) (a * c) (b * c) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (modeq (n * c) (a * c) (b * c))) (mul_comm a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (modeq (n * c) (c * a) (b * c))) (mul_comm b c)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (modeq (n * c) (c * a) (c * b))) (mul_comm n c))) (modeq_mul_left' c h)))

theorem modeq_mul_right {n : ℕ} {a : ℕ} {b : ℕ} (c : ℕ) (h : modeq n a b) : modeq n (a * c) (b * c) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (modeq n (a * c) (b * c))) (mul_comm a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (modeq n (c * a) (b * c))) (mul_comm b c))) (modeq_mul_left c h))

theorem modeq_mul {n : ℕ} {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (h₁ : modeq n a b) (h₂ : modeq n c d) : modeq n (a * c) (b * d) :=
  modeq.trans (modeq_mul_left a h₂) (modeq_mul_right d h₁)

theorem modeq_pow {n : ℕ} {a : ℕ} {b : ℕ} (m : ℕ) (h : modeq n a b) : modeq n (a ^ m) (b ^ m) := sorry

theorem modeq_add {n : ℕ} {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (h₁ : modeq n a b) (h₂ : modeq n c d) : modeq n (a + c) (b + d) := sorry

theorem modeq_add_cancel_left {n : ℕ} {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (h₁ : modeq n a b) (h₂ : modeq n (a + c) (b + d)) : modeq n c d := sorry

theorem modeq_add_cancel_right {n : ℕ} {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (h₁ : modeq n c d) (h₂ : modeq n (a + c) (b + d)) : modeq n a b :=
  modeq_add_cancel_left h₁
    (eq.mp (Eq._oldrec (Eq.refl (modeq n (c + a) (b + d))) (add_comm b d))
      (eq.mp (Eq._oldrec (Eq.refl (modeq n (a + c) (b + d))) (add_comm a c)) h₂))

theorem modeq_of_modeq_mul_left {n : ℕ} {a : ℕ} {b : ℕ} (m : ℕ) (h : modeq (m * n) a b) : modeq n a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (modeq n a b)) (propext modeq_iff_dvd)))
    (dvd.trans (dvd_mul_left ↑n ↑m) (eq.mp (Eq._oldrec (Eq.refl (modeq (m * n) a b)) (propext modeq_iff_dvd)) h))

theorem modeq_of_modeq_mul_right {n : ℕ} {a : ℕ} {b : ℕ} (m : ℕ) : modeq (n * m) a b → modeq n a b :=
  mul_comm m n ▸ modeq_of_modeq_mul_left m

theorem modeq_one {a : ℕ} {b : ℕ} : modeq 1 a b :=
  modeq_of_dvd (one_dvd (↑b - ↑a))

/-- The natural number less than `lcm n m` congruent to `a` mod `n` and `b` mod `m` -/
def chinese_remainder' {n : ℕ} {m : ℕ} {a : ℕ} {b : ℕ} (h : modeq (gcd n m) a b) : Subtype fun (k : ℕ) => modeq n k a ∧ modeq m k b :=
  dite (n = 0) (fun (hn : n = 0) => { val := a, property := sorry })
    fun (hn : ¬n = 0) =>
      dite (m = 0) (fun (hm : m = 0) => { val := b, property := sorry })
        fun (hm : ¬m = 0) => { val := sorry, property := sorry }

/-- The natural number less than `n*m` congruent to `a` mod `n` and `b` mod `m` -/
def chinese_remainder {n : ℕ} {m : ℕ} (co : coprime n m) (a : ℕ) (b : ℕ) : Subtype fun (k : ℕ) => modeq n k a ∧ modeq m k b :=
  chinese_remainder' sorry

theorem modeq_and_modeq_iff_modeq_mul {a : ℕ} {b : ℕ} {m : ℕ} {n : ℕ} (hmn : coprime m n) : modeq m a b ∧ modeq n a b ↔ modeq (m * n) a b := sorry

theorem coprime_of_mul_modeq_one (b : ℕ) {a : ℕ} {n : ℕ} (h : modeq n (a * b) 1) : coprime a n := sorry

end modeq


@[simp] theorem mod_mul_right_mod (a : ℕ) (b : ℕ) (c : ℕ) : a % (b * c) % b = a % b :=
  modeq.modeq_of_modeq_mul_right c (modeq.mod_modeq a (b * c))

@[simp] theorem mod_mul_left_mod (a : ℕ) (b : ℕ) (c : ℕ) : a % (b * c) % c = a % c :=
  modeq.modeq_of_modeq_mul_left b (modeq.mod_modeq a (b * c))

theorem div_mod_eq_mod_mul_div (a : ℕ) (b : ℕ) (c : ℕ) : a / b % c = a % (b * c) / b := sorry

theorem add_mod_add_ite (a : ℕ) (b : ℕ) (c : ℕ) : (a + b) % c + ite (c ≤ a % c + b % c) c 0 = a % c + b % c := sorry

theorem add_mod_of_add_mod_lt {a : ℕ} {b : ℕ} {c : ℕ} (hc : a % c + b % c < c) : (a + b) % c = a % c + b % c := sorry

theorem add_mod_add_of_le_add_mod {a : ℕ} {b : ℕ} {c : ℕ} (hc : c ≤ a % c + b % c) : (a + b) % c + c = a % c + b % c :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a + b) % c + c = a % c + b % c)) (Eq.symm (add_mod_add_ite a b c))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((a + b) % c + c = (a + b) % c + ite (c ≤ a % c + b % c) c 0)) (if_pos hc)))
      (Eq.refl ((a + b) % c + c)))

theorem add_div {a : ℕ} {b : ℕ} {c : ℕ} (hc0 : 0 < c) : (a + b) / c = a / c + b / c + ite (c ≤ a % c + b % c) 1 0 := sorry

theorem add_div_eq_of_add_mod_lt {a : ℕ} {b : ℕ} {c : ℕ} (hc : a % c + b % c < c) : (a + b) / c = a / c + b / c := sorry

protected theorem add_div_of_dvd_right {a : ℕ} {b : ℕ} {c : ℕ} (hca : c ∣ a) : (a + b) / c = a / c + b / c := sorry

protected theorem add_div_of_dvd_left {a : ℕ} {b : ℕ} {c : ℕ} (hca : c ∣ b) : (a + b) / c = a / c + b / c := sorry

theorem add_div_eq_of_le_mod_add_mod {a : ℕ} {b : ℕ} {c : ℕ} (hc : c ≤ a % c + b % c) (hc0 : 0 < c) : (a + b) / c = a / c + b / c + 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a + b) / c = a / c + b / c + 1)) (add_div hc0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / c + b / c + ite (c ≤ a % c + b % c) 1 0 = a / c + b / c + 1)) (if_pos hc)))
      (Eq.refl (a / c + b / c + 1)))

theorem add_div_le_add_div (a : ℕ) (b : ℕ) (c : ℕ) : a / c + b / c ≤ (a + b) / c := sorry

theorem le_mod_add_mod_of_dvd_add_of_not_dvd {a : ℕ} {b : ℕ} {c : ℕ} (h : c ∣ a + b) (ha : ¬c ∣ a) : c ≤ a % c + b % c := sorry

theorem odd_mul_odd {n : ℕ} {m : ℕ} (hn1 : n % bit0 1 = 1) (hm1 : m % bit0 1 = 1) : n * m % bit0 1 = 1 :=
  (fun (this : n * m % bit0 1 = 1 * 1 % bit0 1) => this) (modeq.modeq_mul hn1 hm1)

theorem odd_mul_odd_div_two {m : ℕ} {n : ℕ} (hm1 : m % bit0 1 = 1) (hn1 : n % bit0 1 = 1) : m * n / bit0 1 = m * (n / bit0 1) + m / bit0 1 := sorry

theorem odd_of_mod_four_eq_one {n : ℕ} (h : n % bit0 (bit0 1) = 1) : n % bit0 1 = 1 :=
  modeq.modeq_of_modeq_mul_left (bit0 1) h

theorem odd_of_mod_four_eq_three {n : ℕ} (h : n % bit0 (bit0 1) = bit1 1) : n % bit0 1 = 1 :=
  modeq.modeq_of_modeq_mul_left (bit0 1) h

end nat


namespace list


theorem nth_rotate {α : Type u_1} {l : List α} {n : ℕ} {m : ℕ} (hml : m < length l) : nth (rotate l n) m = nth l ((m + n) % length l) := sorry

theorem rotate_eq_self_iff_eq_repeat {α : Type u_1} [hα : Nonempty α] {l : List α} : (∀ (n : ℕ), rotate l n = l) ↔ ∃ (a : α), l = repeat a (length l) := sorry

