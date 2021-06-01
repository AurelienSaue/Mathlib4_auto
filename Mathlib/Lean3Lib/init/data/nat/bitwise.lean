/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.nat.lemmas
import Mathlib.Lean3Lib.init.meta.well_founded_tactics
 

universes u 

namespace Mathlib

namespace nat


def bodd_div2 : ℕ → Bool × ℕ :=
  sorry

def div2 (n : ℕ) : ℕ :=
  prod.snd (bodd_div2 n)

def bodd (n : ℕ) : Bool :=
  prod.fst (bodd_div2 n)

@[simp] theorem bodd_zero : bodd 0 = false :=
  rfl

@[simp] theorem bodd_one : bodd 1 = tt :=
  rfl

@[simp] theorem bodd_two : bodd (bit0 1) = false :=
  rfl

@[simp] theorem bodd_succ (n : ℕ) : bodd (Nat.succ n) = bnot (bodd n) := sorry

@[simp] theorem bodd_add (m : ℕ) (n : ℕ) : bodd (m + n) = bxor (bodd m) (bodd n) := sorry

@[simp] theorem bodd_mul (m : ℕ) (n : ℕ) : bodd (m * n) = bodd m && bodd n := sorry

theorem mod_two_of_bodd (n : ℕ) : n % bit0 1 = cond (bodd n) 1 0 := sorry

@[simp] theorem div2_zero : div2 0 = 0 :=
  rfl

@[simp] theorem div2_one : div2 1 = 0 :=
  rfl

@[simp] theorem div2_two : div2 (bit0 1) = 1 :=
  rfl

@[simp] theorem div2_succ (n : ℕ) : div2 (Nat.succ n) = cond (bodd n) (Nat.succ (div2 n)) (div2 n) := sorry

theorem bodd_add_div2 (n : ℕ) : cond (bodd n) 1 0 + bit0 1 * div2 n = n := sorry

theorem div2_val (n : ℕ) : div2 n = n / bit0 1 := sorry

def bit (b : Bool) : ℕ → ℕ :=
  cond b bit1 bit0

theorem bit0_val (n : ℕ) : bit0 n = bit0 1 * n :=
  Eq.trans (Eq.trans (eq.mpr (id (Eq._oldrec (Eq.refl (n + n = 0 + n + n)) (nat.zero_add n))) (Eq.refl (n + n))) rfl)
    (nat.mul_comm n (bit0 1))

theorem bit1_val (n : ℕ) : bit1 n = bit0 1 * n + 1 :=
  congr_arg Nat.succ (bit0_val n)

theorem bit_val (b : Bool) (n : ℕ) : bit b n = bit0 1 * n + cond b 1 0 :=
  bool.cases_on b (bit0_val n) (bit1_val n)

theorem bit_decomp (n : ℕ) : bit (bodd n) (div2 n) = n :=
  Eq.trans (bit_val (bodd n) (div2 n)) (Eq.trans (nat.add_comm (bit0 1 * div2 n) (cond (bodd n) 1 0)) (bodd_add_div2 n))

def bit_cases_on {C : ℕ → Sort u} (n : ℕ) (h : (b : Bool) → (n : ℕ) → C (bit b n)) : C n :=
  eq.mpr sorry (h (bodd n) (div2 n))

@[simp] theorem bit_zero : bit false 0 = 0 :=
  rfl

def shiftl' (b : Bool) (m : ℕ) : ℕ → ℕ :=
  sorry

def shiftl : ℕ → ℕ → ℕ :=
  shiftl' false

@[simp] theorem shiftl_zero (m : ℕ) : shiftl m 0 = m :=
  rfl

@[simp] theorem shiftl_succ (m : ℕ) (n : ℕ) : shiftl m (n + 1) = bit0 (shiftl m n) :=
  rfl

def shiftr : ℕ → ℕ → ℕ :=
  sorry

def test_bit (m : ℕ) (n : ℕ) : Bool :=
  bodd (shiftr m n)

def binary_rec {C : ℕ → Sort u} (z : C 0) (f : (b : Bool) → (n : ℕ) → C n → C (bit b n)) (n : ℕ) : C n :=
  sorry

def size : ℕ → ℕ :=
  binary_rec 0 fun (_x : Bool) (_x : ℕ) => Nat.succ

def bits : ℕ → List Bool :=
  binary_rec [] fun (b : Bool) (_x : ℕ) (IH : List Bool) => b :: IH

def bitwise (f : Bool → Bool → Bool) : ℕ → ℕ → ℕ :=
  binary_rec (fun (n : ℕ) => cond (f false tt) n 0)
    fun (a : Bool) (m : ℕ) (Ia : ℕ → ℕ) =>
      binary_rec (cond (f tt false) (bit a m) 0) fun (b : Bool) (n _x : ℕ) => bit (f a b) (Ia n)

def lor : ℕ → ℕ → ℕ :=
  bitwise bor

def land : ℕ → ℕ → ℕ :=
  bitwise band

def ldiff : ℕ → ℕ → ℕ :=
  bitwise fun (a b : Bool) => a && bnot b

def lxor : ℕ → ℕ → ℕ :=
  bitwise bxor

@[simp] theorem binary_rec_zero {C : ℕ → Sort u} (z : C 0) (f : (b : Bool) → (n : ℕ) → C n → C (bit b n)) : binary_rec z f 0 = z := sorry

/- bitwise ops -/

theorem bodd_bit (b : Bool) (n : ℕ) : bodd (bit b n) = b := sorry

theorem div2_bit (b : Bool) (n : ℕ) : div2 (bit b n) = n := sorry

theorem shiftl'_add (b : Bool) (m : ℕ) (n : ℕ) (k : ℕ) : shiftl' b m (n + k) = shiftl' b (shiftl' b m n) k := sorry

theorem shiftl_add (m : ℕ) (n : ℕ) (k : ℕ) : shiftl m (n + k) = shiftl (shiftl m n) k :=
  shiftl'_add false

theorem shiftr_add (m : ℕ) (n : ℕ) (k : ℕ) : shiftr m (n + k) = shiftr (shiftr m n) k := sorry

theorem shiftl'_sub (b : Bool) (m : ℕ) {n : ℕ} {k : ℕ} : k ≤ n → shiftl' b m (n - k) = shiftr (shiftl' b m n) k := sorry

theorem shiftl_sub (m : ℕ) {n : ℕ} {k : ℕ} : k ≤ n → shiftl m (n - k) = shiftr (shiftl m n) k :=
  shiftl'_sub false

@[simp] theorem test_bit_zero (b : Bool) (n : ℕ) : test_bit (bit b n) 0 = b :=
  bodd_bit b n

theorem test_bit_succ (m : ℕ) (b : Bool) (n : ℕ) : test_bit (bit b n) (Nat.succ m) = test_bit n m := sorry

theorem binary_rec_eq {C : ℕ → Sort u} {z : C 0} {f : (b : Bool) → (n : ℕ) → C n → C (bit b n)} (h : f false 0 z = z) (b : Bool) (n : ℕ) : binary_rec z f (bit b n) = f b n (binary_rec z f n) := sorry

theorem bitwise_bit_aux {f : Bool → Bool → Bool} (h : f false false = false) : (binary_rec (cond (f tt false) (bit false 0) 0) fun (b : Bool) (n _x : ℕ) => bit (f false b) (cond (f false tt) n 0)) =
  fun (n : ℕ) => cond (f false tt) n 0 := sorry

@[simp] theorem bitwise_zero_left (f : Bool → Bool → Bool) (n : ℕ) : bitwise f 0 n = cond (f false tt) n 0 := sorry

@[simp] theorem bitwise_zero_right (f : Bool → Bool → Bool) (h : f false false = false) (m : ℕ) : bitwise f m 0 = cond (f tt false) m 0 := sorry

@[simp] theorem bitwise_zero (f : Bool → Bool → Bool) : bitwise f 0 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (bitwise f 0 0 = 0)) (bitwise_zero_left f 0)))
    (bool.cases_on (f false tt) (Eq.refl (cond false 0 0)) (Eq.refl (cond tt 0 0)))

@[simp] theorem bitwise_bit {f : Bool → Bool → Bool} (h : f false false = false) (a : Bool) (m : ℕ) (b : Bool) (n : ℕ) : bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := sorry

theorem bitwise_swap {f : Bool → Bool → Bool} (h : f false false = false) : bitwise (function.swap f) = function.swap (bitwise f) := sorry

@[simp] theorem lor_bit (a : Bool) (m : ℕ) (b : Bool) (n : ℕ) : lor (bit a m) (bit b n) = bit (a || b) (lor m n) :=
  bitwise_bit rfl

@[simp] theorem land_bit (a : Bool) (m : ℕ) (b : Bool) (n : ℕ) : land (bit a m) (bit b n) = bit (a && b) (land m n) :=
  bitwise_bit rfl

@[simp] theorem ldiff_bit (a : Bool) (m : ℕ) (b : Bool) (n : ℕ) : ldiff (bit a m) (bit b n) = bit (a && bnot b) (ldiff m n) :=
  bitwise_bit rfl

@[simp] theorem lxor_bit (a : Bool) (m : ℕ) (b : Bool) (n : ℕ) : lxor (bit a m) (bit b n) = bit (bxor a b) (lxor m n) :=
  bitwise_bit rfl

@[simp] theorem test_bit_bitwise {f : Bool → Bool → Bool} (h : f false false = false) (m : ℕ) (n : ℕ) (k : ℕ) : test_bit (bitwise f m n) k = f (test_bit m k) (test_bit n k) := sorry

@[simp] theorem test_bit_lor (m : ℕ) (n : ℕ) (k : ℕ) : test_bit (lor m n) k = test_bit m k || test_bit n k :=
  test_bit_bitwise rfl

@[simp] theorem test_bit_land (m : ℕ) (n : ℕ) (k : ℕ) : test_bit (land m n) k = test_bit m k && test_bit n k :=
  test_bit_bitwise rfl

@[simp] theorem test_bit_ldiff (m : ℕ) (n : ℕ) (k : ℕ) : test_bit (ldiff m n) k = test_bit m k && bnot (test_bit n k) :=
  test_bit_bitwise rfl

@[simp] theorem test_bit_lxor (m : ℕ) (n : ℕ) (k : ℕ) : test_bit (lxor m n) k = bxor (test_bit m k) (test_bit n k) :=
  test_bit_bitwise rfl

