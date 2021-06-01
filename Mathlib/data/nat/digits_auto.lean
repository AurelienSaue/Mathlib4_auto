/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.int.modeq
import Mathlib.tactic.interval_cases
import Mathlib.tactic.linarith.default
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Digits of a natural number

This provides a basic API for extracting the digits of a natural number in a given base,
and reconstructing numbers from their digits.

We also prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

A basic `norm_digits` tactic is also provided for proving goals of the form
`nat.digits a b = l` where `a` and `b` are numerals.
-/

namespace nat


/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digits_aux_0 : ℕ → List ℕ := sorry

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digits_aux_1 (n : ℕ) : List ℕ := list.repeat 1 n

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digits_aux (b : ℕ) (h : bit0 1 ≤ b) : ℕ → List ℕ := sorry

@[simp] theorem digits_aux_zero (b : ℕ) (h : bit0 1 ≤ b) : digits_aux b h 0 = [] := rfl

theorem digits_aux_def (b : ℕ) (h : bit0 1 ≤ b) (n : ℕ) (w : 0 < n) :
    digits_aux b h n = n % b :: digits_aux b h (n / b) :=
  sorry

/--
`digits b n` gives the digits, in little-endian order,
of a natural number `n` in a specified base `b`.

In any base, we have `of_digits b L = L.foldr (λ x y, x + b * y) 0`.
* For any `2 ≤ b`, we have `l < b` for any `l ∈ digits b n`,
  and the last digit is not zero.
  This uniquely specifies the behaviour of `digits b`.
* For `b = 1`, we define `digits 1 n = list.repeat 1 n`.
* For `b = 0`, we define `digits 0 n = [n]`, except `digits 0 0 = []`.

Note this differs from the existing `nat.to_digits` in core, which is used for printing numerals.
In particular, `nat.to_digits b 0 = [0]`, while `digits b 0 = []`.
-/
def digits : ℕ → ℕ → List ℕ := sorry

@[simp] theorem digits_zero (b : ℕ) : digits b 0 = [] :=
  nat.cases_on b (Eq.refl (digits 0 0))
    fun (b : ℕ) =>
      nat.cases_on b (Eq.refl (digits 1 0))
        fun (b : ℕ) => Eq.refl (digits (Nat.succ (Nat.succ b)) 0)

@[simp] theorem digits_zero_zero : digits 0 0 = [] := rfl

@[simp] theorem digits_zero_succ (n : ℕ) : digits 0 (Nat.succ n) = [n + 1] := rfl

theorem digits_zero_succ' {n : ℕ} (w : 0 < n) : digits 0 n = [n] :=
  nat.cases_on n (fun (w : 0 < 0) => idRhs (digits 0 0 = [0]) (absurd w (of_as_true trivial)))
    (fun (n : ℕ) (w : 0 < Nat.succ n) => idRhs (digits 0 (n + 1) = digits 0 (n + 1)) rfl) w

@[simp] theorem digits_one (n : ℕ) : digits 1 n = list.repeat 1 n := rfl

@[simp] theorem digits_one_succ (n : ℕ) : digits 1 (n + 1) = 1 :: digits 1 n := rfl

@[simp] theorem digits_add_two_add_one (b : ℕ) (n : ℕ) :
    digits (b + bit0 1) (n + 1) =
        (n + 1) % (b + bit0 1) :: digits (b + bit0 1) ((n + 1) / (b + bit0 1)) :=
  rfl

theorem digits_def' {b : ℕ} (h : bit0 1 ≤ b) {n : ℕ} (w : 0 < n) :
    digits b n = n % b :: digits b (n / b) :=
  sorry

@[simp] theorem digits_of_lt (b : ℕ) (x : ℕ) (w₁ : 0 < x) (w₂ : x < b) : digits b x = [x] := sorry

theorem digits_add (b : ℕ) (h : bit0 1 ≤ b) (x : ℕ) (y : ℕ) (w : x < b) (w' : 0 < x ∨ 0 < y) :
    digits b (x + b * y) = x :: digits b y :=
  sorry

/--
`of_digits b L` takes a list `L` of natural numbers, and interprets them
as a number in semiring, as the little-endian digits in base `b`.
-/
-- If we had a function converting a list into a polynomial,

-- and appropriate lemmas about that function,

-- we could rewrite this in terms of that.

def of_digits {α : Type u_1} [semiring α] (b : α) : List ℕ → α := sorry

theorem of_digits_eq_foldr {α : Type u_1} [semiring α] (b : α) (L : List ℕ) :
    of_digits b L = list.foldr (fun (x : ℕ) (y : α) => ↑x + b * y) 0 L :=
  sorry

@[simp] theorem of_digits_singleton {b : ℕ} {n : ℕ} : of_digits b [n] = n := sorry

@[simp] theorem of_digits_one_cons {α : Type u_1} [semiring α] (h : ℕ) (L : List ℕ) :
    of_digits 1 (h :: L) = ↑h + of_digits 1 L :=
  sorry

theorem of_digits_append {b : ℕ} {l1 : List ℕ} {l2 : List ℕ} :
    of_digits b (l1 ++ l2) = of_digits b l1 + b ^ list.length l1 * of_digits b l2 :=
  sorry

theorem coe_of_digits (α : Type u_1) [semiring α] (b : ℕ) (L : List ℕ) :
    ↑(of_digits b L) = of_digits (↑b) L :=
  sorry

theorem coe_int_of_digits (b : ℕ) (L : List ℕ) : ↑(of_digits b L) = of_digits (↑b) L := sorry

theorem digits_zero_of_eq_zero {b : ℕ} (h : 1 ≤ b) {L : List ℕ} (w : of_digits b L = 0) (l : ℕ)
    (H : l ∈ L) : l = 0 :=
  sorry

theorem digits_of_digits (b : ℕ) (h : bit0 1 ≤ b) (L : List ℕ) (w₁ : ∀ (l : ℕ), l ∈ L → l < b)
    (w₂ : ∀ (h : L ≠ []), list.last L h ≠ 0) : digits b (of_digits b L) = L :=
  sorry

theorem of_digits_digits (b : ℕ) (n : ℕ) : of_digits b (digits b n) = n := sorry

theorem of_digits_one (L : List ℕ) : of_digits 1 L = list.sum L := sorry

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `of_digits`.
-/

theorem digits_eq_nil_iff_eq_zero {b : ℕ} {n : ℕ} : digits b n = [] ↔ n = 0 := sorry

theorem digits_ne_nil_iff_ne_zero {b : ℕ} {n : ℕ} : digits b n ≠ [] ↔ n ≠ 0 :=
  not_congr digits_eq_nil_iff_eq_zero

theorem digits_last {b : ℕ} {m : ℕ} (h : bit0 1 ≤ b) (hm : 0 < m) (p : digits b m ≠ [])
    (q : digits b (m / b) ≠ []) : list.last (digits b m) p = list.last (digits b (m / b)) q :=
  sorry

theorem last_digit_ne_zero (b : ℕ) {m : ℕ} (hm : m ≠ 0) :
    list.last (digits b m) (iff.mpr digits_ne_nil_iff_ne_zero hm) ≠ 0 :=
  sorry

/-- The digits in the base b+2 expansion of n are all less than b+2 -/
theorem digits_lt_base' {b : ℕ} {m : ℕ} {d : ℕ} : d ∈ digits (b + bit0 1) m → d < b + bit0 1 :=
  sorry

/-- The digits in the base b expansion of n are all less than b, if b ≥ 2 -/
theorem digits_lt_base {b : ℕ} {m : ℕ} {d : ℕ} (hb : bit0 1 ≤ b) (hd : d ∈ digits b m) : d < b :=
  sorry

/-- an n-digit number in base b + 2 is less than (b + 2)^n -/
theorem of_digits_lt_base_pow_length' {b : ℕ} {l : List ℕ}
    (hl : ∀ (x : ℕ), x ∈ l → x < b + bit0 1) :
    of_digits (b + bit0 1) l < (b + bit0 1) ^ list.length l :=
  sorry

/-- an n-digit number in base b is less than b^n if b ≥ 2 -/
theorem of_digits_lt_base_pow_length {b : ℕ} {l : List ℕ} (hb : bit0 1 ≤ b)
    (hl : ∀ (x : ℕ), x ∈ l → x < b) : of_digits b l < b ^ list.length l :=
  sorry

/-- Any number m is less than (b+2)^(number of digits in the base b + 2 representation of m) -/
theorem lt_base_pow_length_digits' {b : ℕ} {m : ℕ} :
    m < (b + bit0 1) ^ list.length (digits (b + bit0 1) m) :=
  sorry

/-- Any number m is less than b^(number of digits in the base b representation of m) -/
theorem lt_base_pow_length_digits {b : ℕ} {m : ℕ} (hb : bit0 1 ≤ b) :
    m < b ^ list.length (digits b m) :=
  sorry

theorem of_digits_digits_append_digits {b : ℕ} {m : ℕ} {n : ℕ} :
    of_digits b (digits b n ++ digits b m) = n + b ^ list.length (digits b n) * m :=
  sorry

theorem digits_len_le_digits_len_succ (b : ℕ) (n : ℕ) :
    list.length (digits b n) ≤ list.length (digits b (n + 1)) :=
  sorry

theorem le_digits_len_le (b : ℕ) (n : ℕ) (m : ℕ) (h : n ≤ m) :
    list.length (digits b n) ≤ list.length (digits b m) :=
  monotone_of_monotone_nat (digits_len_le_digits_len_succ b) h

theorem pow_length_le_mul_of_digits {b : ℕ} {l : List ℕ} (hl : l ≠ []) (hl2 : list.last l hl ≠ 0) :
    (b + bit0 1) ^ list.length l ≤ (b + bit0 1) * of_digits (b + bit0 1) l :=
  sorry

/--
Any non-zero natural number `m` is greater than
(b+2)^((number of digits in the base (b+2) representation of m) - 1)
-/
theorem base_pow_length_digits_le' (b : ℕ) (m : ℕ) (hm : m ≠ 0) :
    (b + bit0 1) ^ list.length (digits (b + bit0 1) m) ≤ (b + bit0 1) * m :=
  sorry

/--
Any non-zero natural number `m` is greater than
b^((number of digits in the base b representation of m) - 1)
-/
theorem base_pow_length_digits_le (b : ℕ) (m : ℕ) (hb : bit0 1 ≤ b) :
    m ≠ 0 → b ^ list.length (digits b m) ≤ b * m :=
  sorry

/-! ### Modular Arithmetic -/

-- This is really a theorem about polynomials.

theorem dvd_of_digits_sub_of_digits {α : Type u_1} [comm_ring α] {a : α} {b : α} {k : α}
    (h : k ∣ a - b) (L : List ℕ) : k ∣ of_digits a L - of_digits b L :=
  sorry

theorem of_digits_modeq' (b : ℕ) (b' : ℕ) (k : ℕ) (h : modeq k b b') (L : List ℕ) :
    modeq k (of_digits b L) (of_digits b' L) :=
  sorry

theorem of_digits_modeq (b : ℕ) (k : ℕ) (L : List ℕ) :
    modeq k (of_digits b L) (of_digits (b % k) L) :=
  of_digits_modeq' b (b % k) k (modeq.symm (modeq.mod_modeq b k)) L

theorem of_digits_mod (b : ℕ) (k : ℕ) (L : List ℕ) : of_digits b L % k = of_digits (b % k) L % k :=
  of_digits_modeq b k L

theorem of_digits_zmodeq' (b : ℤ) (b' : ℤ) (k : ℕ) (h : int.modeq (↑k) b b') (L : List ℕ) :
    int.modeq (↑k) (of_digits b L) (of_digits b' L) :=
  sorry

theorem of_digits_zmodeq (b : ℤ) (k : ℕ) (L : List ℕ) :
    int.modeq (↑k) (of_digits b L) (of_digits (b % ↑k) L) :=
  of_digits_zmodeq' b (b % ↑k) k (int.modeq.symm (int.modeq.mod_modeq b ↑k)) L

theorem of_digits_zmod (b : ℤ) (k : ℕ) (L : List ℕ) :
    of_digits b L % ↑k = of_digits (b % ↑k) L % ↑k :=
  of_digits_zmodeq b k L

theorem modeq_digits_sum (b : ℕ) (b' : ℕ) (h : b' % b = 1) (n : ℕ) :
    modeq b n (list.sum (digits b' n)) :=
  sorry

theorem modeq_three_digits_sum (n : ℕ) :
    modeq (bit1 1) n (list.sum (digits (bit0 (bit1 (bit0 1))) n)) :=
  sorry

theorem modeq_nine_digits_sum (n : ℕ) :
    modeq (bit1 (bit0 (bit0 1))) n (list.sum (digits (bit0 (bit1 (bit0 1))) n)) :=
  sorry

theorem zmodeq_of_digits_digits (b : ℕ) (b' : ℕ) (c : ℤ) (h : int.modeq (↑b) (↑b') c) (n : ℕ) :
    int.modeq (↑b) (↑n) (of_digits c (digits b' n)) :=
  sorry

theorem of_digits_neg_one (L : List ℕ) :
    of_digits (-1) L = list.alternating_sum (list.map (fun (n : ℕ) => ↑n) L) :=
  sorry

theorem modeq_eleven_digits_sum (n : ℕ) :
    int.modeq (bit1 (bit1 (bit0 1))) (↑n)
        (list.alternating_sum (list.map (fun (n : ℕ) => ↑n) (digits (bit0 (bit1 (bit0 1))) n))) :=
  sorry

/-! ## Divisibility  -/

theorem dvd_iff_dvd_digits_sum (b : ℕ) (b' : ℕ) (h : b' % b = 1) (n : ℕ) :
    b ∣ n ↔ b ∣ list.sum (digits b' n) :=
  sorry

theorem three_dvd_iff (n : ℕ) : bit1 1 ∣ n ↔ bit1 1 ∣ list.sum (digits (bit0 (bit1 (bit0 1))) n) :=
  sorry

theorem nine_dvd_iff (n : ℕ) :
    bit1 (bit0 (bit0 1)) ∣ n ↔ bit1 (bit0 (bit0 1)) ∣ list.sum (digits (bit0 (bit1 (bit0 1))) n) :=
  sorry

theorem dvd_iff_dvd_of_digits (b : ℕ) (b' : ℕ) (c : ℤ) (h : ↑b ∣ ↑b' - c) (n : ℕ) :
    b ∣ n ↔ ↑b ∣ of_digits c (digits b' n) :=
  sorry

theorem eleven_dvd_iff (n : ℕ) :
    bit1 (bit1 (bit0 1)) ∣ n ↔
        bit1 (bit1 (bit0 1)) ∣
          list.alternating_sum (list.map (fun (n : ℕ) => ↑n) (digits (bit0 (bit1 (bit0 1))) n)) :=
  sorry

/-! ### `norm_digits` tactic -/

namespace norm_digits


theorem digits_succ (b : ℕ) (n : ℕ) (m : ℕ) (r : ℕ) (l : List ℕ) (e : r + b * m = n) (hr : r < b)
    (h : digits b m = l ∧ bit0 1 ≤ b ∧ 0 < m) : digits b n = r :: l ∧ bit0 1 ≤ b ∧ 0 < n :=
  sorry

theorem digits_one (b : ℕ) (n : ℕ) (n0 : 0 < n) (nb : n < b) :
    digits b n = [n] ∧ bit0 1 ≤ b ∧ 0 < n :=
  sorry

end Mathlib