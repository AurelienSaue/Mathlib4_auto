/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.linarith.default
import PostPort

namespace Mathlib

/-!
# Bitwise operations on natural numbers

In the first half of this file, we provide theorems for reasoning about natural numbers from their
bitwise properties. In the second half of this file, we show properties of the bitwise operations
`lor`, `land` and `lxor`, which are defined in core.

## Main results
* `eq_of_test_bit_eq`: two natural numbers are equal if they have equal bits at every position.
* `exists_most_significant_bit`: if `n ≠ 0`, then there is some position `i` that contains the most
  significant `1`-bit of `n`.
* `lt_of_test_bit`: if `n` and `m` are numbers and `i` is a position such that the `i`-th bit of
  of `n` is zero, the `i`-th bit of `m` is one, and all more significant bits are equal, then
  `n < m`.

## Future work

There is another way to express bitwise properties of natural number: `digits 2`. The two ways
should be connected.

## Keywords

bitwise, and, or, xor
-/

namespace nat


@[simp] theorem bit_ff : bit false = bit0 :=
  rfl

@[simp] theorem bit_tt : bit tt = bit1 :=
  rfl

@[simp] theorem bit_eq_zero {n : ℕ} {b : Bool} : bit b n = 0 ↔ n = 0 ∧ b = false := sorry

theorem zero_of_test_bit_eq_ff {n : ℕ} (h : ∀ (i : ℕ), test_bit n i = false) : n = 0 := sorry

@[simp] theorem zero_test_bit (i : ℕ) : test_bit 0 i = false := sorry

/-- Bitwise extensionality: Two numbers agree if they agree at every bit position. -/
theorem eq_of_test_bit_eq {n : ℕ} {m : ℕ} (h : ∀ (i : ℕ), test_bit n i = test_bit m i) : n = m := sorry

theorem exists_most_significant_bit {n : ℕ} (h : n ≠ 0) : ∃ (i : ℕ), test_bit n i = tt ∧ ∀ (j : ℕ), i < j → test_bit n j = false := sorry

theorem lt_of_test_bit {n : ℕ} {m : ℕ} (i : ℕ) (hn : test_bit n i = false) (hm : test_bit m i = tt) (hnm : ∀ (j : ℕ), i < j → test_bit n j = test_bit m j) : n < m := sorry

/-- If `f` is a commutative operation on bools such that `f ff ff = ff`, then `bitwise f` is also
    commutative. -/
theorem bitwise_comm {f : Bool → Bool → Bool} (hf : ∀ (b b' : Bool), f b b' = f b' b) (hf' : f false false = false) (n : ℕ) (m : ℕ) : bitwise f n m = bitwise f m n := sorry

theorem lor_comm (n : ℕ) (m : ℕ) : lor n m = lor m n :=
  bitwise_comm bool.bor_comm rfl n m

theorem land_comm (n : ℕ) (m : ℕ) : land n m = land m n :=
  bitwise_comm bool.band_comm rfl n m

theorem lxor_comm (n : ℕ) (m : ℕ) : lxor n m = lxor m n :=
  bitwise_comm bool.bxor_comm rfl n m

@[simp] theorem zero_lxor (n : ℕ) : lxor 0 n = n :=
  rfl

@[simp] theorem lxor_zero (n : ℕ) : lxor n 0 = n :=
  lxor_comm 0 n ▸ rfl

@[simp] theorem zero_land (n : ℕ) : land 0 n = 0 :=
  rfl

@[simp] theorem land_zero (n : ℕ) : land n 0 = 0 :=
  land_comm 0 n ▸ rfl

@[simp] theorem zero_lor (n : ℕ) : lor 0 n = n :=
  rfl

@[simp] theorem lor_zero (n : ℕ) : lor n 0 = n :=
  lor_comm 0 n ▸ rfl

/-- Proving associativity of bitwise operations in general essentially boils down to a huge case
    distinction, so it is shorter to use this tactic instead of proving it in the general case. -/
theorem lxor_assoc (n : ℕ) (m : ℕ) (k : ℕ) : lxor (lxor n m) k = lxor n (lxor m k) := sorry

theorem land_assoc (n : ℕ) (m : ℕ) (k : ℕ) : land (land n m) k = land n (land m k) := sorry

theorem lor_assoc (n : ℕ) (m : ℕ) (k : ℕ) : lor (lor n m) k = lor n (lor m k) := sorry

@[simp] theorem lxor_self (n : ℕ) : lxor n n = 0 := sorry

theorem lxor_right_inj {n : ℕ} {m : ℕ} {m' : ℕ} (h : lxor n m = lxor n m') : m = m' := sorry

theorem lxor_left_inj {n : ℕ} {n' : ℕ} {m : ℕ} (h : lxor n m = lxor n' m) : n = n' :=
  lxor_right_inj
    (eq.mp (Eq._oldrec (Eq.refl (lxor m n = lxor n' m)) (lxor_comm n' m))
      (eq.mp (Eq._oldrec (Eq.refl (lxor n m = lxor n' m)) (lxor_comm n m)) h))

theorem lxor_eq_zero {n : ℕ} {m : ℕ} : lxor n m = 0 ↔ n = m :=
  { mp := eq.mpr (id (Eq._oldrec (Eq.refl (lxor n m = 0 → n = m)) (Eq.symm (lxor_self m)))) lxor_left_inj,
    mpr := fun (ᾰ : n = m) => Eq._oldrec (lxor_self n) ᾰ }

theorem lxor_trichotomy {a : ℕ} {b : ℕ} {c : ℕ} (h : lxor a (lxor b c) ≠ 0) : lxor b c < a ∨ lxor a c < b ∨ lxor a b < c := sorry

