/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.rat.cast
import Mathlib.data.rat.meta_defs
import PostPort

universes u_1 u 

namespace Mathlib

/-!
# `norm_num`

Evaluating arithmetic expressions including `*`, `+`, `-`, `^`, `≤`.
-/

namespace tactic


/-- Reflexivity conversion: given `e` returns `(e, ⊢ e = e)` -/
/-- Transitivity conversion: given two conversions (which take an
expression `e` and returns `(e', ⊢ e = e')`), produces another
conversion that combines them with transitivity, treating failures
as reflexivity conversions. -/
namespace instance_cache


/-- Faster version of `mk_app ``bit0 [e]`. -/
/-- Faster version of `mk_app ``bit1 [e]`. -/
end instance_cache


end tactic


namespace norm_num


theorem subst_into_add {α : Type u_1} [Add α] (l : α) (r : α) (tl : α) (tr : α) (t : α) (prl : l = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (l + r = t)) prl))
    (eq.mpr (id (Eq._oldrec (Eq.refl (tl + r = t)) prr))
      (eq.mpr (id (Eq._oldrec (Eq.refl (tl + tr = t)) prt)) (Eq.refl t)))

theorem subst_into_mul {α : Type u_1} [Mul α] (l : α) (r : α) (tl : α) (tr : α) (t : α) (prl : l = tl) (prr : r = tr) (prt : tl * tr = t) : l * r = t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (l * r = t)) prl))
    (eq.mpr (id (Eq._oldrec (Eq.refl (tl * r = t)) prr))
      (eq.mpr (id (Eq._oldrec (Eq.refl (tl * tr = t)) prt)) (Eq.refl t)))

theorem subst_into_neg {α : Type u_1} [Neg α] (a : α) (ta : α) (t : α) (pra : a = ta) (prt : -ta = t) : -a = t := sorry

/-- The result type of `match_numeral`, either `0`, `1`, or a top level
decomposition of `bit0 e` or `bit1 e`. The `other` case means it is not a numeral. -/
/-- Unfold the top level constructor of the numeral expression. -/
theorem zero_succ {α : Type u_1} [semiring α] : 0 + 1 = 1 :=
  zero_add 1

theorem one_succ {α : Type u_1} [semiring α] : 1 + 1 = bit0 1 :=
  rfl

theorem bit0_succ {α : Type u_1} [semiring α] (a : α) : bit0 a + 1 = bit1 a :=
  rfl

theorem bit1_succ {α : Type u_1} [semiring α] (a : α) (b : α) (h : a + 1 = b) : bit1 a + 1 = bit0 b := sorry

/-- Given `a`, `b` natural numerals, proves `⊢ a + 1 = b`, assuming that this is provable.
(It may prove garbage instead of failing if `a + 1 = b` is false.) -/
theorem zero_adc {α : Type u_1} [semiring α] (a : α) (b : α) (h : a + 1 = b) : 0 + a + 1 = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 + a + 1 = b)) (zero_add a))) h

theorem adc_zero {α : Type u_1} [semiring α] (a : α) (b : α) (h : a + 1 = b) : a + 0 + 1 = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + 0 + 1 = b)) (add_zero a))) h

theorem one_add {α : Type u_1} [semiring α] (a : α) (b : α) (h : a + 1 = b) : 1 + a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 + a = b)) (add_comm 1 a))) h

theorem add_bit0_bit0 {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (h : a + b = c) : bit0 a + bit0 b = bit0 c := sorry

theorem add_bit0_bit1 {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (h : a + b = c) : bit0 a + bit1 b = bit1 c := sorry

theorem add_bit1_bit0 {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (h : a + b = c) : bit1 a + bit0 b = bit1 c := sorry

theorem add_bit1_bit1 {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (h : a + b + 1 = c) : bit1 a + bit1 b = bit0 c := sorry

theorem adc_one_one {α : Type u_1} [semiring α] : 1 + 1 + 1 = bit1 1 :=
  rfl

theorem adc_bit0_one {α : Type u_1} [semiring α] (a : α) (b : α) (h : a + 1 = b) : bit0 a + 1 + 1 = bit0 b := sorry

theorem adc_one_bit0 {α : Type u_1} [semiring α] (a : α) (b : α) (h : a + 1 = b) : 1 + bit0 a + 1 = bit0 b := sorry

theorem adc_bit1_one {α : Type u_1} [semiring α] (a : α) (b : α) (h : a + 1 = b) : bit1 a + 1 + 1 = bit1 b := sorry

theorem adc_one_bit1 {α : Type u_1} [semiring α] (a : α) (b : α) (h : a + 1 = b) : 1 + bit1 a + 1 = bit1 b := sorry

theorem adc_bit0_bit0 {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (h : a + b = c) : bit0 a + bit0 b + 1 = bit1 c := sorry

theorem adc_bit1_bit0 {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (h : a + b + 1 = c) : bit1 a + bit0 b + 1 = bit0 c := sorry

theorem adc_bit0_bit1 {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (h : a + b + 1 = c) : bit0 a + bit1 b + 1 = bit0 c := sorry

theorem adc_bit1_bit1 {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (h : a + b + 1 = c) : bit1 a + bit1 b + 1 = bit1 c := sorry

/-- Given `a`,`b`,`r` natural numerals, proves `⊢ a + b = r`. -/
/-- Given `a`,`b`,`r` natural numerals, proves `⊢ a + b + 1 = r`. -/
/-- Given `a`,`b` natural numerals, returns `(r, ⊢ a + b = r)`. -/
theorem bit0_mul {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (h : a * b = c) : bit0 a * b = bit0 c := sorry

theorem mul_bit0' {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (h : a * b = c) : a * bit0 b = bit0 c := sorry

theorem mul_bit0_bit0 {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (h : a * b = c) : bit0 a * bit0 b = bit0 (bit0 c) :=
  bit0_mul a (bit0 b) (bit0 c) (mul_bit0' a b c h)

theorem mul_bit1_bit1 {α : Type u_1} [semiring α] (a : α) (b : α) (c : α) (d : α) (e : α) (hc : a * b = c) (hd : a + b = d) (he : bit0 c + d = e) : bit1 a * bit1 b = bit1 e := sorry

/-- Given `a`,`b` natural numerals, returns `(r, ⊢ a * b = r)`. -/
/-- Given `a` a positive natural numeral, returns `⊢ 0 < a`. -/
/-- Given `a` a rational numeral, returns `⊢ 0 < a`. -/
/-- `match_neg (- e) = some e`, otherwise `none` -/
/-- `match_sign (- e) = inl e`, `match_sign 0 = inr ff`, otherwise `inr tt` -/
theorem ne_zero_of_pos {α : Type u_1} [ordered_add_comm_group α] (a : α) : 0 < a → a ≠ 0 :=
  ne_of_gt

theorem ne_zero_neg {α : Type u_1} [add_group α] (a : α) : a ≠ 0 → -a ≠ 0 :=
  mt (iff.mp neg_eq_zero)

/-- Given `a` a rational numeral, returns `⊢ a ≠ 0`. -/
theorem clear_denom_div {α : Type u_1} [division_ring α] (a : α) (b : α) (b' : α) (c : α) (d : α) (h₀ : b ≠ 0) (h₁ : b * b' = d) (h₂ : a * b' = c) : a / b * d = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b * d = c)) (Eq.symm h₁)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / b * (b * b') = c)) (Eq.symm (mul_assoc (a / b) b b'))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a / b * b * b' = c)) (div_mul_cancel a h₀))) h₂))

/-- Given `a` nonnegative rational and `d` a natural number, returns `(b, ⊢ a * d = b)`.
(`d` should be a multiple of the denominator of `a`, so that `b` is a natural number.) -/
theorem nonneg_pos {α : Type u_1} [ordered_cancel_add_comm_monoid α] (a : α) : 0 < a → 0 ≤ a :=
  le_of_lt

theorem lt_one_bit0 {α : Type u_1} [linear_ordered_semiring α] (a : α) (h : 1 ≤ a) : 1 < bit0 a :=
  lt_of_lt_of_le one_lt_two (iff.mpr bit0_le_bit0 h)

theorem lt_one_bit1 {α : Type u_1} [linear_ordered_semiring α] (a : α) (h : 0 < a) : 1 < bit1 a :=
  iff.mpr one_lt_bit1 h

theorem lt_bit0_bit0 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) : a < b → bit0 a < bit0 b :=
  iff.mpr bit0_lt_bit0

theorem lt_bit0_bit1 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) (h : a ≤ b) : bit0 a < bit1 b :=
  lt_of_le_of_lt (iff.mpr bit0_le_bit0 h) (lt_add_one (bit0 b))

theorem lt_bit1_bit0 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) (h : a + 1 ≤ b) : bit1 a < bit0 b := sorry

theorem lt_bit1_bit1 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) : a < b → bit1 a < bit1 b :=
  iff.mpr bit1_lt_bit1

theorem le_one_bit0 {α : Type u_1} [linear_ordered_semiring α] (a : α) (h : 1 ≤ a) : 1 ≤ bit0 a :=
  le_of_lt (lt_one_bit0 a h)

-- deliberately strong hypothesis because bit1 0 is not a numeral

theorem le_one_bit1 {α : Type u_1} [linear_ordered_semiring α] (a : α) (h : 0 < a) : 1 ≤ bit1 a :=
  le_of_lt (lt_one_bit1 a h)

theorem le_bit0_bit0 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) : a ≤ b → bit0 a ≤ bit0 b :=
  iff.mpr bit0_le_bit0

theorem le_bit0_bit1 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) (h : a ≤ b) : bit0 a ≤ bit1 b :=
  le_of_lt (lt_bit0_bit1 a b h)

theorem le_bit1_bit0 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) (h : a + 1 ≤ b) : bit1 a ≤ bit0 b :=
  le_of_lt (lt_bit1_bit0 a b h)

theorem le_bit1_bit1 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) : a ≤ b → bit1 a ≤ bit1 b :=
  iff.mpr bit1_le_bit1

theorem sle_one_bit0 {α : Type u_1} [linear_ordered_semiring α] (a : α) : 1 ≤ a → 1 + 1 ≤ bit0 a :=
  iff.mpr bit0_le_bit0

theorem sle_one_bit1 {α : Type u_1} [linear_ordered_semiring α] (a : α) : 1 ≤ a → 1 + 1 ≤ bit1 a :=
  le_bit0_bit1 1 a

theorem sle_bit0_bit0 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) : a + 1 ≤ b → bit0 a + 1 ≤ bit0 b :=
  le_bit1_bit0 a b

theorem sle_bit0_bit1 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) (h : a ≤ b) : bit0 a + 1 ≤ bit1 b :=
  iff.mpr bit1_le_bit1 h

theorem sle_bit1_bit0 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) (h : a + 1 ≤ b) : bit1 a + 1 ≤ bit0 b :=
  Eq.symm (bit1_succ a (a + 1) rfl) ▸ iff.mpr bit0_le_bit0 h

theorem sle_bit1_bit1 {α : Type u_1} [linear_ordered_semiring α] (a : α) (b : α) (h : a + 1 ≤ b) : bit1 a + 1 ≤ bit1 b :=
  Eq.symm (bit1_succ a (a + 1) rfl) ▸ le_bit0_bit1 (a + 1) b h

/-- Given `a` a rational numeral, returns `⊢ 0 ≤ a`. -/
/-- Given `a` a rational numeral, returns `⊢ 1 ≤ a`. -/
/-- Given `a`,`b` natural numerals, proves `⊢ a ≤ b`. -/
/-- Given `a`,`b` natural numerals, proves `⊢ a + 1 ≤ b`. -/
/-- Given `a`,`b` natural numerals, proves `⊢ a < b`. -/
theorem clear_denom_lt {α : Type u_1} [linear_ordered_semiring α] (a : α) (a' : α) (b : α) (b' : α) (d : α) (h₀ : 0 < d) (ha : a * d = a') (hb : b * d = b') (h : a' < b') : a < b :=
  lt_of_mul_lt_mul_right
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * d < b * d)) ha)) (eq.mpr (id (Eq._oldrec (Eq.refl (a' < b * d)) hb)) h))
    (le_of_lt h₀)

/-- Given `a`,`b` nonnegative rational numerals, proves `⊢ a < b`. -/
theorem lt_neg_pos {α : Type u_1} [ordered_add_comm_group α] (a : α) (b : α) (ha : 0 < a) (hb : 0 < b) : -a < b :=
  lt_trans (neg_neg_of_pos ha) hb

/-- Given `a`,`b` rational numerals, proves `⊢ a < b`. -/
theorem clear_denom_le {α : Type u_1} [linear_ordered_semiring α] (a : α) (a' : α) (b : α) (b' : α) (d : α) (h₀ : 0 < d) (ha : a * d = a') (hb : b * d = b') (h : a' ≤ b') : a ≤ b :=
  le_of_mul_le_mul_right
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * d ≤ b * d)) ha)) (eq.mpr (id (Eq._oldrec (Eq.refl (a' ≤ b * d)) hb)) h)) h₀

/-- Given `a`,`b` nonnegative rational numerals, proves `⊢ a ≤ b`. -/
theorem le_neg_pos {α : Type u_1} [ordered_add_comm_group α] (a : α) (b : α) (ha : 0 ≤ a) (hb : 0 ≤ b) : -a ≤ b :=
  le_trans (neg_nonpos_of_nonneg ha) hb

/-- Given `a`,`b` rational numerals, proves `⊢ a ≤ b`. -/
/-- Given `a`,`b` rational numerals, proves `⊢ a ≠ b`. This version tries to prove
`⊢ a < b` or `⊢ b < a`, and so is not appropriate for types without an order relation. -/
theorem nat_cast_zero {α : Type u_1} [semiring α] : ↑0 = 0 :=
  nat.cast_zero

theorem nat_cast_one {α : Type u_1} [semiring α] : ↑1 = 1 :=
  nat.cast_one

theorem nat_cast_bit0 {α : Type u_1} [semiring α] (a : ℕ) (a' : α) (h : ↑a = a') : ↑(bit0 a) = bit0 a' :=
  h ▸ nat.cast_bit0 a

theorem nat_cast_bit1 {α : Type u_1} [semiring α] (a : ℕ) (a' : α) (h : ↑a = a') : ↑(bit1 a) = bit1 a' :=
  h ▸ nat.cast_bit1 a

theorem int_cast_zero {α : Type u_1} [ring α] : ↑0 = 0 :=
  int.cast_zero

theorem int_cast_one {α : Type u_1} [ring α] : ↑1 = 1 :=
  int.cast_one

theorem int_cast_bit0 {α : Type u_1} [ring α] (a : ℤ) (a' : α) (h : ↑a = a') : ↑(bit0 a) = bit0 a' :=
  h ▸ int.cast_bit0 a

theorem int_cast_bit1 {α : Type u_1} [ring α] (a : ℤ) (a' : α) (h : ↑a = a') : ↑(bit1 a) = bit1 a' :=
  h ▸ int.cast_bit1 a

theorem rat_cast_bit0 {α : Type u_1} [division_ring α] [char_zero α] (a : ℚ) (a' : α) (h : ↑a = a') : ↑(bit0 a) = bit0 a' :=
  h ▸ rat.cast_bit0 a

theorem rat_cast_bit1 {α : Type u_1} [division_ring α] [char_zero α] (a : ℚ) (a' : α) (h : ↑a = a') : ↑(bit1 a) = bit1 a' :=
  h ▸ rat.cast_bit1 a

/-- Given `a' : α` a natural numeral, returns `(a : ℕ, ⊢ ↑a = a')`.
(Note that the returned value is on the left of the equality.) -/
/-- Given `a' : α` a natural numeral, returns `(a : ℤ, ⊢ ↑a = a')`.
(Note that the returned value is on the left of the equality.) -/
/-- Given `a' : α` a natural numeral, returns `(a : ℚ, ⊢ ↑a = a')`.
(Note that the returned value is on the left of the equality.) -/
theorem rat_cast_div {α : Type u_1} [division_ring α] [char_zero α] (a : ℚ) (b : ℚ) (a' : α) (b' : α) (ha : ↑a = a') (hb : ↑b = b') : ↑(a / b) = a' / b' :=
  ha ▸ hb ▸ rat.cast_div a b

/-- Given `a' : α` a nonnegative rational numeral, returns `(a : ℚ, ⊢ ↑a = a')`.
(Note that the returned value is on the left of the equality.) -/
theorem int_cast_neg {α : Type u_1} [ring α] (a : ℤ) (a' : α) (h : ↑a = a') : ↑(-a) = -a' :=
  h ▸ int.cast_neg a

theorem rat_cast_neg {α : Type u_1} [division_ring α] (a : ℚ) (a' : α) (h : ↑a = a') : ↑(-a) = -a' :=
  h ▸ rat.cast_neg a

/-- Given `a' : α` an integer numeral, returns `(a : ℤ, ⊢ ↑a = a')`.
(Note that the returned value is on the left of the equality.) -/
/-- Given `a' : α` a rational numeral, returns `(a : ℚ, ⊢ ↑a = a')`.
(Note that the returned value is on the left of the equality.) -/
theorem nat_cast_ne {α : Type u_1} [semiring α] [char_zero α] (a : ℕ) (b : ℕ) (a' : α) (b' : α) (ha : ↑a = a') (hb : ↑b = b') (h : a ≠ b) : a' ≠ b' :=
  ha ▸ hb ▸ mt (iff.mp nat.cast_inj) h

theorem int_cast_ne {α : Type u_1} [ring α] [char_zero α] (a : ℤ) (b : ℤ) (a' : α) (b' : α) (ha : ↑a = a') (hb : ↑b = b') (h : a ≠ b) : a' ≠ b' :=
  ha ▸ hb ▸ mt (iff.mp int.cast_inj) h

theorem rat_cast_ne {α : Type u_1} [division_ring α] [char_zero α] (a : ℚ) (b : ℚ) (a' : α) (b' : α) (ha : ↑a = a') (hb : ↑b = b') (h : a ≠ b) : a' ≠ b' :=
  ha ▸ hb ▸ mt (iff.mp rat.cast_inj) h

/-- Given `a`,`b` rational numerals, proves `⊢ a ≠ b`. Currently it tries two methods:

  * Prove `⊢ a < b` or `⊢ b < a`, if the base type has an order
  * Embed `↑(a':ℚ) = a` and `↑(b':ℚ) = b`, and then prove `a' ≠ b'`.
    This requires that the base type be `char_zero`, and also that it be a `division_ring`
    so that the coercion from `ℚ` is well defined.

We may also add coercions to `ℤ` and `ℕ` as well in order to support `char_zero`
rings and semirings. -/
/-- Given `a` a rational numeral, returns `⊢ a ≠ 0`. -/
/-- Given `a` nonnegative rational and `d` a natural number, returns `(b, ⊢ a * d = b)`.
(`d` should be a multiple of the denominator of `a`, so that `b` is a natural number.) -/
theorem clear_denom_add {α : Type u_1} [division_ring α] (a : α) (a' : α) (b : α) (b' : α) (c : α) (c' : α) (d : α) (h₀ : d ≠ 0) (ha : a * d = a') (hb : b * d = b') (hc : c * d = c') (h : a' + b' = c') : a + b = c := sorry

/-- Given `a`,`b`,`c` nonnegative rational numerals, returns `⊢ a + b = c`. -/
theorem add_pos_neg_pos {α : Type u_1} [add_group α] (a : α) (b : α) (c : α) (h : c + b = a) : a + -b = c := sorry

theorem add_pos_neg_neg {α : Type u_1} [add_group α] (a : α) (b : α) (c : α) (h : c + a = b) : a + -b = -c := sorry

theorem add_neg_pos_pos {α : Type u_1} [add_group α] (a : α) (b : α) (c : α) (h : a + c = b) : -a + b = c := sorry

theorem add_neg_pos_neg {α : Type u_1} [add_group α] (a : α) (b : α) (c : α) (h : b + c = a) : -a + b = -c := sorry

theorem add_neg_neg {α : Type u_1} [add_group α] (a : α) (b : α) (c : α) (h : b + a = c) : -a + -b = -c := sorry

/-- Given `a`,`b`,`c` rational numerals, returns `⊢ a + b = c`. -/
/-- Given `a`,`b` rational numerals, returns `(c, ⊢ a + b = c)`. -/
theorem clear_denom_simple_nat {α : Type u_1} [division_ring α] (a : α) : 1 ≠ 0 ∧ a * 1 = a :=
  { left := one_ne_zero, right := mul_one a }

theorem clear_denom_simple_div {α : Type u_1} [division_ring α] (a : α) (b : α) (h : b ≠ 0) : b ≠ 0 ∧ a / b * b = a :=
  { left := h, right := div_mul_cancel a h }

/-- Given `a` a nonnegative rational numeral, returns `(b, c, ⊢ a * b = c)`
where `b` and `c` are natural numerals. (`b` will be the denominator of `a`.) -/
theorem clear_denom_mul {α : Type u_1} [field α] (a : α) (a' : α) (b : α) (b' : α) (c : α) (c' : α) (d₁ : α) (d₂ : α) (d : α) (ha : d₁ ≠ 0 ∧ a * d₁ = a') (hb : d₂ ≠ 0 ∧ b * d₂ = b') (hc : c * d = c') (hd : d₁ * d₂ = d) (h : a' * b' = c') : a * b = c := sorry

/-- Given `a`,`b` nonnegative rational numerals, returns `(c, ⊢ a * b = c)`. -/
theorem mul_neg_pos {α : Type u_1} [ring α] (a : α) (b : α) (c : α) (h : a * b = c) : -a * b = -c := sorry

theorem mul_pos_neg {α : Type u_1} [ring α] (a : α) (b : α) (c : α) (h : a * b = c) : a * -b = -c := sorry

theorem mul_neg_neg {α : Type u_1} [ring α] (a : α) (b : α) (c : α) (h : a * b = c) : -a * -b = c := sorry

/-- Given `a`,`b` rational numerals, returns `(c, ⊢ a * b = c)`. -/
theorem inv_neg {α : Type u_1} [division_ring α] (a : α) (b : α) (h : a⁻¹ = b) : -a⁻¹ = -b := sorry

theorem inv_one {α : Type u_1} [division_ring α] : 1⁻¹ = 1 :=
  inv_one

theorem inv_one_div {α : Type u_1} [division_ring α] (a : α) : 1 / a⁻¹ = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 / a⁻¹ = a)) (one_div a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹⁻¹ = a)) (inv_inv' a))) (Eq.refl a))

theorem inv_div_one {α : Type u_1} [division_ring α] (a : α) : a⁻¹ = 1 / a :=
  inv_eq_one_div a

theorem inv_div {α : Type u_1} [division_ring α] (a : α) (b : α) : a / b⁻¹ = b / a := sorry

/-- Given `a` a rational numeral, returns `(b, ⊢ a⁻¹ = b)`. -/
theorem div_eq {α : Type u_1} [division_ring α] (a : α) (b : α) (b' : α) (c : α) (hb : b⁻¹ = b') (h : a * b' = c) : a / b = c :=
  eq.mp (Eq._oldrec (Eq.refl (a * (b⁻¹) = c)) (Eq.symm (div_eq_mul_inv a b)))
    (eq.mp (Eq._oldrec (Eq.refl (a * b' = c)) (Eq.symm hb)) h)

/-- Given `a`,`b` rational numerals, returns `(c, ⊢ a / b = c)`. -/
/-- Given `a` a rational numeral, returns `(b, ⊢ -a = b)`. -/
theorem sub_pos {α : Type u_1} [add_group α] (a : α) (b : α) (b' : α) (c : α) (hb : -b = b') (h : a + b' = c) : a - b = c :=
  eq.mp (Eq._oldrec (Eq.refl (a + -b = c)) (Eq.symm (sub_eq_add_neg a b)))
    (eq.mp (Eq._oldrec (Eq.refl (a + b' = c)) (Eq.symm hb)) h)

theorem sub_neg {α : Type u_1} [add_group α] (a : α) (b : α) (c : α) (h : a + b = c) : a - -b = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - -b = c)) (sub_neg_eq_add a b))) h

/-- Given `a`,`b` rational numerals, returns `(c, ⊢ a - b = c)`. -/
theorem sub_nat_pos (a : ℕ) (b : ℕ) (c : ℕ) (h : b + c = a) : a - b = c :=
  h ▸ nat.add_sub_cancel_left b c

theorem sub_nat_neg (a : ℕ) (b : ℕ) (c : ℕ) (h : a + c = b) : a - b = 0 :=
  nat.sub_eq_zero_of_le (h ▸ nat.le_add_right a c)

/-- Given `a : nat`,`b : nat` natural numerals, returns `(c, ⊢ a - b = c)`. -/
/-- Evaluates the basic field operations `+`,`neg`,`-`,`*`,`inv`,`/` on numerals.
Also handles nat subtraction. Does not do recursive simplification; that is,
`1 + 1 + 1` will not simplify but `2 + 1` will. This is handled by the top level
`simp` call in `norm_num.derive`. -/
theorem pow_bit0 {α : Type u} [monoid α] (a : α) (c' : α) (c : α) (b : ℕ) (h : a ^ b = c') (h₂ : c' * c' = c) : a ^ bit0 b = c := sorry

theorem pow_bit1 {α : Type u} [monoid α] (a : α) (c₁ : α) (c₂ : α) (c : α) (b : ℕ) (h : a ^ b = c₁) (h₂ : c₁ * c₁ = c₂) (h₃ : c₂ * a = c) : a ^ bit1 b = c := sorry

/-- Given `a` a rational numeral and `b : nat`, returns `(c, ⊢ a ^ b = c)`. -/
/-- Evaluates expressions of the form `a ^ b`, `monoid.pow a b` or `nat.pow a b`. -/
/-- Given `⊢ p`, returns `(true, ⊢ p = true)`. -/
/-- Given `⊢ ¬ p`, returns `(false, ⊢ p = false)`. -/
theorem not_refl_false_intro {α : Sort u_1} (a : α) : a ≠ a = False :=
  eq_false_intro (not_not_intro rfl)

/-- Evaluates the inequality operations `=`,`<`,`>`,`≤`,`≥`,`≠` on numerals. -/
theorem nat_succ_eq (a : ℕ) (b : ℕ) (c : ℕ) (h₁ : a = b) (h₂ : b + 1 = c) : Nat.succ a = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Nat.succ a = c)) h₁)) h₂

/-- Evaluates the expression `nat.succ ... (nat.succ n)` where `n` is a natural numeral.
(We could also just handle `nat.succ n` here and rely on `simp` to work bottom up, but we figure
that towers of successors coming from e.g. `induction` are a common case.) -/
theorem nat_div (a : ℕ) (b : ℕ) (q : ℕ) (r : ℕ) (m : ℕ) (hm : q * b = m) (h : r + m = a) (h₂ : r < b) : a / b = q := sorry

theorem int_div (a : ℤ) (b : ℤ) (q : ℤ) (r : ℤ) (m : ℤ) (hm : q * b = m) (h : r + m = a) (h₁ : 0 ≤ r) (h₂ : r < b) : a / b = q := sorry

theorem nat_mod (a : ℕ) (b : ℕ) (q : ℕ) (r : ℕ) (m : ℕ) (hm : q * b = m) (h : r + m = a) (h₂ : r < b) : a % b = r := sorry

theorem int_mod (a : ℤ) (b : ℤ) (q : ℤ) (r : ℤ) (m : ℤ) (hm : q * b = m) (h : r + m = a) (h₁ : 0 ≤ r) (h₂ : r < b) : a % b = r := sorry

theorem int_div_neg (a : ℤ) (b : ℤ) (c' : ℤ) (c : ℤ) (h : a / b = c') (h₂ : -c' = c) : a / -b = c :=
  h₂ ▸ h ▸ int.div_neg a b

theorem int_mod_neg (a : ℤ) (b : ℤ) (c : ℤ) (h : a % b = c) : a % -b = c :=
  Eq.trans (int.mod_neg a b) h

/-- Given `a`,`b` numerals in `nat` or `int`,
  * `prove_div_mod ic a b ff` returns `(c, ⊢ a / b = c)`
  * `prove_div_mod ic a b tt` returns `(c, ⊢ a % b = c)`
-/
theorem dvd_eq_nat (a : ℕ) (b : ℕ) (c : ℕ) (p : Prop) (h₁ : b % a = c) (h₂ : c = 0 = p) : a ∣ b = p := sorry

theorem dvd_eq_int (a : ℤ) (b : ℤ) (c : ℤ) (p : Prop) (h₁ : b % a = c) (h₂ : c = 0 = p) : a ∣ b = p := sorry

/-- Evaluates some extra numeric operations on `nat` and `int`, specifically
`nat.succ`, `/` and `%`, and `∣` (divisibility). -/
/-- This version of `derive` does not fail when the input is already a numeral -/
/-- An attribute for adding additional extensions to `norm_num`. To use this attribute, put
`@[norm_num]` on a tactic of type `expr → tactic (expr × expr)`; the tactic will be called on
subterms by `norm_num`, and it is responsible for identifying that the expression is a numerical
function applied to numerals, for example `nat.fib 17`, and should return the reduced numerical
expression (which must be in `norm_num`-normal form: a natural or rational numeral, i.e. `37`,
`12 / 7` or `-(2 / 3)`, although this can be an expression in any type), and the proof that the
original expression is equal to the rewritten expression.

Failure is used to indicate that this tactic does not apply to the term. For performance reasons,
it is best to detect non-applicability as soon as possible so that the next tactic can have a go,
so generally it will start with a pattern match and then checking that the arguments to the term
are numerals or of the appropriate form, followed by proof construction, which should not fail.

Propositions are treated like any other term. The normal form for propositions is `true` or
`false`, so it should produce a proof of the form `p = true` or `p = false`. `eq_true_intro` can be
used to help here.
-/
/-- Look up the `norm_num` extensions in the cache and return a tactic extending `derive.step` with
additional reduction procedures. -/
/-- Simplify an expression bottom-up using `step` to simplify the subexpressions. -/
/-- Simplify an expression bottom-up using the default `norm_num` set to simplify the
subexpressions. -/
end norm_num


/-- Basic version of `norm_num` that does not call `simp`. It uses the provided `step` tactic
to simplify the expression; use `get_step` to get the default `norm_num` set and `derive.step` for
the basic builtin set of simplifications. -/
/-- Normalize numerical expressions. It uses the provided `step` tactic to simplify the expression;
use `get_step` to get the default `norm_num` set and `derive.step` for the basic builtin set of
simplifications. -/
namespace tactic.interactive


/-- Basic version of `norm_num` that does not call `simp`. -/
/-- Normalize numerical expressions. Supports the operations
`+` `-` `*` `/` `^` and `%` over numerical types such as
`ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`,
where `A` and `B` are numerical expressions.
It also has a relatively simple primality prover. -/
/-- Normalizes a numerical expression and tries to close the goal with the result. -/
/--
Normalises numerical expressions. It supports the operations `+` `-` `*` `/` `^` and `%` over
