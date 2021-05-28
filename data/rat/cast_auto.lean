/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.rat.order
import Mathlib.data.int.char_zero
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Casts for Rational Numbers

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/

namespace rat


/-- Construct the canonical injection from `ℚ` into an arbitrary
  division ring. If the field has positive characteristic `p`,
  we define `1 / p = 1 / 0 = 0` for consistency with our
  division by zero convention. -/
-- see Note [coercion into rings]

protected instance cast_coe {α : Type u_1} [division_ring α] : has_coe_t ℚ α :=
  has_coe_t.mk fun (r : ℚ) => ↑(num r) / ↑(denom r)

@[simp] theorem cast_of_int {α : Type u_1} [division_ring α] (n : ℤ) : ↑(of_int n) = ↑n :=
  (fun (this : ↑n / ↑1 = ↑n) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n / ↑1 = ↑n)) nat.cast_one))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑n / 1 = ↑n)) (div_one ↑n))) (Eq.refl ↑n)))

@[simp] theorem cast_coe_int {α : Type u_1} [division_ring α] (n : ℤ) : ↑↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑n)) (coe_int_eq_of_int n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(of_int n) = ↑n)) (cast_of_int n))) (Eq.refl ↑n))

@[simp] theorem cast_coe_nat {α : Type u_1} [division_ring α] (n : ℕ) : ↑↑n = ↑n :=
  cast_coe_int ↑n

@[simp] theorem cast_zero {α : Type u_1} [division_ring α] : ↑0 = 0 :=
  Eq.trans (cast_of_int 0) int.cast_zero

@[simp] theorem cast_one {α : Type u_1} [division_ring α] : ↑1 = 1 :=
  Eq.trans (cast_of_int 1) int.cast_one

theorem cast_commute {α : Type u_1} [division_ring α] (r : ℚ) (a : α) : commute (↑r) a :=
  commute.div_left (int.cast_commute (num r) a) (nat.cast_commute (denom r) a)

theorem commute_cast {α : Type u_1} [division_ring α] (a : α) (r : ℚ) : commute a ↑r :=
  commute.symm (cast_commute r a)

theorem cast_mk_of_ne_zero {α : Type u_1} [division_ring α] (a : ℤ) (b : ℤ) (b0 : ↑b ≠ 0) : ↑(mk a b) = ↑a / ↑b := sorry

theorem cast_add_of_ne_zero {α : Type u_1} [division_ring α] {m : ℚ} {n : ℚ} : ↑(denom m) ≠ 0 → ↑(denom n) ≠ 0 → ↑(m + n) = ↑m + ↑n := sorry

@[simp] theorem cast_neg {α : Type u_1} [division_ring α] (n : ℚ) : ↑(-n) = -↑n := sorry

theorem cast_sub_of_ne_zero {α : Type u_1} [division_ring α] {m : ℚ} {n : ℚ} (m0 : ↑(denom m) ≠ 0) (n0 : ↑(denom n) ≠ 0) : ↑(m - n) = ↑m - ↑n := sorry

theorem cast_mul_of_ne_zero {α : Type u_1} [division_ring α] {m : ℚ} {n : ℚ} : ↑(denom m) ≠ 0 → ↑(denom n) ≠ 0 → ↑(m * n) = ↑m * ↑n := sorry

theorem cast_inv_of_ne_zero {α : Type u_1} [division_ring α] {n : ℚ} : ↑(num n) ≠ 0 → ↑(denom n) ≠ 0 → ↑(n⁻¹) = (↑n⁻¹) := sorry

theorem cast_div_of_ne_zero {α : Type u_1} [division_ring α] {m : ℚ} {n : ℚ} (md : ↑(denom m) ≠ 0) (nn : ↑(num n) ≠ 0) (nd : ↑(denom n) ≠ 0) : ↑(m / n) = ↑m / ↑n := sorry

@[simp] theorem cast_inj {α : Type u_1} [division_ring α] [char_zero α] {m : ℚ} {n : ℚ} : ↑m = ↑n ↔ m = n := sorry

theorem cast_injective {α : Type u_1} [division_ring α] [char_zero α] : function.injective coe :=
  fun {a₁ a₂ : ℚ} => idRhs (↑a₁ = ↑a₂ → a₁ = a₂) (iff.mp cast_inj)

@[simp] theorem cast_eq_zero {α : Type u_1} [division_ring α] [char_zero α] {n : ℚ} : ↑n = 0 ↔ n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n = 0 ↔ n = 0)) (Eq.symm cast_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n = ↑0 ↔ n = 0)) (propext cast_inj))) (iff.refl (n = 0)))

theorem cast_ne_zero {α : Type u_1} [division_ring α] [char_zero α] {n : ℚ} : ↑n ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero

@[simp] theorem cast_add {α : Type u_1} [division_ring α] [char_zero α] (m : ℚ) (n : ℚ) : ↑(m + n) = ↑m + ↑n :=
  cast_add_of_ne_zero (iff.mpr nat.cast_ne_zero (ne_of_gt (pos m))) (iff.mpr nat.cast_ne_zero (ne_of_gt (pos n)))

@[simp] theorem cast_sub {α : Type u_1} [division_ring α] [char_zero α] (m : ℚ) (n : ℚ) : ↑(m - n) = ↑m - ↑n :=
  cast_sub_of_ne_zero (iff.mpr nat.cast_ne_zero (ne_of_gt (pos m))) (iff.mpr nat.cast_ne_zero (ne_of_gt (pos n)))

@[simp] theorem cast_mul {α : Type u_1} [division_ring α] [char_zero α] (m : ℚ) (n : ℚ) : ↑(m * n) = ↑m * ↑n :=
  cast_mul_of_ne_zero (iff.mpr nat.cast_ne_zero (ne_of_gt (pos m))) (iff.mpr nat.cast_ne_zero (ne_of_gt (pos n)))

@[simp] theorem cast_bit0 {α : Type u_1} [division_ring α] [char_zero α] (n : ℚ) : ↑(bit0 n) = bit0 ↑n :=
  cast_add n n

@[simp] theorem cast_bit1 {α : Type u_1} [division_ring α] [char_zero α] (n : ℚ) : ↑(bit1 n) = bit1 ↑n := sorry

/-- Coercion `ℚ → α` as a `ring_hom`. -/
def cast_hom (α : Type u_1) [division_ring α] [char_zero α] : ℚ →+* α :=
  ring_hom.mk coe cast_one cast_mul cast_zero cast_add

@[simp] theorem coe_cast_hom {α : Type u_1} [division_ring α] [char_zero α] : ⇑(cast_hom α) = coe :=
  rfl

@[simp] theorem cast_inv {α : Type u_1} [division_ring α] [char_zero α] (n : ℚ) : ↑(n⁻¹) = (↑n⁻¹) :=
  ring_hom.map_inv (cast_hom α) n

@[simp] theorem cast_div {α : Type u_1} [division_ring α] [char_zero α] (m : ℚ) (n : ℚ) : ↑(m / n) = ↑m / ↑n :=
  ring_hom.map_div (cast_hom α) m n

theorem cast_mk {α : Type u_1} [division_ring α] [char_zero α] (a : ℤ) (b : ℤ) : ↑(mk a b) = ↑a / ↑b := sorry

@[simp] theorem cast_pow {α : Type u_1} [division_ring α] [char_zero α] (q : ℚ) (k : ℕ) : ↑(q ^ k) = ↑q ^ k :=
  ring_hom.map_pow (cast_hom α) q k

@[simp] theorem cast_nonneg {α : Type u_1} [linear_ordered_field α] {n : ℚ} : 0 ≤ ↑n ↔ 0 ≤ n := sorry

@[simp] theorem cast_le {α : Type u_1} [linear_ordered_field α] {m : ℚ} {n : ℚ} : ↑m ≤ ↑n ↔ m ≤ n := sorry

@[simp] theorem cast_lt {α : Type u_1} [linear_ordered_field α] {m : ℚ} {n : ℚ} : ↑m < ↑n ↔ m < n := sorry

@[simp] theorem cast_nonpos {α : Type u_1} [linear_ordered_field α] {n : ℚ} : ↑n ≤ 0 ↔ n ≤ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n ≤ 0 ↔ n ≤ 0)) (Eq.symm cast_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n ≤ ↑0 ↔ n ≤ 0)) (propext cast_le))) (iff.refl (n ≤ 0)))

@[simp] theorem cast_pos {α : Type u_1} [linear_ordered_field α] {n : ℚ} : 0 < ↑n ↔ 0 < n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < ↑n ↔ 0 < n)) (Eq.symm cast_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑0 < ↑n ↔ 0 < n)) (propext cast_lt))) (iff.refl (0 < n)))

@[simp] theorem cast_lt_zero {α : Type u_1} [linear_ordered_field α] {n : ℚ} : ↑n < 0 ↔ n < 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n < 0 ↔ n < 0)) (Eq.symm cast_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n < ↑0 ↔ n < 0)) (propext cast_lt))) (iff.refl (n < 0)))

@[simp] theorem cast_id (n : ℚ) : ↑n = n := sorry

@[simp] theorem cast_min {α : Type u_1} [linear_ordered_field α] {a : ℚ} {b : ℚ} : ↑(min a b) = min ↑a ↑b := sorry

@[simp] theorem cast_max {α : Type u_1} [linear_ordered_field α] {a : ℚ} {b : ℚ} : ↑(max a b) = max ↑a ↑b := sorry

@[simp] theorem cast_abs {α : Type u_1} [linear_ordered_field α] {q : ℚ} : ↑(abs q) = abs ↑q := sorry

end rat


theorem ring_hom.eq_rat_cast {k : Type u_1} [division_ring k] (f : ℚ →+* k) (r : ℚ) : coe_fn f r = ↑r := sorry

-- This seems to be true for a `[char_p k]` too because `k'` must have the same characteristic

-- but the proof would be much longer

theorem ring_hom.map_rat_cast {k : Type u_1} {k' : Type u_2} [division_ring k] [char_zero k] [division_ring k'] (f : k →+* k') (r : ℚ) : coe_fn f ↑r = ↑r :=
  ring_hom.eq_rat_cast (ring_hom.comp f (rat.cast_hom k)) r

theorem ring_hom.ext_rat {R : Type u_1} [semiring R] (f : ℚ →+* R) (g : ℚ →+* R) : f = g := sorry

protected instance rat.subsingleton_ring_hom {R : Type u_1} [semiring R] : subsingleton (ℚ →+* R) :=
  subsingleton.intro ring_hom.ext_rat

