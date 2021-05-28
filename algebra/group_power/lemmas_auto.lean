/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group_power.basic
import Mathlib.algebra.opposites
import Mathlib.data.list.basic
import Mathlib.data.int.cast
import Mathlib.data.equiv.basic
import Mathlib.data.equiv.mul_add
import Mathlib.deprecated.group
import PostPort

universes y u w x z u₁ u_1 

namespace Mathlib

/-!
# Lemmas about power operations on monoids and groups

This file contains lemmas about `monoid.pow`, `group.pow`, `nsmul`, `gsmul`
which require additional imports besides those available in `.basic`.
-/

/-!
### (Additive) monoid
-/

@[simp] theorem nsmul_one {A : Type y} [add_monoid A] [HasOne A] (n : ℕ) : n •ℕ 1 = ↑n :=
  add_monoid_hom.eq_nat_cast
    (add_monoid_hom.mk (fun (n : ℕ) => n •ℕ 1) (zero_nsmul 1) fun (_x _x_1 : ℕ) => add_nsmul 1 _x _x_1) (one_nsmul 1)

@[simp] theorem list.prod_repeat {M : Type u} [monoid M] (a : M) (n : ℕ) : list.prod (list.repeat a n) = a ^ n := sorry

@[simp] theorem list.sum_repeat {A : Type y} [add_monoid A] (a : A) (n : ℕ) : list.sum (list.repeat a n) = n •ℕ a :=
  list.prod_repeat

@[simp] theorem units.coe_pow {M : Type u} [monoid M] (u : units M) (n : ℕ) : ↑(u ^ n) = ↑u ^ n :=
  monoid_hom.map_pow (units.coe_hom M) u n

theorem is_unit_of_pow_eq_one {M : Type u} [monoid M] (x : M) (n : ℕ) (hx : x ^ n = 1) (hn : 0 < n) : is_unit x := sorry

theorem nat.nsmul_eq_mul (m : ℕ) (n : ℕ) : m •ℕ n = m * n := sorry

theorem gsmul_one {A : Type y} [add_group A] [HasOne A] (n : ℤ) : n •ℤ 1 = ↑n := sorry

theorem gpow_add_one {G : Type w} [group G] (a : G) (n : ℤ) : a ^ (n + 1) = a ^ n * a := sorry

theorem add_one_gsmul {A : Type y} [add_group A] (a : A) (i : ℤ) : (i + 1) •ℤ a = i •ℤ a + a :=
  gpow_add_one

theorem gpow_sub_one {G : Type w} [group G] (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * (a⁻¹) := sorry

theorem gpow_add {G : Type w} [group G] (a : G) (m : ℤ) (n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := sorry

theorem mul_self_gpow {G : Type w} [group G] (b : G) (m : ℤ) : b * b ^ m = b ^ (m + 1) := sorry

theorem mul_gpow_self {G : Type w} [group G] (b : G) (m : ℤ) : b ^ m * b = b ^ (m + 1) := sorry

theorem add_gsmul {A : Type y} [add_group A] (a : A) (i : ℤ) (j : ℤ) : (i + j) •ℤ a = i •ℤ a + j •ℤ a :=
  gpow_add

theorem gpow_sub {G : Type w} [group G] (a : G) (m : ℤ) (n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n⁻¹) := sorry

theorem sub_gsmul {A : Type y} [add_group A] (m : ℤ) (n : ℤ) (a : A) : (m - n) •ℤ a = m •ℤ a - n •ℤ a := sorry

theorem gpow_one_add {G : Type w} [group G] (a : G) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (1 + i) = a * a ^ i)) (gpow_add a 1 i)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ 1 * a ^ i = a * a ^ i)) (gpow_one a))) (Eq.refl (a * a ^ i)))

theorem one_add_gsmul {A : Type y} [add_group A] (a : A) (i : ℤ) : (1 + i) •ℤ a = a + i •ℤ a :=
  gpow_one_add

theorem gpow_mul_comm {G : Type w} [group G] (a : G) (i : ℤ) (j : ℤ) : a ^ i * a ^ j = a ^ j * a ^ i :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ i * a ^ j = a ^ j * a ^ i)) (Eq.symm (gpow_add a i j))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (i + j) = a ^ j * a ^ i)) (Eq.symm (gpow_add a j i))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (i + j) = a ^ (j + i))) (add_comm i j))) (Eq.refl (a ^ (j + i)))))

theorem gsmul_add_comm {A : Type y} [add_group A] (a : A) (i : ℤ) (j : ℤ) : i •ℤ a + j •ℤ a = j •ℤ a + i •ℤ a :=
  gpow_mul_comm

theorem gpow_mul {G : Type w} [group G] (a : G) (m : ℤ) (n : ℤ) : a ^ (m * n) = (a ^ m) ^ n := sorry

theorem gsmul_mul' {A : Type y} [add_group A] (a : A) (m : ℤ) (n : ℤ) : m * n •ℤ a = n •ℤ (m •ℤ a) :=
  gpow_mul

theorem gpow_mul' {G : Type w} [group G] (a : G) (m : ℤ) (n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (m * n) = (a ^ n) ^ m)) (mul_comm m n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (n * m) = (a ^ n) ^ m)) (gpow_mul a n m))) (Eq.refl ((a ^ n) ^ m)))

theorem gsmul_mul {A : Type y} [add_group A] (a : A) (m : ℤ) (n : ℤ) : m * n •ℤ a = m •ℤ (n •ℤ a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m * n •ℤ a = m •ℤ (n •ℤ a))) (mul_comm m n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n * m •ℤ a = m •ℤ (n •ℤ a))) (gsmul_mul' a n m))) (Eq.refl (m •ℤ (n •ℤ a))))

theorem gpow_bit0 {G : Type w} [group G] (a : G) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n :=
  gpow_add a n n

theorem bit0_gsmul {A : Type y} [add_group A] (a : A) (n : ℤ) : bit0 n •ℤ a = n •ℤ a + n •ℤ a :=
  gpow_add a n n

theorem gpow_bit1 {G : Type w} [group G] (a : G) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a := sorry

theorem bit1_gsmul {A : Type y} [add_group A] (a : A) (n : ℤ) : bit1 n •ℤ a = n •ℤ a + n •ℤ a + a :=
  gpow_bit1

@[simp] theorem monoid_hom.map_gpow {G : Type w} {H : Type x} [group G] [group H] (f : G →* H) (a : G) (n : ℤ) : coe_fn f (a ^ n) = coe_fn f a ^ n :=
  int.cases_on n (fun (n : ℕ) => monoid_hom.map_pow f a n)
    fun (n : ℕ) =>
      Eq.trans (monoid_hom.map_inv f (a ^ Nat.succ n)) (congr_arg has_inv.inv (monoid_hom.map_pow f a (Nat.succ n)))

@[simp] theorem add_monoid_hom.map_gsmul {A : Type y} {B : Type z} [add_group A] [add_group B] (f : A →+ B) (a : A) (n : ℤ) : coe_fn f (n •ℤ a) = n •ℤ coe_fn f a :=
  monoid_hom.map_gpow (coe_fn add_monoid_hom.to_multiplicative f) a n

@[simp] theorem units.coe_gpow {G : Type w} [group G] (u : units G) (n : ℤ) : ↑(u ^ n) = ↑u ^ n :=
  monoid_hom.map_gpow (units.coe_hom G) u n

/-! Lemmas about `gsmul` under ordering,  placed here (rather than in `algebra.group_power.basic`
with their friends) because they require facts from `data.int.basic`-/

theorem gsmul_pos {A : Type y} [ordered_add_comm_group A] {a : A} (ha : 0 < a) {k : ℤ} (hk : 0 < k) : 0 < k •ℤ a := sorry

theorem gsmul_le_gsmul {A : Type y} [ordered_add_comm_group A] {a : A} {n : ℤ} {m : ℤ} (ha : 0 ≤ a) (h : n ≤ m) : n •ℤ a ≤ m •ℤ a := sorry

theorem gsmul_lt_gsmul {A : Type y} [ordered_add_comm_group A] {a : A} {n : ℤ} {m : ℤ} (ha : 0 < a) (h : n < m) : n •ℤ a < m •ℤ a := sorry

theorem gsmul_le_gsmul_iff {A : Type y} [linear_ordered_add_comm_group A] {a : A} {n : ℤ} {m : ℤ} (ha : 0 < a) : n •ℤ a ≤ m •ℤ a ↔ n ≤ m := sorry

theorem gsmul_lt_gsmul_iff {A : Type y} [linear_ordered_add_comm_group A] {a : A} {n : ℤ} {m : ℤ} (ha : 0 < a) : n •ℤ a < m •ℤ a ↔ n < m := sorry

theorem nsmul_le_nsmul_iff {A : Type y} [linear_ordered_add_comm_group A] {a : A} {n : ℕ} {m : ℕ} (ha : 0 < a) : n •ℕ a ≤ m •ℕ a ↔ n ≤ m := sorry

theorem nsmul_lt_nsmul_iff {A : Type y} [linear_ordered_add_comm_group A] {a : A} {n : ℕ} {m : ℕ} (ha : 0 < a) : n •ℕ a < m •ℕ a ↔ n < m := sorry

@[simp] theorem with_bot.coe_nsmul {A : Type y} [add_monoid A] (a : A) (n : ℕ) : ↑(n •ℕ a) = n •ℕ ↑a :=
  add_monoid_hom.map_nsmul (add_monoid_hom.mk coe with_bot.coe_zero with_bot.coe_add) a n

theorem nsmul_eq_mul' {R : Type u₁} [semiring R] (a : R) (n : ℕ) : n •ℕ a = a * ↑n := sorry

@[simp] theorem nsmul_eq_mul {R : Type u₁} [semiring R] (n : ℕ) (a : R) : n •ℕ a = ↑n * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n •ℕ a = ↑n * a)) (nsmul_eq_mul' a n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * ↑n = ↑n * a)) (commute.eq (nat.cast_commute n a)))) (Eq.refl (a * ↑n)))

theorem mul_nsmul_left {R : Type u₁} [semiring R] (a : R) (b : R) (n : ℕ) : n •ℕ (a * b) = a * (n •ℕ b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n •ℕ (a * b) = a * (n •ℕ b))) (nsmul_eq_mul' (a * b) n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * b * ↑n = a * (n •ℕ b))) (nsmul_eq_mul' b n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * b * ↑n = a * (b * ↑n))) (mul_assoc a b ↑n))) (Eq.refl (a * (b * ↑n)))))

theorem mul_nsmul_assoc {R : Type u₁} [semiring R] (a : R) (b : R) (n : ℕ) : n •ℕ (a * b) = n •ℕ a * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n •ℕ (a * b) = n •ℕ a * b)) (nsmul_eq_mul n (a * b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n * (a * b) = n •ℕ a * b)) (nsmul_eq_mul n a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑n * (a * b) = ↑n * a * b)) (mul_assoc (↑n) a b))) (Eq.refl (↑n * (a * b)))))

@[simp] theorem nat.cast_pow {R : Type u₁} [semiring R] (n : ℕ) (m : ℕ) : ↑(n ^ m) = ↑n ^ m := sorry

@[simp] theorem int.coe_nat_pow (n : ℕ) (m : ℕ) : ↑(n ^ m) = ↑n ^ m := sorry

theorem int.nat_abs_pow (n : ℤ) (k : ℕ) : int.nat_abs (n ^ k) = int.nat_abs n ^ k := sorry

-- The next four lemmas allow us to replace multiplication by a numeral with a `gsmul` expression.

-- They are used by the `noncomm_ring` tactic, to normalise expressions before passing to `abel`.

theorem bit0_mul {R : Type u₁} [ring R] {n : R} {r : R} : bit0 n * r = bit0 1 •ℤ (n * r) := sorry

theorem mul_bit0 {R : Type u₁} [ring R] {n : R} {r : R} : r * bit0 n = bit0 1 •ℤ (r * n) := sorry

theorem bit1_mul {R : Type u₁} [ring R] {n : R} {r : R} : bit1 n * r = bit0 1 •ℤ (n * r) + r := sorry

theorem mul_bit1 {R : Type u₁} [ring R] {n : R} {r : R} : r * bit1 n = bit0 1 •ℤ (r * n) + r := sorry

@[simp] theorem gsmul_eq_mul {R : Type u₁} [ring R] (a : R) (n : ℤ) : n •ℤ a = ↑n * a := sorry

theorem gsmul_eq_mul' {R : Type u₁} [ring R] (a : R) (n : ℤ) : n •ℤ a = a * ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n •ℤ a = a * ↑n)) (gsmul_eq_mul a n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n * a = a * ↑n)) (commute.eq (int.cast_commute n a)))) (Eq.refl (a * ↑n)))

theorem mul_gsmul_left {R : Type u₁} [ring R] (a : R) (b : R) (n : ℤ) : n •ℤ (a * b) = a * (n •ℤ b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n •ℤ (a * b) = a * (n •ℤ b))) (gsmul_eq_mul' (a * b) n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * b * ↑n = a * (n •ℤ b))) (gsmul_eq_mul' b n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * b * ↑n = a * (b * ↑n))) (mul_assoc a b ↑n))) (Eq.refl (a * (b * ↑n)))))

theorem mul_gsmul_assoc {R : Type u₁} [ring R] (a : R) (b : R) (n : ℤ) : n •ℤ (a * b) = n •ℤ a * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n •ℤ (a * b) = n •ℤ a * b)) (gsmul_eq_mul (a * b) n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n * (a * b) = n •ℤ a * b)) (gsmul_eq_mul a n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑n * (a * b) = ↑n * a * b)) (mul_assoc (↑n) a b))) (Eq.refl (↑n * (a * b)))))

@[simp] theorem gsmul_int_int (a : ℤ) (b : ℤ) : a •ℤ b = a * b := sorry

theorem gsmul_int_one (n : ℤ) : n •ℤ 1 = n := sorry

@[simp] theorem int.cast_pow {R : Type u₁} [ring R] (n : ℤ) (m : ℕ) : ↑(n ^ m) = ↑n ^ m := sorry

theorem neg_one_pow_eq_pow_mod_two {R : Type u₁} [ring R] {n : ℕ} : (-1) ^ n = (-1) ^ (n % bit0 1) := sorry

/-- Bernoulli's inequality. This version works for semirings but requires
additional hypotheses `0 ≤ a * a` and `0 ≤ (1 + a) * (1 + a)`. -/
theorem one_add_mul_le_pow' {R : Type u₁} [ordered_semiring R] {a : R} (Hsqr : 0 ≤ a * a) (Hsqr' : 0 ≤ (1 + a) * (1 + a)) (H : 0 ≤ bit0 1 + a) (n : ℕ) : 1 + ↑n * a ≤ (1 + a) ^ n := sorry

theorem pow_lt_pow_of_lt_one {R : Type u₁} [ordered_semiring R] {a : R} (h : 0 < a) (ha : a < 1) {i : ℕ} {j : ℕ} (hij : i < j) : a ^ j < a ^ i := sorry

theorem pow_lt_pow_iff_of_lt_one {R : Type u₁} [ordered_semiring R] {a : R} {n : ℕ} {m : ℕ} (hpos : 0 < a) (h : a < 1) : a ^ m < a ^ n ↔ n < m :=
  strict_mono.lt_iff_lt fun (m n : order_dual ℕ) => pow_lt_pow_of_lt_one hpos h

theorem pow_le_pow_of_le_one {R : Type u₁} [ordered_semiring R] {a : R} (h : 0 ≤ a) (ha : a ≤ 1) {i : ℕ} {j : ℕ} (hij : i ≤ j) : a ^ j ≤ a ^ i := sorry

theorem pow_le_one {R : Type u₁} [ordered_semiring R] {x : R} (n : ℕ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ^ n ≤ 1 := sorry

theorem sign_cases_of_C_mul_pow_nonneg {R : Type u₁} [linear_ordered_semiring R] {C : R} {r : R} (h : ∀ (n : ℕ), 0 ≤ C * r ^ n) : C = 0 ∨ 0 < C ∧ 0 ≤ r := sorry

@[simp] theorem abs_pow {R : Type u₁} [linear_ordered_ring R] (a : R) (n : ℕ) : abs (a ^ n) = abs a ^ n :=
  monoid_hom.map_pow (monoid_with_zero_hom.to_monoid_hom abs_hom) a n

@[simp] theorem pow_bit1_neg_iff {R : Type u₁} [linear_ordered_ring R] {a : R} {n : ℕ} : a ^ bit1 n < 0 ↔ a < 0 :=
  { mp := fun (h : a ^ bit1 n < 0) => iff.mp not_le fun (h' : 0 ≤ a) => iff.mpr not_le h (pow_nonneg h' (bit1 n)),
    mpr := fun (h : a < 0) => mul_neg_of_neg_of_pos h (pow_bit0_pos (has_lt.lt.ne h) n) }

@[simp] theorem pow_bit1_nonneg_iff {R : Type u₁} [linear_ordered_ring R] {a : R} {n : ℕ} : 0 ≤ a ^ bit1 n ↔ 0 ≤ a :=
  iff.mpr le_iff_le_iff_lt_iff_lt pow_bit1_neg_iff

@[simp] theorem pow_bit1_nonpos_iff {R : Type u₁} [linear_ordered_ring R] {a : R} {n : ℕ} : a ^ bit1 n ≤ 0 ↔ a ≤ 0 := sorry

@[simp] theorem pow_bit1_pos_iff {R : Type u₁} [linear_ordered_ring R] {a : R} {n : ℕ} : 0 < a ^ bit1 n ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le pow_bit1_nonpos_iff

theorem strict_mono_pow_bit1 {R : Type u₁} [linear_ordered_ring R] (n : ℕ) : strict_mono fun (a : R) => a ^ bit1 n := sorry

/-- Bernoulli's inequality for `n : ℕ`, `-2 ≤ a`. -/
theorem one_add_mul_le_pow {R : Type u₁} [linear_ordered_ring R] {a : R} (H : -bit0 1 ≤ a) (n : ℕ) : 1 + ↑n * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow' (mul_self_nonneg a) (mul_self_nonneg (1 + a)) (iff.mp neg_le_iff_add_nonneg' H) n

/-- Bernoulli's inequality reformulated to estimate `a^n`. -/
theorem one_add_mul_sub_le_pow {R : Type u₁} [linear_ordered_ring R] {a : R} (H : -1 ≤ a) (n : ℕ) : 1 + ↑n * (a - 1) ≤ a ^ n := sorry

/-- Bernoulli's inequality reformulated to estimate `(n : K)`. -/
theorem nat.cast_le_pow_sub_div_sub {K : Type u_1} [linear_ordered_field K] {a : K} (H : 1 < a) (n : ℕ) : ↑n ≤ (a ^ n - 1) / (a - 1) :=
  iff.mpr (le_div_iff (iff.mpr sub_pos H))
    (le_sub_left_of_add_le (one_add_mul_sub_le_pow (has_le.le.trans (neg_le_self zero_le_one) (has_lt.lt.le H)) n))

/-- For any `a > 1` and a natural `n` we have `n ≤ a ^ n / (a - 1)`. See also
`nat.cast_le_pow_sub_div_sub` for a stronger inequality with `a ^ n - 1` in the numerator. -/
theorem nat.cast_le_pow_div_sub {K : Type u_1} [linear_ordered_field K] {a : K} (H : 1 < a) (n : ℕ) : ↑n ≤ a ^ n / (a - 1) :=
  has_le.le.trans (nat.cast_le_pow_sub_div_sub H n)
    (div_le_div_of_le (iff.mpr sub_nonneg (has_lt.lt.le H)) (sub_le_self (a ^ n) zero_le_one))

namespace int


theorem units_pow_two (u : units ℤ) : u ^ bit0 1 = 1 :=
  Eq.symm (pow_two u) ▸ units_mul_self u

theorem units_pow_eq_pow_mod_two (u : units ℤ) (n : ℕ) : u ^ n = u ^ (n % bit0 1) := sorry

@[simp] theorem nat_abs_pow_two (x : ℤ) : ↑(nat_abs x) ^ bit0 1 = x ^ bit0 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(nat_abs x) ^ bit0 1 = x ^ bit0 1)) (pow_two ↑(nat_abs x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(nat_abs x) * ↑(nat_abs x) = x ^ bit0 1)) (nat_abs_mul_self' x)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (x * x = x ^ bit0 1)) (pow_two x))) (Eq.refl (x * x))))

theorem abs_le_self_pow_two (a : ℤ) : ↑(nat_abs a) ≤ a ^ bit0 1 := sorry

theorem le_self_pow_two (b : ℤ) : b ≤ b ^ bit0 1 :=
  le_trans le_nat_abs (abs_le_self_pow_two b)

end int


/-- Monoid homomorphisms from `multiplicative ℕ` are defined by the image
of `multiplicative.of_add 1`. -/
def powers_hom (M : Type u) [monoid M] : M ≃ (multiplicative ℕ →* M) :=
  equiv.mk
    (fun (x : M) => monoid_hom.mk (fun (n : multiplicative ℕ) => x ^ coe_fn multiplicative.to_add n) (pow_zero x) sorry)
    (fun (f : multiplicative ℕ →* M) => coe_fn f (coe_fn multiplicative.of_add 1)) pow_one sorry

/-- Monoid homomorphisms from `multiplicative ℤ` are defined by the image
of `multiplicative.of_add 1`. -/
def gpowers_hom (G : Type w) [group G] : G ≃ (multiplicative ℤ →* G) :=
  equiv.mk
    (fun (x : G) => monoid_hom.mk (fun (n : multiplicative ℤ) => x ^ coe_fn multiplicative.to_add n) (gpow_zero x) sorry)
    (fun (f : multiplicative ℤ →* G) => coe_fn f (coe_fn multiplicative.of_add 1)) gpow_one sorry

/-- Additive homomorphisms from `ℕ` are defined by the image of `1`. -/
def multiples_hom (A : Type y) [add_monoid A] : A ≃ (ℕ →+ A) :=
  equiv.mk (fun (x : A) => add_monoid_hom.mk (fun (n : ℕ) => n •ℕ x) (zero_nsmul x) sorry)
    (fun (f : ℕ →+ A) => coe_fn f 1) one_nsmul sorry

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
def gmultiples_hom (A : Type y) [add_group A] : A ≃ (ℤ →+ A) :=
  equiv.mk (fun (x : A) => add_monoid_hom.mk (fun (n : ℤ) => n •ℤ x) (zero_gsmul x) sorry)
    (fun (f : ℤ →+ A) => coe_fn f 1) one_gsmul sorry

@[simp] theorem powers_hom_apply {M : Type u} [monoid M] (x : M) (n : multiplicative ℕ) : coe_fn (coe_fn (powers_hom M) x) n = x ^ coe_fn multiplicative.to_add n :=
  rfl

@[simp] theorem powers_hom_symm_apply {M : Type u} [monoid M] (f : multiplicative ℕ →* M) : coe_fn (equiv.symm (powers_hom M)) f = coe_fn f (coe_fn multiplicative.of_add 1) :=
  rfl

@[simp] theorem gpowers_hom_apply {G : Type w} [group G] (x : G) (n : multiplicative ℤ) : coe_fn (coe_fn (gpowers_hom G) x) n = x ^ coe_fn multiplicative.to_add n :=
  rfl

@[simp] theorem gpowers_hom_symm_apply {G : Type w} [group G] (f : multiplicative ℤ →* G) : coe_fn (equiv.symm (gpowers_hom G)) f = coe_fn f (coe_fn multiplicative.of_add 1) :=
  rfl

@[simp] theorem multiples_hom_apply {A : Type y} [add_monoid A] (x : A) (n : ℕ) : coe_fn (coe_fn (multiples_hom A) x) n = n •ℕ x :=
  rfl

@[simp] theorem multiples_hom_symm_apply {A : Type y} [add_monoid A] (f : ℕ →+ A) : coe_fn (equiv.symm (multiples_hom A)) f = coe_fn f 1 :=
  rfl

@[simp] theorem gmultiples_hom_apply {A : Type y} [add_group A] (x : A) (n : ℤ) : coe_fn (coe_fn (gmultiples_hom A) x) n = n •ℤ x :=
  rfl

@[simp] theorem gmultiples_hom_symm_apply {A : Type y} [add_group A] (f : ℤ →+ A) : coe_fn (equiv.symm (gmultiples_hom A)) f = coe_fn f 1 :=
  rfl

theorem monoid_hom.apply_mnat {M : Type u} [monoid M] (f : multiplicative ℕ →* M) (n : multiplicative ℕ) : coe_fn f n = coe_fn f (coe_fn multiplicative.of_add 1) ^ coe_fn multiplicative.to_add n := sorry

theorem monoid_hom.ext_mnat {M : Type u} [monoid M] {f : multiplicative ℕ →* M} {g : multiplicative ℕ →* M} (h : coe_fn f (coe_fn multiplicative.of_add 1) = coe_fn g (coe_fn multiplicative.of_add 1)) : f = g := sorry

theorem monoid_hom.apply_mint {M : Type u} [group M] (f : multiplicative ℤ →* M) (n : multiplicative ℤ) : coe_fn f n = coe_fn f (coe_fn multiplicative.of_add 1) ^ coe_fn multiplicative.to_add n := sorry

theorem monoid_hom.ext_mint {M : Type u} [group M] {f : multiplicative ℤ →* M} {g : multiplicative ℤ →* M} (h : coe_fn f (coe_fn multiplicative.of_add 1) = coe_fn g (coe_fn multiplicative.of_add 1)) : f = g := sorry

theorem add_monoid_hom.apply_nat {M : Type u} [add_monoid M] (f : ℕ →+ M) (n : ℕ) : coe_fn f n = n •ℕ coe_fn f 1 := sorry

/-! `add_monoid_hom.ext_nat` is defined in `data.nat.cast` -/

theorem add_monoid_hom.apply_int {M : Type u} [add_group M] (f : ℤ →+ M) (n : ℤ) : coe_fn f n = n •ℤ coe_fn f 1 := sorry

/-! `add_monoid_hom.ext_int` is defined in `data.int.cast` -/

/-- If `M` is commutative, `powers_hom` is a multiplicative equivalence. -/
def powers_mul_hom (M : Type u) [comm_monoid M] : M ≃* (multiplicative ℕ →* M) :=
  mul_equiv.mk (equiv.to_fun (powers_hom M)) (equiv.inv_fun (powers_hom M)) sorry sorry sorry

/-- If `M` is commutative, `gpowers_hom` is a multiplicative equivalence. -/
def gpowers_mul_hom (G : Type w) [comm_group G] : G ≃* (multiplicative ℤ →* G) :=
  mul_equiv.mk (equiv.to_fun (gpowers_hom G)) (equiv.inv_fun (gpowers_hom G)) sorry sorry sorry

/-- If `M` is commutative, `multiples_hom` is an additive equivalence. -/
def multiples_add_hom (A : Type y) [add_comm_monoid A] : A ≃+ (ℕ →+ A) :=
  add_equiv.mk (equiv.to_fun (multiples_hom A)) (equiv.inv_fun (multiples_hom A)) sorry sorry sorry

/-- If `M` is commutative, `gmultiples_hom` is an additive equivalence. -/
def gmultiples_add_hom (A : Type y) [add_comm_group A] : A ≃+ (ℤ →+ A) :=
  add_equiv.mk (equiv.to_fun (gmultiples_hom A)) (equiv.inv_fun (gmultiples_hom A)) sorry sorry sorry

@[simp] theorem powers_mul_hom_apply {M : Type u} [comm_monoid M] (x : M) (n : multiplicative ℕ) : coe_fn (coe_fn (powers_mul_hom M) x) n = x ^ coe_fn multiplicative.to_add n :=
  rfl

@[simp] theorem powers_mul_hom_symm_apply {M : Type u} [comm_monoid M] (f : multiplicative ℕ →* M) : coe_fn (mul_equiv.symm (powers_mul_hom M)) f = coe_fn f (coe_fn multiplicative.of_add 1) :=
  rfl

@[simp] theorem gpowers_mul_hom_apply {G : Type w} [comm_group G] (x : G) (n : multiplicative ℤ) : coe_fn (coe_fn (gpowers_mul_hom G) x) n = x ^ coe_fn multiplicative.to_add n :=
  rfl

@[simp] theorem gpowers_mul_hom_symm_apply {G : Type w} [comm_group G] (f : multiplicative ℤ →* G) : coe_fn (mul_equiv.symm (gpowers_mul_hom G)) f = coe_fn f (coe_fn multiplicative.of_add 1) :=
  rfl

@[simp] theorem multiples_add_hom_apply {A : Type y} [add_comm_monoid A] (x : A) (n : ℕ) : coe_fn (coe_fn (multiples_add_hom A) x) n = n •ℕ x :=
  rfl

@[simp] theorem multiples_add_hom_symm_apply {A : Type y} [add_comm_monoid A] (f : ℕ →+ A) : coe_fn (add_equiv.symm (multiples_add_hom A)) f = coe_fn f 1 :=
  rfl

@[simp] theorem gmultiples_add_hom_apply {A : Type y} [add_comm_group A] (x : A) (n : ℤ) : coe_fn (coe_fn (gmultiples_add_hom A) x) n = n •ℤ x :=
  rfl

@[simp] theorem gmultiples_add_hom_symm_apply {A : Type y} [add_comm_group A] (f : ℤ →+ A) : coe_fn (add_equiv.symm (gmultiples_add_hom A)) f = coe_fn f 1 :=
  rfl

/-!
### Commutativity (again)

Facts about `semiconj_by` and `commute` that require `gpow` or `gsmul`, or the fact that integer
multiplication equals semiring multiplication.
-/

namespace semiconj_by


@[simp] theorem cast_nat_mul_right {R : Type u₁} [semiring R] {a : R} {x : R} {y : R} (h : semiconj_by a x y) (n : ℕ) : semiconj_by a (↑n * x) (↑n * y) :=
  mul_right (nat.commute_cast a n) h

@[simp] theorem cast_nat_mul_left {R : Type u₁} [semiring R] {a : R} {x : R} {y : R} (h : semiconj_by a x y) (n : ℕ) : semiconj_by (↑n * a) x y :=
  mul_left (nat.cast_commute n y) h

@[simp] theorem cast_nat_mul_cast_nat_mul {R : Type u₁} [semiring R] {a : R} {x : R} {y : R} (h : semiconj_by a x y) (m : ℕ) (n : ℕ) : semiconj_by (↑m * a) (↑n * x) (↑n * y) :=
  cast_nat_mul_right (cast_nat_mul_left h m) n

@[simp] theorem units_gpow_right {M : Type u} [monoid M] {a : M} {x : units M} {y : units M} (h : semiconj_by a ↑x ↑y) (m : ℤ) : semiconj_by a ↑(x ^ m) ↑(y ^ m) := sorry

@[simp] theorem cast_int_mul_right {R : Type u₁} [ring R] {a : R} {x : R} {y : R} (h : semiconj_by a x y) (m : ℤ) : semiconj_by a (↑m * x) (↑m * y) :=
  mul_right (int.commute_cast a m) h

@[simp] theorem cast_int_mul_left {R : Type u₁} [ring R] {a : R} {x : R} {y : R} (h : semiconj_by a x y) (m : ℤ) : semiconj_by (↑m * a) x y :=
  mul_left (int.cast_commute m y) h

@[simp] theorem cast_int_mul_cast_int_mul {R : Type u₁} [ring R] {a : R} {x : R} {y : R} (h : semiconj_by a x y) (m : ℤ) (n : ℤ) : semiconj_by (↑m * a) (↑n * x) (↑n * y) :=
  cast_int_mul_right (cast_int_mul_left h m) n

end semiconj_by


namespace commute


@[simp] theorem cast_nat_mul_right {R : Type u₁} [semiring R] {a : R} {b : R} (h : commute a b) (n : ℕ) : commute a (↑n * b) :=
  semiconj_by.cast_nat_mul_right h n

@[simp] theorem cast_nat_mul_left {R : Type u₁} [semiring R] {a : R} {b : R} (h : commute a b) (n : ℕ) : commute (↑n * a) b :=
  semiconj_by.cast_nat_mul_left h n

@[simp] theorem cast_nat_mul_cast_nat_mul {R : Type u₁} [semiring R] {a : R} {b : R} (h : commute a b) (m : ℕ) (n : ℕ) : commute (↑m * a) (↑n * b) :=
  semiconj_by.cast_nat_mul_cast_nat_mul h m n

@[simp] theorem self_cast_nat_mul {R : Type u₁} [semiring R] {a : R} (n : ℕ) : commute a (↑n * a) :=
  cast_nat_mul_right (commute.refl a) n

@[simp] theorem cast_nat_mul_self {R : Type u₁} [semiring R] {a : R} (n : ℕ) : commute (↑n * a) a :=
  cast_nat_mul_left (commute.refl a) n

@[simp] theorem self_cast_nat_mul_cast_nat_mul {R : Type u₁} [semiring R] {a : R} (m : ℕ) (n : ℕ) : commute (↑m * a) (↑n * a) :=
  cast_nat_mul_cast_nat_mul (commute.refl a) m n

@[simp] theorem units_gpow_right {M : Type u} [monoid M] {a : M} {u : units M} (h : commute a ↑u) (m : ℤ) : commute a ↑(u ^ m) :=
  semiconj_by.units_gpow_right h m

@[simp] theorem units_gpow_left {M : Type u} [monoid M] {u : units M} {a : M} (h : commute (↑u) a) (m : ℤ) : commute (↑(u ^ m)) a :=
  commute.symm (units_gpow_right (commute.symm h) m)

@[simp] theorem cast_int_mul_right {R : Type u₁} [ring R] {a : R} {b : R} (h : commute a b) (m : ℤ) : commute a (↑m * b) :=
  semiconj_by.cast_int_mul_right h m

@[simp] theorem cast_int_mul_left {R : Type u₁} [ring R] {a : R} {b : R} (h : commute a b) (m : ℤ) : commute (↑m * a) b :=
  semiconj_by.cast_int_mul_left h m

theorem cast_int_mul_cast_int_mul {R : Type u₁} [ring R] {a : R} {b : R} (h : commute a b) (m : ℤ) (n : ℤ) : commute (↑m * a) (↑n * b) :=
  semiconj_by.cast_int_mul_cast_int_mul h m n

@[simp] theorem self_cast_int_mul {R : Type u₁} [ring R] (a : R) (n : ℤ) : commute a (↑n * a) :=
  cast_int_mul_right (commute.refl a) n

@[simp] theorem cast_int_mul_self {R : Type u₁} [ring R] (a : R) (n : ℤ) : commute (↑n * a) a :=
  cast_int_mul_left (commute.refl a) n

theorem self_cast_int_mul_cast_int_mul {R : Type u₁} [ring R] (a : R) (m : ℤ) (n : ℤ) : commute (↑m * a) (↑n * a) :=
  cast_int_mul_cast_int_mul (commute.refl a) m n

end commute


@[simp] theorem nat.to_add_pow (a : multiplicative ℕ) (b : ℕ) : coe_fn multiplicative.to_add (a ^ b) = coe_fn multiplicative.to_add a * b := sorry

@[simp] theorem nat.of_add_mul (a : ℕ) (b : ℕ) : coe_fn multiplicative.of_add (a * b) = coe_fn multiplicative.of_add a ^ b :=
  Eq.symm (nat.to_add_pow a b)

@[simp] theorem int.to_add_pow (a : multiplicative ℤ) (b : ℕ) : coe_fn multiplicative.to_add (a ^ b) = coe_fn multiplicative.to_add a * ↑b := sorry

@[simp] theorem int.to_add_gpow (a : multiplicative ℤ) (b : ℤ) : coe_fn multiplicative.to_add (a ^ b) = coe_fn multiplicative.to_add a * b := sorry

@[simp] theorem int.of_add_mul (a : ℤ) (b : ℤ) : coe_fn multiplicative.of_add (a * b) = coe_fn multiplicative.of_add a ^ b :=
  Eq.symm (int.to_add_gpow a b)

namespace units


theorem conj_pow {M : Type u} [monoid M] (u : units M) (x : M) (n : ℕ) : (↑u * x * ↑(u⁻¹)) ^ n = ↑u * x ^ n * ↑(u⁻¹) :=
  Eq.symm (iff.mpr divp_eq_iff_mul_eq (Eq.symm (semiconj_by.eq (semiconj_by.pow_right (mk_semiconj_by u x) n))))

theorem conj_pow' {M : Type u} [monoid M] (u : units M) (x : M) (n : ℕ) : (↑(u⁻¹) * x * ↑u) ^ n = ↑(u⁻¹) * x ^ n * ↑u :=
  conj_pow (u⁻¹) x n

/-- Moving to the opposite monoid commutes with taking powers. -/
@[simp] theorem op_pow {M : Type u} [monoid M] (x : M) (n : ℕ) : opposite.op (x ^ n) = opposite.op x ^ n := sorry

@[simp] theorem unop_pow {M : Type u} [monoid M] (x : Mᵒᵖ) (n : ℕ) : opposite.unop (x ^ n) = opposite.unop x ^ n := sorry

