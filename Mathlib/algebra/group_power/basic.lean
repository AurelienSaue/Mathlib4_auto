/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.ordered_ring
import Mathlib.tactic.monotonicity.basic
import Mathlib.deprecated.group
import Mathlib.PostPort

universes u y v z u₁ w u₂ u_1 

namespace Mathlib

/-!
# Power operations on monoids and groups

The power operation on monoids and groups.
We separate this from group, because it depends on `ℕ`,
which in turn depends on other parts of algebra.

This module contains the definitions of `monoid.pow` and `group.pow`
and their additive counterparts `nsmul` and `gsmul`, along with a few lemmas.
Further lemmas can be found in `algebra.group_power.lemmas`.

## Notation

The class `has_pow α β` provides the notation `a^b` for powers.
We define instances of `has_pow M ℕ`, for monoids `M`, and `has_pow G ℤ` for groups `G`.

We also define infix operators `•ℕ` and `•ℤ` for scalar multiplication by a natural and an integer
numbers, respectively.

## Implementation details

We adopt the convention that `0^0 = 1`.

This module provides the instance `has_pow ℕ ℕ` (via `monoid.has_pow`)
and is imported by `data.nat.basic`, so it has to live low in the import hierarchy.
Not all of its imports are needed yet; the intent is to move more lemmas here from `.lemmas`
so that they are available in `data.nat.basic`, and the imports will be required then.
-/

/-- The power operation in a monoid. `a^n = a*a*...*a` n times. -/
def monoid.pow {M : Type u} [Mul M] [HasOne M] (a : M) : ℕ → M :=
  sorry

/-- The scalar multiplication in an additive monoid.
`n •ℕ a = a+a+...+a` n times. -/
def nsmul {A : Type y} [Add A] [HasZero A] (n : ℕ) (a : A) : A :=
  monoid.pow a n

infixl:70 " •ℕ " => Mathlib.nsmul

protected instance monoid.has_pow {M : Type u} [monoid M] : has_pow M ℕ :=
  has_pow.mk monoid.pow

@[simp] theorem monoid.pow_eq_has_pow {M : Type u} [monoid M] (a : M) (n : ℕ) : monoid.pow a n = a ^ n :=
  rfl

/-!
### Commutativity

First we prove some facts about `semiconj_by` and `commute`. They do not require any theory about
`pow` and/or `nsmul` and will be useful later in this file.
-/

namespace semiconj_by


@[simp] theorem pow_right {M : Type u} [monoid M] {a : M} {x : M} {y : M} (h : semiconj_by a x y) (n : ℕ) : semiconj_by a (x ^ n) (y ^ n) :=
  nat.rec_on n (one_right a) fun (n : ℕ) (ihn : semiconj_by a (x ^ n) (y ^ n)) => mul_right h ihn

end semiconj_by


namespace commute


@[simp] theorem pow_right {M : Type u} [monoid M] {a : M} {b : M} (h : commute a b) (n : ℕ) : commute a (b ^ n) :=
  semiconj_by.pow_right h n

@[simp] theorem pow_left {M : Type u} [monoid M] {a : M} {b : M} (h : commute a b) (n : ℕ) : commute (a ^ n) b :=
  commute.symm (pow_right (commute.symm h) n)

@[simp] theorem pow_pow {M : Type u} [monoid M] {a : M} {b : M} (h : commute a b) (m : ℕ) (n : ℕ) : commute (a ^ m) (b ^ n) :=
  pow_right (pow_left h m) n

@[simp] theorem self_pow {M : Type u} [monoid M] (a : M) (n : ℕ) : commute a (a ^ n) :=
  pow_right (commute.refl a) n

@[simp] theorem pow_self {M : Type u} [monoid M] (a : M) (n : ℕ) : commute (a ^ n) a :=
  pow_left (commute.refl a) n

@[simp] theorem pow_pow_self {M : Type u} [monoid M] (a : M) (m : ℕ) (n : ℕ) : commute (a ^ m) (a ^ n) :=
  pow_pow (commute.refl a) m n

end commute


@[simp] theorem pow_zero {M : Type u} [monoid M] (a : M) : a ^ 0 = 1 :=
  rfl

@[simp] theorem zero_nsmul {A : Type y} [add_monoid A] (a : A) : 0 •ℕ a = 0 :=
  rfl

theorem pow_succ {M : Type u} [monoid M] (a : M) (n : ℕ) : a ^ (n + 1) = a * a ^ n :=
  rfl

theorem succ_nsmul {A : Type y} [add_monoid A] (a : A) (n : ℕ) : (n + 1) •ℕ a = a + n •ℕ a :=
  rfl

theorem pow_two {M : Type u} [monoid M] (a : M) : a ^ bit0 1 = a * a :=
  (fun (this : a * (a * 1) = a * a) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (a * 1) = a * a)) (mul_one a))) (Eq.refl (a * a)))

theorem two_nsmul {A : Type y} [add_monoid A] (a : A) : bit0 1 •ℕ a = a + a :=
  pow_two a

theorem pow_mul_comm' {M : Type u} [monoid M] (a : M) (n : ℕ) : a ^ n * a = a * a ^ n :=
  commute.pow_self a n

theorem nsmul_add_comm' {A : Type y} [add_monoid A] (a : A) (n : ℕ) : n •ℕ a + a = a + n •ℕ a :=
  pow_mul_comm'

theorem pow_succ' {M : Type u} [monoid M] (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (n + 1) = a ^ n * a)) (pow_succ a n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * a ^ n = a ^ n * a)) (pow_mul_comm' a n))) (Eq.refl (a * a ^ n)))

theorem succ_nsmul' {A : Type y} [add_monoid A] (a : A) (n : ℕ) : (n + 1) •ℕ a = n •ℕ a + a :=
  pow_succ' a n

theorem pow_add {M : Type u} [monoid M] (a : M) (m : ℕ) (n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := sorry

theorem add_nsmul {A : Type y} [add_monoid A] (a : A) (m : ℕ) (n : ℕ) : (m + n) •ℕ a = m •ℕ a + n •ℕ a :=
  pow_add

@[simp] theorem pow_one {M : Type u} [monoid M] (a : M) : a ^ 1 = a :=
  mul_one a

@[simp] theorem one_nsmul {A : Type y} [add_monoid A] (a : A) : 1 •ℕ a = a :=
  add_zero (coe_fn multiplicative.to_add a)

@[simp] theorem pow_ite {M : Type u} [monoid M] (P : Prop) [Decidable P] (a : M) (b : ℕ) (c : ℕ) : a ^ ite P b c = ite P (a ^ b) (a ^ c) := sorry

@[simp] theorem ite_pow {M : Type u} [monoid M] (P : Prop) [Decidable P] (a : M) (b : M) (c : ℕ) : ite P a b ^ c = ite P (a ^ c) (b ^ c) := sorry

@[simp] theorem pow_boole {M : Type u} [monoid M] (P : Prop) [Decidable P] (a : M) : a ^ ite P 1 0 = ite P a 1 := sorry

@[simp] theorem one_pow {M : Type u} [monoid M] (n : ℕ) : 1 ^ n = 1 := sorry

@[simp] theorem nsmul_zero {A : Type y} [add_monoid A] (n : ℕ) : n •ℕ 0 = 0 := sorry

theorem pow_mul {M : Type u} [monoid M] (a : M) (m : ℕ) (n : ℕ) : a ^ (m * n) = (a ^ m) ^ n := sorry

theorem mul_nsmul' {A : Type y} [add_monoid A] (a : A) (m : ℕ) (n : ℕ) : m * n •ℕ a = n •ℕ (m •ℕ a) :=
  pow_mul

theorem pow_mul' {M : Type u} [monoid M] (a : M) (m : ℕ) (n : ℕ) : a ^ (m * n) = (a ^ n) ^ m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (m * n) = (a ^ n) ^ m)) (nat.mul_comm m n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (n * m) = (a ^ n) ^ m)) (pow_mul a n m))) (Eq.refl ((a ^ n) ^ m)))

theorem mul_nsmul {A : Type y} [add_monoid A] (a : A) (m : ℕ) (n : ℕ) : m * n •ℕ a = m •ℕ (n •ℕ a) :=
  pow_mul' a m n

theorem pow_mul_pow_sub {M : Type u} [monoid M] (a : M) {m : ℕ} {n : ℕ} (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ m * a ^ (n - m) = a ^ n)) (Eq.symm (pow_add a m (n - m)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (m + (n - m)) = a ^ n)) (nat.add_comm m (n - m))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (n - m + m) = a ^ n)) (nat.sub_add_cancel h))) (Eq.refl (a ^ n))))

theorem nsmul_add_sub_nsmul {A : Type y} [add_monoid A] (a : A) {m : ℕ} {n : ℕ} (h : m ≤ n) : m •ℕ a + (n - m) •ℕ a = n •ℕ a :=
  pow_mul_pow_sub a h

theorem pow_sub_mul_pow {M : Type u} [monoid M] (a : M) {m : ℕ} {n : ℕ} (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (n - m) * a ^ m = a ^ n)) (Eq.symm (pow_add a (n - m) m))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (n - m + m) = a ^ n)) (nat.sub_add_cancel h))) (Eq.refl (a ^ n)))

theorem sub_nsmul_nsmul_add {A : Type y} [add_monoid A] (a : A) {m : ℕ} {n : ℕ} (h : m ≤ n) : (n - m) •ℕ a + m •ℕ a = n •ℕ a :=
  pow_sub_mul_pow a h

theorem pow_bit0 {M : Type u} [monoid M] (a : M) (n : ℕ) : a ^ bit0 n = a ^ n * a ^ n :=
  pow_add a n n

theorem bit0_nsmul {A : Type y} [add_monoid A] (a : A) (n : ℕ) : bit0 n •ℕ a = n •ℕ a + n •ℕ a :=
  add_nsmul a n n

theorem pow_bit1 {M : Type u} [monoid M] (a : M) (n : ℕ) : a ^ bit1 n = a ^ n * a ^ n * a := sorry

theorem bit1_nsmul {A : Type y} [add_monoid A] (a : A) (n : ℕ) : bit1 n •ℕ a = n •ℕ a + n •ℕ a + a :=
  pow_bit1

theorem pow_mul_comm {M : Type u} [monoid M] (a : M) (m : ℕ) (n : ℕ) : a ^ m * a ^ n = a ^ n * a ^ m :=
  commute.pow_pow_self a m n

theorem nsmul_add_comm {A : Type y} [add_monoid A] (a : A) (m : ℕ) (n : ℕ) : m •ℕ a + n •ℕ a = n •ℕ a + m •ℕ a :=
  pow_mul_comm

@[simp] theorem monoid_hom.map_pow {M : Type u} {N : Type v} [monoid M] [monoid N] (f : M →* N) (a : M) (n : ℕ) : coe_fn f (a ^ n) = coe_fn f a ^ n := sorry

@[simp] theorem add_monoid_hom.map_nsmul {A : Type y} {B : Type z} [add_monoid A] [add_monoid B] (f : A →+ B) (a : A) (n : ℕ) : coe_fn f (n •ℕ a) = n •ℕ coe_fn f a :=
  monoid_hom.map_pow (coe_fn add_monoid_hom.to_multiplicative f) a n

theorem is_monoid_hom.map_pow {M : Type u} {N : Type v} [monoid M] [monoid N] (f : M → N) [is_monoid_hom f] (a : M) (n : ℕ) : f (a ^ n) = f a ^ n :=
  monoid_hom.map_pow (monoid_hom.of f) a

theorem is_add_monoid_hom.map_nsmul {A : Type y} {B : Type z} [add_monoid A] [add_monoid B] (f : A → B) [is_add_monoid_hom f] (a : A) (n : ℕ) : f (n •ℕ a) = n •ℕ f a :=
  add_monoid_hom.map_nsmul (add_monoid_hom.of f) a n

theorem commute.mul_pow {M : Type u} [monoid M] {a : M} {b : M} (h : commute a b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := sorry

theorem neg_pow {R : Type u₁} [ring R] (a : R) (n : ℕ) : (-a) ^ n = (-1) ^ n * a ^ n :=
  neg_one_mul a ▸ commute.mul_pow (commute.neg_one_left a) n

theorem pow_bit0' {M : Type u} [monoid M] (a : M) (n : ℕ) : a ^ bit0 n = (a * a) ^ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ bit0 n = (a * a) ^ n)) (pow_bit0 a n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ n * a ^ n = (a * a) ^ n)) (commute.mul_pow (commute.refl a) n)))
      (Eq.refl (a ^ n * a ^ n)))

theorem bit0_nsmul' {A : Type y} [add_monoid A] (a : A) (n : ℕ) : bit0 n •ℕ a = n •ℕ (a + a) :=
  pow_bit0' a n

theorem pow_bit1' {M : Type u} [monoid M] (a : M) (n : ℕ) : a ^ bit1 n = (a * a) ^ n * a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ bit1 n = (a * a) ^ n * a)) (bit1.equations._eqn_1 n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (bit0 n + 1) = (a * a) ^ n * a)) (pow_succ' a (bit0 n))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ bit0 n * a = (a * a) ^ n * a)) (pow_bit0' a n))) (Eq.refl ((a * a) ^ n * a))))

theorem bit1_nsmul' {A : Type y} [add_monoid A] (a : A) (n : ℕ) : bit1 n •ℕ a = n •ℕ (a + a) + a :=
  pow_bit1'

@[simp] theorem neg_pow_bit0 {R : Type u₁} [ring R] (a : R) (n : ℕ) : (-a) ^ bit0 n = a ^ bit0 n :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((-a) ^ bit0 n = a ^ bit0 n)) (pow_bit0' (-a) n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((-a * -a) ^ n = a ^ bit0 n)) (neg_mul_neg a a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl ((a * a) ^ n = a ^ bit0 n)) (pow_bit0' a n))) (Eq.refl ((a * a) ^ n))))

@[simp] theorem neg_pow_bit1 {R : Type u₁} [ring R] (a : R) (n : ℕ) : (-a) ^ bit1 n = -a ^ bit1 n := sorry

/-!
### Commutative (additive) monoid
-/

theorem mul_pow {M : Type u} [comm_monoid M] (a : M) (b : M) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
  commute.mul_pow (commute.all a b) n

theorem nsmul_add {A : Type y} [add_comm_monoid A] (a : A) (b : A) (n : ℕ) : n •ℕ (a + b) = n •ℕ a + n •ℕ b :=
  mul_pow

protected instance pow.is_monoid_hom {M : Type u} [comm_monoid M] (n : ℕ) : is_monoid_hom fun (_x : M) => _x ^ n :=
  is_monoid_hom.mk (one_pow n)

protected instance nsmul.is_add_monoid_hom {A : Type y} [add_comm_monoid A] (n : ℕ) : is_add_monoid_hom (nsmul n) :=
  is_add_monoid_hom.mk (nsmul_zero n)

theorem dvd_pow {M : Type u} [comm_monoid M] {x : M} {y : M} {n : ℕ} (hxy : x ∣ y) (hn : n ≠ 0) : x ∣ y ^ n := sorry

/--
The power operation in a group. This extends `monoid.pow` to negative integers
with the definition `a^(-n) = (a^n)⁻¹`.
-/
def gpow {G : Type w} [group G] (a : G) : ℤ → G :=
  sorry

/--
The scalar multiplication by integers on an additive group.
This extends `nsmul` to negative integers
with the definition `(-n) •ℤ a = -(n •ℕ a)`.
-/
def gsmul {A : Type y} [add_group A] (n : ℤ) (a : A) : A :=
  gpow a n

protected instance group.has_pow {G : Type w} [group G] : has_pow G ℤ :=
  has_pow.mk gpow

infixl:70 " •ℤ " => Mathlib.gsmul

@[simp] theorem group.gpow_eq_has_pow {G : Type w} [group G] (a : G) (n : ℤ) : gpow a n = a ^ n :=
  rfl

@[simp] theorem inv_pow {G : Type w} [group G] (a : G) (n : ℕ) : a⁻¹ ^ n = (a ^ n⁻¹) := sorry

@[simp] theorem neg_nsmul {A : Type y} [add_group A] (a : A) (n : ℕ) : n •ℕ -a = -(n •ℕ a) :=
  inv_pow

theorem pow_sub {G : Type w} [group G] (a : G) {m : ℕ} {n : ℕ} (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n⁻¹) := sorry

theorem nsmul_sub {A : Type y} [add_group A] (a : A) {m : ℕ} {n : ℕ} : n ≤ m → (m - n) •ℕ a = m •ℕ a - n •ℕ a := sorry

theorem pow_inv_comm {G : Type w} [group G] (a : G) (m : ℕ) (n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  commute.pow_pow (commute.inv_left (commute.refl a)) m n

theorem nsmul_neg_comm {A : Type y} [add_group A] (a : A) (m : ℕ) (n : ℕ) : m •ℕ -a + n •ℕ a = n •ℕ a + m •ℕ -a :=
  pow_inv_comm

@[simp] theorem gpow_coe_nat {G : Type w} [group G] (a : G) (n : ℕ) : a ^ ↑n = a ^ n :=
  rfl

@[simp] theorem gsmul_coe_nat {A : Type y} [add_group A] (a : A) (n : ℕ) : ↑n •ℤ a = n •ℕ a :=
  rfl

theorem gpow_of_nat {G : Type w} [group G] (a : G) (n : ℕ) : a ^ Int.ofNat n = a ^ n :=
  rfl

theorem gsmul_of_nat {A : Type y} [add_group A] (a : A) (n : ℕ) : Int.ofNat n •ℤ a = n •ℕ a :=
  rfl

@[simp] theorem gpow_neg_succ_of_nat {G : Type w} [group G] (a : G) (n : ℕ) : a ^ Int.negSucc n = (a ^ Nat.succ n⁻¹) :=
  rfl

@[simp] theorem gsmul_neg_succ_of_nat {A : Type y} [add_group A] (a : A) (n : ℕ) : Int.negSucc n •ℤ a = -(Nat.succ n •ℕ a) :=
  rfl

@[simp] theorem gpow_zero {G : Type w} [group G] (a : G) : a ^ 0 = 1 :=
  rfl

@[simp] theorem zero_gsmul {A : Type y} [add_group A] (a : A) : 0 •ℤ a = 0 :=
  rfl

@[simp] theorem gpow_one {G : Type w} [group G] (a : G) : a ^ 1 = a :=
  pow_one a

@[simp] theorem one_gsmul {A : Type y} [add_group A] (a : A) : 1 •ℤ a = a :=
  add_zero (coe_fn multiplicative.to_add a)

@[simp] theorem one_gpow {G : Type w} [group G] (n : ℤ) : 1 ^ n = 1 := sorry

@[simp] theorem gsmul_zero {A : Type y} [add_group A] (n : ℤ) : n •ℤ 0 = 0 :=
  one_gpow

@[simp] theorem gpow_neg {G : Type w} [group G] (a : G) (n : ℤ) : a ^ (-n) = (a ^ n⁻¹) := sorry

theorem mul_gpow_neg_one {G : Type w} [group G] (a : G) (b : G) : (a * b) ^ (-1) = b ^ (-1) * a ^ (-1) := sorry

@[simp] theorem neg_gsmul {A : Type y} [add_group A] (a : A) (n : ℤ) : -n •ℤ a = -(n •ℤ a) :=
  gpow_neg

theorem gpow_neg_one {G : Type w} [group G] (x : G) : x ^ (-1) = (x⁻¹) :=
  congr_arg has_inv.inv (pow_one x)

theorem neg_one_gsmul {A : Type y} [add_group A] (x : A) : -1 •ℤ x = -x :=
  congr_arg Neg.neg (one_nsmul x)

theorem inv_gpow {G : Type w} [group G] (a : G) (n : ℤ) : a⁻¹ ^ n = (a ^ n⁻¹) :=
  int.cases_on n (fun (n : ℕ) => idRhs (a⁻¹ ^ n = (a ^ n⁻¹)) (inv_pow a n))
    fun (n : ℕ) => idRhs (a⁻¹ ^ (n + 1)⁻¹ = (a ^ (n + 1)⁻¹⁻¹)) (congr_arg has_inv.inv (inv_pow a (n + 1)))

theorem gsmul_neg {A : Type y} [add_group A] (a : A) (n : ℤ) : n •ℤ -a = -(n •ℤ a) :=
  inv_gpow a n

theorem commute.mul_gpow {G : Type w} [group G] {a : G} {b : G} (h : commute a b) (n : ℤ) : (a * b) ^ n = a ^ n * b ^ n := sorry

theorem mul_gpow {G : Type w} [comm_group G] (a : G) (b : G) (n : ℤ) : (a * b) ^ n = a ^ n * b ^ n :=
  commute.mul_gpow (commute.all a b) n

theorem gsmul_add {A : Type y} [add_comm_group A] (a : A) (b : A) (n : ℤ) : n •ℤ (a + b) = n •ℤ a + n •ℤ b :=
  mul_gpow

theorem gsmul_sub {A : Type y} [add_comm_group A] (a : A) (b : A) (n : ℤ) : n •ℤ (a - b) = n •ℤ a - n •ℤ b := sorry

protected instance gpow.is_group_hom {G : Type w} [comm_group G] (n : ℤ) : is_group_hom fun (_x : G) => _x ^ n :=
  is_group_hom.mk

protected instance gsmul.is_add_group_hom {A : Type y} [add_comm_group A] (n : ℤ) : is_add_group_hom (gsmul n) :=
  is_add_group_hom.mk

theorem zero_pow {R : Type u₁} [monoid_with_zero R] {n : ℕ} : 0 < n → 0 ^ n = 0 := sorry

namespace ring_hom


@[simp] theorem map_pow {R : Type u₁} {S : Type u₂} [semiring R] [semiring S] (f : R →+* S) (a : R) (n : ℕ) : coe_fn f (a ^ n) = coe_fn f a ^ n :=
  monoid_hom.map_pow (to_monoid_hom f) a

end ring_hom


theorem neg_one_pow_eq_or {R : Type u₁} [ring R] (n : ℕ) : (-1) ^ n = 1 ∨ (-1) ^ n = -1 := sorry

theorem pow_dvd_pow {R : Type u₁} [monoid R] (a : R) {m : ℕ} {n : ℕ} (h : m ≤ n) : a ^ m ∣ a ^ n := sorry

theorem pow_dvd_pow_of_dvd {R : Type u₁} [comm_monoid R] {a : R} {b : R} (h : a ∣ b) (n : ℕ) : a ^ n ∣ b ^ n := sorry

theorem pow_two_sub_pow_two {R : Type u_1} [comm_ring R] (a : R) (b : R) : a ^ bit0 1 - b ^ bit0 1 = (a + b) * (a - b) := sorry

theorem eq_or_eq_neg_of_pow_two_eq_pow_two {R : Type u₁} [integral_domain R] (a : R) (b : R) (h : a ^ bit0 1 = b ^ bit0 1) : a = b ∨ a = -b := sorry

theorem sq_sub_sq {R : Type u₁} [comm_ring R] (a : R) (b : R) : a ^ bit0 1 - b ^ bit0 1 = (a + b) * (a - b) := sorry

theorem pow_eq_zero {R : Type u₁} [monoid_with_zero R] [no_zero_divisors R] {x : R} {n : ℕ} (H : x ^ n = 0) : x = 0 := sorry

@[simp] theorem pow_eq_zero_iff {R : Type u₁} [monoid_with_zero R] [no_zero_divisors R] {a : R} {n : ℕ} (hn : 0 < n) : a ^ n = 0 ↔ a = 0 :=
  { mp := pow_eq_zero, mpr := fun (ᾰ : a = 0) => Eq._oldrec (zero_pow hn) (Eq.symm ᾰ) }

theorem pow_ne_zero {R : Type u₁} [monoid_with_zero R] [no_zero_divisors R] {a : R} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
  mt pow_eq_zero h

theorem pow_abs {R : Type u₁} [linear_ordered_comm_ring R] (a : R) (n : ℕ) : abs a ^ n = abs (a ^ n) :=
  Eq.symm (monoid_hom.map_pow (monoid_with_zero_hom.to_monoid_hom abs_hom) a n)

theorem abs_neg_one_pow {R : Type u₁} [linear_ordered_comm_ring R] (n : ℕ) : abs ((-1) ^ n) = 1 := sorry

theorem nsmul_nonneg {A : Type y} [ordered_add_comm_monoid A] {a : A} (H : 0 ≤ a) (n : ℕ) : 0 ≤ n •ℕ a := sorry

theorem nsmul_pos {A : Type y} [ordered_add_comm_monoid A] {a : A} (ha : 0 < a) {k : ℕ} (hk : 0 < k) : 0 < k •ℕ a := sorry

theorem nsmul_le_nsmul {A : Type y} [ordered_add_comm_monoid A] {a : A} {n : ℕ} {m : ℕ} (ha : 0 ≤ a) (h : n ≤ m) : n •ℕ a ≤ m •ℕ a := sorry

theorem nsmul_le_nsmul_of_le_right {A : Type y} [ordered_add_comm_monoid A] {a : A} {b : A} (hab : a ≤ b) (i : ℕ) : i •ℕ a ≤ i •ℕ b := sorry

theorem gsmul_nonneg {A : Type y} [ordered_add_comm_group A] {a : A} (H : 0 ≤ a) {n : ℤ} (hn : 0 ≤ n) : 0 ≤ n •ℤ a := sorry

theorem nsmul_lt_nsmul {A : Type y} [ordered_cancel_add_comm_monoid A] {a : A} {n : ℕ} {m : ℕ} (ha : 0 < a) (h : n < m) : n •ℕ a < m •ℕ a := sorry

theorem min_pow_dvd_add {R : Type u₁} [semiring R] {n : ℕ} {m : ℕ} {a : R} {b : R} {c : R} (ha : c ^ n ∣ a) (hb : c ^ m ∣ b) : c ^ min n m ∣ a + b :=
  dvd_add (dvd.trans (pow_dvd_pow c (min_le_left n m)) ha) (dvd.trans (pow_dvd_pow c (min_le_right n m)) hb)

theorem add_pow_two {R : Type u₁} [comm_semiring R] (a : R) (b : R) : (a + b) ^ bit0 1 = a ^ bit0 1 + bit0 1 * a * b + b ^ bit0 1 := sorry

namespace canonically_ordered_semiring


theorem pow_pos {R : Type u₁} [canonically_ordered_comm_semiring R] {a : R} (H : 0 < a) (n : ℕ) : 0 < a ^ n := sorry

theorem pow_le_pow_of_le_left {R : Type u₁} [canonically_ordered_comm_semiring R] {a : R} {b : R} (hab : a ≤ b) (i : ℕ) : a ^ i ≤ b ^ i := sorry

theorem one_le_pow_of_one_le {R : Type u₁} [canonically_ordered_comm_semiring R] {a : R} (H : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n := sorry

theorem pow_le_one {R : Type u₁} [canonically_ordered_comm_semiring R] {a : R} (H : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 := sorry

end canonically_ordered_semiring


@[simp] theorem pow_pos {R : Type u₁} [ordered_semiring R] {a : R} (H : 0 < a) (n : ℕ) : 0 < a ^ n := sorry

@[simp] theorem pow_nonneg {R : Type u₁} [ordered_semiring R] {a : R} (H : 0 ≤ a) (n : ℕ) : 0 ≤ a ^ n := sorry

theorem pow_lt_pow_of_lt_left {R : Type u₁} [ordered_semiring R] {x : R} {y : R} {n : ℕ} (Hxy : x < y) (Hxpos : 0 ≤ x) (Hnpos : 0 < n) : x ^ n < y ^ n := sorry

theorem strict_mono_incr_on_pow {R : Type u₁} [ordered_semiring R] {n : ℕ} (hn : 0 < n) : strict_mono_incr_on (fun (x : R) => x ^ n) (set.Ici 0) :=
  fun (x : R) (hx : x ∈ set.Ici 0) (y : R) (hy : y ∈ set.Ici 0) (h : x < y) => pow_lt_pow_of_lt_left h hx hn

theorem one_le_pow_of_one_le {R : Type u₁} [ordered_semiring R] {a : R} (H : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n := sorry

theorem pow_mono {R : Type u₁} [ordered_semiring R] {a : R} (h : 1 ≤ a) : monotone fun (n : ℕ) => a ^ n :=
  monotone_of_monotone_nat fun (n : ℕ) => le_mul_of_one_le_left (pow_nonneg (has_le.le.trans zero_le_one h) n) h

theorem pow_le_pow {R : Type u₁} [ordered_semiring R] {a : R} {n : ℕ} {m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
  pow_mono ha h

theorem strict_mono_pow {R : Type u₁} [ordered_semiring R] {a : R} (h : 1 < a) : strict_mono fun (n : ℕ) => a ^ n := sorry

theorem pow_lt_pow {R : Type u₁} [ordered_semiring R] {a : R} {n : ℕ} {m : ℕ} (h : 1 < a) (h2 : n < m) : a ^ n < a ^ m :=
  strict_mono_pow h h2

theorem pow_lt_pow_iff {R : Type u₁} [ordered_semiring R] {a : R} {n : ℕ} {m : ℕ} (h : 1 < a) : a ^ n < a ^ m ↔ n < m :=
  strict_mono.lt_iff_lt (strict_mono_pow h)

theorem pow_le_pow_of_le_left {R : Type u₁} [ordered_semiring R] {a : R} {b : R} (ha : 0 ≤ a) (hab : a ≤ b) (i : ℕ) : a ^ i ≤ b ^ i := sorry

theorem pow_left_inj {R : Type u₁} [linear_ordered_semiring R] {x : R} {y : R} {n : ℕ} (Hxpos : 0 ≤ x) (Hypos : 0 ≤ y) (Hnpos : 0 < n) (Hxyn : x ^ n = y ^ n) : x = y :=
  strict_mono_incr_on.inj_on (strict_mono_incr_on_pow Hnpos) Hxpos Hypos Hxyn

theorem lt_of_pow_lt_pow {R : Type u₁} [linear_ordered_semiring R] {a : R} {b : R} (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
  lt_of_not_ge fun (hn : a ≥ b) => not_lt_of_ge (pow_le_pow_of_le_left hb hn n) h

theorem le_of_pow_le_pow {R : Type u₁} [linear_ordered_semiring R] {a : R} {b : R} (n : ℕ) (hb : 0 ≤ b) (hn : 0 < n) (h : a ^ n ≤ b ^ n) : a ≤ b :=
  le_of_not_lt fun (h1 : b < a) => not_le_of_lt (pow_lt_pow_of_lt_left h1 hb hn) h

theorem pow_bit0_nonneg {R : Type u₁} [linear_ordered_ring R] (a : R) (n : ℕ) : 0 ≤ a ^ bit0 n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ a ^ bit0 n)) (pow_bit0 a n))) (mul_self_nonneg (a ^ n))

theorem pow_two_nonneg {R : Type u₁} [linear_ordered_ring R] (a : R) : 0 ≤ a ^ bit0 1 :=
  pow_bit0_nonneg a 1

theorem pow_bit0_pos {R : Type u₁} [linear_ordered_ring R] {a : R} (h : a ≠ 0) (n : ℕ) : 0 < a ^ bit0 n :=
  has_le.le.lt_of_ne (pow_bit0_nonneg a n) (ne.symm (pow_ne_zero (bit0 n) h))

theorem pow_two_pos_of_ne_zero {R : Type u₁} [linear_ordered_ring R] (a : R) (h : a ≠ 0) : 0 < a ^ bit0 1 :=
  pow_bit0_pos h 1

@[simp] theorem eq_of_pow_two_eq_pow_two {R : Type u₁} [linear_ordered_comm_ring R] {a : R} {b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ bit0 1 = b ^ bit0 1 ↔ a = b := sorry

@[simp] theorem neg_square {α : Type u_1} [ring α] (z : α) : (-z) ^ bit0 1 = z ^ bit0 1 := sorry

theorem of_add_nsmul {A : Type y} [add_monoid A] (x : A) (n : ℕ) : coe_fn multiplicative.of_add (n •ℕ x) = coe_fn multiplicative.of_add x ^ n :=
  rfl

theorem of_add_gsmul {A : Type y} [add_group A] (x : A) (n : ℤ) : coe_fn multiplicative.of_add (n •ℤ x) = coe_fn multiplicative.of_add x ^ n :=
  rfl

@[simp] theorem semiconj_by.gpow_right {G : Type w} [group G] {a : G} {x : G} {y : G} (h : semiconj_by a x y) (m : ℤ) : semiconj_by a (x ^ m) (y ^ m) := sorry

namespace commute


@[simp] theorem gpow_right {G : Type w} [group G] {a : G} {b : G} (h : commute a b) (m : ℤ) : commute a (b ^ m) :=
  semiconj_by.gpow_right h m

@[simp] theorem gpow_left {G : Type w} [group G] {a : G} {b : G} (h : commute a b) (m : ℤ) : commute (a ^ m) b :=
  commute.symm (gpow_right (commute.symm h) m)

theorem gpow_gpow {G : Type w} [group G] {a : G} {b : G} (h : commute a b) (m : ℤ) (n : ℤ) : commute (a ^ m) (b ^ n) :=
  gpow_right (gpow_left h m) n

@[simp] theorem self_gpow {G : Type w} [group G] (a : G) (n : ℕ) : commute a (a ^ n) :=
  gpow_right (commute.refl a) ↑n

@[simp] theorem gpow_self {G : Type w} [group G] (a : G) (n : ℕ) : commute (a ^ n) a :=
  gpow_left (commute.refl a) ↑n

@[simp] theorem gpow_gpow_self {G : Type w} [group G] (a : G) (m : ℕ) (n : ℕ) : commute (a ^ m) (a ^ n) :=
  gpow_gpow (commute.refl a) ↑m ↑n

