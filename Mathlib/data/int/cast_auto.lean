/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.int.basic
import Mathlib.data.nat.cast
import PostPort

universes u_1 u_2 

namespace Mathlib

namespace int


/- cast (injection into groups with one) -/

@[simp] theorem nat_cast_eq_coe_nat (n : ℕ) : ↑n = ↑n := sorry

/-- Coercion `ℕ → ℤ` as a `ring_hom`. -/
def of_nat_hom : ℕ →+* ℤ :=
  ring_hom.mk coe sorry of_nat_mul sorry of_nat_add

/-- Canonical homomorphism from the integers to any ring(-like) structure `α` -/
protected def cast {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] : ℤ → α :=
  sorry

-- see Note [coercion into rings]

protected instance cast_coe {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] : has_coe_t ℤ α :=
  has_coe_t.mk int.cast

@[simp] theorem cast_zero {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] : ↑0 = 0 :=
  rfl

theorem cast_of_nat {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] (n : ℕ) : ↑(Int.ofNat n) = ↑n :=
  rfl

@[simp] theorem cast_coe_nat {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] (n : ℕ) : ↑↑n = ↑n :=
  rfl

theorem cast_coe_nat' {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] (n : ℕ) : ↑↑n = ↑n := sorry

@[simp] theorem cast_neg_succ_of_nat {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] (n : ℕ) : ↑(Int.negSucc n) = -(↑n + 1) :=
  rfl

@[simp] theorem cast_one {α : Type u_1} [add_monoid α] [HasOne α] [Neg α] : ↑1 = 1 :=
  nat.cast_one

@[simp] theorem cast_sub_nat_nat {α : Type u_1} [add_group α] [HasOne α] (m : ℕ) (n : ℕ) : ↑(sub_nat_nat m n) = ↑m - ↑n := sorry

@[simp] theorem cast_neg_of_nat {α : Type u_1} [add_group α] [HasOne α] (n : ℕ) : ↑(neg_of_nat n) = -↑n :=
  nat.cases_on n (idRhs (0 = -0) (Eq.symm neg_zero))
    fun (n : ℕ) => idRhs (↑(neg_of_nat (n + 1)) = ↑(neg_of_nat (n + 1))) rfl

@[simp] theorem cast_add {α : Type u_1} [add_group α] [HasOne α] (m : ℤ) (n : ℤ) : ↑(m + n) = ↑m + ↑n := sorry

@[simp] theorem cast_neg {α : Type u_1} [add_group α] [HasOne α] (n : ℤ) : ↑(-n) = -↑n :=
  int.cases_on n (fun (n : ℕ) => idRhs (↑(neg_of_nat n) = -↑n) (cast_neg_of_nat n))
    fun (n : ℕ) => idRhs (↑(-Int.negSucc n) = --↑(-Int.negSucc n)) (Eq.symm (neg_neg ↑(-Int.negSucc n)))

@[simp] theorem cast_sub {α : Type u_1} [add_group α] [HasOne α] (m : ℤ) (n : ℤ) : ↑(m - n) = ↑m - ↑n := sorry

@[simp] theorem cast_mul {α : Type u_1} [ring α] (m : ℤ) (n : ℤ) : ↑(m * n) = ↑m * ↑n := sorry

/-- `coe : ℤ → α` as an `add_monoid_hom`. -/
def cast_add_hom (α : Type u_1) [add_group α] [HasOne α] : ℤ →+ α :=
  add_monoid_hom.mk coe sorry cast_add

@[simp] theorem coe_cast_add_hom {α : Type u_1} [add_group α] [HasOne α] : ⇑(cast_add_hom α) = coe :=
  rfl

/-- `coe : ℤ → α` as a `ring_hom`. -/
def cast_ring_hom (α : Type u_1) [ring α] : ℤ →+* α :=
  ring_hom.mk coe sorry cast_mul sorry sorry

@[simp] theorem coe_cast_ring_hom {α : Type u_1} [ring α] : ⇑(cast_ring_hom α) = coe :=
  rfl

theorem cast_commute {α : Type u_1} [ring α] (m : ℤ) (x : α) : commute (↑m) x :=
  int.cases_on m (fun (n : ℕ) => nat.cast_commute n x) fun (n : ℕ) => commute.neg_left (nat.cast_commute (n + 1) x)

theorem commute_cast {α : Type u_1} [ring α] (x : α) (m : ℤ) : commute x ↑m :=
  commute.symm (cast_commute m x)

@[simp] theorem coe_nat_bit0 (n : ℕ) : ↑(bit0 n) = bit0 ↑n := sorry

@[simp] theorem coe_nat_bit1 (n : ℕ) : ↑(bit1 n) = bit1 ↑n := sorry

@[simp] theorem cast_bit0 {α : Type u_1} [ring α] (n : ℤ) : ↑(bit0 n) = bit0 ↑n :=
  cast_add n n

@[simp] theorem cast_bit1 {α : Type u_1} [ring α] (n : ℤ) : ↑(bit1 n) = bit1 ↑n := sorry

theorem cast_two {α : Type u_1} [ring α] : ↑(bit0 1) = bit0 1 := sorry

theorem cast_mono {α : Type u_1} [ordered_ring α] : monotone coe := sorry

@[simp] theorem cast_nonneg {α : Type u_1} [ordered_ring α] [nontrivial α] {n : ℤ} : 0 ≤ ↑n ↔ 0 ≤ n := sorry

@[simp] theorem cast_le {α : Type u_1} [ordered_ring α] [nontrivial α] {m : ℤ} {n : ℤ} : ↑m ≤ ↑n ↔ m ≤ n := sorry

theorem cast_strict_mono {α : Type u_1} [ordered_ring α] [nontrivial α] : strict_mono coe :=
  strict_mono_of_le_iff_le fun (m n : ℤ) => iff.symm cast_le

@[simp] theorem cast_lt {α : Type u_1} [ordered_ring α] [nontrivial α] {m : ℤ} {n : ℤ} : ↑m < ↑n ↔ m < n :=
  strict_mono.lt_iff_lt cast_strict_mono

@[simp] theorem cast_nonpos {α : Type u_1} [ordered_ring α] [nontrivial α] {n : ℤ} : ↑n ≤ 0 ↔ n ≤ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n ≤ 0 ↔ n ≤ 0)) (Eq.symm cast_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n ≤ ↑0 ↔ n ≤ 0)) (propext cast_le))) (iff.refl (n ≤ 0)))

@[simp] theorem cast_pos {α : Type u_1} [ordered_ring α] [nontrivial α] {n : ℤ} : 0 < ↑n ↔ 0 < n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < ↑n ↔ 0 < n)) (Eq.symm cast_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑0 < ↑n ↔ 0 < n)) (propext cast_lt))) (iff.refl (0 < n)))

@[simp] theorem cast_lt_zero {α : Type u_1} [ordered_ring α] [nontrivial α] {n : ℤ} : ↑n < 0 ↔ n < 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n < 0 ↔ n < 0)) (Eq.symm cast_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n < ↑0 ↔ n < 0)) (propext cast_lt))) (iff.refl (n < 0)))

@[simp] theorem cast_min {α : Type u_1} [linear_ordered_ring α] {a : ℤ} {b : ℤ} : ↑(min a b) = min ↑a ↑b :=
  monotone.map_min cast_mono

@[simp] theorem cast_max {α : Type u_1} [linear_ordered_ring α] {a : ℤ} {b : ℤ} : ↑(max a b) = max ↑a ↑b :=
  monotone.map_max cast_mono

@[simp] theorem cast_abs {α : Type u_1} [linear_ordered_ring α] {q : ℤ} : ↑(abs q) = abs ↑q := sorry

theorem coe_int_dvd {α : Type u_1} [comm_ring α] (m : ℤ) (n : ℤ) (h : m ∣ n) : ↑m ∣ ↑n :=
  ring_hom.map_dvd (cast_ring_hom α) h

end int


namespace add_monoid_hom


/-- Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
theorem ext_int {A : Type u_1} [add_monoid A] {f : ℤ →+ A} {g : ℤ →+ A} (h1 : coe_fn f 1 = coe_fn g 1) : f = g := sorry

theorem eq_int_cast_hom {A : Type u_1} [add_group A] [HasOne A] (f : ℤ →+ A) (h1 : coe_fn f 1 = 1) : f = int.cast_add_hom A := sorry

theorem eq_int_cast {A : Type u_1} [add_group A] [HasOne A] (f : ℤ →+ A) (h1 : coe_fn f 1 = 1) (n : ℤ) : coe_fn f n = ↑n :=
  iff.mp ext_iff (eq_int_cast_hom f h1)

end add_monoid_hom


namespace monoid_hom


theorem ext_int {M : Type u_1} [monoid M] {f : multiplicative ℤ →* M} {g : multiplicative ℤ →* M} (h1 : coe_fn f (coe_fn multiplicative.of_add 1) = coe_fn g (coe_fn multiplicative.of_add 1)) : f = g :=
  ext fun (x : multiplicative ℤ) => iff.mp add_monoid_hom.ext_iff (add_monoid_hom.ext_int h1) x

end monoid_hom


namespace ring_hom


@[simp] theorem eq_int_cast {α : Type u_1} [ring α] (f : ℤ →+* α) (n : ℤ) : coe_fn f n = ↑n :=
  add_monoid_hom.eq_int_cast (to_add_monoid_hom f) (map_one f) n

theorem eq_int_cast' {α : Type u_1} [ring α] (f : ℤ →+* α) : f = int.cast_ring_hom α :=
  ext (eq_int_cast f)

@[simp] theorem map_int_cast {α : Type u_1} {β : Type u_2} [ring α] [ring β] (f : α →+* β) (n : ℤ) : coe_fn f ↑n = ↑n :=
  eq_int_cast (comp f (int.cast_ring_hom α)) n

theorem ext_int {R : Type u_1} [semiring R] (f : ℤ →+* R) (g : ℤ →+* R) : f = g :=
  coe_add_monoid_hom_injective (add_monoid_hom.ext_int (Eq.trans (map_one f) (Eq.symm (map_one g))))

protected instance int.subsingleton_ring_hom {R : Type u_1} [semiring R] : subsingleton (ℤ →+* R) :=
  subsingleton.intro ext_int

end ring_hom


@[simp] theorem int.cast_id (n : ℤ) : ↑n = n :=
  Eq.symm (ring_hom.eq_int_cast (ring_hom.id ℤ) n)

