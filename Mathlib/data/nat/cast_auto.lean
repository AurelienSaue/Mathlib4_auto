/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Natural homomorphism from the natural numbers into a monoid with one.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.ordered_field
import Mathlib.data.nat.basic
import PostPort

universes u_1 u_2 

namespace Mathlib

namespace nat


/-- Canonical homomorphism from `ℕ` to a type `α` with `0`, `1` and `+`. -/
protected def cast {α : Type u_1} [HasZero α] [HasOne α] [Add α] : ℕ → α :=
  sorry

/-- Computationally friendlier cast than `nat.cast`, using binary representation. -/
protected def bin_cast {α : Type u_1} [HasZero α] [HasOne α] [Add α] (n : ℕ) : α :=
  binary_rec 0 (fun (odd : Bool) (k : ℕ) (a : α) => cond odd (a + a + 1) (a + a)) n

/--
Coercions such as `nat.cast_coe` that go from a concrete structure such as
`ℕ` to an arbitrary ring `α` should be set up as follows:
```lean
@[priority 900] instance : has_coe_t ℕ α := ⟨...⟩
```

It needs to be `has_coe_t` instead of `has_coe` because otherwise type-class
inference would loop when constructing the transitive coercion `ℕ → ℕ → ℕ → ...`.
The reduced priority is necessary so that it doesn't conflict with instances
such as `has_coe_t α (option α)`.

For this to work, we reduce the priority of the `coe_base` and `coe_trans`
instances because we want the instances for `has_coe_t` to be tried in the
following order:

 1. `has_coe_t` instances declared in mathlib (such as `has_coe_t α (with_top α)`, etc.)
 2. `coe_base`, which contains instances such as `has_coe (fin n) n`
 3. `nat.cast_coe : has_coe_t ℕ α` etc.
 4. `coe_trans`

If `coe_trans` is tried first, then `nat.cast_coe` doesn't get a chance to apply.
-/
-- see note [coercion into rings]

protected instance cast_coe {α : Type u_1} [HasZero α] [HasOne α] [Add α] : has_coe_t ℕ α :=
  has_coe_t.mk nat.cast

@[simp] theorem cast_zero {α : Type u_1} [HasZero α] [HasOne α] [Add α] : ↑0 = 0 :=
  rfl

theorem cast_add_one {α : Type u_1} [HasZero α] [HasOne α] [Add α] (n : ℕ) : ↑(n + 1) = ↑n + 1 :=
  rfl

@[simp] theorem cast_succ {α : Type u_1} [HasZero α] [HasOne α] [Add α] (n : ℕ) : ↑(Nat.succ n) = ↑n + 1 :=
  rfl

@[simp] theorem cast_ite {α : Type u_1} [HasZero α] [HasOne α] [Add α] (P : Prop) [Decidable P] (m : ℕ) (n : ℕ) : ↑(ite P m n) = ite P ↑m ↑n := sorry

@[simp] theorem cast_one {α : Type u_1} [add_monoid α] [HasOne α] : ↑1 = 1 :=
  zero_add 1

@[simp] theorem cast_add {α : Type u_1} [add_monoid α] [HasOne α] (m : ℕ) (n : ℕ) : ↑(m + n) = ↑m + ↑n := sorry

@[simp] theorem bin_cast_eq {α : Type u_1} [add_monoid α] [HasOne α] (n : ℕ) : nat.bin_cast n = ↑n := sorry

/-- `coe : ℕ → α` as an `add_monoid_hom`. -/
def cast_add_monoid_hom (α : Type u_1) [add_monoid α] [HasOne α] : ℕ →+ α :=
  add_monoid_hom.mk coe sorry cast_add

@[simp] theorem coe_cast_add_monoid_hom {α : Type u_1} [add_monoid α] [HasOne α] : ⇑(cast_add_monoid_hom α) = coe :=
  rfl

@[simp] theorem cast_bit0 {α : Type u_1} [add_monoid α] [HasOne α] (n : ℕ) : ↑(bit0 n) = bit0 ↑n :=
  cast_add n n

@[simp] theorem cast_bit1 {α : Type u_1} [add_monoid α] [HasOne α] (n : ℕ) : ↑(bit1 n) = bit1 ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(bit1 n) = bit1 ↑n)) (bit1.equations._eqn_1 n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(bit0 n + 1) = bit1 ↑n)) (cast_add_one (bit0 n))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑(bit0 n) + 1 = bit1 ↑n)) (cast_bit0 n))) (Eq.refl (bit0 ↑n + 1))))

theorem cast_two {α : Type u_1} [add_monoid α] [HasOne α] : ↑(bit0 1) = bit0 1 := sorry

@[simp] theorem cast_pred {α : Type u_1} [add_group α] [HasOne α] {n : ℕ} : 0 < n → ↑(n - 1) = ↑n - 1 := sorry

@[simp] theorem cast_sub {α : Type u_1} [add_group α] [HasOne α] {m : ℕ} {n : ℕ} (h : m ≤ n) : ↑(n - m) = ↑n - ↑m :=
  eq_sub_of_add_eq
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(n - m) + ↑m = ↑n)) (Eq.symm (cast_add (n - m) m))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑(n - m + m) = ↑n)) (nat.sub_add_cancel h))) (Eq.refl ↑n)))

@[simp] theorem cast_mul {α : Type u_1} [semiring α] (m : ℕ) (n : ℕ) : ↑(m * n) = ↑m * ↑n := sorry

@[simp] theorem cast_dvd {α : Type u_1} [field α] {m : ℕ} {n : ℕ} (n_dvd : n ∣ m) (n_nonzero : ↑n ≠ 0) : ↑(m / n) = ↑m / ↑n := sorry

/-- `coe : ℕ → α` as a `ring_hom` -/
def cast_ring_hom (α : Type u_1) [semiring α] : ℕ →+* α :=
  ring_hom.mk coe sorry cast_mul sorry sorry

@[simp] theorem coe_cast_ring_hom {α : Type u_1} [semiring α] : ⇑(cast_ring_hom α) = coe :=
  rfl

theorem cast_commute {α : Type u_1} [semiring α] (n : ℕ) (x : α) : commute (↑n) x :=
  nat.rec_on n (commute.zero_left x) fun (n : ℕ) (ihn : commute (↑n) x) => commute.add_left ihn (commute.one_left x)

theorem commute_cast {α : Type u_1} [semiring α] (x : α) (n : ℕ) : commute x ↑n :=
  commute.symm (cast_commute n x)

@[simp] theorem cast_nonneg {α : Type u_1} [ordered_semiring α] (n : ℕ) : 0 ≤ ↑n := sorry

theorem mono_cast {α : Type u_1} [ordered_semiring α] : monotone coe := sorry

theorem strict_mono_cast {α : Type u_1} [ordered_semiring α] [nontrivial α] : strict_mono coe :=
  fun (m n : ℕ) (h : m < n) =>
    le_induction (lt_add_of_pos_right (↑m) zero_lt_one)
      (fun (n : ℕ) (_x : Nat.succ m ≤ n) (h : ↑m < ↑n) => lt_add_of_lt_of_pos h zero_lt_one) n h

@[simp] theorem cast_le {α : Type u_1} [ordered_semiring α] [nontrivial α] {m : ℕ} {n : ℕ} : ↑m ≤ ↑n ↔ m ≤ n :=
  strict_mono.le_iff_le strict_mono_cast

@[simp] theorem cast_lt {α : Type u_1} [ordered_semiring α] [nontrivial α] {m : ℕ} {n : ℕ} : ↑m < ↑n ↔ m < n :=
  strict_mono.lt_iff_lt strict_mono_cast

@[simp] theorem cast_pos {α : Type u_1} [ordered_semiring α] [nontrivial α] {n : ℕ} : 0 < ↑n ↔ 0 < n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < ↑n ↔ 0 < n)) (Eq.symm cast_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑0 < ↑n ↔ 0 < n)) (propext cast_lt))) (iff.refl (0 < n)))

theorem cast_add_one_pos {α : Type u_1} [ordered_semiring α] [nontrivial α] (n : ℕ) : 0 < ↑n + 1 :=
  add_pos_of_nonneg_of_pos (cast_nonneg n) zero_lt_one

@[simp] theorem one_lt_cast {α : Type u_1} [ordered_semiring α] [nontrivial α] {n : ℕ} : 1 < ↑n ↔ 1 < n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 < ↑n ↔ 1 < n)) (Eq.symm cast_one)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑1 < ↑n ↔ 1 < n)) (propext cast_lt))) (iff.refl (1 < n)))

@[simp] theorem one_le_cast {α : Type u_1} [ordered_semiring α] [nontrivial α] {n : ℕ} : 1 ≤ ↑n ↔ 1 ≤ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ ↑n ↔ 1 ≤ n)) (Eq.symm cast_one)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑1 ≤ ↑n ↔ 1 ≤ n)) (propext cast_le))) (iff.refl (1 ≤ n)))

@[simp] theorem cast_lt_one {α : Type u_1} [ordered_semiring α] [nontrivial α] {n : ℕ} : ↑n < 1 ↔ n = 0 := sorry

@[simp] theorem cast_le_one {α : Type u_1} [ordered_semiring α] [nontrivial α] {n : ℕ} : ↑n ≤ 1 ↔ n ≤ 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n ≤ 1 ↔ n ≤ 1)) (Eq.symm cast_one)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n ≤ ↑1 ↔ n ≤ 1)) (propext cast_le))) (iff.refl (n ≤ 1)))

@[simp] theorem cast_min {α : Type u_1} [linear_ordered_semiring α] {a : ℕ} {b : ℕ} : ↑(min a b) = min ↑a ↑b := sorry

@[simp] theorem cast_max {α : Type u_1} [linear_ordered_semiring α] {a : ℕ} {b : ℕ} : ↑(max a b) = max ↑a ↑b := sorry

@[simp] theorem abs_cast {α : Type u_1} [linear_ordered_ring α] (a : ℕ) : abs ↑a = ↑a :=
  abs_of_nonneg (cast_nonneg a)

theorem coe_nat_dvd {α : Type u_1} [comm_semiring α] {m : ℕ} {n : ℕ} (h : m ∣ n) : ↑m ∣ ↑n :=
  ring_hom.map_dvd (cast_ring_hom α) h

theorem Mathlib.has_dvd.dvd.nat_cast {α : Type u_1} [comm_semiring α] {m : ℕ} {n : ℕ} (h : m ∣ n) : ↑m ∣ ↑n :=
  coe_nat_dvd

theorem inv_pos_of_nat {α : Type u_1} [linear_ordered_field α] {n : ℕ} : 0 < (↑n + 1⁻¹) :=
  iff.mpr inv_pos (add_pos_of_nonneg_of_pos (cast_nonneg n) zero_lt_one)

theorem one_div_pos_of_nat {α : Type u_1} [linear_ordered_field α] {n : ℕ} : 0 < 1 / (↑n + 1) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < 1 / (↑n + 1))) (one_div (↑n + 1)))) inv_pos_of_nat

theorem one_div_le_one_div {α : Type u_1} [linear_ordered_field α] {n : ℕ} {m : ℕ} (h : n ≤ m) : 1 / (↑m + 1) ≤ 1 / (↑n + 1) :=
  one_div_le_one_div_of_le (cast_add_one_pos n)
    (eq.mpr (id (Eq.trans (propext (add_le_add_iff_right 1)) (propext cast_le))) h)

theorem one_div_lt_one_div {α : Type u_1} [linear_ordered_field α] {n : ℕ} {m : ℕ} (h : n < m) : 1 / (↑m + 1) < 1 / (↑n + 1) :=
  one_div_lt_one_div_of_lt (cast_add_one_pos n)
    (eq.mpr (id (Eq.trans (propext (add_lt_add_iff_right 1)) (propext cast_lt))) h)

end nat


namespace add_monoid_hom


theorem ext_nat {A : Type u_1} [add_monoid A] {f : ℕ →+ A} {g : ℕ →+ A} (h : coe_fn f 1 = coe_fn g 1) : f = g := sorry

theorem eq_nat_cast {A : Type u_1} [add_monoid A] [HasOne A] (f : ℕ →+ A) (h1 : coe_fn f 1 = 1) (n : ℕ) : coe_fn f n = ↑n :=
  congr_fun ((fun (this : f = nat.cast_add_monoid_hom A) => this) (ext_nat (Eq.trans h1 (Eq.symm nat.cast_one))))

theorem map_nat_cast {A : Type u_1} {B : Type u_2} [add_monoid A] [HasOne A] [add_monoid B] [HasOne B] (f : A →+ B) (h1 : coe_fn f 1 = 1) (n : ℕ) : coe_fn f ↑n = ↑n := sorry

end add_monoid_hom


namespace ring_hom


@[simp] theorem eq_nat_cast {R : Type u_1} [semiring R] (f : ℕ →+* R) (n : ℕ) : coe_fn f n = ↑n :=
  add_monoid_hom.eq_nat_cast (to_add_monoid_hom f) (map_one f) n

@[simp] theorem map_nat_cast {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R →+* S) (n : ℕ) : coe_fn f ↑n = ↑n :=
  eq_nat_cast (comp f (nat.cast_ring_hom R)) n

theorem ext_nat {R : Type u_1} [semiring R] (f : ℕ →+* R) (g : ℕ →+* R) : f = g :=
  coe_add_monoid_hom_injective (add_monoid_hom.ext_nat (Eq.trans (map_one f) (Eq.symm (map_one g))))

end ring_hom


@[simp] theorem nat.cast_id (n : ℕ) : ↑n = n :=
  Eq.symm (ring_hom.eq_nat_cast (ring_hom.id ℕ) n)

@[simp] theorem nat.cast_with_bot (n : ℕ) : ↑n = ↑n := sorry

protected instance nat.subsingleton_ring_hom {R : Type u_1} [semiring R] : subsingleton (ℕ →+* R) :=
  subsingleton.intro ring_hom.ext_nat

namespace with_top


@[simp] theorem coe_nat {α : Type u_1} [HasZero α] [HasOne α] [Add α] (n : ℕ) : ↑↑n = ↑n := sorry

@[simp] theorem nat_ne_top {α : Type u_1} [HasZero α] [HasOne α] [Add α] (n : ℕ) : ↑n ≠ ⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n ≠ ⊤)) (Eq.symm (coe_nat n)))) coe_ne_top

@[simp] theorem top_ne_nat {α : Type u_1} [HasZero α] [HasOne α] [Add α] (n : ℕ) : ⊤ ≠ ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (⊤ ≠ ↑n)) (Eq.symm (coe_nat n)))) top_ne_coe

theorem add_one_le_of_lt {i : with_top ℕ} {n : with_top ℕ} (h : i < n) : i + 1 ≤ n := sorry

theorem one_le_iff_pos {n : with_top ℕ} : 1 ≤ n ↔ 0 < n := sorry

theorem nat_induction {P : with_top ℕ → Prop} (a : with_top ℕ) (h0 : P 0) (hsuc : ∀ (n : ℕ), P ↑n → P ↑(Nat.succ n)) (htop : (∀ (n : ℕ), P ↑n) → P ⊤) : P a :=
  option.cases_on a (htop fun (n : ℕ) => nat.rec_on n h0 hsuc) fun (a : ℕ) => (fun (n : ℕ) => nat.rec_on n h0 hsuc) a

