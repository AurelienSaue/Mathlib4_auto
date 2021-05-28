/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.num.bitwise
import Mathlib.data.int.char_zero
import Mathlib.data.nat.gcd
import Mathlib.data.nat.psub
import PostPort

universes u_1 

namespace Mathlib

/-!
# Properties of the binary representation of integers
-/

namespace pos_num


@[simp] theorem cast_one {α : Type u_1} [HasOne α] [Add α] : ↑1 = 1 :=
  rfl

@[simp] theorem cast_one' {α : Type u_1} [HasOne α] [Add α] : ↑one = 1 :=
  rfl

@[simp] theorem cast_bit0 {α : Type u_1} [HasOne α] [Add α] (n : pos_num) : ↑(bit0 n) = bit0 ↑n :=
  rfl

@[simp] theorem cast_bit1 {α : Type u_1} [HasOne α] [Add α] (n : pos_num) : ↑(bit1 n) = bit1 ↑n :=
  rfl

@[simp] theorem cast_to_nat {α : Type u_1} [add_monoid α] [HasOne α] (n : pos_num) : ↑↑n = ↑n := sorry

@[simp] theorem to_nat_to_int (n : pos_num) : ↑↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑n)) (Eq.symm (int.nat_cast_eq_coe_nat ↑n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑n)) (cast_to_nat n))) (Eq.refl ↑n))

@[simp] theorem cast_to_int {α : Type u_1} [add_group α] [HasOne α] (n : pos_num) : ↑↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑n)) (Eq.symm (to_nat_to_int n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑↑n = ↑n)) (int.cast_coe_nat ↑n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑n)) (cast_to_nat n))) (Eq.refl ↑n)))

theorem succ_to_nat (n : pos_num) : ↑(succ n) = ↑n + 1 := sorry

theorem one_add (n : pos_num) : 1 + n = succ n :=
  pos_num.cases_on n (Eq.refl (1 + one)) (fun (n : pos_num) => Eq.refl (1 + bit1 n))
    fun (n : pos_num) => Eq.refl (1 + bit0 n)

theorem add_one (n : pos_num) : n + 1 = succ n :=
  pos_num.cases_on n (Eq.refl (one + 1)) (fun (n : pos_num) => Eq.refl (bit1 n + 1))
    fun (n : pos_num) => Eq.refl (bit0 n + 1)

theorem add_to_nat (m : pos_num) (n : pos_num) : ↑(m + n) = ↑m + ↑n := sorry

theorem add_succ (m : pos_num) (n : pos_num) : m + succ n = succ (m + n) := sorry

theorem bit0_of_bit0 (n : pos_num) : bit0 n = bit0 n := sorry

theorem bit1_of_bit1 (n : pos_num) : bit1 n = bit1 n :=
  (fun (this : bit0 n + 1 = bit1 n) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (bit0 n + 1 = bit1 n)) (add_one (bit0 n))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (succ (bit0 n) = bit1 n)) (bit0_of_bit0 n))) (Eq.refl (succ (bit0 n)))))

theorem mul_to_nat (m : pos_num) (n : pos_num) : ↑(m * n) = ↑m * ↑n := sorry

theorem to_nat_pos (n : pos_num) : 0 < ↑n := sorry

theorem cmp_to_nat_lemma {m : pos_num} {n : pos_num} : ↑m < ↑n → ↑(bit1 m) < ↑(bit0 n) := sorry

theorem cmp_swap (m : pos_num) (n : pos_num) : ordering.swap (cmp m n) = cmp n m := sorry

theorem cmp_to_nat (m : pos_num) (n : pos_num) : ordering.cases_on (cmp m n) (↑m < ↑n) (m = n) (↑n < ↑m) := sorry

theorem lt_to_nat {m : pos_num} {n : pos_num} : ↑m < ↑n ↔ m < n := sorry

theorem le_to_nat {m : pos_num} {n : pos_num} : ↑m ≤ ↑n ↔ m ≤ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑m ≤ ↑n ↔ m ≤ n)) (Eq.symm (propext not_lt)))) (not_congr lt_to_nat)

end pos_num


namespace num


theorem add_zero (n : num) : n + 0 = n :=
  num.cases_on n (Eq.refl (zero + 0)) fun (n : pos_num) => Eq.refl (pos n + 0)

theorem zero_add (n : num) : 0 + n = n :=
  num.cases_on n (Eq.refl (0 + zero)) fun (n : pos_num) => Eq.refl (0 + pos n)

theorem add_one (n : num) : n + 1 = succ n := sorry

theorem add_succ (m : num) (n : num) : m + succ n = succ (m + n) := sorry

@[simp] theorem add_of_nat (m : ℕ) (n : ℕ) : ↑(m + n) = ↑m + ↑n := sorry

theorem bit0_of_bit0 (n : num) : bit0 n = num.bit0 n :=
  num.cases_on n (idRhs (bit0 0 = bit0 0) rfl)
    fun (n : pos_num) => idRhs (pos (bit0 n) = pos (pos_num.bit0 n)) (congr_arg pos (pos_num.bit0_of_bit0 n))

theorem bit1_of_bit1 (n : num) : bit1 n = num.bit1 n :=
  num.cases_on n (idRhs (bit1 0 = bit1 0) rfl)
    fun (n : pos_num) => idRhs (pos (bit1 n) = pos (pos_num.bit1 n)) (congr_arg pos (pos_num.bit1_of_bit1 n))

@[simp] theorem cast_zero {α : Type u_1} [HasZero α] [HasOne α] [Add α] : ↑0 = 0 :=
  rfl

@[simp] theorem cast_zero' {α : Type u_1} [HasZero α] [HasOne α] [Add α] : ↑zero = 0 :=
  rfl

@[simp] theorem cast_one {α : Type u_1} [HasZero α] [HasOne α] [Add α] : ↑1 = 1 :=
  rfl

@[simp] theorem cast_pos {α : Type u_1} [HasZero α] [HasOne α] [Add α] (n : pos_num) : ↑(pos n) = ↑n :=
  rfl

theorem succ'_to_nat (n : num) : ↑(succ' n) = ↑n + 1 :=
  num.cases_on n (idRhs (↑(succ' 0) = 0 + ↑(succ' 0)) (Eq.symm (zero_add ↑(succ' 0))))
    fun (n : pos_num) => idRhs (↑(pos_num.succ n) = ↑n + 1) (pos_num.succ_to_nat n)

theorem succ_to_nat (n : num) : ↑(succ n) = ↑n + 1 :=
  succ'_to_nat n

@[simp] theorem cast_to_nat {α : Type u_1} [add_monoid α] [HasOne α] (n : num) : ↑↑n = ↑n :=
  num.cases_on n (idRhs (↑0 = 0) nat.cast_zero) fun (n : pos_num) => idRhs (↑↑n = ↑n) (pos_num.cast_to_nat n)

@[simp] theorem to_nat_to_int (n : num) : ↑↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑n)) (Eq.symm (int.nat_cast_eq_coe_nat ↑n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑n)) (cast_to_nat n))) (Eq.refl ↑n))

@[simp] theorem cast_to_int {α : Type u_1} [add_group α] [HasOne α] (n : num) : ↑↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑n)) (Eq.symm (to_nat_to_int n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑↑n = ↑n)) (int.cast_coe_nat ↑n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑n)) (cast_to_nat n))) (Eq.refl ↑n)))

theorem to_of_nat (n : ℕ) : ↑↑n = n := sorry

@[simp] theorem of_nat_cast {α : Type u_1} [add_monoid α] [HasOne α] (n : ℕ) : ↑↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑n)) (Eq.symm (cast_to_nat ↑n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑↑n = ↑n)) (to_of_nat n))) (Eq.refl ↑n))

theorem of_nat_inj {m : ℕ} {n : ℕ} : ↑m = ↑n ↔ m = n :=
  { mp := fun (h : ↑m = ↑n) => function.left_inverse.injective to_of_nat h, mpr := congr_arg fun (x : ℕ) => ↑x }

theorem add_to_nat (m : num) (n : num) : ↑(m + n) = ↑m + ↑n := sorry

theorem mul_to_nat (m : num) (n : num) : ↑(m * n) = ↑m * ↑n := sorry

theorem cmp_to_nat (m : num) (n : num) : ordering.cases_on (cmp m n) (↑m < ↑n) (m = n) (↑n < ↑m) := sorry

theorem lt_to_nat {m : num} {n : num} : ↑m < ↑n ↔ m < n := sorry

theorem le_to_nat {m : num} {n : num} : ↑m ≤ ↑n ↔ m ≤ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑m ≤ ↑n ↔ m ≤ n)) (Eq.symm (propext not_lt)))) (not_congr lt_to_nat)

end num


namespace pos_num


@[simp] theorem of_to_nat (n : pos_num) : ↑↑n = num.pos n := sorry

end pos_num


namespace num


@[simp] theorem of_to_nat (n : num) : ↑↑n = n :=
  num.cases_on n (idRhs (↑↑0 = ↑↑0) rfl) fun (n : pos_num) => idRhs (↑↑n = pos n) (pos_num.of_to_nat n)

theorem to_nat_inj {m : num} {n : num} : ↑m = ↑n ↔ m = n :=
  { mp := fun (h : ↑m = ↑n) => function.left_inverse.injective of_to_nat h, mpr := congr_arg fun (x : num) => ↑x }

/--
This tactic tries to turn an (in)equality about `num`s to one about `nat`s by rewriting.
```lean
example (n : num) (m : num) : n ≤ n + m :=
begin
  num.transfer_rw,
  exact nat.le_add_right _ _
end
```
-/
/--
This tactic tries to prove (in)equalities about `num`s by transfering them to the `nat` world and
then trying to call `simp`.
```lean
example (n : num) (m : num) : n ≤ n + m := by num.transfer
```
-/
protected instance comm_semiring : comm_semiring num :=
  comm_semiring.mk Add.add sorry 0 zero_add add_zero sorry Mul.mul sorry 1 sorry sorry sorry sorry sorry sorry sorry

protected instance ordered_cancel_add_comm_monoid : ordered_cancel_add_comm_monoid num :=
  ordered_cancel_add_comm_monoid.mk comm_semiring.add comm_semiring.add_assoc sorry comm_semiring.zero
    comm_semiring.zero_add comm_semiring.add_zero comm_semiring.add_comm sorry LessEq Less sorry sorry sorry sorry sorry

protected instance linear_ordered_semiring : linear_ordered_semiring num :=
  linear_ordered_semiring.mk comm_semiring.add comm_semiring.add_assoc comm_semiring.zero comm_semiring.zero_add
    comm_semiring.add_zero comm_semiring.add_comm comm_semiring.mul comm_semiring.mul_assoc comm_semiring.one
    comm_semiring.one_mul comm_semiring.mul_one comm_semiring.zero_mul comm_semiring.mul_zero comm_semiring.left_distrib
    comm_semiring.right_distrib ordered_cancel_add_comm_monoid.add_left_cancel
    ordered_cancel_add_comm_monoid.add_right_cancel ordered_cancel_add_comm_monoid.le ordered_cancel_add_comm_monoid.lt
    ordered_cancel_add_comm_monoid.le_refl ordered_cancel_add_comm_monoid.le_trans
    ordered_cancel_add_comm_monoid.le_antisymm ordered_cancel_add_comm_monoid.add_le_add_left
    ordered_cancel_add_comm_monoid.le_of_add_le_add_left sorry sorry sorry sorry num.decidable_le num.decidable_eq
    num.decidable_lt sorry

theorem dvd_to_nat (m : num) (n : num) : ↑m ∣ ↑n ↔ m ∣ n := sorry

end num


namespace pos_num


theorem to_nat_inj {m : pos_num} {n : pos_num} : ↑m = ↑n ↔ m = n := sorry

theorem pred'_to_nat (n : pos_num) : ↑(pred' n) = Nat.pred ↑n := sorry

@[simp] theorem pred'_succ' (n : num) : pred' (num.succ' n) = n := sorry

@[simp] theorem succ'_pred' (n : pos_num) : num.succ' (pred' n) = n := sorry

protected instance has_dvd : has_dvd pos_num :=
  has_dvd.mk fun (m n : pos_num) => num.pos m ∣ num.pos n

theorem dvd_to_nat {m : pos_num} {n : pos_num} : ↑m ∣ ↑n ↔ m ∣ n :=
  num.dvd_to_nat (num.pos m) (num.pos n)

theorem size_to_nat (n : pos_num) : ↑(size n) = nat.size ↑n := sorry

theorem size_eq_nat_size (n : pos_num) : ↑(size n) = nat_size n := sorry

theorem nat_size_to_nat (n : pos_num) : nat_size n = nat.size ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_size n = nat.size ↑n)) (Eq.symm (size_eq_nat_size n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(size n) = nat.size ↑n)) (size_to_nat n))) (Eq.refl (nat.size ↑n)))

theorem nat_size_pos (n : pos_num) : 0 < nat_size n :=
  pos_num.cases_on n (nat.succ_pos 0) (fun (n : pos_num) => nat.succ_pos (nat_size n))
    fun (n : pos_num) => nat.succ_pos (nat_size n)

/--
This tactic tries to turn an (in)equality about `pos_num`s to one about `nat`s by rewriting.
```lean
example (n : pos_num) (m : pos_num) : n ≤ n + m :=
begin
  pos_num.transfer_rw,
  exact nat.le_add_right _ _
end
```
-/
/--
This tactic tries to prove (in)equalities about `pos_num`s by transferring them to the `nat` world
and then trying to call `simp`.
```lean
example (n : pos_num) (m : pos_num) : n ≤ n + m := by pos_num.transfer
```
-/
protected instance add_comm_semigroup : add_comm_semigroup pos_num :=
  add_comm_semigroup.mk Add.add sorry sorry

protected instance comm_monoid : comm_monoid pos_num :=
  comm_monoid.mk Mul.mul sorry 1 sorry sorry sorry

protected instance distrib : distrib pos_num :=
  distrib.mk Mul.mul Add.add sorry sorry

protected instance linear_order : linear_order pos_num :=
  linear_order.mk LessEq Less sorry sorry sorry sorry (fun (a b : pos_num) => pos_num.decidable_le a b)
    (fun (a b : pos_num) => pos_num.decidable_eq a b) fun (a b : pos_num) => pos_num.decidable_lt a b

@[simp] theorem cast_to_num (n : pos_num) : ↑n = num.pos n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n = num.pos n)) (Eq.symm (cast_to_nat n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = num.pos n)) (Eq.symm (of_to_nat n)))) (Eq.refl ↑↑n))

@[simp] theorem bit_to_nat (b : Bool) (n : pos_num) : ↑(bit b n) = nat.bit b ↑n :=
  bool.cases_on b (Eq.refl ↑(bit false n)) (Eq.refl ↑(bit tt n))

@[simp] theorem cast_add {α : Type u_1} [add_monoid α] [HasOne α] (m : pos_num) (n : pos_num) : ↑(m + n) = ↑m + ↑n := sorry

@[simp] theorem cast_succ {α : Type u_1} [add_monoid α] [HasOne α] (n : pos_num) : ↑(succ n) = ↑n + 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(succ n) = ↑n + 1)) (Eq.symm (add_one n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(n + 1) = ↑n + 1)) (cast_add n 1)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑n + ↑1 = ↑n + 1)) cast_one)) (Eq.refl (↑n + 1))))

@[simp] theorem cast_inj {α : Type u_1} [add_monoid α] [HasOne α] [char_zero α] {m : pos_num} {n : pos_num} : ↑m = ↑n ↔ m = n := sorry

@[simp] theorem one_le_cast {α : Type u_1} [linear_ordered_semiring α] (n : pos_num) : 1 ≤ ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ ↑n)) (Eq.symm (cast_to_nat n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ ↑↑n)) (Eq.symm nat.cast_one)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑1 ≤ ↑↑n)) (propext nat.cast_le))) (to_nat_pos n)))

@[simp] theorem cast_pos {α : Type u_1} [linear_ordered_semiring α] (n : pos_num) : 0 < ↑n :=
  lt_of_lt_of_le zero_lt_one (one_le_cast n)

@[simp] theorem cast_mul {α : Type u_1} [semiring α] (m : pos_num) (n : pos_num) : ↑(m * n) = ↑m * ↑n := sorry

@[simp] theorem cmp_eq (m : pos_num) (n : pos_num) : cmp m n = ordering.eq ↔ m = n := sorry

@[simp] theorem cast_lt {α : Type u_1} [linear_ordered_semiring α] {m : pos_num} {n : pos_num} : ↑m < ↑n ↔ m < n := sorry

@[simp] theorem cast_le {α : Type u_1} [linear_ordered_semiring α] {m : pos_num} {n : pos_num} : ↑m ≤ ↑n ↔ m ≤ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑m ≤ ↑n ↔ m ≤ n)) (Eq.symm (propext not_lt)))) (not_congr cast_lt)

end pos_num


namespace num


theorem bit_to_nat (b : Bool) (n : num) : ↑(bit b n) = nat.bit b ↑n :=
  bool.cases_on b (num.cases_on n (Eq.refl ↑(bit false zero)) fun (n : pos_num) => Eq.refl ↑(bit false (pos n)))
    (num.cases_on n (Eq.refl ↑(bit tt zero)) fun (n : pos_num) => Eq.refl ↑(bit tt (pos n)))

theorem cast_succ' {α : Type u_1} [add_monoid α] [HasOne α] (n : num) : ↑(succ' n) = ↑n + 1 := sorry

theorem cast_succ {α : Type u_1} [add_monoid α] [HasOne α] (n : num) : ↑(succ n) = ↑n + 1 :=
  cast_succ' n

@[simp] theorem cast_add {α : Type u_1} [semiring α] (m : num) (n : num) : ↑(m + n) = ↑m + ↑n := sorry

@[simp] theorem cast_bit0 {α : Type u_1} [semiring α] (n : num) : ↑(num.bit0 n) = bit0 ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(num.bit0 n) = bit0 ↑n)) (Eq.symm (bit0_of_bit0 n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(bit0 n) = bit0 ↑n)) (bit0.equations._eqn_1 n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑(n + n) = bit0 ↑n)) (cast_add n n))) (Eq.refl (↑n + ↑n))))

@[simp] theorem cast_bit1 {α : Type u_1} [semiring α] (n : num) : ↑(num.bit1 n) = bit1 ↑n := sorry

@[simp] theorem cast_mul {α : Type u_1} [semiring α] (m : num) (n : num) : ↑(m * n) = ↑m * ↑n := sorry

theorem size_to_nat (n : num) : ↑(size n) = nat.size ↑n :=
  num.cases_on n (idRhs (0 = nat.size 0) (Eq.symm nat.size_zero))
    fun (n : pos_num) => idRhs (↑(pos_num.size n) = nat.size ↑n) (pos_num.size_to_nat n)

theorem size_eq_nat_size (n : num) : ↑(size n) = nat_size n :=
  num.cases_on n (idRhs (↑(size 0) = ↑(size 0)) rfl)
    fun (n : pos_num) => idRhs (↑(pos_num.size n) = pos_num.nat_size n) (pos_num.size_eq_nat_size n)

theorem nat_size_to_nat (n : num) : nat_size n = nat.size ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_size n = nat.size ↑n)) (Eq.symm (size_eq_nat_size n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(size n) = nat.size ↑n)) (size_to_nat n))) (Eq.refl (nat.size ↑n)))

@[simp] theorem of_nat'_eq (n : ℕ) : of_nat' n = ↑n := sorry

theorem zneg_to_znum (n : num) : -to_znum n = to_znum_neg n :=
  num.cases_on n (Eq.refl (-to_znum zero)) fun (n : pos_num) => Eq.refl (-to_znum (pos n))

theorem zneg_to_znum_neg (n : num) : -to_znum_neg n = to_znum n :=
  num.cases_on n (Eq.refl (-to_znum_neg zero)) fun (n : pos_num) => Eq.refl (-to_znum_neg (pos n))

theorem to_znum_inj {m : num} {n : num} : to_znum m = to_znum n ↔ m = n := sorry

@[simp] theorem cast_to_znum {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] (n : num) : ↑(to_znum n) = ↑n :=
  num.cases_on n (idRhs (↑(to_znum 0) = ↑(to_znum 0)) rfl)
    fun (n : pos_num) => idRhs (↑(to_znum (pos n)) = ↑(to_znum (pos n))) rfl

@[simp] theorem cast_to_znum_neg {α : Type u_1} [add_group α] [HasOne α] (n : num) : ↑(to_znum_neg n) = -↑n :=
  num.cases_on n (idRhs (0 = -0) (Eq.symm neg_zero))
    fun (n : pos_num) => idRhs (↑(to_znum_neg (pos n)) = ↑(to_znum_neg (pos n))) rfl

@[simp] theorem add_to_znum (m : num) (n : num) : to_znum (m + n) = to_znum m + to_znum n :=
  num.cases_on m (num.cases_on n (Eq.refl (to_znum (zero + zero))) fun (n : pos_num) => Eq.refl (to_znum (zero + pos n)))
    fun (m : pos_num) =>
      num.cases_on n (Eq.refl (to_znum (pos m + zero))) fun (n : pos_num) => Eq.refl (to_znum (pos m + pos n))

end num


namespace pos_num


theorem pred_to_nat {n : pos_num} (h : 1 < n) : ↑(pred n) = Nat.pred ↑n := sorry

theorem sub'_one (a : pos_num) : sub' a 1 = num.to_znum (pred' a) :=
  pos_num.cases_on a (Eq.refl (sub' one 1)) (fun (a : pos_num) => Eq.refl (sub' (bit1 a) 1))
    fun (a : pos_num) => Eq.refl (sub' (bit0 a) 1)

theorem one_sub' (a : pos_num) : sub' 1 a = num.to_znum_neg (pred' a) :=
  pos_num.cases_on a (Eq.refl (sub' 1 one)) (fun (a : pos_num) => Eq.refl (sub' 1 (bit1 a)))
    fun (a : pos_num) => Eq.refl (sub' 1 (bit0 a))

theorem lt_iff_cmp {m : pos_num} {n : pos_num} : m < n ↔ cmp m n = ordering.lt :=
  iff.rfl

theorem le_iff_cmp {m : pos_num} {n : pos_num} : m ≤ n ↔ cmp m n ≠ ordering.gt := sorry

end pos_num


namespace num


theorem pred_to_nat (n : num) : ↑(pred n) = Nat.pred ↑n := sorry

theorem ppred_to_nat (n : num) : coe <$> ppred n = nat.ppred ↑n := sorry

theorem cmp_swap (m : num) (n : num) : ordering.swap (cmp m n) = cmp n m := sorry

theorem cmp_eq (m : num) (n : num) : cmp m n = ordering.eq ↔ m = n := sorry

@[simp] theorem cast_lt {α : Type u_1} [linear_ordered_semiring α] {m : num} {n : num} : ↑m < ↑n ↔ m < n := sorry

@[simp] theorem cast_le {α : Type u_1} [linear_ordered_semiring α] {m : num} {n : num} : ↑m ≤ ↑n ↔ m ≤ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑m ≤ ↑n ↔ m ≤ n)) (Eq.symm (propext not_lt)))) (not_congr cast_lt)

@[simp] theorem cast_inj {α : Type u_1} [linear_ordered_semiring α] {m : num} {n : num} : ↑m = ↑n ↔ m = n := sorry

theorem lt_iff_cmp {m : num} {n : num} : m < n ↔ cmp m n = ordering.lt :=
  iff.rfl

theorem le_iff_cmp {m : num} {n : num} : m ≤ n ↔ cmp m n ≠ ordering.gt := sorry

theorem bitwise_to_nat {f : num → num → num} {g : Bool → Bool → Bool} (p : pos_num → pos_num → num) (gff : g false false = false) (f00 : f 0 0 = 0) (f0n : ∀ (n : pos_num), f 0 (pos n) = cond (g false tt) (pos n) 0) (fn0 : ∀ (n : pos_num), f (pos n) 0 = cond (g tt false) (pos n) 0) (fnn : ∀ (m n : pos_num), f (pos m) (pos n) = p m n) (p11 : p 1 1 = cond (g tt tt) 1 0) (p1b : ∀ (b : Bool) (n : pos_num), p 1 (pos_num.bit b n) = bit (g tt b) (cond (g false tt) (pos n) 0)) (pb1 : ∀ (a : Bool) (m : pos_num), p (pos_num.bit a m) 1 = bit (g a tt) (cond (g tt false) (pos m) 0)) (pbb : ∀ (a b : Bool) (m n : pos_num), p (pos_num.bit a m) (pos_num.bit b n) = bit (g a b) (p m n)) (m : num) (n : num) : ↑(f m n) = nat.bitwise g ↑m ↑n := sorry

@[simp] theorem lor_to_nat (m : num) (n : num) : ↑(lor m n) = nat.lor ↑m ↑n := sorry

@[simp] theorem land_to_nat (m : num) (n : num) : ↑(land m n) = nat.land ↑m ↑n := sorry

@[simp] theorem ldiff_to_nat (m : num) (n : num) : ↑(ldiff m n) = nat.ldiff ↑m ↑n := sorry

@[simp] theorem lxor_to_nat (m : num) (n : num) : ↑(lxor m n) = nat.lxor ↑m ↑n := sorry

@[simp] theorem shiftl_to_nat (m : num) (n : ℕ) : ↑(shiftl m n) = nat.shiftl (↑m) n := sorry

@[simp] theorem shiftr_to_nat (m : num) (n : ℕ) : ↑(shiftr m n) = nat.shiftr (↑m) n := sorry

@[simp] theorem test_bit_to_nat (m : num) (n : ℕ) : test_bit m n = nat.test_bit (↑m) n := sorry

end num


namespace znum


@[simp] theorem cast_zero {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] : ↑0 = 0 :=
  rfl

@[simp] theorem cast_zero' {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] : ↑zero = 0 :=
  rfl

@[simp] theorem cast_one {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] : ↑1 = 1 :=
  rfl

@[simp] theorem cast_pos {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] (n : pos_num) : ↑(pos n) = ↑n :=
  rfl

@[simp] theorem cast_neg {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] (n : pos_num) : ↑(neg n) = -↑n :=
  rfl

@[simp] theorem cast_zneg {α : Type u_1} [add_group α] [HasOne α] (n : znum) : ↑(-n) = -↑n :=
  znum.cases_on n (idRhs (0 = -0) (Eq.symm neg_zero)) (fun (n : pos_num) => idRhs (↑(-pos n) = ↑(-pos n)) rfl)
    fun (n : pos_num) => idRhs (↑(-neg n) = --↑(-neg n)) (Eq.symm (neg_neg ↑(-neg n)))

theorem neg_zero : -0 = 0 :=
  rfl

theorem zneg_pos (n : pos_num) : -pos n = neg n :=
  rfl

theorem zneg_neg (n : pos_num) : -neg n = pos n :=
  rfl

theorem zneg_zneg (n : znum) : --n = n :=
  znum.cases_on n (Eq.refl ( --zero)) (fun (n : pos_num) => Eq.refl ( --pos n)) fun (n : pos_num) => Eq.refl ( --neg n)

theorem zneg_bit1 (n : znum) : -znum.bit1 n = znum.bitm1 (-n) :=
  znum.cases_on n (Eq.refl (-znum.bit1 zero)) (fun (n : pos_num) => Eq.refl (-znum.bit1 (pos n)))
    fun (n : pos_num) => Eq.refl (-znum.bit1 (neg n))

theorem zneg_bitm1 (n : znum) : -znum.bitm1 n = znum.bit1 (-n) :=
  znum.cases_on n (Eq.refl (-znum.bitm1 zero)) (fun (n : pos_num) => Eq.refl (-znum.bitm1 (pos n)))
    fun (n : pos_num) => Eq.refl (-znum.bitm1 (neg n))

theorem zneg_succ (n : znum) : -succ n = pred (-n) := sorry

theorem zneg_pred (n : znum) : -pred n = succ (-n) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-pred n = succ (-n))) (Eq.symm (zneg_zneg (succ (-n))))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-pred n = --succ (-n))) (zneg_succ (-n))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (-pred n = -pred ( --n))) (zneg_zneg n))) (Eq.refl (-pred n))))

@[simp] theorem neg_of_int (n : ℤ) : ↑(-n) = -↑n :=
  int.cases_on n
    (fun (n : ℕ) => nat.cases_on n (idRhs (↑(-0) = ↑(-0)) rfl) fun (n : ℕ) => idRhs (↑(-↑(n + 1)) = ↑(-↑(n + 1))) rfl)
    fun (n : ℕ) => idRhs (↑(-Int.negSucc n) = --↑(-Int.negSucc n)) (Eq.symm (zneg_zneg ↑(-Int.negSucc n)))

@[simp] theorem abs_to_nat (n : znum) : ↑(abs n) = int.nat_abs ↑n := sorry

@[simp] theorem abs_to_znum (n : num) : abs (num.to_znum n) = n :=
  num.cases_on n (idRhs (abs (num.to_znum 0) = abs (num.to_znum 0)) rfl)
    fun (n : pos_num) => idRhs (abs (num.to_znum (num.pos n)) = abs (num.to_znum (num.pos n))) rfl

@[simp] theorem cast_to_int {α : Type u_1} [add_group α] [HasOne α] (n : znum) : ↑↑n = ↑n := sorry

theorem bit0_of_bit0 (n : znum) : bit0 n = znum.bit0 n :=
  znum.cases_on n (idRhs (bit0 0 = bit0 0) rfl)
    (fun (n : pos_num) => idRhs (pos (bit0 n) = pos (pos_num.bit0 n)) (congr_arg pos (pos_num.bit0_of_bit0 n)))
    fun (n : pos_num) => idRhs (neg (bit0 n) = neg (pos_num.bit0 n)) (congr_arg neg (pos_num.bit0_of_bit0 n))

theorem bit1_of_bit1 (n : znum) : bit1 n = znum.bit1 n := sorry

@[simp] theorem cast_bit0 {α : Type u_1} [add_group α] [HasOne α] (n : znum) : ↑(znum.bit0 n) = bit0 ↑n := sorry

@[simp] theorem cast_bit1 {α : Type u_1} [add_group α] [HasOne α] (n : znum) : ↑(znum.bit1 n) = bit1 ↑n := sorry

@[simp] theorem cast_bitm1 {α : Type u_1} [add_group α] [HasOne α] (n : znum) : ↑(znum.bitm1 n) = bit0 ↑n - 1 := sorry

theorem add_zero (n : znum) : n + 0 = n :=
  znum.cases_on n (Eq.refl (zero + 0)) (fun (n : pos_num) => Eq.refl (pos n + 0)) fun (n : pos_num) => Eq.refl (neg n + 0)

theorem zero_add (n : znum) : 0 + n = n :=
  znum.cases_on n (Eq.refl (0 + zero)) (fun (n : pos_num) => Eq.refl (0 + pos n)) fun (n : pos_num) => Eq.refl (0 + neg n)

theorem add_one (n : znum) : n + 1 = succ n := sorry

end znum


namespace pos_num


theorem cast_to_znum (n : pos_num) : ↑n = znum.pos n := sorry

theorem cast_sub' {α : Type u_1} [add_group α] [HasOne α] (m : pos_num) (n : pos_num) : ↑(sub' m n) = ↑m - ↑n := sorry

theorem to_nat_eq_succ_pred (n : pos_num) : ↑n = ↑(pred' n) + 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n = ↑(pred' n) + 1)) (Eq.symm (num.succ'_to_nat (pred' n)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n = ↑(num.succ' (pred' n)))) (succ'_pred' n))) (Eq.refl ↑n))

theorem to_int_eq_succ_pred (n : pos_num) : ↑n = ↑↑(pred' n) + 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n = ↑↑(pred' n) + 1)) (Eq.symm (to_nat_to_int n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑↑(pred' n) + 1)) (to_nat_eq_succ_pred n))) (Eq.refl ↑(↑(pred' n) + 1)))

end pos_num


namespace num


@[simp] theorem cast_sub' {α : Type u_1} [add_group α] [HasOne α] (m : num) (n : num) : ↑(sub' m n) = ↑m - ↑n := sorry

@[simp] theorem of_nat_to_znum (n : ℕ) : to_znum ↑n = ↑n := sorry

@[simp] theorem of_nat_to_znum_neg (n : ℕ) : to_znum_neg ↑n = -↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (to_znum_neg ↑n = -↑n)) (Eq.symm (of_nat_to_znum n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (to_znum_neg ↑n = -to_znum ↑n)) (zneg_to_znum ↑n))) (Eq.refl (to_znum_neg ↑n)))

theorem mem_of_znum' {m : num} {n : znum} : m ∈ of_znum' n ↔ n = to_znum m := sorry

theorem of_znum'_to_nat (n : znum) : coe <$> of_znum' n = int.to_nat' ↑n := sorry

@[simp] theorem of_znum_to_nat (n : znum) : ↑(of_znum n) = int.to_nat ↑n := sorry

@[simp] theorem cast_of_znum {α : Type u_1} [add_group α] [HasOne α] (n : znum) : ↑(of_znum n) = ↑(int.to_nat ↑n) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(of_znum n) = ↑(int.to_nat ↑n))) (Eq.symm (cast_to_nat (of_znum n)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑(of_znum n) = ↑(int.to_nat ↑n))) (of_znum_to_nat n))) (Eq.refl ↑(int.to_nat ↑n)))

@[simp] theorem sub_to_nat (m : num) (n : num) : ↑(m - n) = ↑m - ↑n := sorry

end num


namespace znum


@[simp] theorem cast_add {α : Type u_1} [add_group α] [HasOne α] (m : znum) (n : znum) : ↑(m + n) = ↑m + ↑n := sorry

@[simp] theorem cast_succ {α : Type u_1} [add_group α] [HasOne α] (n : znum) : ↑(succ n) = ↑n + 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(succ n) = ↑n + 1)) (Eq.symm (add_one n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(n + 1) = ↑n + 1)) (cast_add n 1)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑n + ↑1 = ↑n + 1)) cast_one)) (Eq.refl (↑n + 1))))

@[simp] theorem mul_to_int (m : znum) (n : znum) : ↑(m * n) = ↑m * ↑n := sorry

theorem cast_mul {α : Type u_1} [ring α] (m : znum) (n : znum) : ↑(m * n) = ↑m * ↑n := sorry

@[simp] theorem of_to_int (n : znum) : ↑↑n = n := sorry

theorem to_of_int (n : ℤ) : ↑↑n = n := sorry

theorem to_int_inj {m : znum} {n : znum} : ↑m = ↑n ↔ m = n :=
  { mp := fun (h : ↑m = ↑n) => function.left_inverse.injective of_to_int h, mpr := congr_arg fun (x : znum) => ↑x }

@[simp] theorem of_int_cast {α : Type u_1} [add_group α] [HasOne α] (n : ℤ) : ↑↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = ↑n)) (Eq.symm (cast_to_int ↑n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑↑n = ↑n)) (to_of_int n))) (Eq.refl ↑n))

@[simp] theorem of_nat_cast {α : Type u_1} [add_group α] [HasOne α] (n : ℕ) : ↑↑n = ↑n :=
  of_int_cast ↑n

@[simp] theorem of_int'_eq (n : ℤ) : of_int' n = ↑n := sorry

theorem cmp_to_int (m : znum) (n : znum) : ordering.cases_on (cmp m n) (↑m < ↑n) (m = n) (↑n < ↑m) := sorry

theorem lt_to_int {m : znum} {n : znum} : ↑m < ↑n ↔ m < n := sorry

theorem le_to_int {m : znum} {n : znum} : ↑m ≤ ↑n ↔ m ≤ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑m ≤ ↑n ↔ m ≤ n)) (Eq.symm (propext not_lt)))) (not_congr lt_to_int)

@[simp] theorem cast_lt {α : Type u_1} [linear_ordered_ring α] {m : znum} {n : znum} : ↑m < ↑n ↔ m < n := sorry

@[simp] theorem cast_le {α : Type u_1} [linear_ordered_ring α] {m : znum} {n : znum} : ↑m ≤ ↑n ↔ m ≤ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑m ≤ ↑n ↔ m ≤ n)) (Eq.symm (propext not_lt)))) (not_congr cast_lt)

@[simp] theorem cast_inj {α : Type u_1} [linear_ordered_ring α] {m : znum} {n : znum} : ↑m = ↑n ↔ m = n := sorry

/--
This tactic tries to turn an (in)equality about `znum`s to one about `int`s by rewriting.
```lean
example (n : znum) (m : znum) : n ≤ n + m * m :=
begin
  znum.transfer_rw,
  exact le_add_of_nonneg_right (mul_self_nonneg _)
end
```
-/
/--
This tactic tries to prove (in)equalities about `znum`s by transfering them to the `int` world and
then trying to call `simp`.
```lean
example (n : znum) (m : znum) : n ≤ n + m * m :=
begin
  znum.transfer,
  exact mul_self_nonneg _
end
```
-/
protected instance linear_order : linear_order znum :=
  linear_order.mk LessEq Less sorry sorry sorry sorry znum.decidable_le znum.decidable_eq znum.decidable_lt

protected instance add_comm_group : add_comm_group znum :=
  add_comm_group.mk Add.add sorry 0 zero_add add_zero Neg.neg
    (add_group.sub._default Add.add sorry 0 zero_add add_zero Neg.neg) sorry sorry

protected instance linear_ordered_comm_ring : linear_ordered_comm_ring znum :=
  linear_ordered_comm_ring.mk add_comm_group.add add_comm_group.add_assoc add_comm_group.zero add_comm_group.zero_add
    add_comm_group.add_zero add_comm_group.neg add_comm_group.sub add_comm_group.add_left_neg add_comm_group.add_comm
    Mul.mul sorry 1 sorry sorry sorry sorry linear_order.le linear_order.lt linear_order.le_refl linear_order.le_trans
    linear_order.le_antisymm sorry sorry sorry linear_order.le_total linear_order.decidable_le linear_order.decidable_eq
    linear_order.decidable_lt sorry sorry

@[simp] theorem dvd_to_int (m : znum) (n : znum) : ↑m ∣ ↑n ↔ m ∣ n := sorry

end znum


namespace pos_num


theorem divmod_to_nat_aux {n : pos_num} {d : pos_num} {q : num} {r : num} (h₁ : ↑r + ↑d * bit0 ↑q = ↑n) (h₂ : ↑r < bit0 1 * ↑d) : ↑(prod.snd (divmod_aux d q r)) + ↑d * ↑(prod.fst (divmod_aux d q r)) = ↑n ∧ ↑(prod.snd (divmod_aux d q r)) < ↑d := sorry

theorem divmod_to_nat (d : pos_num) (n : pos_num) : ↑n / ↑d = ↑(prod.fst (divmod d n)) ∧ ↑n % ↑d = ↑(prod.snd (divmod d n)) := sorry

@[simp] theorem div'_to_nat (n : pos_num) (d : pos_num) : ↑(div' n d) = ↑n / ↑d :=
  Eq.symm (and.left (divmod_to_nat d n))

@[simp] theorem mod'_to_nat (n : pos_num) (d : pos_num) : ↑(mod' n d) = ↑n % ↑d :=
  Eq.symm (and.right (divmod_to_nat d n))

end pos_num


namespace num


@[simp] theorem div_to_nat (n : num) (d : num) : ↑(n / d) = ↑n / ↑d := sorry

@[simp] theorem mod_to_nat (n : num) (d : num) : ↑(n % d) = ↑n % ↑d := sorry

theorem gcd_to_nat_aux {n : ℕ} {a : num} {b : num} : a ≤ b → nat_size (a * b) ≤ n → ↑(gcd_aux n a b) = nat.gcd ↑a ↑b := sorry

@[simp] theorem gcd_to_nat (a : num) (b : num) : ↑(gcd a b) = nat.gcd ↑a ↑b := sorry

theorem dvd_iff_mod_eq_zero {m : num} {n : num} : m ∣ n ↔ n % m = 0 := sorry

protected instance decidable_dvd : DecidableRel has_dvd.dvd :=
  sorry

end num


protected instance pos_num.decidable_dvd : DecidableRel has_dvd.dvd :=
  sorry

namespace znum


@[simp] theorem div_to_int (n : znum) (d : znum) : ↑(n / d) = ↑n / ↑d := sorry

@[simp] theorem mod_to_int (n : znum) (d : znum) : ↑(n % d) = ↑n % ↑d := sorry

@[simp] theorem gcd_to_nat (a : znum) (b : znum) : ↑(gcd a b) = int.gcd ↑a ↑b := sorry

theorem dvd_iff_mod_eq_zero {m : znum} {n : znum} : m ∣ n ↔ n % m = 0 := sorry

protected instance has_dvd.dvd.decidable_rel : DecidableRel has_dvd.dvd :=
  sorry

end znum


namespace int


/-- Cast a `snum` to the corresponding integer. -/
def of_snum : snum → ℤ :=
  snum.rec' (fun (a : Bool) => cond a (-1) 0) fun (a : Bool) (p : snum) (IH : ℤ) => cond a (bit1 IH) (bit0 IH)

end int


protected instance int.snum_coe : has_coe snum ℤ :=
  has_coe.mk int.of_snum

protected instance snum.has_lt : HasLess snum :=
  { Less := fun (a b : snum) => ↑a < ↑b }

protected instance snum.has_le : HasLessEq snum :=
  { LessEq := fun (a b : snum) => ↑a ≤ ↑b }

