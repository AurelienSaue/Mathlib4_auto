/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.basic
import Mathlib.algebra.order_functions
import PostPort

universes u_1 u 

namespace Mathlib

namespace int


protected instance inhabited : Inhabited ℤ :=
  { default := int.zero }

protected instance nontrivial : nontrivial ℤ :=
  nontrivial.mk (Exists.intro 0 (Exists.intro 1 int.zero_ne_one))

protected instance comm_ring : comm_ring ℤ :=
  comm_ring.mk int.add int.add_assoc int.zero int.zero_add int.add_zero int.neg int.sub int.add_left_neg int.add_comm
    int.mul int.mul_assoc int.one int.one_mul int.mul_one int.distrib_left int.distrib_right int.mul_comm

/-! ### Extra instances to short-circuit type class resolution -/

-- instance : has_sub int            := by apply_instance -- This is in core

protected instance add_comm_monoid : add_comm_monoid ℤ :=
  add_comm_group.to_add_comm_monoid ℤ

protected instance add_monoid : add_monoid ℤ :=
  sub_neg_monoid.to_add_monoid ℤ

protected instance monoid : monoid ℤ :=
  ring.to_monoid ℤ

protected instance comm_monoid : comm_monoid ℤ :=
  comm_semiring.to_comm_monoid ℤ

protected instance comm_semigroup : comm_semigroup ℤ :=
  comm_ring.to_comm_semigroup ℤ

protected instance semigroup : semigroup ℤ :=
  monoid.to_semigroup ℤ

protected instance add_comm_semigroup : add_comm_semigroup ℤ :=
  add_comm_monoid.to_add_comm_semigroup ℤ

protected instance add_semigroup : add_semigroup ℤ :=
  add_monoid.to_add_semigroup ℤ

protected instance comm_semiring : comm_semiring ℤ :=
  comm_ring.to_comm_semiring

protected instance semiring : semiring ℤ :=
  ring.to_semiring

protected instance ring : ring ℤ :=
  comm_ring.to_ring ℤ

protected instance distrib : distrib ℤ :=
  ring.to_distrib ℤ

protected instance linear_ordered_comm_ring : linear_ordered_comm_ring ℤ :=
  linear_ordered_comm_ring.mk comm_ring.add comm_ring.add_assoc comm_ring.zero comm_ring.zero_add comm_ring.add_zero
    comm_ring.neg comm_ring.sub comm_ring.add_left_neg comm_ring.add_comm comm_ring.mul comm_ring.mul_assoc comm_ring.one
    comm_ring.one_mul comm_ring.mul_one comm_ring.left_distrib comm_ring.right_distrib linear_order.le linear_order.lt
    linear_order.le_refl linear_order.le_trans linear_order.le_antisymm int.add_le_add_left sorry int.mul_pos
    linear_order.le_total linear_order.decidable_le linear_order.decidable_eq linear_order.decidable_lt
    nontrivial.exists_pair_ne comm_ring.mul_comm

protected instance linear_ordered_add_comm_group : linear_ordered_add_comm_group ℤ :=
  linear_ordered_ring.to_linear_ordered_add_comm_group

theorem abs_eq_nat_abs (a : ℤ) : abs a = ↑(nat_abs a) :=
  int.cases_on a (fun (a : ℕ) => idRhs (abs ↑a = ↑a) (abs_of_nonneg (coe_zero_le a)))
    fun (a : ℕ) => idRhs (abs (Int.negSucc a) = -Int.negSucc a) (abs_of_nonpos (le_of_lt (neg_succ_lt_zero a)))

theorem nat_abs_abs (a : ℤ) : nat_abs (abs a) = nat_abs a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs (abs a) = nat_abs a)) (abs_eq_nat_abs a))) (Eq.refl (nat_abs ↑(nat_abs a)))

theorem sign_mul_abs (a : ℤ) : sign a * abs a = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sign a * abs a = a)) (abs_eq_nat_abs a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sign a * ↑(nat_abs a) = a)) (sign_mul_nat_abs a))) (Eq.refl a))

@[simp] theorem default_eq_zero : Inhabited.default = 0 :=
  rfl

@[simp] theorem add_def {a : ℤ} {b : ℤ} : int.add a b = a + b :=
  rfl

@[simp] theorem mul_def {a : ℤ} {b : ℤ} : int.mul a b = a * b :=
  rfl

@[simp] theorem coe_nat_mul_neg_succ (m : ℕ) (n : ℕ) : ↑m * Int.negSucc n = -(↑m * ↑(Nat.succ n)) :=
  rfl

@[simp] theorem neg_succ_mul_coe_nat (m : ℕ) (n : ℕ) : Int.negSucc m * ↑n = -(↑(Nat.succ m) * ↑n) :=
  rfl

@[simp] theorem neg_succ_mul_neg_succ (m : ℕ) (n : ℕ) : Int.negSucc m * Int.negSucc n = ↑(Nat.succ m) * ↑(Nat.succ n) :=
  rfl

@[simp] theorem coe_nat_le {m : ℕ} {n : ℕ} : ↑m ≤ ↑n ↔ m ≤ n :=
  coe_nat_le_coe_nat_iff m n

@[simp] theorem coe_nat_lt {m : ℕ} {n : ℕ} : ↑m < ↑n ↔ m < n :=
  coe_nat_lt_coe_nat_iff m n

@[simp] theorem coe_nat_inj' {m : ℕ} {n : ℕ} : ↑m = ↑n ↔ m = n :=
  int.coe_nat_eq_coe_nat_iff m n

@[simp] theorem coe_nat_pos {n : ℕ} : 0 < ↑n ↔ 0 < n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < ↑n ↔ 0 < n)) (Eq.symm int.coe_nat_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑0 < ↑n ↔ 0 < n)) (propext coe_nat_lt))) (iff.refl (0 < n)))

@[simp] theorem coe_nat_eq_zero {n : ℕ} : ↑n = 0 ↔ n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n = 0 ↔ n = 0)) (Eq.symm int.coe_nat_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n = ↑0 ↔ n = 0)) (propext coe_nat_inj'))) (iff.refl (n = 0)))

theorem coe_nat_ne_zero {n : ℕ} : ↑n ≠ 0 ↔ n ≠ 0 :=
  not_congr coe_nat_eq_zero

@[simp] theorem coe_nat_nonneg (n : ℕ) : 0 ≤ ↑n :=
  iff.mpr coe_nat_le (nat.zero_le n)

theorem coe_nat_ne_zero_iff_pos {n : ℕ} : ↑n ≠ 0 ↔ 0 < n :=
  { mp := fun (h : ↑n ≠ 0) => nat.pos_of_ne_zero (iff.mp coe_nat_ne_zero h),
    mpr := fun (h : 0 < n) => ne.symm (ne_of_lt (iff.mpr coe_nat_lt h)) }

theorem coe_nat_succ_pos (n : ℕ) : 0 < ↑(Nat.succ n) :=
  iff.mpr coe_nat_pos (nat.succ_pos n)

@[simp] theorem coe_nat_abs (n : ℕ) : abs ↑n = ↑n :=
  abs_of_nonneg (coe_nat_nonneg n)

/-! ### succ and pred -/

/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) : ℤ :=
  a + 1

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) : ℤ :=
  a - 1

theorem nat_succ_eq_int_succ (n : ℕ) : ↑(Nat.succ n) = succ ↑n :=
  rfl

theorem pred_succ (a : ℤ) : pred (succ a) = a :=
  add_sub_cancel a 1

theorem succ_pred (a : ℤ) : succ (pred a) = a :=
  sub_add_cancel a 1

theorem neg_succ (a : ℤ) : -succ a = pred (-a) :=
  neg_add a 1

theorem succ_neg_succ (a : ℤ) : succ (-succ a) = -a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (succ (-succ a) = -a)) (neg_succ a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (succ (pred (-a)) = -a)) (succ_pred (-a)))) (Eq.refl (-a)))

theorem neg_pred (a : ℤ) : -pred a = succ (-a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-pred a = succ (-a))) (eq_neg_of_eq_neg (Eq.symm (neg_succ (-a))))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-pred a = -pred ( --a))) (neg_neg a))) (Eq.refl (-pred a)))

theorem pred_neg_pred (a : ℤ) : pred (-pred a) = -a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (pred (-pred a) = -a)) (neg_pred a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (pred (succ (-a)) = -a)) (pred_succ (-a)))) (Eq.refl (-a)))

theorem pred_nat_succ (n : ℕ) : pred ↑(Nat.succ n) = ↑n :=
  pred_succ ↑n

theorem neg_nat_succ (n : ℕ) : -↑(Nat.succ n) = pred (-↑n) :=
  neg_succ ↑n

theorem succ_neg_nat_succ (n : ℕ) : succ (-↑(Nat.succ n)) = -↑n :=
  succ_neg_succ ↑n

theorem lt_succ_self (a : ℤ) : a < succ a :=
  lt_add_of_pos_right a zero_lt_one

theorem pred_self_lt (a : ℤ) : pred a < a :=
  sub_lt_self a zero_lt_one

theorem add_one_le_iff {a : ℤ} {b : ℤ} : a + 1 ≤ b ↔ a < b :=
  iff.rfl

theorem lt_add_one_iff {a : ℤ} {b : ℤ} : a < b + 1 ↔ a ≤ b :=
  add_le_add_iff_right 1

theorem le_add_one {a : ℤ} {b : ℤ} (h : a ≤ b) : a ≤ b + 1 :=
  le_of_lt (iff.mpr lt_add_one_iff h)

theorem sub_one_lt_iff {a : ℤ} {b : ℤ} : a - 1 < b ↔ a ≤ b :=
  iff.trans sub_lt_iff_lt_add lt_add_one_iff

theorem le_sub_one_iff {a : ℤ} {b : ℤ} : a ≤ b - 1 ↔ a < b :=
  le_sub_iff_add_le

protected theorem induction_on {p : ℤ → Prop} (i : ℤ) (hz : p 0) (hp : ∀ (i : ℕ), p ↑i → p (↑i + 1)) (hn : ∀ (i : ℕ), p (-↑i) → p (-↑i - 1)) : p i := sorry

/-- Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater
  than `b`, and the `pred` of a number less than `b`. -/
protected def induction_on' {C : ℤ → Sort u_1} (z : ℤ) (b : ℤ) : C b → ((k : ℤ) → b ≤ k → C k → C (k + 1)) → ((k : ℤ) → k ≤ b → C k → C (k - 1)) → C z :=
  fun (H0 : C b) (Hs : (k : ℤ) → b ≤ k → C k → C (k + 1)) (Hp : (k : ℤ) → k ≤ b → C k → C (k - 1)) =>
    eq.mpr sorry
      (Int.rec
        (fun (n : ℕ) =>
          Nat.rec (eq.mpr sorry (eq.mpr sorry H0))
            (fun (n : ℕ) (ih : C (Int.ofNat n + b)) =>
              eq.mpr sorry (eq.mpr sorry (eq.mpr sorry (eq.mpr sorry (Hs (Int.ofNat n + b) sorry ih)))))
            n)
        (fun (n : ℕ) =>
          Nat.rec (eq.mpr sorry (eq.mpr sorry (eq.mpr sorry (eq.mpr sorry (eq.mpr sorry (Hp b sorry H0))))))
            (fun (n : ℕ) (ih : C (Int.negSucc n + b)) =>
              eq.mpr sorry (eq.mpr sorry (eq.mpr sorry (eq.mpr sorry (Hp (Int.negSucc n + b) sorry ih)))))
            n)
        (z - b))

/-! ### nat abs -/

theorem nat_abs_add_le (a : ℤ) (b : ℤ) : nat_abs (a + b) ≤ nat_abs a + nat_abs b := sorry

theorem nat_abs_neg_of_nat (n : ℕ) : nat_abs (neg_of_nat n) = n :=
  nat.cases_on n (Eq.refl (nat_abs (neg_of_nat 0))) fun (n : ℕ) => Eq.refl (nat_abs (neg_of_nat (Nat.succ n)))

theorem nat_abs_mul (a : ℤ) (b : ℤ) : nat_abs (a * b) = nat_abs a * nat_abs b := sorry

theorem nat_abs_mul_nat_abs_eq {a : ℤ} {b : ℤ} {c : ℕ} (h : a * b = ↑c) : nat_abs a * nat_abs b = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs a * nat_abs b = c)) (Eq.symm (nat_abs_mul a b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs (a * b) = c)) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs ↑c = c)) (nat_abs_of_nat c))) (Eq.refl c)))

@[simp] theorem nat_abs_mul_self' (a : ℤ) : ↑(nat_abs a) * ↑(nat_abs a) = a * a :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (↑(nat_abs a) * ↑(nat_abs a) = a * a)) (Eq.symm (int.coe_nat_mul (nat_abs a) (nat_abs a)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(nat_abs a * nat_abs a) = a * a)) nat_abs_mul_self)) (Eq.refl (a * a)))

theorem neg_succ_of_nat_eq' (m : ℕ) : Int.negSucc m = -↑m - 1 := sorry

theorem nat_abs_ne_zero_of_ne_zero {z : ℤ} (hz : z ≠ 0) : nat_abs z ≠ 0 :=
  fun (h : nat_abs z = 0) => hz (eq_zero_of_nat_abs_eq_zero h)

@[simp] theorem nat_abs_eq_zero {a : ℤ} : nat_abs a = 0 ↔ a = 0 :=
  { mp := eq_zero_of_nat_abs_eq_zero, mpr := fun (h : a = 0) => Eq.symm h ▸ rfl }

theorem nat_abs_lt_nat_abs_of_nonneg_of_lt {a : ℤ} {b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) : nat_abs a < nat_abs b := sorry

theorem nat_abs_eq_iff_mul_self_eq {a : ℤ} {b : ℤ} : nat_abs a = nat_abs b ↔ a * a = b * b := sorry

theorem nat_abs_lt_iff_mul_self_lt {a : ℤ} {b : ℤ} : nat_abs a < nat_abs b ↔ a * a < b * b := sorry

theorem nat_abs_le_iff_mul_self_le {a : ℤ} {b : ℤ} : nat_abs a ≤ nat_abs b ↔ a * a ≤ b * b := sorry

theorem nat_abs_eq_iff_sq_eq {a : ℤ} {b : ℤ} : nat_abs a = nat_abs b ↔ a ^ bit0 1 = b ^ bit0 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs a = nat_abs b ↔ a ^ bit0 1 = b ^ bit0 1)) (pow_two a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs a = nat_abs b ↔ a * a = b ^ bit0 1)) (pow_two b)))
      nat_abs_eq_iff_mul_self_eq)

theorem nat_abs_lt_iff_sq_lt {a : ℤ} {b : ℤ} : nat_abs a < nat_abs b ↔ a ^ bit0 1 < b ^ bit0 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs a < nat_abs b ↔ a ^ bit0 1 < b ^ bit0 1)) (pow_two a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs a < nat_abs b ↔ a * a < b ^ bit0 1)) (pow_two b)))
      nat_abs_lt_iff_mul_self_lt)

theorem nat_abs_le_iff_sq_le {a : ℤ} {b : ℤ} : nat_abs a ≤ nat_abs b ↔ a ^ bit0 1 ≤ b ^ bit0 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs a ≤ nat_abs b ↔ a ^ bit0 1 ≤ b ^ bit0 1)) (pow_two a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nat_abs a ≤ nat_abs b ↔ a * a ≤ b ^ bit0 1)) (pow_two b)))
      nat_abs_le_iff_mul_self_le)

/-! ### `/`  -/

@[simp] theorem of_nat_div (m : ℕ) (n : ℕ) : Int.ofNat (m / n) = Int.ofNat m / Int.ofNat n :=
  rfl

@[simp] theorem coe_nat_div (m : ℕ) (n : ℕ) : ↑(m / n) = ↑m / ↑n :=
  rfl

theorem neg_succ_of_nat_div (m : ℕ) {b : ℤ} (H : 0 < b) : Int.negSucc m / b = -(↑m / b + 1) := sorry

@[simp] protected theorem div_neg (a : ℤ) (b : ℤ) : a / -b = -(a / b) := sorry

theorem div_of_neg_of_pos {a : ℤ} {b : ℤ} (Ha : a < 0) (Hb : 0 < b) : a / b = -((-a - 1) / b + 1) := sorry

protected theorem div_nonneg {a : ℤ} {b : ℤ} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a / b := sorry

protected theorem div_nonpos {a : ℤ} {b : ℤ} (Ha : 0 ≤ a) (Hb : b ≤ 0) : a / b ≤ 0 :=
  nonpos_of_neg_nonneg
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ -(a / b))) (Eq.symm (int.div_neg a b))))
      (int.div_nonneg Ha (neg_nonneg_of_nonpos Hb)))

theorem div_neg' {a : ℤ} {b : ℤ} (Ha : a < 0) (Hb : 0 < b) : a / b < 0 := sorry

-- Will be generalized to Euclidean domains.

protected theorem zero_div (b : ℤ) : 0 / b = 0 :=
  int.cases_on b
    (fun (b : ℕ) => nat.cases_on b (idRhs (0 / 0 = 0 / 0) rfl) fun (b : ℕ) => idRhs (0 / ↑(b + 1) = 0 / ↑(b + 1)) rfl)
    fun (b : ℕ) => idRhs (0 / Int.negSucc b = 0 / Int.negSucc b) rfl

protected theorem div_zero (a : ℤ) : a / 0 = 0 :=
  int.cases_on a
    (fun (a : ℕ) => nat.cases_on a (idRhs (0 / 0 = 0 / 0) rfl) fun (a : ℕ) => idRhs (↑(a + 1) / 0 = ↑(a + 1) / 0) rfl)
    fun (a : ℕ) => idRhs (Int.negSucc a / 0 = Int.negSucc a / 0) rfl

@[simp] protected theorem div_one (a : ℤ) : a / 1 = a := sorry

theorem div_eq_zero_of_lt {a : ℤ} {b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a / b = 0 := sorry

theorem div_eq_zero_of_lt_abs {a : ℤ} {b : ℤ} (H1 : 0 ≤ a) (H2 : a < abs b) : a / b = 0 := sorry

protected theorem add_mul_div_right (a : ℤ) (b : ℤ) {c : ℤ} (H : c ≠ 0) : (a + b * c) / c = a / c + b := sorry

protected theorem add_mul_div_left (a : ℤ) {b : ℤ} (c : ℤ) (H : b ≠ 0) : (a + b * c) / b = a / b + c :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a + b * c) / b = a / b + c)) (mul_comm b c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((a + c * b) / b = a / b + c)) (int.add_mul_div_right a c H))) (Eq.refl (a / b + c)))

protected theorem add_div_of_dvd_right {a : ℤ} {b : ℤ} {c : ℤ} (H : c ∣ b) : (a + b) / c = a / c + b / c := sorry

protected theorem add_div_of_dvd_left {a : ℤ} {b : ℤ} {c : ℤ} (H : c ∣ a) : (a + b) / c = a / c + b / c := sorry

@[simp] protected theorem mul_div_cancel (a : ℤ) {b : ℤ} (H : b ≠ 0) : a * b / b = a :=
  eq.mp (Eq._oldrec (Eq.refl (a * b / b = 0 + a)) (zero_add a))
    (eq.mp (Eq._oldrec (Eq.refl (a * b / b = 0 / b + a)) (int.zero_div b))
      (eq.mp (Eq._oldrec (Eq.refl ((0 + a * b) / b = 0 / b + a)) (zero_add (a * b))) (int.add_mul_div_right 0 a H)))

@[simp] protected theorem mul_div_cancel_left {a : ℤ} (b : ℤ) (H : a ≠ 0) : a * b / a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b / a = b)) (mul_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a / a = b)) (int.mul_div_cancel b H))) (Eq.refl b))

@[simp] protected theorem div_self {a : ℤ} (H : a ≠ 0) : a / a = 1 :=
  eq.mp (Eq._oldrec (Eq.refl (1 * a / a = 1)) (one_mul a)) (int.mul_div_cancel 1 H)

/-! ### mod -/

theorem of_nat_mod (m : ℕ) (n : ℕ) : ↑m % ↑n = Int.ofNat (m % n) :=
  rfl

@[simp] theorem coe_nat_mod (m : ℕ) (n : ℕ) : ↑(m % n) = ↑m % ↑n :=
  rfl

theorem neg_succ_of_nat_mod (m : ℕ) {b : ℤ} (bpos : 0 < b) : Int.negSucc m % b = b - 1 - ↑m % b := sorry

@[simp] theorem mod_neg (a : ℤ) (b : ℤ) : a % -b = a % b := sorry

@[simp] theorem mod_abs (a : ℤ) (b : ℤ) : a % abs b = a % b :=
  abs_by_cases (fun (i : ℤ) => a % i = a % b) rfl (mod_neg a b)

theorem zero_mod (b : ℤ) : 0 % b = 0 :=
  congr_arg Int.ofNat (nat.zero_mod (nat_abs b))

theorem mod_zero (a : ℤ) : a % 0 = a :=
  int.cases_on a (fun (a : ℕ) => idRhs (Int.ofNat (a % 0) = Int.ofNat a) (congr_arg Int.ofNat (nat.mod_zero a)))
    fun (a : ℕ) => idRhs (Int.negSucc (a % 0) = Int.negSucc a) (congr_arg Int.negSucc (nat.mod_zero a))

theorem mod_one (a : ℤ) : a % 1 = 0 := sorry

theorem mod_eq_of_lt {a : ℤ} {b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a := sorry

theorem mod_nonneg (a : ℤ) {b : ℤ} : b ≠ 0 → 0 ≤ a % b := sorry

theorem mod_lt_of_pos (a : ℤ) {b : ℤ} (H : 0 < b) : a % b < b := sorry

theorem mod_lt (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b < abs b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a % b < abs b)) (Eq.symm (mod_abs a b)))) (mod_lt_of_pos a (iff.mpr abs_pos H))

theorem mod_add_div_aux (m : ℕ) (n : ℕ) : ↑n - (↑m % ↑n + 1) - (↑n * (↑m / ↑n) + ↑n) = Int.negSucc m := sorry

theorem mod_add_div (a : ℤ) (b : ℤ) : a % b + b * (a / b) = a := sorry

theorem div_add_mod (a : ℤ) (b : ℤ) : b * (a / b) + a % b = a :=
  Eq.trans (add_comm (b * (a / b)) (a % b)) (mod_add_div a b)

theorem mod_def (a : ℤ) (b : ℤ) : a % b = a - b * (a / b) :=
  eq_sub_of_add_eq (mod_add_div a b)

@[simp] theorem add_mul_mod_self {a : ℤ} {b : ℤ} {c : ℤ} : (a + b * c) % c = a % c := sorry

@[simp] theorem add_mul_mod_self_left (a : ℤ) (b : ℤ) (c : ℤ) : (a + b * c) % b = a % b :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a + b * c) % b = a % b)) (mul_comm b c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((a + c * b) % b = a % b)) add_mul_mod_self)) (Eq.refl (a % b)))

@[simp] theorem add_mod_self {a : ℤ} {b : ℤ} : (a + b) % b = a % b :=
  eq.mp (Eq._oldrec (Eq.refl ((a + b * 1) % b = a % b)) (mul_one b)) (add_mul_mod_self_left a b 1)

@[simp] theorem add_mod_self_left {a : ℤ} {b : ℤ} : (a + b) % a = b % a :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a + b) % a = b % a)) (add_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((b + a) % a = b % a)) add_mod_self)) (Eq.refl (b % a)))

@[simp] theorem mod_add_mod (m : ℤ) (n : ℤ) (k : ℤ) : (m % n + k) % n = (m + k) % n := sorry

@[simp] theorem add_mod_mod (m : ℤ) (n : ℤ) (k : ℤ) : (m + n % k) % k = (m + n) % k :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((m + n % k) % k = (m + n) % k)) (add_comm m (n % k))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((n % k + m) % k = (m + n) % k)) (mod_add_mod n k m)))
      (eq.mpr (id (Eq._oldrec (Eq.refl ((n + m) % k = (m + n) % k)) (add_comm n m))) (Eq.refl ((m + n) % k))))

theorem add_mod (a : ℤ) (b : ℤ) (n : ℤ) : (a + b) % n = (a % n + b % n) % n :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a + b) % n = (a % n + b % n) % n)) (add_mod_mod (a % n) b n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((a + b) % n = (a % n + b) % n)) (mod_add_mod a n b))) (Eq.refl ((a + b) % n)))

theorem add_mod_eq_add_mod_right {m : ℤ} {n : ℤ} {k : ℤ} (i : ℤ) (H : m % n = k % n) : (m + i) % n = (k + i) % n :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((m + i) % n = (k + i) % n)) (Eq.symm (mod_add_mod m n i))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((m % n + i) % n = (k + i) % n)) (Eq.symm (mod_add_mod k n i))))
      (eq.mpr (id (Eq._oldrec (Eq.refl ((m % n + i) % n = (k % n + i) % n)) H)) (Eq.refl ((k % n + i) % n))))

theorem add_mod_eq_add_mod_left {m : ℤ} {n : ℤ} {k : ℤ} (i : ℤ) (H : m % n = k % n) : (i + m) % n = (i + k) % n :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((i + m) % n = (i + k) % n)) (add_comm i m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((m + i) % n = (i + k) % n)) (add_mod_eq_add_mod_right i H)))
      (eq.mpr (id (Eq._oldrec (Eq.refl ((k + i) % n = (i + k) % n)) (add_comm k i))) (Eq.refl ((i + k) % n))))

theorem mod_add_cancel_right {m : ℤ} {n : ℤ} {k : ℤ} (i : ℤ) : (m + i) % n = (k + i) % n ↔ m % n = k % n := sorry

theorem mod_add_cancel_left {m : ℤ} {n : ℤ} {k : ℤ} {i : ℤ} : (i + m) % n = (i + k) % n ↔ m % n = k % n := sorry

theorem mod_sub_cancel_right {m : ℤ} {n : ℤ} {k : ℤ} (i : ℤ) : (m - i) % n = (k - i) % n ↔ m % n = k % n :=
  mod_add_cancel_right (-i)

theorem mod_eq_mod_iff_mod_sub_eq_zero {m : ℤ} {n : ℤ} {k : ℤ} : m % n = k % n ↔ (m - k) % n = 0 := sorry

@[simp] theorem mul_mod_left (a : ℤ) (b : ℤ) : a * b % b = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b % b = 0)) (Eq.symm (zero_add (a * b)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((0 + a * b) % b = 0)) add_mul_mod_self))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 % b = 0)) (zero_mod b))) (Eq.refl 0)))

@[simp] theorem mul_mod_right (a : ℤ) (b : ℤ) : a * b % a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b % a = 0)) (mul_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a % a = 0)) (mul_mod_left b a))) (Eq.refl 0))

theorem mul_mod (a : ℤ) (b : ℤ) (n : ℤ) : a * b % n = a % n * (b % n) % n := sorry

@[simp] theorem neg_mod_two (i : ℤ) : -i % bit0 1 = i % bit0 1 := sorry

theorem mod_self {a : ℤ} : a % a = 0 :=
  eq.mp (Eq._oldrec (Eq.refl (1 * a % a = 0)) (one_mul a)) (mul_mod_left 1 a)

@[simp] theorem mod_mod_of_dvd (n : ℤ) {m : ℤ} {k : ℤ} (h : m ∣ k) : n % k % m = n % m := sorry

@[simp] theorem mod_mod (a : ℤ) (b : ℤ) : a % b % b = a % b := sorry

theorem sub_mod (a : ℤ) (b : ℤ) (n : ℤ) : (a - b) % n = (a % n - b % n) % n := sorry

/-! ### properties of `/` and `%` -/

@[simp] theorem mul_div_mul_of_pos {a : ℤ} (b : ℤ) (c : ℤ) (H : 0 < a) : a * b / (a * c) = b / c := sorry

@[simp] theorem mul_div_mul_of_pos_left (a : ℤ) {b : ℤ} (c : ℤ) (H : 0 < b) : a * b / (c * b) = a / c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b / (c * b) = a / c)) (mul_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a / (c * b) = a / c)) (mul_comm c b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b * a / (b * c) = a / c)) (mul_div_mul_of_pos a c H))) (Eq.refl (a / c))))

@[simp] theorem mul_mod_mul_of_pos {a : ℤ} (b : ℤ) (c : ℤ) (H : 0 < a) : a * b % (a * c) = a * (b % c) := sorry

theorem lt_div_add_one_mul_self (a : ℤ) {b : ℤ} (H : 0 < b) : a < (a / b + 1) * b := sorry

theorem abs_div_le_abs (a : ℤ) (b : ℤ) : abs (a / b) ≤ abs a := sorry

theorem div_le_self {a : ℤ} (b : ℤ) (Ha : 0 ≤ a) : a / b ≤ a :=
  eq.mp (Eq._oldrec (Eq.refl (a / b ≤ abs a)) (abs_of_nonneg Ha)) (le_trans (le_abs_self (a / b)) (abs_div_le_abs a b))

theorem mul_div_cancel_of_mod_eq_zero {a : ℤ} {b : ℤ} (H : a % b = 0) : b * (a / b) = a :=
  eq.mp (Eq._oldrec (Eq.refl (0 + b * (a / b) = a)) (zero_add (b * (a / b))))
    (eq.mp (Eq._oldrec (Eq.refl (a % b + b * (a / b) = a)) H) (mod_add_div a b))

theorem div_mul_cancel_of_mod_eq_zero {a : ℤ} {b : ℤ} (H : a % b = 0) : a / b * b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b * b = a)) (mul_comm (a / b) b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * (a / b) = a)) (mul_div_cancel_of_mod_eq_zero H))) (Eq.refl a))

theorem mod_two_eq_zero_or_one (n : ℤ) : n % bit0 1 = 0 ∨ n % bit0 1 = 1 := sorry

/-! ### dvd -/

theorem coe_nat_dvd {m : ℕ} {n : ℕ} : ↑m ∣ ↑n ↔ m ∣ n := sorry

theorem coe_nat_dvd_left {n : ℕ} {z : ℤ} : ↑n ∣ z ↔ n ∣ nat_abs z := sorry

theorem coe_nat_dvd_right {n : ℕ} {z : ℤ} : z ∣ ↑n ↔ nat_abs z ∣ n := sorry

theorem dvd_antisymm {a : ℤ} {b : ℤ} (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b := sorry

theorem dvd_of_mod_eq_zero {a : ℤ} {b : ℤ} (H : b % a = 0) : a ∣ b :=
  Exists.intro (b / a) (Eq.symm (mul_div_cancel_of_mod_eq_zero H))

theorem mod_eq_zero_of_dvd {a : ℤ} {b : ℤ} : a ∣ b → b % a = 0 := sorry

theorem dvd_iff_mod_eq_zero (a : ℤ) (b : ℤ) : a ∣ b ↔ b % a = 0 :=
  { mp := mod_eq_zero_of_dvd, mpr := dvd_of_mod_eq_zero }

/-- If `a % b = c` then `b` divides `a - c`. -/
theorem dvd_sub_of_mod_eq {a : ℤ} {b : ℤ} {c : ℤ} (h : a % b = c) : b ∣ a - c := sorry

theorem nat_abs_dvd {a : ℤ} {b : ℤ} : ↑(nat_abs a) ∣ b ↔ a ∣ b := sorry

theorem dvd_nat_abs {a : ℤ} {b : ℤ} : a ∣ ↑(nat_abs b) ↔ a ∣ b := sorry

protected instance decidable_dvd : DecidableRel has_dvd.dvd :=
  fun (a n : ℤ) => decidable_of_decidable_of_iff (int.decidable_eq (n % a) 0) sorry

protected theorem div_mul_cancel {a : ℤ} {b : ℤ} (H : b ∣ a) : a / b * b = a :=
  div_mul_cancel_of_mod_eq_zero (mod_eq_zero_of_dvd H)

protected theorem mul_div_cancel' {a : ℤ} {b : ℤ} (H : a ∣ b) : a * (b / a) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (b / a) = b)) (mul_comm a (b / a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b / a * a = b)) (int.div_mul_cancel H))) (Eq.refl b))

protected theorem mul_div_assoc (a : ℤ) {b : ℤ} {c : ℤ} : c ∣ b → a * b / c = a * (b / c) := sorry

protected theorem mul_div_assoc' (b : ℤ) {a : ℤ} {c : ℤ} (h : c ∣ a) : a * b / c = a / c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b / c = a / c * b)) (mul_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a / c = a / c * b)) (int.mul_div_assoc b h)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b * (a / c) = a / c * b)) (mul_comm b (a / c)))) (Eq.refl (a / c * b))))

theorem div_dvd_div {a : ℤ} {b : ℤ} {c : ℤ} (H1 : a ∣ b) (H2 : b ∣ c) : b / a ∣ c / a := sorry

protected theorem eq_mul_of_div_eq_right {a : ℤ} {b : ℤ} {c : ℤ} (H1 : b ∣ a) (H2 : a / b = c) : a = b * c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = b * c)) (Eq.symm H2)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = b * (a / b))) (int.mul_div_cancel' H1))) (Eq.refl a))

protected theorem div_eq_of_eq_mul_right {a : ℤ} {b : ℤ} {c : ℤ} (H1 : b ≠ 0) (H2 : a = b * c) : a / b = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b = c)) H2))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * c / b = c)) (int.mul_div_cancel_left c H1))) (Eq.refl c))

protected theorem eq_div_of_mul_eq_right {a : ℤ} {b : ℤ} {c : ℤ} (H1 : a ≠ 0) (H2 : a * b = c) : b = c / a :=
  Eq.symm (int.div_eq_of_eq_mul_right H1 (Eq.symm H2))

protected theorem div_eq_iff_eq_mul_right {a : ℤ} {b : ℤ} {c : ℤ} (H : b ≠ 0) (H' : b ∣ a) : a / b = c ↔ a = b * c :=
  { mp := int.eq_mul_of_div_eq_right H', mpr := int.div_eq_of_eq_mul_right H }

protected theorem div_eq_iff_eq_mul_left {a : ℤ} {b : ℤ} {c : ℤ} (H : b ≠ 0) (H' : b ∣ a) : a / b = c ↔ a = c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b = c ↔ a = c * b)) (mul_comm c b))) (int.div_eq_iff_eq_mul_right H H')

protected theorem eq_mul_of_div_eq_left {a : ℤ} {b : ℤ} {c : ℤ} (H1 : b ∣ a) (H2 : a / b = c) : a = c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = c * b)) (mul_comm c b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = b * c)) (int.eq_mul_of_div_eq_right H1 H2))) (Eq.refl (b * c)))

protected theorem div_eq_of_eq_mul_left {a : ℤ} {b : ℤ} {c : ℤ} (H1 : b ≠ 0) (H2 : a = c * b) : a / b = c :=
  int.div_eq_of_eq_mul_right H1
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = b * c)) (mul_comm b c)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a = c * b)) H2)) (Eq.refl (c * b))))

theorem neg_div_of_dvd {a : ℤ} {b : ℤ} (H : b ∣ a) : -a / b = -(a / b) := sorry

theorem sub_div_of_dvd {a : ℤ} {b : ℤ} {c : ℤ} (hcb : c ∣ b) : (a - b) / c = a / c - b / c := sorry

theorem sub_div_of_dvd_sub {a : ℤ} {b : ℤ} {c : ℤ} (hcab : c ∣ a - b) : (a - b) / c = a / c - b / c :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a - b) / c = a / c - b / c)) (propext eq_sub_iff_add_eq)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((a - b) / c + b / c = a / c)) (Eq.symm (int.add_div_of_dvd_left hcab))))
      (eq.mpr (id (Eq._oldrec (Eq.refl ((a - b + b) / c = a / c)) (sub_add_cancel a b))) (Eq.refl (a / c))))

theorem div_sign (a : ℤ) (b : ℤ) : a / sign b = a * sign b := sorry

@[simp] theorem sign_mul (a : ℤ) (b : ℤ) : sign (a * b) = sign a * sign b := sorry

protected theorem sign_eq_div_abs (a : ℤ) : sign a = a / abs a := sorry

theorem mul_sign (i : ℤ) : i * sign i = ↑(nat_abs i) := sorry

theorem le_of_dvd {a : ℤ} {b : ℤ} (bpos : 0 < b) (H : a ∣ b) : a ≤ b := sorry

theorem eq_one_of_dvd_one {a : ℤ} (H : 0 ≤ a) (H' : a ∣ 1) : a = 1 := sorry

theorem eq_one_of_mul_eq_one_right {a : ℤ} {b : ℤ} (H : 0 ≤ a) (H' : a * b = 1) : a = 1 :=
  eq_one_of_dvd_one H (Exists.intro b (Eq.symm H'))

theorem eq_one_of_mul_eq_one_left {a : ℤ} {b : ℤ} (H : 0 ≤ b) (H' : a * b = 1) : b = 1 :=
  eq_one_of_mul_eq_one_right H
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a = 1)) (mul_comm b a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * b = 1)) H')) (Eq.refl 1)))

theorem of_nat_dvd_of_dvd_nat_abs {a : ℕ} {z : ℤ} (haz : a ∣ nat_abs z) : ↑a ∣ z := sorry

theorem dvd_nat_abs_of_of_nat_dvd {a : ℕ} {z : ℤ} (haz : ↑a ∣ z) : a ∣ nat_abs z := sorry

theorem pow_dvd_of_le_of_pow_dvd {p : ℕ} {m : ℕ} {n : ℕ} {k : ℤ} (hmn : m ≤ n) (hdiv : ↑(p ^ n) ∣ k) : ↑(p ^ m) ∣ k := sorry

theorem dvd_of_pow_dvd {p : ℕ} {k : ℕ} {m : ℤ} (hk : 1 ≤ k) (hpk : ↑(p ^ k) ∣ m) : ↑p ∣ m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑p ∣ m)) (Eq.symm (pow_one p)))) (pow_dvd_of_le_of_pow_dvd hk hpk)

/-- If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)`
  for some `k`. -/
theorem exists_lt_and_lt_iff_not_dvd (m : ℤ) {n : ℤ} (hn : 0 < n) : (∃ (k : ℤ), n * k < m ∧ m < n * (k + 1)) ↔ ¬n ∣ m := sorry

/-! ### `/` and ordering -/

protected theorem div_mul_le (a : ℤ) {b : ℤ} (H : b ≠ 0) : a / b * b ≤ a :=
  le_of_sub_nonneg
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ a - a / b * b)) (mul_comm (a / b) b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ a - b * (a / b))) (Eq.symm (mod_def a b)))) (mod_nonneg a H)))

protected theorem div_le_of_le_mul {a : ℤ} {b : ℤ} {c : ℤ} (H : 0 < c) (H' : a ≤ b * c) : a / c ≤ b :=
  le_of_mul_le_mul_right (le_trans (int.div_mul_le a (ne_of_gt H)) H') H

protected theorem mul_lt_of_lt_div {a : ℤ} {b : ℤ} {c : ℤ} (H : 0 < c) (H3 : a < b / c) : a * c < b :=
  lt_of_not_ge (mt (int.div_le_of_le_mul H) (not_le_of_gt H3))

protected theorem mul_le_of_le_div {a : ℤ} {b : ℤ} {c : ℤ} (H1 : 0 < c) (H2 : a ≤ b / c) : a * c ≤ b :=
  le_trans (mul_le_mul_of_nonneg_right H2 (le_of_lt H1)) (int.div_mul_le b (ne_of_gt H1))

protected theorem le_div_of_mul_le {a : ℤ} {b : ℤ} {c : ℤ} (H1 : 0 < c) (H2 : a * c ≤ b) : a ≤ b / c :=
  le_of_lt_add_one (lt_of_mul_lt_mul_right (lt_of_le_of_lt H2 (lt_div_add_one_mul_self b H1)) (le_of_lt H1))

protected theorem le_div_iff_mul_le {a : ℤ} {b : ℤ} {c : ℤ} (H : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
  { mp := int.mul_le_of_le_div H, mpr := int.le_div_of_mul_le H }

protected theorem div_le_div {a : ℤ} {b : ℤ} {c : ℤ} (H : 0 < c) (H' : a ≤ b) : a / c ≤ b / c :=
  int.le_div_of_mul_le H (le_trans (int.div_mul_le a (ne_of_gt H)) H')

protected theorem div_lt_of_lt_mul {a : ℤ} {b : ℤ} {c : ℤ} (H : 0 < c) (H' : a < b * c) : a / c < b :=
  lt_of_not_ge (mt (int.mul_le_of_le_div H) (not_le_of_gt H'))

protected theorem lt_mul_of_div_lt {a : ℤ} {b : ℤ} {c : ℤ} (H1 : 0 < c) (H2 : a / c < b) : a < b * c :=
  lt_of_not_ge (mt (int.le_div_of_mul_le H1) (not_le_of_gt H2))

protected theorem div_lt_iff_lt_mul {a : ℤ} {b : ℤ} {c : ℤ} (H : 0 < c) : a / c < b ↔ a < b * c :=
  { mp := int.lt_mul_of_div_lt H, mpr := int.div_lt_of_lt_mul H }

protected theorem le_mul_of_div_le {a : ℤ} {b : ℤ} {c : ℤ} (H1 : 0 ≤ b) (H2 : b ∣ a) (H3 : a / b ≤ c) : a ≤ c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ c * b)) (Eq.symm (int.div_mul_cancel H2)))) (mul_le_mul_of_nonneg_right H3 H1)

protected theorem lt_div_of_mul_lt {a : ℤ} {b : ℤ} {c : ℤ} (H1 : 0 ≤ b) (H2 : b ∣ c) (H3 : a * b < c) : a < c / b :=
  lt_of_not_ge (mt (int.le_mul_of_div_le H1 H2) (not_le_of_gt H3))

protected theorem lt_div_iff_mul_lt {a : ℤ} {b : ℤ} (c : ℤ) (H : 0 < c) (H' : c ∣ b) : a < b / c ↔ a * c < b :=
  { mp := int.mul_lt_of_lt_div H, mpr := int.lt_div_of_mul_lt (le_of_lt H) H' }

theorem div_pos_of_pos_of_dvd {a : ℤ} {b : ℤ} (H1 : 0 < a) (H2 : 0 ≤ b) (H3 : b ∣ a) : 0 < a / b :=
  int.lt_div_of_mul_lt H2 H3 (eq.mpr (id (Eq._oldrec (Eq.refl (0 * b < a)) (zero_mul b))) H1)

theorem div_eq_div_of_mul_eq_mul {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (H2 : d ∣ c) (H3 : b ≠ 0) (H4 : d ≠ 0) (H5 : a * d = b * c) : a / b = c / d :=
  int.div_eq_of_eq_mul_right H3
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = b * (c / d))) (Eq.symm (int.mul_div_assoc b H2))))
      (Eq.symm (int.div_eq_of_eq_mul_left H4 (Eq.symm H5))))

theorem eq_mul_div_of_mul_eq_mul_of_dvd_left {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (hb : b ≠ 0) (hbc : b ∣ c) (h : b * a = c * d) : a = c / b * d := sorry

/-- If an integer with larger absolute value divides an integer, it is
zero. -/
theorem eq_zero_of_dvd_of_nat_abs_lt_nat_abs {a : ℤ} {b : ℤ} (w : a ∣ b) (h : nat_abs b < nat_abs a) : b = 0 := sorry

theorem eq_zero_of_dvd_of_nonneg_of_lt {a : ℤ} {b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) (h : b ∣ a) : a = 0 :=
  eq_zero_of_dvd_of_nat_abs_lt_nat_abs h (nat_abs_lt_nat_abs_of_nonneg_of_lt w₁ w₂)

/-- If two integers are congruent to a sufficiently large modulus,
they are equal. -/
theorem eq_of_mod_eq_of_nat_abs_sub_lt_nat_abs {a : ℤ} {b : ℤ} {c : ℤ} (h1 : a % b = c) (h2 : nat_abs (a - c) < nat_abs b) : a = c :=
  eq_of_sub_eq_zero (eq_zero_of_dvd_of_nat_abs_lt_nat_abs (dvd_sub_of_mod_eq h1) h2)

theorem of_nat_add_neg_succ_of_nat_of_lt {m : ℕ} {n : ℕ} (h : m < Nat.succ n) : Int.ofNat m + Int.negSucc n = Int.negSucc (n - m) := sorry

theorem of_nat_add_neg_succ_of_nat_of_ge {m : ℕ} {n : ℕ} (h : Nat.succ n ≤ m) : Int.ofNat m + Int.negSucc n = Int.ofNat (m - Nat.succ n) := sorry

@[simp] theorem neg_add_neg (m : ℕ) (n : ℕ) : Int.negSucc m + Int.negSucc n = Int.negSucc (Nat.succ (m + n)) :=
  rfl

/-! ### to_nat -/

theorem to_nat_eq_max (a : ℤ) : ↑(to_nat a) = max a 0 :=
  int.cases_on a (fun (a : ℕ) => idRhs (↑a = max (↑a) 0) (Eq.symm (max_eq_left (coe_zero_le a))))
    fun (a : ℕ) => idRhs (0 = max (Int.negSucc a) 0) (Eq.symm (max_eq_right (le_of_lt (neg_succ_lt_zero a))))

@[simp] theorem to_nat_zero : to_nat 0 = 0 :=
  rfl

@[simp] theorem to_nat_one : to_nat 1 = 1 :=
  rfl

@[simp] theorem to_nat_of_nonneg {a : ℤ} (h : 0 ≤ a) : ↑(to_nat a) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(to_nat a) = a)) (to_nat_eq_max a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (max a 0 = a)) (max_eq_left h))) (Eq.refl a))

@[simp] theorem to_nat_sub_of_le (a : ℤ) (b : ℤ) (h : b ≤ a) : ↑(to_nat (a + -b)) = a + -b :=
  to_nat_of_nonneg (sub_nonneg_of_le h)

@[simp] theorem to_nat_coe_nat (n : ℕ) : to_nat ↑n = n :=
  rfl

@[simp] theorem to_nat_coe_nat_add_one {n : ℕ} : to_nat (↑n + 1) = n + 1 :=
  rfl

theorem le_to_nat (a : ℤ) : a ≤ ↑(to_nat a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ ↑(to_nat a))) (to_nat_eq_max a))) (le_max_left a 0)

@[simp] theorem to_nat_le {a : ℤ} {n : ℕ} : to_nat a ≤ n ↔ a ≤ ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (to_nat a ≤ n ↔ a ≤ ↑n)) (propext (iff.symm (coe_nat_le_coe_nat_iff (to_nat a) n)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(to_nat a) ≤ ↑n ↔ a ≤ ↑n)) (to_nat_eq_max a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (max a 0 ≤ ↑n ↔ a ≤ ↑n)) (propext max_le_iff))) (and_iff_left (coe_zero_le n))))

@[simp] theorem lt_to_nat {n : ℕ} {a : ℤ} : n < to_nat a ↔ ↑n < a :=
  iff.mp le_iff_le_iff_lt_iff_lt to_nat_le

theorem to_nat_le_to_nat {a : ℤ} {b : ℤ} (h : a ≤ b) : to_nat a ≤ to_nat b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (to_nat a ≤ to_nat b)) (propext to_nat_le))) (le_trans h (le_to_nat b))

theorem to_nat_lt_to_nat {a : ℤ} {b : ℤ} (hb : 0 < b) : to_nat a < to_nat b ↔ a < b := sorry

theorem lt_of_to_nat_lt {a : ℤ} {b : ℤ} (h : to_nat a < to_nat b) : a < b :=
  iff.mp (to_nat_lt_to_nat (iff.mp lt_to_nat (lt_of_le_of_lt (nat.zero_le (to_nat a)) h))) h

theorem to_nat_add {a : ℤ} {b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : to_nat (a + b) = to_nat a + to_nat b := sorry

theorem to_nat_add_one {a : ℤ} (h : 0 ≤ a) : to_nat (a + 1) = to_nat a + 1 :=
  to_nat_add h zero_le_one

/-- If `n : ℕ`, then `int.to_nat' n = some n`, if `n : ℤ` is negative, then `int.to_nat' n = none`.
-/
def to_nat' : ℤ → Option ℕ :=
  sorry

theorem mem_to_nat' (a : ℤ) (n : ℕ) : n ∈ to_nat' a ↔ a = ↑n := sorry

theorem to_nat_zero_of_neg {z : ℤ} : z < 0 → to_nat z = 0 := sorry

/-! ### units -/

@[simp] theorem units_nat_abs (u : units ℤ) : nat_abs ↑u = 1 := sorry

theorem units_eq_one_or (u : units ℤ) : u = 1 ∨ u = -1 := sorry

theorem units_inv_eq_self (u : units ℤ) : u⁻¹ = u :=
  or.elim (units_eq_one_or u) (fun (h : u = 1) => Eq.symm h ▸ rfl) fun (h : u = -1) => Eq.symm h ▸ rfl

@[simp] theorem units_mul_self (u : units ℤ) : u * u = 1 :=
  or.elim (units_eq_one_or u) (fun (h : u = 1) => Eq.symm h ▸ rfl) fun (h : u = -1) => Eq.symm h ▸ rfl

-- `units.coe_mul` is a "wrong turn" for the simplifier, this undoes it and simplifies further

@[simp] theorem units_coe_mul_self (u : units ℤ) : ↑u * ↑u = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑u * ↑u = 1)) (Eq.symm (units.coe_mul u u))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(u * u) = 1)) (units_mul_self u)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑1 = 1)) units.coe_one)) (Eq.refl 1)))

/-! ### bitwise ops -/

@[simp] theorem bodd_zero : bodd 0 = false :=
  rfl

@[simp] theorem bodd_one : bodd 1 = tt :=
  rfl

theorem bodd_two : bodd (bit0 1) = false :=
  rfl

@[simp] theorem bodd_coe (n : ℕ) : bodd ↑n = nat.bodd n :=
  rfl

@[simp] theorem bodd_sub_nat_nat (m : ℕ) (n : ℕ) : bodd (sub_nat_nat m n) = bxor (nat.bodd m) (nat.bodd n) := sorry

@[simp] theorem bodd_neg_of_nat (n : ℕ) : bodd (neg_of_nat n) = nat.bodd n := sorry

@[simp] theorem bodd_neg (n : ℤ) : bodd (-n) = bodd n := sorry

@[simp] theorem bodd_add (m : ℤ) (n : ℤ) : bodd (m + n) = bxor (bodd m) (bodd n) := sorry

@[simp] theorem bodd_mul (m : ℤ) (n : ℤ) : bodd (m * n) = bodd m && bodd n := sorry

theorem bodd_add_div2 (n : ℤ) : cond (bodd n) 1 0 + bit0 1 * div2 n = n := sorry

theorem div2_val (n : ℤ) : div2 n = n / bit0 1 :=
  int.cases_on n
    (fun (n : ℕ) => idRhs (Int.ofNat (nat.div2 n) = Int.ofNat (n / bit0 1)) (congr_arg Int.ofNat (nat.div2_val n)))
    fun (n : ℕ) => idRhs (Int.negSucc (nat.div2 n) = Int.negSucc (n / bit0 1)) (congr_arg Int.negSucc (nat.div2_val n))

theorem bit0_val (n : ℤ) : bit0 n = bit0 1 * n :=
  Eq.symm (two_mul n)

theorem bit1_val (n : ℤ) : bit1 n = bit0 1 * n + 1 :=
  congr_arg (fun (_x : ℤ) => _x + 1) (bit0_val n)

theorem bit_val (b : Bool) (n : ℤ) : bit b n = bit0 1 * n + cond b 1 0 :=
  bool.cases_on b (Eq.trans (bit0_val n) (Eq.symm (add_zero (bit0 1 * n)))) (bit1_val n)

theorem bit_decomp (n : ℤ) : bit (bodd n) (div2 n) = n :=
  Eq.trans (bit_val (bodd n) (div2 n)) (Eq.trans (add_comm (bit0 1 * div2 n) (cond (bodd n) 1 0)) (bodd_add_div2 n))

/-- Defines a function from `ℤ` conditionally, if it is defined for odd and even integers separately
  using `bit`. -/
def bit_cases_on {C : ℤ → Sort u} (n : ℤ) (h : (b : Bool) → (n : ℤ) → C (bit b n)) : C n :=
  eq.mpr sorry (h (bodd n) (div2 n))

@[simp] theorem bit_zero : bit false 0 = 0 :=
  rfl

@[simp] theorem bit_coe_nat (b : Bool) (n : ℕ) : bit b ↑n = ↑(nat.bit b n) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (bit b ↑n = ↑(nat.bit b n))) (bit_val b ↑n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (bit0 1 * ↑n + cond b 1 0 = ↑(nat.bit b n))) (nat.bit_val b n)))
      (bool.cases_on b (Eq.refl (bit0 1 * ↑n + cond false 1 0)) (Eq.refl (bit0 1 * ↑n + cond tt 1 0))))

@[simp] theorem bit_neg_succ (b : Bool) (n : ℕ) : bit b (Int.negSucc n) = Int.negSucc (nat.bit (!b) n) := sorry

@[simp] theorem bodd_bit (b : Bool) (n : ℤ) : bodd (bit b n) = b := sorry

@[simp] theorem bodd_bit0 (n : ℤ) : bodd (bit0 n) = false :=
  bodd_bit false n

@[simp] theorem bodd_bit1 (n : ℤ) : bodd (bit1 n) = tt :=
  bodd_bit tt n

@[simp] theorem div2_bit (b : Bool) (n : ℤ) : div2 (bit b n) = n := sorry

theorem bit0_ne_bit1 (m : ℤ) (n : ℤ) : bit0 m ≠ bit1 n := sorry

theorem bit1_ne_bit0 (m : ℤ) (n : ℤ) : bit1 m ≠ bit0 n :=
  ne.symm (bit0_ne_bit1 n m)

theorem bit1_ne_zero (m : ℤ) : bit1 m ≠ 0 := sorry

@[simp] theorem test_bit_zero (b : Bool) (n : ℤ) : test_bit (bit b n) 0 = b := sorry

@[simp] theorem test_bit_succ (m : ℕ) (b : Bool) (n : ℤ) : test_bit (bit b n) (Nat.succ m) = test_bit n m := sorry

theorem bitwise_or : bitwise bor = lor := sorry

theorem bitwise_and : bitwise band = land := sorry

theorem bitwise_diff : (bitwise fun (a b : Bool) => a && !b) = ldiff := sorry

theorem bitwise_xor : bitwise bxor = lxor := sorry

@[simp] theorem bitwise_bit (f : Bool → Bool → Bool) (a : Bool) (m : ℤ) (b : Bool) (n : ℤ) : bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := sorry

@[simp] theorem lor_bit (a : Bool) (m : ℤ) (b : Bool) (n : ℤ) : lor (bit a m) (bit b n) = bit (a || b) (lor m n) := sorry

@[simp] theorem land_bit (a : Bool) (m : ℤ) (b : Bool) (n : ℤ) : land (bit a m) (bit b n) = bit (a && b) (land m n) := sorry

@[simp] theorem ldiff_bit (a : Bool) (m : ℤ) (b : Bool) (n : ℤ) : ldiff (bit a m) (bit b n) = bit (a && !b) (ldiff m n) := sorry

@[simp] theorem lxor_bit (a : Bool) (m : ℤ) (b : Bool) (n : ℤ) : lxor (bit a m) (bit b n) = bit (bxor a b) (lxor m n) := sorry

@[simp] theorem lnot_bit (b : Bool) (n : ℤ) : lnot (bit b n) = bit (!b) (lnot n) := sorry

@[simp] theorem test_bit_bitwise (f : Bool → Bool → Bool) (m : ℤ) (n : ℤ) (k : ℕ) : test_bit (bitwise f m n) k = f (test_bit m k) (test_bit n k) := sorry

@[simp] theorem test_bit_lor (m : ℤ) (n : ℤ) (k : ℕ) : test_bit (lor m n) k = test_bit m k || test_bit n k := sorry

@[simp] theorem test_bit_land (m : ℤ) (n : ℤ) (k : ℕ) : test_bit (land m n) k = test_bit m k && test_bit n k := sorry

@[simp] theorem test_bit_ldiff (m : ℤ) (n : ℤ) (k : ℕ) : test_bit (ldiff m n) k = test_bit m k && !test_bit n k := sorry

@[simp] theorem test_bit_lxor (m : ℤ) (n : ℤ) (k : ℕ) : test_bit (lxor m n) k = bxor (test_bit m k) (test_bit n k) := sorry

@[simp] theorem test_bit_lnot (n : ℤ) (k : ℕ) : test_bit (lnot n) k = !test_bit n k := sorry

theorem shiftl_add (m : ℤ) (n : ℕ) (k : ℤ) : shiftl m (↑n + k) = shiftl (shiftl m ↑n) k := sorry

theorem shiftl_sub (m : ℤ) (n : ℕ) (k : ℤ) : shiftl m (↑n - k) = shiftr (shiftl m ↑n) k :=
  shiftl_add m n (-k)

@[simp] theorem shiftl_neg (m : ℤ) (n : ℤ) : shiftl m (-n) = shiftr m n :=
  rfl

@[simp] theorem shiftr_neg (m : ℤ) (n : ℤ) : shiftr m (-n) = shiftl m n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (shiftr m (-n) = shiftl m n)) (Eq.symm (shiftl_neg m (-n)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (shiftl m ( --n) = shiftl m n)) (neg_neg n))) (Eq.refl (shiftl m n)))

@[simp] theorem shiftl_coe_nat (m : ℕ) (n : ℕ) : shiftl ↑m ↑n = ↑(nat.shiftl m n) :=
  rfl

@[simp] theorem shiftr_coe_nat (m : ℕ) (n : ℕ) : shiftr ↑m ↑n = ↑(nat.shiftr m n) :=
  nat.cases_on n (Eq.refl (shiftr ↑m ↑0)) fun (n : ℕ) => Eq.refl (shiftr ↑m ↑(Nat.succ n))

@[simp] theorem shiftl_neg_succ (m : ℕ) (n : ℕ) : shiftl (Int.negSucc m) ↑n = Int.negSucc (nat.shiftl' tt m n) :=
  rfl

@[simp] theorem shiftr_neg_succ (m : ℕ) (n : ℕ) : shiftr (Int.negSucc m) ↑n = Int.negSucc (nat.shiftr m n) :=
  nat.cases_on n (Eq.refl (shiftr (Int.negSucc m) ↑0)) fun (n : ℕ) => Eq.refl (shiftr (Int.negSucc m) ↑(Nat.succ n))

theorem shiftr_add (m : ℤ) (n : ℕ) (k : ℕ) : shiftr m (↑n + ↑k) = shiftr (shiftr m ↑n) ↑k := sorry

theorem shiftl_eq_mul_pow (m : ℤ) (n : ℕ) : shiftl m ↑n = m * ↑(bit0 1 ^ n) := sorry

theorem shiftr_eq_div_pow (m : ℤ) (n : ℕ) : shiftr m ↑n = m / ↑(bit0 1 ^ n) := sorry

theorem one_shiftl (n : ℕ) : shiftl 1 ↑n = ↑(bit0 1 ^ n) :=
  congr_arg coe (nat.one_shiftl n)

@[simp] theorem zero_shiftl (n : ℤ) : shiftl 0 n = 0 :=
  int.cases_on n (fun (n : ℕ) => idRhs (↑(nat.shiftl 0 n) = ↑0) (congr_arg coe (nat.zero_shiftl n)))
    fun (n : ℕ) => idRhs (↑(nat.shiftr 0 (Nat.succ n)) = ↑0) (congr_arg coe (nat.zero_shiftr (Nat.succ n)))

@[simp] theorem zero_shiftr (n : ℤ) : shiftr 0 n = 0 :=
  zero_shiftl (-n)

/-! ### Least upper bound property for integers -/

theorem exists_least_of_bdd {P : ℤ → Prop} (Hbdd : ∃ (b : ℤ), ∀ (z : ℤ), P z → b ≤ z) (Hinh : ∃ (z : ℤ), P z) : ∃ (lb : ℤ), P lb ∧ ∀ (z : ℤ), P z → lb ≤ z := sorry

theorem exists_greatest_of_bdd {P : ℤ → Prop} (Hbdd : ∃ (b : ℤ), ∀ (z : ℤ), P z → z ≤ b) (Hinh : ∃ (z : ℤ), P z) : ∃ (ub : ℤ), P ub ∧ ∀ (z : ℤ), P z → z ≤ ub := sorry

