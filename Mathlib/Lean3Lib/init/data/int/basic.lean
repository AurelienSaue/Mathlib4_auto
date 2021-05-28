/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.nat.lemmas
import Mathlib.Lean3Lib.init.data.nat.gcd
 

universes l 

namespace Mathlib

/- the type, coercions, and notation -/

not foundnotation:1024 "ℤ" => Mathlib.int

protected instance int.has_coe : has_coe ℕ ℤ :=
  has_coe.mk Int.ofNat

protected def int.repr : ℤ → string :=
  sorry

protected instance int.has_repr : has_repr ℤ :=
  has_repr.mk int.repr

protected instance int.has_to_string : has_to_string ℤ :=
  has_to_string.mk int.repr

namespace int


protected theorem coe_nat_eq (n : ℕ) : ↑n = Int.ofNat n :=
  rfl

protected def zero : ℤ :=
  Int.ofNat 0

protected def one : ℤ :=
  Int.ofNat 1

protected instance has_zero : HasZero ℤ :=
  { zero := int.zero }

protected instance has_one : HasOne ℤ :=
  { one := int.one }

theorem of_nat_zero : Int.ofNat 0 = 0 :=
  rfl

theorem of_nat_one : Int.ofNat 1 = 1 :=
  rfl

/- definitions of basic functions -/

def neg_of_nat : ℕ → ℤ :=
  sorry

def sub_nat_nat (m : ℕ) (n : ℕ) : ℤ :=
  sorry

theorem sub_nat_nat_of_sub_eq_zero {m : ℕ} {n : ℕ} (h : n - m = 0) : sub_nat_nat m n = Int.ofNat (m - n) := sorry

theorem sub_nat_nat_of_sub_eq_succ {m : ℕ} {n : ℕ} {k : ℕ} (h : n - m = Nat.succ k) : sub_nat_nat m n = Int.negSucc k := sorry

protected def neg : ℤ → ℤ :=
  sorry

protected def add : ℤ → ℤ → ℤ :=
  sorry

protected def mul : ℤ → ℤ → ℤ :=
  sorry

protected instance has_neg : Neg ℤ :=
  { neg := int.neg }

protected instance has_add : Add ℤ :=
  { add := int.add }

protected instance has_mul : Mul ℤ :=
  { mul := int.mul }

-- defeq to algebra.sub which gives subtraction for arbitrary `add_group`s

protected def sub : ℤ → ℤ → ℤ :=
  fun (m n : ℤ) => m + -n

protected instance has_sub : Sub ℤ :=
  { sub := int.sub }

protected theorem neg_zero : -0 = 0 :=
  rfl

theorem of_nat_add (n : ℕ) (m : ℕ) : Int.ofNat (n + m) = Int.ofNat n + Int.ofNat m :=
  rfl

theorem of_nat_mul (n : ℕ) (m : ℕ) : Int.ofNat (n * m) = Int.ofNat n * Int.ofNat m :=
  rfl

theorem of_nat_succ (n : ℕ) : Int.ofNat (Nat.succ n) = Int.ofNat n + 1 :=
  rfl

theorem neg_of_nat_zero : -Int.ofNat 0 = 0 :=
  rfl

theorem neg_of_nat_of_succ (n : ℕ) : -Int.ofNat (Nat.succ n) = Int.negSucc n :=
  rfl

theorem neg_neg_of_nat_succ (n : ℕ) : -Int.negSucc n = Int.ofNat (Nat.succ n) :=
  rfl

theorem of_nat_eq_coe (n : ℕ) : Int.ofNat n = ↑n :=
  rfl

theorem neg_succ_of_nat_coe (n : ℕ) : Int.negSucc n = -↑(n + 1) :=
  rfl

protected theorem coe_nat_add (m : ℕ) (n : ℕ) : ↑(m + n) = ↑m + ↑n :=
  rfl

protected theorem coe_nat_mul (m : ℕ) (n : ℕ) : ↑(m * n) = ↑m * ↑n :=
  rfl

protected theorem coe_nat_zero : ↑0 = 0 :=
  rfl

protected theorem coe_nat_one : ↑1 = 1 :=
  rfl

protected theorem coe_nat_succ (n : ℕ) : ↑(Nat.succ n) = ↑n + 1 :=
  rfl

protected theorem coe_nat_add_out (m : ℕ) (n : ℕ) : ↑m + ↑n = ↑m + ↑n :=
  rfl

protected theorem coe_nat_mul_out (m : ℕ) (n : ℕ) : ↑m * ↑n = ↑(m * n) :=
  rfl

protected theorem coe_nat_add_one_out (n : ℕ) : ↑n + 1 = ↑(Nat.succ n) :=
  rfl

/- these are only for internal use -/

theorem of_nat_add_of_nat (m : ℕ) (n : ℕ) : Int.ofNat m + Int.ofNat n = Int.ofNat (m + n) :=
  rfl

theorem of_nat_add_neg_succ_of_nat (m : ℕ) (n : ℕ) : Int.ofNat m + Int.negSucc n = sub_nat_nat m (Nat.succ n) :=
  rfl

theorem neg_succ_of_nat_add_of_nat (m : ℕ) (n : ℕ) : Int.negSucc m + Int.ofNat n = sub_nat_nat n (Nat.succ m) :=
  rfl

theorem neg_succ_of_nat_add_neg_succ_of_nat (m : ℕ) (n : ℕ) : Int.negSucc m + Int.negSucc n = Int.negSucc (Nat.succ (m + n)) :=
  rfl

theorem of_nat_mul_of_nat (m : ℕ) (n : ℕ) : Int.ofNat m * Int.ofNat n = Int.ofNat (m * n) :=
  rfl

theorem of_nat_mul_neg_succ_of_nat (m : ℕ) (n : ℕ) : Int.ofNat m * Int.negSucc n = neg_of_nat (m * Nat.succ n) :=
  rfl

theorem neg_succ_of_nat_of_nat (m : ℕ) (n : ℕ) : Int.negSucc m * Int.ofNat n = neg_of_nat (Nat.succ m * n) :=
  rfl

theorem mul_neg_succ_of_nat_neg_succ_of_nat (m : ℕ) (n : ℕ) : Int.negSucc m * Int.negSucc n = Int.ofNat (Nat.succ m * Nat.succ n) :=
  rfl

/- some basic functions and properties -/

protected theorem coe_nat_inj {m : ℕ} {n : ℕ} (h : ↑m = ↑n) : m = n :=
  of_nat.inj h

theorem of_nat_eq_of_nat_iff (m : ℕ) (n : ℕ) : Int.ofNat m = Int.ofNat n ↔ m = n :=
  { mp := of_nat.inj, mpr := congr_arg fun (m : ℕ) => Int.ofNat m }

protected theorem coe_nat_eq_coe_nat_iff (m : ℕ) (n : ℕ) : ↑m = ↑n ↔ m = n :=
  of_nat_eq_of_nat_iff m n

theorem neg_succ_of_nat_inj_iff {m : ℕ} {n : ℕ} : Int.negSucc m = Int.negSucc n ↔ m = n := sorry

theorem neg_succ_of_nat_eq (n : ℕ) : Int.negSucc n = -(↑n + 1) :=
  rfl

/- neg -/

protected theorem neg_neg (a : ℤ) : --a = a := sorry

protected theorem neg_inj {a : ℤ} {b : ℤ} (h : -a = -b) : a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = b)) (Eq.symm (int.neg_neg a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ( --a = b)) (Eq.symm (int.neg_neg b))))
      (eq.mpr (id (Eq._oldrec (Eq.refl ( --a = --b)) h)) (Eq.refl ( --b))))

protected theorem sub_eq_add_neg {a : ℤ} {b : ℤ} : a - b = a + -b :=
  rfl

/- basic properties of sub_nat_nat -/

theorem sub_nat_nat_elim (m : ℕ) (n : ℕ) (P : ℕ → ℕ → ℤ → Prop) (hp : ∀ (i n : ℕ), P (n + i) n (Int.ofNat i)) (hn : ∀ (i m : ℕ), P m (m + i + 1) (Int.negSucc i)) : P m n (sub_nat_nat m n) := sorry

theorem sub_nat_nat_add_left {m : ℕ} {n : ℕ} : sub_nat_nat (m + n) m = Int.ofNat n := sorry

theorem sub_nat_nat_add_right {m : ℕ} {n : ℕ} : sub_nat_nat m (m + n + 1) = Int.negSucc n := sorry

theorem sub_nat_nat_add_add (m : ℕ) (n : ℕ) (k : ℕ) : sub_nat_nat (m + k) (n + k) = sub_nat_nat m n := sorry

theorem sub_nat_nat_of_ge {m : ℕ} {n : ℕ} (h : m ≥ n) : sub_nat_nat m n = Int.ofNat (m - n) :=
  sub_nat_nat_of_sub_eq_zero (nat.sub_eq_zero_of_le h)

theorem sub_nat_nat_of_lt {m : ℕ} {n : ℕ} (h : m < n) : sub_nat_nat m n = Int.negSucc (Nat.pred (n - m)) := sorry

/- nat_abs -/

@[simp] def nat_abs : ℤ → ℕ :=
  sorry

theorem nat_abs_of_nat (n : ℕ) : nat_abs ↑n = n :=
  rfl

theorem eq_zero_of_nat_abs_eq_zero {a : ℤ} : nat_abs a = 0 → a = 0 := sorry

theorem nat_abs_pos_of_ne_zero {a : ℤ} (h : a ≠ 0) : nat_abs a > 0 :=
  or.resolve_left (nat.eq_zero_or_pos (nat_abs a)) (mt eq_zero_of_nat_abs_eq_zero h)

theorem nat_abs_zero : nat_abs 0 = 0 :=
  rfl

theorem nat_abs_one : nat_abs 1 = 1 :=
  rfl

theorem nat_abs_mul_self {a : ℤ} : ↑(nat_abs a * nat_abs a) = a * a := sorry

@[simp] theorem nat_abs_neg (a : ℤ) : nat_abs (-a) = nat_abs a := sorry

theorem nat_abs_eq (a : ℤ) : a = ↑(nat_abs a) ∨ a = -↑(nat_abs a) := sorry

theorem eq_coe_or_neg (a : ℤ) : ∃ (n : ℕ), a = ↑n ∨ a = -↑n :=
  Exists.intro (nat_abs a) (nat_abs_eq a)

/- sign -/

def sign : ℤ → ℤ :=
  sorry

@[simp] theorem sign_zero : sign 0 = 0 :=
  rfl

@[simp] theorem sign_one : sign 1 = 1 :=
  rfl

@[simp] theorem sign_neg_one : sign (-1) = -1 :=
  rfl

/- Quotient and remainder -/

-- There are three main conventions for integer division,

-- referred here as the E, F, T rounding conventions.

-- All three pairs satisfy the identity x % y + (x / y) * y = x

-- unconditionally.

-- E-rounding: This pair satisfies 0 ≤ mod x y < nat_abs y for y ≠ 0

protected def div : ℤ → ℤ → ℤ :=
  sorry

protected def mod : ℤ → ℤ → ℤ :=
  sorry

-- F-rounding: This pair satisfies fdiv x y = floor (x / y)

def fdiv : ℤ → ℤ → ℤ :=
  sorry

def fmod : ℤ → ℤ → ℤ :=
  sorry

-- T-rounding: This pair satisfies quot x y = round_to_zero (x / y)

def quot : ℤ → ℤ → ℤ :=
  sorry

def rem : ℤ → ℤ → ℤ :=
  sorry

protected instance has_div : Div ℤ :=
  { div := int.div }

protected instance has_mod : Mod ℤ :=
  { mod := int.mod }

/- gcd -/

def gcd (m : ℤ) (n : ℤ) : ℕ :=
  nat.gcd (nat_abs m) (nat_abs n)

/-
   int is a ring
-/

/- addition -/

protected theorem add_comm (a : ℤ) (b : ℤ) : a + b = b + a := sorry

protected theorem add_zero (a : ℤ) : a + 0 = a :=
  int.cases_on a (fun (a : ℕ) => idRhs (Int.ofNat a + 0 = Int.ofNat a + 0) rfl)
    fun (a : ℕ) => idRhs (Int.negSucc a + 0 = Int.negSucc a + 0) rfl

protected theorem zero_add (a : ℤ) : 0 + a = a :=
  int.add_comm a 0 ▸ int.add_zero a

theorem sub_nat_nat_sub {m : ℕ} {n : ℕ} (h : m ≥ n) (k : ℕ) : sub_nat_nat (m - n) k = sub_nat_nat m (k + n) := sorry

theorem sub_nat_nat_add (m : ℕ) (n : ℕ) (k : ℕ) : sub_nat_nat (m + n) k = Int.ofNat m + sub_nat_nat n k := sorry

theorem sub_nat_nat_add_neg_succ_of_nat (m : ℕ) (n : ℕ) (k : ℕ) : sub_nat_nat m n + Int.negSucc k = sub_nat_nat m (n + Nat.succ k) := sorry

theorem add_assoc_aux1 (m : ℕ) (n : ℕ) (c : ℤ) : Int.ofNat m + Int.ofNat n + c = Int.ofNat m + (Int.ofNat n + c) := sorry

theorem add_assoc_aux2 (m : ℕ) (n : ℕ) (k : ℕ) : Int.negSucc m + Int.negSucc n + Int.ofNat k = Int.negSucc m + (Int.negSucc n + Int.ofNat k) := sorry

protected theorem add_assoc (a : ℤ) (b : ℤ) (c : ℤ) : a + b + c = a + (b + c) := sorry

/- negation -/

theorem sub_nat_self (n : ℕ) : sub_nat_nat n n = 0 := sorry

protected theorem add_left_neg (a : ℤ) : -a + a = 0 := sorry

protected theorem add_right_neg (a : ℤ) : a + -a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + -a = 0)) (int.add_comm a (-a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-a + a = 0)) (int.add_left_neg a))) (Eq.refl 0))

/- multiplication -/

protected theorem mul_comm (a : ℤ) (b : ℤ) : a * b = b * a := sorry

theorem of_nat_mul_neg_of_nat (m : ℕ) (n : ℕ) : Int.ofNat m * neg_of_nat n = neg_of_nat (m * n) := sorry

theorem neg_of_nat_mul_of_nat (m : ℕ) (n : ℕ) : neg_of_nat m * Int.ofNat n = neg_of_nat (m * n) := sorry

theorem neg_succ_of_nat_mul_neg_of_nat (m : ℕ) (n : ℕ) : Int.negSucc m * neg_of_nat n = Int.ofNat (Nat.succ m * n) := sorry

theorem neg_of_nat_mul_neg_succ_of_nat (m : ℕ) (n : ℕ) : neg_of_nat n * Int.negSucc m = Int.ofNat (n * Nat.succ m) := sorry

protected theorem mul_assoc (a : ℤ) (b : ℤ) (c : ℤ) : a * b * c = a * (b * c) := sorry

protected theorem mul_zero (a : ℤ) : a * 0 = 0 :=
  int.cases_on a (fun (a : ℕ) => idRhs (Int.ofNat a * 0 = Int.ofNat a * 0) rfl)
    fun (a : ℕ) => idRhs (Int.negSucc a * 0 = Int.negSucc a * 0) rfl

protected theorem zero_mul (a : ℤ) : 0 * a = 0 :=
  int.mul_comm a 0 ▸ int.mul_zero a

theorem neg_of_nat_eq_sub_nat_nat_zero (n : ℕ) : neg_of_nat n = sub_nat_nat 0 n :=
  nat.cases_on n (idRhs (neg_of_nat 0 = neg_of_nat 0) rfl)
    fun (n : ℕ) => idRhs (neg_of_nat (Nat.succ n) = neg_of_nat (Nat.succ n)) rfl

theorem of_nat_mul_sub_nat_nat (m : ℕ) (n : ℕ) (k : ℕ) : Int.ofNat m * sub_nat_nat n k = sub_nat_nat (m * n) (m * k) := sorry

theorem neg_of_nat_add (m : ℕ) (n : ℕ) : neg_of_nat m + neg_of_nat n = neg_of_nat (m + n) := sorry

theorem neg_succ_of_nat_mul_sub_nat_nat (m : ℕ) (n : ℕ) (k : ℕ) : Int.negSucc m * sub_nat_nat n k = sub_nat_nat (Nat.succ m * k) (Nat.succ m * n) := sorry

protected theorem distrib_left (a : ℤ) (b : ℤ) (c : ℤ) : a * (b + c) = a * b + a * c := sorry

protected theorem distrib_right (a : ℤ) (b : ℤ) (c : ℤ) : (a + b) * c = a * c + b * c := sorry

protected theorem zero_ne_one : 0 ≠ 1 :=
  fun (h : 0 = 1) => nat.succ_ne_zero 0 (Eq.symm (of_nat.inj h))

theorem of_nat_sub {n : ℕ} {m : ℕ} (h : m ≤ n) : Int.ofNat (n - m) = Int.ofNat n - Int.ofNat m := sorry

protected theorem add_left_comm (a : ℤ) (b : ℤ) (c : ℤ) : a + (b + c) = b + (a + c) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + (b + c) = b + (a + c))) (Eq.symm (int.add_assoc a b c))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + b + c = b + (a + c))) (int.add_comm a b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b + a + c = b + (a + c))) (int.add_assoc b a c))) (Eq.refl (b + (a + c)))))

protected theorem add_left_cancel {a : ℤ} {b : ℤ} {c : ℤ} (h : a + b = a + c) : b = c := sorry

protected theorem neg_add {a : ℤ} {b : ℤ} : -(a + b) = -a + -b := sorry

theorem neg_succ_of_nat_coe' (n : ℕ) : Int.negSucc n = -↑n - 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Int.negSucc n = -↑n - 1)) int.sub_eq_add_neg))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Int.negSucc n = -↑n + -1)) (Eq.symm int.neg_add))) (Eq.refl (Int.negSucc n)))

protected theorem coe_nat_sub {n : ℕ} {m : ℕ} : n ≤ m → ↑(m - n) = ↑m - ↑n :=
  of_nat_sub

protected theorem sub_nat_nat_eq_coe {m : ℕ} {n : ℕ} : sub_nat_nat m n = ↑m - ↑n := sorry

def to_nat : ℤ → ℕ :=
  sorry

theorem to_nat_sub (m : ℕ) (n : ℕ) : to_nat (↑m - ↑n) = m - n := sorry

-- Since mod x y is always nonnegative when y ≠ 0, we can make a nat version of it

def nat_mod (m : ℤ) (n : ℤ) : ℕ :=
  to_nat (m % n)

protected theorem one_mul (a : ℤ) : 1 * a = a := sorry

protected theorem mul_one (a : ℤ) : a * 1 = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * 1 = a)) (int.mul_comm a 1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 * a = a)) (int.one_mul a))) (Eq.refl a))

protected theorem neg_eq_neg_one_mul (a : ℤ) : -a = -1 * a := sorry

theorem sign_mul_nat_abs (a : ℤ) : sign a * ↑(nat_abs a) = a := sorry

