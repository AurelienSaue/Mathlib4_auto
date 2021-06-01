/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.vector2
import Mathlib.data.nat.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# Basic operations on bitvectors

This is a work-in-progress, and contains additions to other theories.

This file was moved to mathlib from core Lean in the switch to Lean 3.20.0c. It is not fully in compliance with mathlib style standards.
-/

/-- `bitvec n` is a `vector` of `bool` with length `n`. -/
def bitvec (n : ℕ) := vector Bool n

namespace bitvec


/-- Create a zero bitvector -/
protected def zero (n : ℕ) : bitvec n := vector.repeat false n

/-- Create a bitvector of length `n` whose `n-1`st entry is 1 and other entries are 0. -/
protected def one (n : ℕ) : bitvec n := sorry

/-- Create a bitvector from another with a provably equal length. -/
protected def cong {a : ℕ} {b : ℕ} (h : a = b) : bitvec a → bitvec b := sorry

/-- `bitvec` specific version of `vector.append` -/
def append {m : ℕ} {n : ℕ} : bitvec m → bitvec n → bitvec (m + n) := vector.append

/-! ### Shift operations -/

/-- `shl x i` is the bitvector obtained by left-shifting `x` `i` times and padding with `ff`.
If `x.length < i` then this will return the all-`ff`s bitvector. -/
def shl {n : ℕ} (x : bitvec n) (i : ℕ) : bitvec n :=
  bitvec.cong sorry (vector.append (vector.drop i x) (vector.repeat false (min n i)))

/-- `fill_shr x i fill` is the bitvector obtained by right-shifting `x` `i` times and then
padding with `fill : bool`. If `x.length < i` then this will return the constant `fill`
bitvector. -/
def fill_shr {n : ℕ} (x : bitvec n) (i : ℕ) (fill : Bool) : bitvec n :=
  bitvec.cong sorry (vector.append (vector.repeat fill (min n i)) (vector.take (n - i) x))

/-- unsigned shift right -/
def ushr {n : ℕ} (x : bitvec n) (i : ℕ) : bitvec n := fill_shr x i false

/-- signed shift right -/
def sshr {m : ℕ} : bitvec m → ℕ → bitvec m := sorry

/-! ### Bitwise operations -/

/-- bitwise not -/
/-- bitwise and -/
def not {n : ℕ} : bitvec n → bitvec n := vector.map bnot

/-- bitwise or -/
def and {n : ℕ} : bitvec n → bitvec n → bitvec n := vector.map₂ band

/-- bitwise xor -/
def or {n : ℕ} : bitvec n → bitvec n → bitvec n := vector.map₂ bor

def xor {n : ℕ} : bitvec n → bitvec n → bitvec n := vector.map₂ bxor

/-! ### Arithmetic operators -/

/-- `xor3 x y c` is `((x XOR y) XOR c)`. -/
/-- `carry x y c` is `x && y || x && c || y && c`. -/
protected def xor3 (x : Bool) (y : Bool) (c : Bool) : Bool := bxor (bxor x y) c

protected def carry (x : Bool) (y : Bool) (c : Bool) : Bool := x && y || x && c || y && c

/-- `neg x` is the two's complement of `x`. -/
protected def neg {n : ℕ} (x : bitvec n) : bitvec n :=
  let f : Bool → Bool → Bool × Bool := fun (y c : Bool) => (y || c, bxor y c);
  prod.snd (vector.map_accumr f x false)

/-- Add with carry (no overflow) -/
def adc {n : ℕ} (x : bitvec n) (y : bitvec n) (c : Bool) : bitvec (n + 1) :=
  let f : Bool → Bool → Bool → Bool × Bool :=
    fun (x y c : Bool) => (bitvec.carry x y c, bitvec.xor3 x y c);
  sorry

/-- The sum of two bitvectors -/
protected def add {n : ℕ} (x : bitvec n) (y : bitvec n) : bitvec n := vector.tail (adc x y false)

/-- Subtract with borrow -/
def sbb {n : ℕ} (x : bitvec n) (y : bitvec n) (b : Bool) : Bool × bitvec n :=
  let f : Bool → Bool → Bool → Bool × Bool :=
    fun (x y c : Bool) => (bitvec.carry (!x) y c, bitvec.xor3 x y c);
  vector.map_accumr₂ f x y b

/-- The difference of two bitvectors -/
protected def sub {n : ℕ} (x : bitvec n) (y : bitvec n) : bitvec n := prod.snd (sbb x y false)

protected instance has_zero {n : ℕ} : HasZero (bitvec n) := { zero := bitvec.zero n }

protected instance has_one {n : ℕ} : HasOne (bitvec n) := { one := bitvec.one n }

protected instance has_add {n : ℕ} : Add (bitvec n) := { add := bitvec.add }

protected instance has_sub {n : ℕ} : Sub (bitvec n) := { sub := bitvec.sub }

protected instance has_neg {n : ℕ} : Neg (bitvec n) := { neg := bitvec.neg }

/-- The product of two bitvectors -/
protected def mul {n : ℕ} (x : bitvec n) (y : bitvec n) : bitvec n :=
  let f : bitvec n → Bool → bitvec n := fun (r : bitvec n) (b : Bool) => cond b (r + r + y) (r + r);
  list.foldl f 0 (vector.to_list x)

protected instance has_mul {n : ℕ} : Mul (bitvec n) := { mul := bitvec.mul }

/-! ### Comparison operators -/

/-- `uborrow x y` returns `tt` iff the "subtract with borrow" operation on `x`, `y` and `ff`
required a borrow. -/
def uborrow {n : ℕ} (x : bitvec n) (y : bitvec n) : Bool := prod.fst (sbb x y false)

/-- unsigned less-than proposition -/
/-- unsigned greater-than proposition -/
def ult {n : ℕ} (x : bitvec n) (y : bitvec n) := ↥(uborrow x y)

def ugt {n : ℕ} (x : bitvec n) (y : bitvec n) := ult y x

/-- unsigned less-than-or-equal-to proposition -/
/-- unsigned greater-than-or-equal-to proposition -/
def ule {n : ℕ} (x : bitvec n) (y : bitvec n) := ¬ult y x

def uge {n : ℕ} (x : bitvec n) (y : bitvec n) := ule y x

/-- `sborrow x y` returns `tt` iff `x < y` as two's complement integers -/
def sborrow {n : ℕ} : bitvec n → bitvec n → Bool := sorry

/-- signed less-than proposition -/
/-- signed greater-than proposition -/
def slt {n : ℕ} (x : bitvec n) (y : bitvec n) := ↥(sborrow x y)

/-- signed less-than-or-equal-to proposition -/
def sgt {n : ℕ} (x : bitvec n) (y : bitvec n) := slt y x

/-- signed greater-than-or-equal-to proposition -/
def sle {n : ℕ} (x : bitvec n) (y : bitvec n) := ¬slt y x

def sge {n : ℕ} (x : bitvec n) (y : bitvec n) := sle y x

/-! ### Conversion to `nat` and `int` -/

/-- Create a bitvector from a `nat` -/
protected def of_nat (n : ℕ) : ℕ → bitvec n := sorry

/-- Create a bitvector in the two's complement representation from an `int` -/
protected def of_int (n : ℕ) : ℤ → bitvec (Nat.succ n) := sorry

/-- `add_lsb r b` is `r + r + 1` if `b` is `tt` and `r + r` otherwise. -/
def add_lsb (r : ℕ) (b : Bool) : ℕ := r + r + cond b 1 0

/-- Given a `list` of `bool`s, return the `nat` they represent as a list of binary digits. -/
def bits_to_nat (v : List Bool) : ℕ := list.foldl add_lsb 0 v

/-- Return the natural number encoded by the input bitvector -/
protected def to_nat {n : ℕ} (v : bitvec n) : ℕ := bits_to_nat (vector.to_list v)

theorem bits_to_nat_to_list {n : ℕ} (x : bitvec n) :
    bitvec.to_nat x = bits_to_nat (vector.to_list x) :=
  rfl

-- mul_left_comm

theorem to_nat_append {m : ℕ} (xs : bitvec m) (b : Bool) :
    bitvec.to_nat (vector.append xs (b::ᵥvector.nil)) =
        bitvec.to_nat xs * bit0 1 + bitvec.to_nat (b::ᵥvector.nil) :=
  sorry

theorem bits_to_nat_to_bool (n : ℕ) :
    bitvec.to_nat (to_bool (n % bit0 1 = 1)::ᵥvector.nil) = n % bit0 1 :=
  sorry

theorem of_nat_succ {k : ℕ} {n : ℕ} :
    bitvec.of_nat (Nat.succ k) n =
        vector.append (bitvec.of_nat k (n / bit0 1)) (to_bool (n % bit0 1 = 1)::ᵥvector.nil) :=
  rfl

theorem to_nat_of_nat {k : ℕ} {n : ℕ} : bitvec.to_nat (bitvec.of_nat k n) = n % bit0 1 ^ k := sorry

/-- Return the integer encoded by the input bitvector -/
protected def to_int {n : ℕ} : bitvec n → ℤ := sorry

/-! ### Miscellaneous instances -/

protected instance has_repr (n : ℕ) : has_repr (bitvec n) := has_repr.mk repr

end bitvec


protected instance bitvec.ult.decidable {n : ℕ} {x : bitvec n} {y : bitvec n} :
    Decidable (bitvec.ult x y) :=
  bool.decidable_eq (bitvec.uborrow x y) tt

protected instance bitvec.ugt.decidable {n : ℕ} {x : bitvec n} {y : bitvec n} :
    Decidable (bitvec.ugt x y) :=
  bool.decidable_eq (bitvec.uborrow y x) tt

end Mathlib