/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.num.basic
import Mathlib.data.bitvec.core
import PostPort

universes l u_1 

namespace Mathlib

/-!
# Bitwise operations using binary representation of integers

## Definitions

* bitwise operations for `pos_num` and `num`,
* `snum`, a type that represents integers as a bit string with a sign bit at the end,
* arithmetic operations for `snum`.
-/

namespace pos_num


def lor : pos_num → pos_num → pos_num :=
  sorry

def land : pos_num → pos_num → num :=
  sorry

def ldiff : pos_num → pos_num → num :=
  sorry

def lxor : pos_num → pos_num → num :=
  sorry

def test_bit : pos_num → ℕ → Bool :=
  sorry

def one_bits : pos_num → ℕ → List ℕ :=
  sorry

def shiftl (p : pos_num) : ℕ → pos_num :=
  sorry

def shiftr : pos_num → ℕ → num :=
  sorry

end pos_num


namespace num


def lor : num → num → num :=
  sorry

def land : num → num → num :=
  sorry

def ldiff : num → num → num :=
  sorry

def lxor : num → num → num :=
  sorry

def shiftl : num → ℕ → num :=
  sorry

def shiftr : num → ℕ → num :=
  sorry

def test_bit : num → ℕ → Bool :=
  sorry

def one_bits : num → List ℕ :=
  sorry

end num


/-- This is a nonzero (and "non minus one") version of `snum`.
    See the documentation of `snum` for more details. -/
inductive nzsnum 
where
| msb : Bool → nzsnum
| bit : Bool → nzsnum → nzsnum

/-- Alternative representation of integers using a sign bit at the end.
  The convention on sign here is to have the argument to `msb` denote
  the sign of the MSB itself, with all higher bits set to the negation
  of this sign. The result is interpreted in two's complement.

     13  = ..0001101(base 2) = nz (bit1 (bit0 (bit1 (msb tt))))
     -13 = ..1110011(base 2) = nz (bit1 (bit1 (bit0 (msb ff))))

  As with `num`, a special case must be added for zero, which has no msb,
  but by two's complement symmetry there is a second special case for -1.
  Here the `bool` field indicates the sign of the number.

     0  = ..0000000(base 2) = zero ff
     -1 = ..1111111(base 2) = zero tt -/
inductive snum 
where
| zero : Bool → snum
| nz : nzsnum → snum

protected instance snum.has_coe : has_coe nzsnum snum :=
  has_coe.mk snum.nz

protected instance snum.has_zero : HasZero snum :=
  { zero := snum.zero false }

protected instance nzsnum.has_one : HasOne nzsnum :=
  { one := nzsnum.msb tt }

protected instance snum.has_one : HasOne snum :=
  { one := snum.nz 1 }

protected instance nzsnum.inhabited : Inhabited nzsnum :=
  { default := 1 }

protected instance snum.inhabited : Inhabited snum :=
  { default := 0 }

infixr:67 " :: " => Mathlib.nzsnum.bit

/-!
The `snum` representation uses a bit string, essentially a list of 0 (`ff`) and 1 (`tt`) bits,
and the negation of the MSB is sign-extended to all higher bits.
-/

namespace nzsnum


def sign : nzsnum → Bool :=
  sorry

def not : nzsnum → nzsnum :=
  sorry

prefix:40 "~" => Mathlib.nzsnum.not

def bit0 : nzsnum → nzsnum :=
  bit false

def bit1 : nzsnum → nzsnum :=
  bit tt

def head : nzsnum → Bool :=
  sorry

def tail : nzsnum → snum :=
  sorry

end nzsnum


namespace snum


def sign : snum → Bool :=
  sorry

def not : snum → snum :=
  sorry

prefix:40 "~" => Mathlib.snum.not

def bit : Bool → snum → snum :=
  sorry

infixr:67 " :: " => Mathlib.snum.bit

def bit0 : snum → snum :=
  bit false

def bit1 : snum → snum :=
  bit tt

theorem bit_zero (b : Bool) : b :: zero b = zero b :=
  bool.cases_on b (Eq.refl (false :: zero false)) (Eq.refl (tt :: zero tt))

theorem bit_one (b : Bool) : b :: zero (!b) = ↑(nzsnum.msb b) :=
  bool.cases_on b (Eq.refl (false :: zero (!false))) (Eq.refl (tt :: zero (!tt)))

end snum


namespace nzsnum


def drec' {C : snum → Sort u_1} (z : (b : Bool) → C (snum.zero b)) (s : (b : Bool) → (p : snum) → C p → C (b :: p)) (p : nzsnum) : C ↑p :=
  sorry

end nzsnum


namespace snum


def head : snum → Bool :=
  sorry

def tail : snum → snum :=
  sorry

def drec' {C : snum → Sort u_1} (z : (b : Bool) → C (zero b)) (s : (b : Bool) → (p : snum) → C p → C (b :: p)) (p : snum) : C p :=
  sorry

def rec' {α : Sort u_1} (z : Bool → α) (s : Bool → snum → α → α) : snum → α :=
  drec' z s

def test_bit : ℕ → snum → Bool :=
  sorry

def succ : snum → snum :=
  rec' (fun (b : Bool) => cond b 0 1) fun (b : Bool) (p succp : snum) => cond b (false :: succp) (tt :: p)

def pred : snum → snum :=
  rec' (fun (b : Bool) => cond b (~1) (~0)) fun (b : Bool) (p predp : snum) => cond b (false :: p) (tt :: predp)

protected def neg (n : snum) : snum :=
  succ (~n)

protected instance has_neg : Neg snum :=
  { neg := snum.neg }

def czadd : Bool → Bool → snum → snum :=
  sorry

end snum


namespace snum


/-- `a.bits n` is the vector of the `n` first bits of `a` (starting from the LSB). -/
def bits : snum → (n : ℕ) → vector Bool n :=
  sorry

def cadd : snum → snum → Bool → snum :=
  rec' (fun (a : Bool) (p : snum) (c : Bool) => czadd c a p)
    fun (a : Bool) (p : snum) (IH : snum → Bool → snum) =>
      rec' (fun (b c : Bool) => czadd c b (a :: p))
        fun (b : Bool) (q : snum) (_x : Bool → snum) (c : Bool) => bitvec.xor3 a b c :: IH q (bitvec.carry a b c)

/-- Add two `snum`s. -/
protected def add (a : snum) (b : snum) : snum :=
  cadd a b false

protected instance has_add : Add snum :=
  { add := snum.add }

/-- Substract two `snum`s. -/
protected def sub (a : snum) (b : snum) : snum :=
  a + -b

protected instance has_sub : Sub snum :=
  { sub := snum.sub }

/-- Multiply two `snum`s. -/
protected def mul (a : snum) : snum → snum :=
  rec' (fun (b : Bool) => cond b (-a) 0) fun (b : Bool) (q IH : snum) => cond b (bit0 IH + a) (bit0 IH)

protected instance has_mul : Mul snum :=
  { mul := snum.mul }

