/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.int.basic
import Mathlib.Lean3Lib.init.data.nat.bitwise
import PostPort

namespace Mathlib

namespace int


def div2 : ℤ → ℤ :=
  sorry

def bodd : ℤ → Bool :=
  sorry

def bit (b : Bool) : ℤ → ℤ :=
  cond b bit1 bit0

def test_bit : ℤ → ℕ → Bool :=
  sorry

def nat_bitwise (f : Bool → Bool → Bool) (m : ℕ) (n : ℕ) : ℤ :=
  cond (f false false) (Int.negSucc (nat.bitwise (fun (x y : Bool) => bnot (f x y)) m n)) ↑(nat.bitwise f m n)

def bitwise (f : Bool → Bool → Bool) : ℤ → ℤ → ℤ :=
  sorry

def lnot : ℤ → ℤ :=
  sorry

def lor : ℤ → ℤ → ℤ :=
  sorry

def land : ℤ → ℤ → ℤ :=
  sorry

def ldiff : ℤ → ℤ → ℤ :=
  sorry

def lxor : ℤ → ℤ → ℤ :=
  sorry

def shiftl : ℤ → ℤ → ℤ :=
  sorry

def shiftr (m : ℤ) (n : ℤ) : ℤ :=
  shiftl m (-n)

