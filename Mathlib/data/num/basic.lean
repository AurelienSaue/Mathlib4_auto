/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.PostPort

universes l u_1 

namespace Mathlib

/-!
# Binary representation of integers using inductive types

Note: Unlike in Coq, where this representation is preferred because of
the reliance on kernel reduction, in Lean this representation is discouraged
in favor of the "Peano" natural numbers `nat`, and the purpose of this
collection of theorems is to show the equivalence of the different approaches.
-/

/-- The type of positive binary numbers.

     13 = 1101(base 2) = bit1 (bit0 (bit1 one)) -/
inductive pos_num 
where
| one : pos_num
| bit1 : pos_num → pos_num
| bit0 : pos_num → pos_num

protected instance pos_num.has_one : HasOne pos_num :=
  { one := pos_num.one }

protected instance pos_num.inhabited : Inhabited pos_num :=
  { default := 1 }

/-- The type of nonnegative binary numbers, using `pos_num`.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one))) -/
inductive num 
where
| zero : num
| pos : pos_num → num

protected instance num.has_zero : HasZero num :=
  { zero := num.zero }

protected instance num.has_one : HasOne num :=
  { one := num.pos 1 }

protected instance num.inhabited : Inhabited num :=
  { default := 0 }

/-- Representation of integers using trichotomy around zero.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one)))
     -13 = -1101(base 2) = neg (bit1 (bit0 (bit1 one))) -/
inductive znum 
where
| zero : znum
| pos : pos_num → znum
| neg : pos_num → znum

protected instance znum.has_zero : HasZero znum :=
  { zero := znum.zero }

protected instance znum.has_one : HasOne znum :=
  { one := znum.pos 1 }

protected instance znum.inhabited : Inhabited znum :=
  { default := 0 }

namespace pos_num


def bit (b : Bool) : pos_num → pos_num :=
  cond b bit1 bit0

def succ : pos_num → pos_num :=
  sorry

def is_one : pos_num → Bool :=
  sorry

protected def add : pos_num → pos_num → pos_num :=
  sorry

protected instance has_add : Add pos_num :=
  { add := pos_num.add }

def pred' : pos_num → num :=
  sorry

def pred (a : pos_num) : pos_num :=
  num.cases_on (pred' a) 1 id

def size : pos_num → pos_num :=
  sorry

def nat_size : pos_num → ℕ :=
  sorry

protected def mul (a : pos_num) : pos_num → pos_num :=
  sorry

protected instance has_mul : Mul pos_num :=
  { mul := pos_num.mul }

def of_nat_succ : ℕ → pos_num :=
  sorry

def of_nat (n : ℕ) : pos_num :=
  of_nat_succ (Nat.pred n)

def cmp : pos_num → pos_num → ordering :=
  sorry

protected instance has_lt : HasLess pos_num :=
  { Less := fun (a b : pos_num) => cmp a b = ordering.lt }

protected instance has_le : HasLessEq pos_num :=
  { LessEq := fun (a b : pos_num) => ¬b < a }

protected instance decidable_lt : DecidableRel Less :=
  sorry

protected instance decidable_le : DecidableRel LessEq :=
  sorry

end pos_num


def cast_pos_num {α : Type u_1} [HasOne α] [Add α] : pos_num → α :=
  sorry

def cast_num {α : Type u_1} [HasOne α] [Add α] [z : HasZero α] : num → α :=
  sorry

protected instance pos_num_coe {α : Type u_1} [HasOne α] [Add α] : has_coe_t pos_num α :=
  has_coe_t.mk cast_pos_num

protected instance num_nat_coe {α : Type u_1} [HasOne α] [Add α] [z : HasZero α] : has_coe_t num α :=
  has_coe_t.mk cast_num

protected instance pos_num.has_repr : has_repr pos_num :=
  has_repr.mk fun (n : pos_num) => repr ↑n

protected instance num.has_repr : has_repr num :=
  has_repr.mk fun (n : num) => repr ↑n

namespace num


def succ' : num → pos_num :=
  sorry

def succ (n : num) : num :=
  pos (succ' n)

protected def add : num → num → num :=
  sorry

protected instance has_add : Add num :=
  { add := num.add }

protected def bit0 : num → num :=
  sorry

protected def bit1 : num → num :=
  sorry

def bit (b : Bool) : num → num :=
  cond b num.bit1 num.bit0

def size : num → num :=
  sorry

def nat_size : num → ℕ :=
  sorry

protected def mul : num → num → num :=
  sorry

protected instance has_mul : Mul num :=
  { mul := num.mul }

def cmp : num → num → ordering :=
  sorry

protected instance has_lt : HasLess num :=
  { Less := fun (a b : num) => cmp a b = ordering.lt }

protected instance has_le : HasLessEq num :=
  { LessEq := fun (a b : num) => ¬b < a }

protected instance decidable_lt : DecidableRel Less :=
  sorry

protected instance decidable_le : DecidableRel LessEq :=
  sorry

def to_znum : num → znum :=
  sorry

def to_znum_neg : num → znum :=
  sorry

def of_nat' : ℕ → num :=
  nat.binary_rec 0 fun (b : Bool) (n : ℕ) => cond b num.bit1 num.bit0

end num


namespace znum


def zneg : znum → znum :=
  sorry

protected instance has_neg : Neg znum :=
  { neg := zneg }

def abs : znum → num :=
  sorry

def succ : znum → znum :=
  sorry

def pred : znum → znum :=
  sorry

protected def bit0 : znum → znum :=
  sorry

protected def bit1 : znum → znum :=
  sorry

protected def bitm1 : znum → znum :=
  sorry

def of_int' : ℤ → znum :=
  sorry

end znum


namespace pos_num


def sub' : pos_num → pos_num → znum :=
  sorry

def of_znum' : znum → Option pos_num :=
  sorry

def of_znum : znum → pos_num :=
  sorry

protected def sub (a : pos_num) (b : pos_num) : pos_num :=
  sorry

end pos_num


protected instance pos_num.has_sub : Sub pos_num :=
  { sub := pos_num.sub }

namespace num


def ppred : num → Option num :=
  sorry

def pred : num → num :=
  sorry

def div2 : num → num :=
  sorry

def of_znum' : znum → Option num :=
  sorry

def of_znum : znum → num :=
  sorry

def sub' : num → num → znum :=
  sorry

def psub (a : num) (b : num) : Option num :=
  of_znum' (sub' a b)

protected def sub (a : num) (b : num) : num :=
  of_znum (sub' a b)

end num


protected instance num.has_sub : Sub num :=
  { sub := num.sub }

namespace znum


protected def add : znum → znum → znum :=
  sorry

protected instance has_add : Add znum :=
  { add := znum.add }

protected def mul : znum → znum → znum :=
  sorry

protected instance has_mul : Mul znum :=
  { mul := znum.mul }

def cmp : znum → znum → ordering :=
  sorry

protected instance has_lt : HasLess znum :=
  { Less := fun (a b : znum) => cmp a b = ordering.lt }

protected instance has_le : HasLessEq znum :=
  { LessEq := fun (a b : znum) => ¬b < a }

protected instance decidable_lt : DecidableRel Less :=
  sorry

protected instance decidable_le : DecidableRel LessEq :=
  sorry

end znum


namespace pos_num


def divmod_aux (d : pos_num) (q : num) (r : num) : num × num :=
  sorry

def divmod (d : pos_num) : pos_num → num × num :=
  sorry

def div' (n : pos_num) (d : pos_num) : num :=
  prod.fst (divmod d n)

def mod' (n : pos_num) (d : pos_num) : num :=
  prod.snd (divmod d n)

/-

def sqrt_aux : ℕ → ℕ → ℕ → ℕ
| b r n := if b0 : b = 0 then r else
  let b' := shiftr b 2 in
  have b' < b, from sqrt_aux_dec b0,
  match (n - (r + b : ℕ) : ℤ) with
  | (n' : ℕ) := sqrt_aux b' (div2 r + b) n'
  | _ := sqrt_aux b' (div2 r) n
  end

/-- `sqrt n` is the square root of a natural number `n`. If `n` is not a
  perfect square, it returns the largest `k:ℕ` such that `k*k ≤ n`. -/

def sqrt (n : ℕ) : ℕ :=
match size n with
| 0      := 0
| succ s := sqrt_aux (shiftl 1 (bit0 (div2 s))) 0 n
end
-/
end pos_num


namespace num


def div : num → num → num :=
  sorry

def mod : num → num → num :=
  sorry

protected instance has_div : Div num :=
  { div := div }

protected instance has_mod : Mod num :=
  { mod := mod }

def gcd_aux : ℕ → num → num → num :=
  sorry

def gcd (a : num) (b : num) : num :=
  ite (a ≤ b) (gcd_aux (nat_size a + nat_size b) a b) (gcd_aux (nat_size b + nat_size a) b a)

end num


namespace znum


def div : znum → znum → znum :=
  sorry

def mod : znum → znum → znum :=
  sorry

protected instance has_div : Div znum :=
  { div := div }

protected instance has_mod : Mod znum :=
  { mod := mod }

def gcd (a : znum) (b : znum) : num :=
  num.gcd (abs a) (abs b)

end znum


def cast_znum {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] : znum → α :=
  sorry

protected instance znum_coe {α : Type u_1} [HasZero α] [HasOne α] [Add α] [Neg α] : has_coe_t znum α :=
  has_coe_t.mk cast_znum

protected instance znum.has_repr : has_repr znum :=
  has_repr.mk fun (n : znum) => repr ↑n

