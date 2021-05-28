/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.nat.basic
import PostPort

universes l 

namespace Mathlib

def is_valid_char (n : ℕ)  :=
  n < bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit1 (bit1 (bit0 (bit1 1)))))))))))))) ∨
    bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit0 (bit1 1)))))))))))))) < n ∧
      n <
        bit0
          (bit0
            (bit0
              (bit0
                (bit0
                  (bit0
                    (bit0
                      (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit1 (bit0 (bit0 (bit0 1)))))))))))))))))))

theorem is_valid_char_range_1 (n : ℕ) (h : n < bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit1 (bit1 (bit0 (bit1 1))))))))))))))) : is_valid_char n :=
  Or.inl h

theorem is_valid_char_range_2 (n : ℕ) (h₁ : bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit0 (bit1 1)))))))))))))) < n) (h₂ : n <
  bit0
    (bit0
      (bit0
        (bit0
          (bit0
            (bit0
              (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit1 (bit0 (bit0 (bit0 1)))))))))))))))))))) : is_valid_char n :=
  Or.inr { left := h₁, right := h₂ }

/-- The `char` type represents an unicode scalar value.
    See http://www.unicode.org/glossary/#unicode_scalar_value). -/
structure char 
where
  val : ℕ
  valid : is_valid_char val

protected instance char.has_sizeof : SizeOf char :=
  { sizeOf := fun (c : char) => char.val c }

namespace char


protected def lt (a : char) (b : char)  :=
  val a < val b

protected def le (a : char) (b : char)  :=
  val a ≤ val b

protected instance has_lt : HasLess char :=
  { Less := char.lt }

protected instance has_le : HasLessEq char :=
  { LessEq := char.le }

protected instance decidable_lt (a : char) (b : char) : Decidable (a < b) :=
  nat.decidable_lt (val a) (val b)

protected instance decidable_le (a : char) (b : char) : Decidable (a ≤ b) :=
  nat.decidable_le (val a) (val b)

/-
We cannot use tactics dec_trivial or comp_val here because the tactic framework has not been defined yet.
We also do not use `zero_lt_succ _` as a proof term because this proof may not be trivial to check by
external type checkers. See discussion at: https://github.com/leanprover/tc/issues/8
-/

theorem zero_lt_d800 : 0 < bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit1 (bit1 (bit0 (bit1 1)))))))))))))) := sorry

def of_nat (n : ℕ) : char :=
  dite (is_valid_char n) (fun (h : is_valid_char n) => mk n h) fun (h : ¬is_valid_char n) => mk 0 sorry

def to_nat (c : char) : ℕ :=
  val c

theorem eq_of_veq {c : char} {d : char} : val c = val d → c = d := sorry

theorem veq_of_eq {c : char} {d : char} : c = d → val c = val d := sorry

theorem ne_of_vne {c : char} {d : char} (h : val c ≠ val d) : c ≠ d :=
  fun (h' : c = d) => absurd (veq_of_eq h') h

theorem vne_of_ne {c : char} {d : char} (h : c ≠ d) : val c ≠ val d :=
  fun (h' : val c = val d) => absurd (eq_of_veq h') h

end char


protected instance char.decidable_eq : DecidableEq char :=
  fun (i j : char) => decidable_of_decidable_of_iff (nat.decidable_eq (char.val i) (char.val j)) sorry

protected instance char.inhabited : Inhabited char :=
  { default := char.of_nat (bit1 (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) }

