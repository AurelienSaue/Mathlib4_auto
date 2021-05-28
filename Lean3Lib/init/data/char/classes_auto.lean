/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import PrePort
import Lean3Lib.init.data.char.basic
import Lean3Lib.init.data.char.lemmas
import Lean3Lib.init.meta.default
import Lean3Lib.init.data.int.default
import PostPort

namespace Mathlib

namespace char


def is_whitespace (c : char)  :=
  c ∈ [of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1))))), of_nat (bit1 (bit0 (bit0 1))), of_nat (bit0 (bit1 (bit0 1)))]

def is_upper (c : char)  :=
  val c ≥ bit1 (bit0 (bit0 (bit0 (bit0 (bit0 1))))) ∧ val c ≤ bit0 (bit1 (bit0 (bit1 (bit1 (bit0 1)))))

def is_lower (c : char)  :=
  val c ≥ bit1 (bit0 (bit0 (bit0 (bit0 (bit1 1))))) ∧ val c ≤ bit0 (bit1 (bit0 (bit1 (bit1 (bit1 1)))))

def is_alpha (c : char)  :=
  is_upper c ∨ is_lower c

def is_digit (c : char)  :=
  val c ≥ bit0 (bit0 (bit0 (bit0 (bit1 1)))) ∧ val c ≤ bit1 (bit0 (bit0 (bit1 (bit1 1))))

def is_alphanum (c : char)  :=
  is_alpha c ∨ is_digit c

def is_punctuation (c : char)  :=
  c ∈
    [of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1))))), of_nat (bit0 (bit0 (bit1 (bit1 (bit0 1))))),
      of_nat (bit0 (bit1 (bit1 (bit1 (bit0 1))))), of_nat (bit1 (bit1 (bit1 (bit1 (bit1 1))))),
      of_nat (bit1 (bit0 (bit0 (bit0 (bit0 1))))), of_nat (bit1 (bit1 (bit0 (bit1 (bit1 1))))),
      of_nat (bit1 (bit0 (bit1 (bit1 (bit0 1))))), of_nat (bit1 (bit1 (bit1 (bit0 (bit0 1)))))]

def to_lower (c : char) : char :=
  let n : ℕ := to_nat c;
  ite (n ≥ bit1 (bit0 (bit0 (bit0 (bit0 (bit0 1))))) ∧ n ≤ bit0 (bit1 (bit0 (bit1 (bit1 (bit0 1))))))
    (of_nat (n + bit0 (bit0 (bit0 (bit0 (bit0 1)))))) c

protected instance decidable_is_whitespace : decidable_pred is_whitespace :=
  id
    fun (c : char) =>
      id
        (list.decidable_mem c
          [of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1))))), of_nat (bit1 (bit0 (bit0 1))), of_nat (bit0 (bit1 (bit0 1)))])

protected instance decidable_is_upper : decidable_pred is_upper :=
  id fun (c : char) => id and.decidable

protected instance decidable_is_lower : decidable_pred is_lower :=
  id fun (c : char) => id and.decidable

protected instance decidable_is_alpha : decidable_pred is_alpha :=
  id fun (c : char) => id or.decidable

protected instance decidable_is_digit : decidable_pred is_digit :=
  id fun (c : char) => id and.decidable

protected instance decidable_is_alphanum : decidable_pred is_alphanum :=
  id fun (c : char) => id or.decidable

protected instance decidable_is_punctuation : decidable_pred is_punctuation :=
  id
    fun (c : char) =>
      id
        (list.decidable_mem c
          [of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1))))), of_nat (bit0 (bit0 (bit1 (bit1 (bit0 1))))),
            of_nat (bit0 (bit1 (bit1 (bit1 (bit0 1))))), of_nat (bit1 (bit1 (bit1 (bit1 (bit1 1))))),
            of_nat (bit1 (bit0 (bit0 (bit0 (bit0 1))))), of_nat (bit1 (bit1 (bit0 (bit1 (bit1 1))))),
            of_nat (bit1 (bit0 (bit1 (bit1 (bit0 1))))), of_nat (bit1 (bit1 (bit1 (bit0 (bit0 1)))))])

