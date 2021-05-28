/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import PostPort

namespace Mathlib

namespace debugger


def is_space (c : char) : Bool :=
  ite
    (c = char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1))))) ∨
      c = char.of_nat (bit1 (bit1 (bit0 1))) ∨ c = char.of_nat (bit0 (bit1 (bit0 1))))
    tt false

def split (s : string) : List string :=
  split_core (string.to_list s) none

def to_qualified_name_core : List char → name → string → name :=
  sorry

def to_qualified_name (s : string) : name :=
  to_qualified_name_core (string.to_list s) name.anonymous string.empty

def olean_to_lean (s : string) : string :=
  string.popn_back s (bit1 (bit0 1)) ++
    string.str
      (string.str
        (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit0 (bit1 1))))))))
          (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit0 (bit1 1))))))))
        (char.of_nat (bit1 (bit0 (bit0 (bit0 (bit0 (bit1 1))))))))
      (char.of_nat (bit0 (bit1 (bit1 (bit1 (bit0 (bit1 1)))))))

