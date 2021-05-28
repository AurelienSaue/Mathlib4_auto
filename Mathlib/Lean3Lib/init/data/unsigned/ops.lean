/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.unsigned.basic
import Mathlib.Lean3Lib.init.data.fin.ops
import Mathlib.PostPort

namespace Mathlib

namespace unsigned


def of_nat (n : ℕ) : unsigned :=
  fin.of_nat n

protected instance has_zero : HasZero unsigned :=
  { zero := fin.of_nat 0 }

protected instance has_one : HasOne unsigned :=
  { one := fin.of_nat 1 }

protected instance has_add : Add unsigned :=
  { add := fin.add }

protected instance has_sub : Sub unsigned :=
  { sub := fin.sub }

protected instance has_mul : Mul unsigned :=
  { mul := fin.mul }

protected instance has_mod : Mod unsigned :=
  { mod := fin.mod }

protected instance has_div : Div unsigned :=
  { div := fin.div }

protected instance has_lt : HasLess unsigned :=
  { Less := fin.lt }

end unsigned


protected instance unsigned.has_le : HasLessEq unsigned :=
  { LessEq := fin.le }

