/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.logic
import Mathlib.PostPort

universes u_1 

namespace Mathlib

theorem punit_eq (a : PUnit) (b : PUnit) : a = b :=
  punit.rec_on a (punit.rec_on b rfl)

theorem punit_eq_star (a : PUnit) : a = PUnit.unit :=
  punit_eq a PUnit.unit

protected instance punit.subsingleton : subsingleton PUnit :=
  subsingleton.intro punit_eq

protected instance punit.inhabited : Inhabited PUnit :=
  { default := PUnit.unit }

protected instance punit.decidable_eq : DecidableEq PUnit :=
  fun (a b : PUnit) => is_true (punit_eq a b)

