/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.bool.basic
import Mathlib.Lean3Lib.init.meta.default

universes u 

namespace Mathlib

@[simp] theorem cond_a_a {α : Type u} (b : Bool) (a : α) : cond b a a = a := sorry

@[simp] theorem band_self (b : Bool) : b && b = b := sorry

@[simp] theorem band_tt (b : Bool) : b && tt = b := sorry

@[simp] theorem band_ff (b : Bool) : b && false = false := sorry

@[simp] theorem tt_band (b : Bool) : tt && b = b := sorry

@[simp] theorem ff_band (b : Bool) : false && b = false := sorry

@[simp] theorem bor_self (b : Bool) : b || b = b := sorry

@[simp] theorem bor_tt (b : Bool) : b || tt = tt := sorry

@[simp] theorem bor_ff (b : Bool) : b || false = b := sorry

@[simp] theorem tt_bor (b : Bool) : tt || b = tt := sorry

@[simp] theorem ff_bor (b : Bool) : false || b = b := sorry

@[simp] theorem bxor_self (b : Bool) : bxor b b = false := sorry

@[simp] theorem bxor_tt (b : Bool) : bxor b tt = bnot b := sorry

@[simp] theorem bxor_ff (b : Bool) : bxor b false = b := sorry

@[simp] theorem tt_bxor (b : Bool) : bxor tt b = bnot b := sorry

@[simp] theorem ff_bxor (b : Bool) : bxor false b = b := sorry

@[simp] theorem bnot_bnot (b : Bool) : bnot (bnot b) = b := sorry

@[simp] theorem tt_eq_ff_eq_false : ¬tt = false := id fun (ᾰ : tt = false) => bool.no_confusion ᾰ

@[simp] theorem ff_eq_tt_eq_false : ¬false = tt := id fun (ᾰ : false = tt) => bool.no_confusion ᾰ

@[simp] theorem eq_ff_eq_not_eq_tt (b : Bool) : (¬b = tt) = (b = false) := sorry

@[simp] theorem eq_tt_eq_not_eq_ff (b : Bool) : (¬b = false) = (b = tt) := sorry

theorem eq_ff_of_not_eq_tt {b : Bool} : ¬b = tt → b = false := eq.mp (eq_ff_eq_not_eq_tt b)

theorem eq_tt_of_not_eq_ff {b : Bool} : ¬b = false → b = tt := eq.mp (eq_tt_eq_not_eq_ff b)

@[simp] theorem band_eq_true_eq_eq_tt_and_eq_tt (a : Bool) (b : Bool) :
    a && b = tt = (a = tt ∧ b = tt) :=
  sorry

@[simp] theorem bor_eq_true_eq_eq_tt_or_eq_tt (a : Bool) (b : Bool) :
    a || b = tt = (a = tt ∨ b = tt) :=
  sorry

@[simp] theorem bnot_eq_true_eq_eq_ff (a : Bool) : bnot a = tt = (a = false) := sorry

@[simp] theorem band_eq_false_eq_eq_ff_or_eq_ff (a : Bool) (b : Bool) :
    a && b = false = (a = false ∨ b = false) :=
  sorry

@[simp] theorem bor_eq_false_eq_eq_ff_and_eq_ff (a : Bool) (b : Bool) :
    a || b = false = (a = false ∧ b = false) :=
  sorry

@[simp] theorem bnot_eq_ff_eq_eq_tt (a : Bool) : bnot a = false = (a = tt) := sorry

@[simp] theorem coe_ff : ↑false = False := sorry

@[simp] theorem coe_tt : ↑tt = True := sorry

@[simp] theorem coe_sort_ff : ↥false = False := sorry

@[simp] theorem coe_sort_tt : ↥tt = True := sorry

@[simp] theorem to_bool_iff (p : Prop) [d : Decidable p] : to_bool p = tt ↔ p := sorry

theorem to_bool_true {p : Prop} [Decidable p] : p → ↥(to_bool p) := iff.mpr (to_bool_iff p)

theorem to_bool_tt {p : Prop} [Decidable p] : p → to_bool p = tt := to_bool_true

theorem of_to_bool_true {p : Prop} [Decidable p] : ↥(to_bool p) → p := iff.mp (to_bool_iff p)

theorem bool_iff_false {b : Bool} : ¬↥b ↔ b = false :=
  bool.cases_on b (of_as_true trivial) (of_as_true trivial)

theorem bool_eq_false {b : Bool} : ¬↥b → b = false := iff.mp bool_iff_false

@[simp] theorem to_bool_ff_iff (p : Prop) [Decidable p] : to_bool p = false ↔ ¬p :=
  iff.trans (iff.symm bool_iff_false) (not_congr (to_bool_iff p))

theorem to_bool_ff {p : Prop} [Decidable p] : ¬p → to_bool p = false := iff.mpr (to_bool_ff_iff p)

theorem of_to_bool_ff {p : Prop} [Decidable p] : to_bool p = false → ¬p := iff.mp (to_bool_ff_iff p)

theorem to_bool_congr {p : Prop} {q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    to_bool p = to_bool q :=
  sorry

@[simp] theorem bor_coe_iff (a : Bool) (b : Bool) : ↥(a || b) ↔ ↥a ∨ ↥b :=
  bool.cases_on a (bool.cases_on b (of_as_true trivial) (of_as_true trivial))
    (bool.cases_on b (of_as_true trivial) (of_as_true trivial))

@[simp] theorem band_coe_iff (a : Bool) (b : Bool) : ↥(a && b) ↔ ↥a ∧ ↥b :=
  bool.cases_on a (bool.cases_on b (of_as_true trivial) (of_as_true trivial))
    (bool.cases_on b (of_as_true trivial) (of_as_true trivial))

@[simp] theorem bxor_coe_iff (a : Bool) (b : Bool) : ↥(bxor a b) ↔ xor ↥a ↥b :=
  bool.cases_on a (bool.cases_on b (of_as_true trivial) (of_as_true trivial))
    (bool.cases_on b (of_as_true trivial) (of_as_true trivial))

@[simp] theorem ite_eq_tt_distrib (c : Prop) [Decidable c] (a : Bool) (b : Bool) :
    ite c a b = tt = ite c (a = tt) (b = tt) :=
  sorry

@[simp] theorem ite_eq_ff_distrib (c : Prop) [Decidable c] (a : Bool) (b : Bool) :
    ite c a b = false = ite c (a = false) (b = false) :=
  sorry

end Mathlib