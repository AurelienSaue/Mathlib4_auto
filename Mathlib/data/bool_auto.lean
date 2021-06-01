/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# booleans

This file proves various trivial lemmas about booleans and their
relation to decidable propositions.

## Notations

This file introduces the notation `!b` for `bnot b`, the boolean "not".

## Tags
bool, boolean, De Morgan
-/

namespace bool


prefix:90 "!" => Mathlib.bnot

@[simp] theorem coe_sort_tt : ↥tt = True := eq_true_intro rfl

@[simp] theorem coe_sort_ff : ↥false = False := eq_false_intro ff_ne_tt

@[simp] theorem to_bool_true {h : Decidable True} : to_bool True = tt := sorry

@[simp] theorem to_bool_false {h : Decidable False} : to_bool False = false := sorry

@[simp] theorem to_bool_coe (b : Bool) {h : Decidable ↥b} : to_bool ↥b = b := sorry

theorem coe_to_bool (p : Prop) [Decidable p] : ↥(to_bool p) ↔ p := to_bool_iff p

@[simp] theorem of_to_bool_iff {p : Prop} [Decidable p] : ↥(to_bool p) ↔ p :=
  { mp := of_to_bool_true, mpr := to_bool_true }

@[simp] theorem tt_eq_to_bool_iff {p : Prop} [Decidable p] : tt = to_bool p ↔ p :=
  iff.trans eq_comm of_to_bool_iff

@[simp] theorem ff_eq_to_bool_iff {p : Prop} [Decidable p] : false = to_bool p ↔ ¬p :=
  iff.trans eq_comm (to_bool_ff_iff p)

@[simp] theorem to_bool_not (p : Prop) [Decidable p] : to_bool (¬p) = !to_bool p := sorry

@[simp] theorem to_bool_and (p : Prop) (q : Prop) [Decidable p] [Decidable q] :
    to_bool (p ∧ q) = to_bool p && to_bool q :=
  sorry

@[simp] theorem to_bool_or (p : Prop) (q : Prop) [Decidable p] [Decidable q] :
    to_bool (p ∨ q) = to_bool p || to_bool q :=
  sorry

@[simp] theorem to_bool_eq {p : Prop} {q : Prop} [Decidable p] [Decidable q] :
    to_bool p = to_bool q ↔ (p ↔ q) :=
  sorry

theorem not_ff : ¬↥false := sorry

@[simp] theorem default_bool : Inhabited.default = false := rfl

theorem dichotomy (b : Bool) : b = false ∨ b = tt := sorry

@[simp] theorem forall_bool {p : Bool → Prop} : (∀ (b : Bool), p b) ↔ p false ∧ p tt := sorry

@[simp] theorem exists_bool {p : Bool → Prop} : (∃ (b : Bool), p b) ↔ p false ∨ p tt := sorry

/-- If `p b` is decidable for all `b : bool`, then `∀ b, p b` is decidable -/
protected instance decidable_forall_bool {p : Bool → Prop} [(b : Bool) → Decidable (p b)] :
    Decidable (∀ (b : Bool), p b) :=
  decidable_of_decidable_of_iff and.decidable sorry

/-- If `p b` is decidable for all `b : bool`, then `∃ b, p b` is decidable -/
protected instance decidable_exists_bool {p : Bool → Prop} [(b : Bool) → Decidable (p b)] :
    Decidable (∃ (b : Bool), p b) :=
  decidable_of_decidable_of_iff or.decidable sorry

@[simp] theorem cond_ff {α : Type u_1} (t : α) (e : α) : cond false t e = e := rfl

@[simp] theorem cond_tt {α : Type u_1} (t : α) (e : α) : cond tt t e = t := rfl

@[simp] theorem cond_to_bool {α : Type u_1} (p : Prop) [Decidable p] (t : α) (e : α) :
    cond (to_bool p) t e = ite p t e :=
  sorry

theorem coe_bool_iff {a : Bool} {b : Bool} : ↥a ↔ ↥b ↔ a = b := of_as_true trivial

theorem eq_tt_of_ne_ff {a : Bool} : a ≠ false → a = tt := of_as_true trivial

theorem eq_ff_of_ne_tt {a : Bool} : a ≠ tt → a = false := of_as_true trivial

theorem bor_comm (a : Bool) (b : Bool) : a || b = b || a := of_as_true trivial

@[simp] theorem bor_assoc (a : Bool) (b : Bool) (c : Bool) : a || b || c = a || (b || c) :=
  of_as_true trivial

theorem bor_left_comm (a : Bool) (b : Bool) (c : Bool) : a || (b || c) = b || (a || c) :=
  of_as_true trivial

theorem bor_inl {a : Bool} {b : Bool} (H : ↥a) : ↥(a || b) := sorry

theorem bor_inr {a : Bool} {b : Bool} (H : ↥b) : ↥(a || b) := sorry

theorem band_comm (a : Bool) (b : Bool) : a && b = b && a := of_as_true trivial

@[simp] theorem band_assoc (a : Bool) (b : Bool) (c : Bool) : a && b && c = a && (b && c) :=
  of_as_true trivial

theorem band_left_comm (a : Bool) (b : Bool) (c : Bool) : a && (b && c) = b && (a && c) :=
  of_as_true trivial

theorem band_elim_left {a : Bool} {b : Bool} : ↥(a && b) → ↥a := of_as_true trivial

theorem band_intro {a : Bool} {b : Bool} : ↥a → ↥b → ↥(a && b) := of_as_true trivial

theorem band_elim_right {a : Bool} {b : Bool} : ↥(a && b) → ↥b := of_as_true trivial

@[simp] theorem bnot_false : !false = tt := rfl

@[simp] theorem bnot_true : !tt = false := rfl

theorem eq_tt_of_bnot_eq_ff {a : Bool} : !a = false → a = tt := of_as_true trivial

theorem eq_ff_of_bnot_eq_tt {a : Bool} : !a = tt → a = false := of_as_true trivial

theorem bxor_comm (a : Bool) (b : Bool) : bxor a b = bxor b a := of_as_true trivial

@[simp] theorem bxor_assoc (a : Bool) (b : Bool) (c : Bool) :
    bxor (bxor a b) c = bxor a (bxor b c) :=
  of_as_true trivial

theorem bxor_left_comm (a : Bool) (b : Bool) (c : Bool) : bxor a (bxor b c) = bxor b (bxor a c) :=
  of_as_true trivial

@[simp] theorem bxor_bnot_left (a : Bool) : bxor (!a) a = tt := of_as_true trivial

@[simp] theorem bxor_bnot_right (a : Bool) : bxor a (!a) = tt := of_as_true trivial

@[simp] theorem bxor_bnot_bnot (a : Bool) (b : Bool) : bxor (!a) (!b) = bxor a b :=
  of_as_true trivial

@[simp] theorem bxor_ff_left (a : Bool) : bxor false a = a := of_as_true trivial

@[simp] theorem bxor_ff_right (a : Bool) : bxor a false = a := of_as_true trivial

theorem bxor_iff_ne {x : Bool} {y : Bool} : bxor x y = tt ↔ x ≠ y := of_as_true trivial

/-! ### De Morgan's laws for booleans-/

@[simp] theorem bnot_band (a : Bool) (b : Bool) : !(a && b) = !a || !b := of_as_true trivial

@[simp] theorem bnot_bor (a : Bool) (b : Bool) : !(a || b) = !a && !b := of_as_true trivial

theorem bnot_inj {a : Bool} {b : Bool} : !a = !b → a = b := of_as_true trivial

end bool


protected instance bool.linear_order : linear_order Bool :=
  linear_order.mk (fun (a b : Bool) => a = false ∨ b = tt)
    (partial_order.lt._default fun (a b : Bool) => a = false ∨ b = tt) sorry sorry sorry sorry
    infer_instance infer_instance infer_instance

namespace bool


@[simp] theorem ff_le {x : Bool} : false ≤ x := or.intro_left (x = tt) rfl

@[simp] theorem le_tt {x : Bool} : x ≤ tt := or.intro_right (x = false) rfl

@[simp] theorem ff_lt_tt : false < tt := lt_of_le_of_ne ff_le ff_ne_tt

/-- convert a `bool` to a `ℕ`, `false -> 0`, `true -> 1` -/
def to_nat (b : Bool) : ℕ := cond b 1 0

/-- convert a `ℕ` to a `bool`, `0 -> false`, everything else -> `true` -/
def of_nat (n : ℕ) : Bool := to_bool (n ≠ 0)

theorem of_nat_le_of_nat {n : ℕ} {m : ℕ} (h : n ≤ m) : of_nat n ≤ of_nat m := sorry

theorem to_nat_le_to_nat {b₀ : Bool} {b₁ : Bool} (h : b₀ ≤ b₁) : to_nat b₀ ≤ to_nat b₁ := sorry

theorem of_nat_to_nat (b : Bool) : of_nat (to_nat b) = b := sorry

end Mathlib