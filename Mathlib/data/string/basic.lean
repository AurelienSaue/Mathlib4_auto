/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Supplementary theorems about the `string` type.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.basic
import Mathlib.data.char
import Mathlib.PostPort

namespace Mathlib

namespace string


def ltb : iterator → iterator → Bool :=
  sorry

protected instance has_lt' : HasLess string :=
  { Less := fun (s₁ s₂ : string) => ↥(ltb (mk_iterator s₁) (mk_iterator s₂)) }

protected instance decidable_lt : DecidableRel Less :=
  fun (a b : string) => bool.decidable_eq (ltb (mk_iterator a) (mk_iterator b)) tt

@[simp] theorem lt_iff_to_list_lt {s₁ : string} {s₂ : string} : s₁ < s₂ ↔ to_list s₁ < to_list s₂ := sorry

protected instance has_le : HasLessEq string :=
  { LessEq := fun (s₁ s₂ : string) => ¬s₂ < s₁ }

protected instance decidable_le : DecidableRel LessEq :=
  fun (a b : string) => ne.decidable (ltb (mk_iterator b) (mk_iterator a)) tt

@[simp] theorem le_iff_to_list_le {s₁ : string} {s₂ : string} : s₁ ≤ s₂ ↔ to_list s₁ ≤ to_list s₂ :=
  iff.trans (not_congr lt_iff_to_list_lt) not_lt

theorem to_list_inj {s₁ : string} {s₂ : string} : to_list s₁ = to_list s₂ ↔ s₁ = s₂ := sorry

theorem nil_as_string_eq_empty : list.as_string [] = empty :=
  rfl

@[simp] theorem to_list_empty : to_list empty = [] :=
  rfl

theorem as_string_inv_to_list (s : string) : list.as_string (to_list s) = s :=
  string_imp.cases_on s fun (s : List char) => Eq.refl (list.as_string (to_list (string_imp.mk s)))

@[simp] theorem to_list_singleton (c : char) : to_list (singleton c) = [c] :=
  rfl

theorem to_list_nonempty {s : string} (h : s ≠ empty) : to_list s = head s :: to_list (popn s 1) := sorry

@[simp] theorem head_empty : head empty = Inhabited.default :=
  rfl

@[simp] theorem popn_empty {n : ℕ} : popn empty n = empty := sorry

protected instance linear_order : linear_order string :=
  linear_order.mk LessEq Less sorry sorry sorry sorry string.decidable_le
    (fun (a b : string) => string.has_decidable_eq a b) fun (a b : string) => string.decidable_lt a b

end string


theorem list.to_list_inv_as_string (l : List char) : string.to_list (list.as_string l) = l := sorry

@[simp] theorem list.as_string_inj {l : List char} {l' : List char} : list.as_string l = list.as_string l' ↔ l = l' := sorry

theorem list.as_string_eq {l : List char} {s : string} : list.as_string l = s ↔ l = string.to_list s := sorry

