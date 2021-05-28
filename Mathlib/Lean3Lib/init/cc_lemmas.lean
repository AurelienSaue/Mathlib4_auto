/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.propext
import Mathlib.Lean3Lib.init.classical
import PostPort

universes u 

namespace Mathlib

/- Lemmas use by the congruence closure module -/

theorem iff_eq_of_eq_true_left {a : Prop} {b : Prop} (h : a = True) : (a ↔ b) = b :=
  Eq.symm h ▸ propext (true_iff b)

theorem iff_eq_of_eq_true_right {a : Prop} {b : Prop} (h : b = True) : (a ↔ b) = a :=
  Eq.symm h ▸ propext (iff_true a)

theorem iff_eq_true_of_eq {a : Prop} {b : Prop} (h : a = b) : (a ↔ b) = True :=
  h ▸ propext (iff_self a)

theorem and_eq_of_eq_true_left {a : Prop} {b : Prop} (h : a = True) : (a ∧ b) = b :=
  Eq.symm h ▸ propext (true_and b)

theorem and_eq_of_eq_true_right {a : Prop} {b : Prop} (h : b = True) : (a ∧ b) = a :=
  Eq.symm h ▸ propext (and_true a)

theorem and_eq_of_eq_false_left {a : Prop} {b : Prop} (h : a = False) : (a ∧ b) = False :=
  Eq.symm h ▸ propext (false_and b)

theorem and_eq_of_eq_false_right {a : Prop} {b : Prop} (h : b = False) : (a ∧ b) = False :=
  Eq.symm h ▸ propext (and_false a)

theorem and_eq_of_eq {a : Prop} {b : Prop} (h : a = b) : (a ∧ b) = a :=
  h ▸ propext (and_self a)

theorem or_eq_of_eq_true_left {a : Prop} {b : Prop} (h : a = True) : (a ∨ b) = True :=
  Eq.symm h ▸ propext (true_or b)

theorem or_eq_of_eq_true_right {a : Prop} {b : Prop} (h : b = True) : (a ∨ b) = True :=
  Eq.symm h ▸ propext (or_true a)

theorem or_eq_of_eq_false_left {a : Prop} {b : Prop} (h : a = False) : (a ∨ b) = b :=
  Eq.symm h ▸ propext (false_or b)

theorem or_eq_of_eq_false_right {a : Prop} {b : Prop} (h : b = False) : (a ∨ b) = a :=
  Eq.symm h ▸ propext (or_false a)

theorem or_eq_of_eq {a : Prop} {b : Prop} (h : a = b) : (a ∨ b) = a :=
  h ▸ propext (or_self a)

theorem imp_eq_of_eq_true_left {a : Prop} {b : Prop} (h : a = True) : (a → b) = b :=
  Eq.symm h ▸ propext { mp := fun (h : True → b) => h trivial, mpr := fun (h₁ : b) (h₂ : True) => h₁ }

theorem imp_eq_of_eq_true_right {a : Prop} {b : Prop} (h : b = True) : (a → b) = True :=
  Eq.symm h ▸ propext { mp := fun (h : a → True) => trivial, mpr := fun (h₁ : True) (h₂ : a) => h₁ }

theorem imp_eq_of_eq_false_left {a : Prop} {b : Prop} (h : a = False) : (a → b) = True :=
  Eq.symm h ▸ propext { mp := fun (h : False → b) => trivial, mpr := fun (h₁ : True) (h₂ : False) => false.elim h₂ }

theorem imp_eq_of_eq_false_right {a : Prop} {b : Prop} (h : b = False) : (a → b) = (¬a) :=
  Eq.symm h ▸ propext { mp := fun (h : a → False) => h, mpr := fun (hna : ¬a) (ha : a) => hna ha }

/- Remark: the congruence closure module will only use the following lemma is
   cc_config.em is tt. -/

theorem not_imp_eq_of_eq_false_right {a : Prop} {b : Prop} (h : b = False) : (¬a → b) = a := sorry

theorem imp_eq_true_of_eq {a : Prop} {b : Prop} (h : a = b) : (a → b) = True :=
  h ▸ propext { mp := fun (h : a → a) => trivial, mpr := fun (h : True) (ha : a) => ha }

theorem not_eq_of_eq_true {a : Prop} (h : a = True) : (¬a) = False :=
  Eq.symm h ▸ propext not_true_iff

theorem not_eq_of_eq_false {a : Prop} (h : a = False) : (¬a) = True :=
  Eq.symm h ▸ propext not_false_iff

theorem false_of_a_eq_not_a {a : Prop} (h : a = (¬a)) : False :=
  (fun (this : ¬a) => absurd (eq.mpr h this) this) fun (ha : a) => absurd ha (eq.mp h ha)

theorem if_eq_of_eq_true {c : Prop} [d : Decidable c] {α : Sort u} (t : α) (e : α) (h : c = True) : ite c t e = t :=
  if_pos (of_eq_true h)

theorem if_eq_of_eq_false {c : Prop} [d : Decidable c] {α : Sort u} (t : α) (e : α) (h : c = False) : ite c t e = e :=
  if_neg (not_of_eq_false h)

theorem if_eq_of_eq (c : Prop) [d : Decidable c] {α : Sort u} {t : α} {e : α} (h : t = e) : ite c t e = t := sorry

theorem eq_true_of_and_eq_true_left {a : Prop} {b : Prop} (h : (a ∧ b) = True) : a = True :=
  eq_true_intro (and.left (of_eq_true h))

theorem eq_true_of_and_eq_true_right {a : Prop} {b : Prop} (h : (a ∧ b) = True) : b = True :=
  eq_true_intro (and.right (of_eq_true h))

theorem eq_false_of_or_eq_false_left {a : Prop} {b : Prop} (h : (a ∨ b) = False) : a = False :=
  eq_false_intro fun (ha : a) => false.elim (eq.mp h (Or.inl ha))

theorem eq_false_of_or_eq_false_right {a : Prop} {b : Prop} (h : (a ∨ b) = False) : b = False :=
  eq_false_intro fun (hb : b) => false.elim (eq.mp h (Or.inr hb))

theorem eq_false_of_not_eq_true {a : Prop} (h : (¬a) = True) : a = False :=
  eq_false_intro fun (ha : a) => absurd ha (eq.mpr h trivial)

/- Remark: the congruence closure module will only use the following lemma is
   cc_config.em is tt. -/

theorem eq_true_of_not_eq_false {a : Prop} (h : (¬a) = False) : a = True :=
  eq_true_intro (classical.by_contradiction fun (hna : ¬a) => eq.mp h hna)

theorem ne_of_eq_of_ne {α : Sort u} {a : α} {b : α} {c : α} (h₁ : a = b) (h₂ : b ≠ c) : a ≠ c :=
  Eq.symm h₁ ▸ h₂

theorem ne_of_ne_of_eq {α : Sort u} {a : α} {b : α} {c : α} (h₁ : a ≠ b) (h₂ : b = c) : a ≠ c :=
  h₂ ▸ h₁

