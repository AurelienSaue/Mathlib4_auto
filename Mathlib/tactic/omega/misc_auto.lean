/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.localized
import PostPort

namespace Mathlib

/-
Miscellaneous.
-/

namespace omega


theorem fun_mono_2 {α : Type} {β : Type} {γ : Type} {p : α → β → γ} {a1 : α} {a2 : α} {b1 : β} {b2 : β} : a1 = a2 → b1 = b2 → p a1 b1 = p a2 b2 :=
  fun (h1 : a1 = a2) (h2 : b1 = b2) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (p a1 b1 = p a2 b2)) h1))
      (eq.mpr (id (Eq._oldrec (Eq.refl (p a2 b1 = p a2 b2)) h2)) (Eq.refl (p a2 b2)))

theorem pred_mono_2 {α : Type} {β : Type} {p : α → β → Prop} {a1 : α} {a2 : α} {b1 : β} {b2 : β} : a1 = a2 → b1 = b2 → (p a1 b1 ↔ p a2 b2) :=
  fun (h1 : a1 = a2) (h2 : b1 = b2) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (p a1 b1 ↔ p a2 b2)) h1))
      (eq.mpr (id (Eq._oldrec (Eq.refl (p a2 b1 ↔ p a2 b2)) h2)) (iff.refl (p a2 b2)))

theorem pred_mono_2' {c : Prop → Prop → Prop} {a1 : Prop} {a2 : Prop} {b1 : Prop} {b2 : Prop} : (a1 ↔ a2) → (b1 ↔ b2) → (c a1 b1 ↔ c a2 b2) :=
  fun (h1 : a1 ↔ a2) (h2 : b1 ↔ b2) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (c a1 b1 ↔ c a2 b2)) (propext h1)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (c a2 b1 ↔ c a2 b2)) (propext h2))) (iff.refl (c a2 b2)))

/-- Update variable assignment for a specific variable
    and leave everything else unchanged -/
def update {α : Type} (m : ℕ) (a : α) (v : ℕ → α) : ℕ → α :=
  sorry

theorem update_eq {α : Type} (m : ℕ) (a : α) (v : ℕ → α) : update m a v m = a := sorry

theorem update_eq_of_ne {α : Type} {m : ℕ} {a : α} {v : ℕ → α} (k : ℕ) : k ≠ m → update m a v k = v k := sorry

/-- Assign a new value to the zeroth variable, and push all
    other assignments up by 1 -/
def update_zero {α : Type} (a : α) (v : ℕ → α) : ℕ → α :=
  sorry

