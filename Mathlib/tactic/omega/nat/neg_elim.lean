/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.omega.nat.form
import Mathlib.PostPort

namespace Mathlib

/-
Negation elimination.
-/

namespace omega


namespace nat


/-- push_neg p returns the result of normalizing ¬ p by
    pushing the outermost negation all the way down,
    until it reaches either a negation or an atom -/
@[simp] def push_neg : preform → preform :=
  sorry

theorem push_neg_equiv {p : preform} : preform.equiv (push_neg p) (preform.not p) := sorry

/-- NNF transformation -/
def nnf : preform → preform :=
  sorry

/-- Asserts that the given preform is in NNF -/
def is_nnf : preform → Prop :=
  sorry

theorem is_nnf_push_neg (p : preform) : is_nnf p → is_nnf (push_neg p) := sorry

theorem is_nnf_nnf (p : preform) : is_nnf (nnf p) := sorry

theorem nnf_equiv {p : preform} : preform.equiv (nnf p) p := sorry

@[simp] def neg_elim_core : preform → preform :=
  sorry

theorem neg_free_neg_elim_core (p : preform) : is_nnf p → preform.neg_free (neg_elim_core p) := sorry

theorem le_and_le_iff_eq {α : Type} [partial_order α] {a : α} {b : α} : a ≤ b ∧ b ≤ a ↔ a = b := sorry

theorem implies_neg_elim_core {p : preform} : preform.implies p (neg_elim_core p) := sorry

/-- Eliminate all negations in a preform -/
def neg_elim : preform → preform :=
  neg_elim_core ∘ nnf

theorem neg_free_neg_elim {p : preform} : preform.neg_free (neg_elim p) :=
  neg_free_neg_elim_core (nnf p) (is_nnf_nnf p)

theorem implies_neg_elim {p : preform} : preform.implies p (neg_elim p) :=
  id fun (v : ℕ → ℕ) (h1 : preform.holds v p) => implies_neg_elim_core v (iff.elim_right (nnf_equiv v) h1)

