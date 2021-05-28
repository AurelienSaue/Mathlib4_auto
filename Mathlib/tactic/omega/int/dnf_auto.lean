/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.omega.clause
import Mathlib.tactic.omega.int.form
import PostPort

namespace Mathlib

/-
DNF transformation.
-/

namespace omega


namespace int


/-- push_neg p returns the result of normalizing ¬ p by
    pushing the outermost negation all the way down,
    until it reaches either a negation or an atom -/
@[simp] def push_neg : preform → preform :=
  sorry

theorem push_neg_equiv {p : preform} : preform.equiv (push_neg p) (preform.not p) := sorry

/-- NNF transformation -/
def nnf : preform → preform :=
  sorry

def is_nnf : preform → Prop :=
  sorry

theorem is_nnf_push_neg (p : preform) : is_nnf p → is_nnf (push_neg p) := sorry

/-- Argument is free of negations -/
def neg_free : preform → Prop :=
  sorry

theorem is_nnf_nnf (p : preform) : is_nnf (nnf p) := sorry

theorem nnf_equiv {p : preform} : preform.equiv (nnf p) p := sorry

/-- Eliminate all negations from preform -/
@[simp] def neg_elim : preform → preform :=
  sorry

theorem neg_free_neg_elim (p : preform) : is_nnf p → neg_free (neg_elim p) := sorry

theorem le_and_le_iff_eq {α : Type} [partial_order α] {a : α} {b : α} : a ≤ b ∧ b ≤ a ↔ a = b := sorry

theorem implies_neg_elim {p : preform} : preform.implies p (neg_elim p) := sorry

@[simp] def dnf_core : preform → List clause :=
  sorry

/-- DNF transformation -/
def dnf (p : preform) : List clause :=
  dnf_core (neg_elim (nnf p))

theorem exists_clause_holds {v : ℕ → ℤ} {p : preform} : neg_free p → preform.holds v p → ∃ (c : clause), ∃ (H : c ∈ dnf_core p), clause.holds v c := sorry

theorem clauses_sat_dnf_core {p : preform} : neg_free p → preform.sat p → clauses.sat (dnf_core p) := sorry

theorem unsat_of_clauses_unsat {p : preform} : clauses.unsat (dnf p) → preform.unsat p := sorry

