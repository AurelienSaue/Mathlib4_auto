/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.omega.nat.preterm
import Mathlib.PostPort

universes l 

namespace Mathlib

/-
Linear natural number arithmetic preformulas in pre-normalized preform.
-/

namespace omega


namespace nat


/-- Intermediate shadow syntax for LNA formulas that includes unreified exprs -/
/-- Intermediate shadow syntax for LNA formulas that includes non-canonical terms -/
inductive preform 
where
| eq : preterm → preterm → preform
| le : preterm → preterm → preform
| not : preform → preform
| or : preform → preform → preform
| and : preform → preform → preform

namespace preform


/-- Evaluate a preform into prop using the valuation `v`. -/
@[simp] def holds (v : ℕ → ℕ) : preform → Prop :=
  sorry

end preform


/-- `univ_close p n` := `p` closed by prepending `n` universal quantifiers -/
@[simp] def univ_close (p : preform) : (ℕ → ℕ) → ℕ → Prop :=
  sorry

namespace preform


/-- Argument is free of negations -/
def neg_free : preform → Prop :=
  sorry

/-- Return expr of proof that argument is free of subtractions -/
def sub_free : preform → Prop :=
  sorry

/-- Fresh de Brujin index not used by any variable in argument -/
def fresh_index : preform → ℕ :=
  sorry

theorem holds_constant {v : ℕ → ℕ} {w : ℕ → ℕ} (p : preform) : (∀ (x : ℕ), x < fresh_index p → v x = w x) → (holds v p ↔ holds w p) := sorry

/-- All valuations satisfy argument -/
def valid (p : preform)  :=
  ∀ (v : ℕ → ℕ), holds v p

/-- There exists some valuation that satisfies argument -/
def sat (p : preform)  :=
  ∃ (v : ℕ → ℕ), holds v p

/-- `implies p q` := under any valuation, `q` holds if `p` holds -/
def implies (p : preform) (q : preform)  :=
  ∀ (v : ℕ → ℕ), holds v p → holds v q

/-- `equiv p q` := under any valuation, `p` holds iff `q` holds -/
def equiv (p : preform) (q : preform)  :=
  ∀ (v : ℕ → ℕ), holds v p ↔ holds v q

theorem sat_of_implies_of_sat {p : preform} {q : preform} : implies p q → sat p → sat q :=
  fun (h1 : implies p q) (h2 : sat p) => exists_imp_exists h1 h2

theorem sat_or {p : preform} {q : preform} : sat (or p q) ↔ sat p ∨ sat q := sorry

/-- There does not exist any valuation that satisfies argument -/
def unsat (p : preform)  :=
  ¬sat p

def repr : preform → string :=
  sorry

protected instance has_repr : has_repr preform :=
  has_repr.mk repr

end preform


theorem univ_close_of_valid {p : preform} {m : ℕ} {v : ℕ → ℕ} : preform.valid p → univ_close p v m := sorry

theorem valid_of_unsat_not {p : preform} : preform.unsat (preform.not p) → preform.valid p := sorry

