/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.omega.term
import Mathlib.PostPort

namespace Mathlib

/-
Definition of linear constrain clauses.
-/

namespace omega


/-- (([t₁,...tₘ],[s₁,...,sₙ]) : clause) encodes the constraints
0 = ⟦t₁⟧ ∧ ... ∧ 0 = ⟦tₘ⟧ ∧ 0 ≤ ⟦s₁⟧ ∧ ... ∧ 0 ≤ ⟦sₙ⟧, where
⟦t⟧ is the value of (t : term). -/
def clause := List term × List term

namespace clause


/-- holds v c := clause c holds under valuation v -/
def holds (v : ℕ → ℤ) : clause → Prop := sorry

/-- sat c := there exists a valuation v under which c holds -/
def sat (c : clause) := ∃ (v : ℕ → ℤ), holds v c

/-- unsat c := there is no valuation v under which c holds -/
def unsat (c : clause) := ¬sat c

/-- append two clauses by elementwise appending -/
def append (c1 : clause) (c2 : clause) : clause :=
  (prod.fst c1 ++ prod.fst c2, prod.snd c1 ++ prod.snd c2)

theorem holds_append {v : ℕ → ℤ} {c1 : clause} {c2 : clause} :
    holds v c1 → holds v c2 → holds v (append c1 c2) :=
  sorry

end clause


/-- There exists a satisfiable clause c in argument -/
def clauses.sat (cs : List clause) := ∃ (c : clause), ∃ (H : c ∈ cs), clause.sat c

/-- There is no satisfiable clause c in argument -/
def clauses.unsat (cs : List clause) := ¬clauses.sat cs

theorem clauses.unsat_nil : clauses.unsat [] := sorry

theorem clauses.unsat_cons (c : clause) (cs : List clause) :
    clause.unsat c → clauses.unsat cs → clauses.unsat (c :: cs) :=
  sorry

end Mathlib