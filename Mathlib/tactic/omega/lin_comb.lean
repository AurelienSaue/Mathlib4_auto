/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.omega.clause
import Mathlib.PostPort

namespace Mathlib

/-
Linear combination of constraints.
-/

namespace omega


/-- Linear combination of constraints. The second
    argument is the list of constraints, and the first
    argument is the list of conefficients by which the
    constraints are multiplied -/
@[simp] def lin_comb : List ℕ → List term → term :=
  sorry

theorem lin_comb_holds {v : ℕ → ℤ} {ts : List term} (ns : List ℕ) : (∀ (t : term), t ∈ ts → 0 ≤ term.val v t) → 0 ≤ term.val v (lin_comb ns ts) := sorry

/-- `unsat_lin_comb ns ts` asserts that the linear combination
    `lin_comb ns ts` is unsatisfiable  -/
def unsat_lin_comb (ns : List ℕ) (ts : List term)  :=
  prod.fst (lin_comb ns ts) < 0 ∧ ∀ (x : ℤ), x ∈ prod.snd (lin_comb ns ts) → x = 0

theorem unsat_lin_comb_of (ns : List ℕ) (ts : List term) : prod.fst (lin_comb ns ts) < 0 → (∀ (x : ℤ), x ∈ prod.snd (lin_comb ns ts) → x = 0) → unsat_lin_comb ns ts :=
  fun (h1 : prod.fst (lin_comb ns ts) < 0) (h2 : ∀ (x : ℤ), x ∈ prod.snd (lin_comb ns ts) → x = 0) =>
    { left := h1, right := h2 }

theorem unsat_of_unsat_lin_comb (ns : List ℕ) (ts : List term) : unsat_lin_comb ns ts → clause.unsat ([], ts) := sorry

