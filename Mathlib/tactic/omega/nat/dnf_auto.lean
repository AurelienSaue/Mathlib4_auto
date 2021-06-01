/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.omega.clause
import Mathlib.tactic.omega.nat.form
import Mathlib.PostPort

namespace Mathlib

/-
DNF transformation.
-/

namespace omega


namespace nat


@[simp] def dnf_core : preform → List clause := sorry

theorem exists_clause_holds_core {v : ℕ → ℕ} {p : preform} :
    preform.neg_free p →
        preform.sub_free p →
          preform.holds v p →
            ∃ (c : clause), ∃ (H : c ∈ dnf_core p), clause.holds (fun (x : ℕ) => ↑(v x)) c :=
  sorry

def term.vars_core (is : List ℤ) : List Bool := list.map (fun (i : ℤ) => ite (i = 0) false tt) is

/-- Return a list of bools that encodes which variables have nonzero coefficients -/
def term.vars (t : term) : List Bool := term.vars_core (prod.snd t)

def bools.or : List Bool → List Bool → List Bool := sorry

/-- Return a list of bools that encodes which variables have nonzero coefficients in any one of the input terms -/
def terms.vars : List term → List Bool := sorry

def nonneg_consts_core : ℕ → List Bool → List term := sorry

def nonneg_consts (bs : List Bool) : List term := nonneg_consts_core 0 bs

def nonnegate : clause → clause := sorry

/-- DNF transformation -/
def dnf (p : preform) : List clause := list.map nonnegate (dnf_core p)

theorem holds_nonneg_consts_core {v : ℕ → ℤ} (h1 : ∀ (x : ℕ), 0 ≤ v x) (m : ℕ) (bs : List Bool)
    (t : term) (H : t ∈ nonneg_consts_core m bs) : 0 ≤ term.val v t :=
  sorry

theorem holds_nonneg_consts {v : ℕ → ℤ} {bs : List Bool} :
    (∀ (x : ℕ), 0 ≤ v x) → ∀ (t : term), t ∈ nonneg_consts bs → 0 ≤ term.val v t :=
  fun (ᾰ : ∀ (x : ℕ), 0 ≤ v x) =>
    idRhs (∀ (t : term), t ∈ nonneg_consts_core 0 bs → 0 ≤ term.val (fun (x : ℕ) => v x) t)
      (holds_nonneg_consts_core ᾰ 0 bs)

theorem exists_clause_holds {v : ℕ → ℕ} {p : preform} :
    preform.neg_free p →
        preform.sub_free p →
          preform.holds v p →
            ∃ (c : clause), ∃ (H : c ∈ dnf p), clause.holds (fun (x : ℕ) => ↑(v x)) c :=
  sorry

theorem exists_clause_sat {p : preform} :
    preform.neg_free p →
        preform.sub_free p → preform.sat p → ∃ (c : clause), ∃ (H : c ∈ dnf p), clause.sat c :=
  sorry

theorem unsat_of_unsat_dnf (p : preform) :
    preform.neg_free p → preform.sub_free p → clauses.unsat (dnf p) → preform.unsat p :=
  fun (hnf : preform.neg_free p) (hsf : preform.sub_free p) (h1 : clauses.unsat (dnf p)) =>
    id fun (h2 : preform.sat p) => h1 (exists_clause_sat hnf hsf h2)

end Mathlib