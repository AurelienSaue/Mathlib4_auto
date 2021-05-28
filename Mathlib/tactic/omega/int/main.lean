/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.omega.prove_unsats
import Mathlib.tactic.omega.int.dnf
import Mathlib.PostPort

namespace Mathlib

/-
Main procedure for linear integer arithmetic.
-/

namespace omega


namespace int


theorem univ_close_of_unsat_clausify (m : ℕ) (p : preform) : clauses.unsat (dnf (preform.not p)) → univ_close p (fun (x : ℕ) => 0) m :=
  fun (ᾰ : clauses.unsat (dnf (preform.not p))) =>
    idRhs (univ_close p (fun (x : ℕ) => 0) m) (univ_close_of_valid (valid_of_unsat_not (unsat_of_clauses_unsat ᾰ)))

