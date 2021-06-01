/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.omega.prove_unsats
import Mathlib.tactic.omega.nat.dnf
import Mathlib.tactic.omega.nat.neg_elim
import Mathlib.tactic.omega.nat.sub_elim
import Mathlib.PostPort

namespace Mathlib

/-
Main procedure for linear natural number arithmetic.
-/

namespace omega


namespace nat


theorem univ_close_of_unsat_neg_elim_not (m : ℕ) (p : preform) :
    preform.unsat (neg_elim (preform.not p)) → univ_close p (fun (_x : ℕ) => 0) m :=
  sorry

end Mathlib