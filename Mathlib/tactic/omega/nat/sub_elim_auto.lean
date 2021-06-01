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
Subtraction elimination for linear natural number arithmetic.
Works by repeatedly rewriting goals of the preform `P[t-s]` into
`P[x] ∧ (t = s + x ∨ (t ≤ s ∧ x = 0))`, where `x` is fresh.
-/

namespace omega


namespace nat


namespace preterm


/-- Find subtraction inside preterm and return its operands -/
def sub_terms : preterm → Option (preterm × preterm) := sorry

/-- Find (t - s) inside a preterm and replace it with variable k -/
def sub_subst (t : preterm) (s : preterm) (k : ℕ) : preterm → preterm := sorry

theorem val_sub_subst {k : ℕ} {x : preterm} {y : preterm} {v : ℕ → ℕ} {t : preterm} :
    fresh_index t ≤ k → val (update k (val v x - val v y) v) (sub_subst x y k t) = val v t :=
  sorry

end preterm


namespace preform


/-- Find subtraction inside preform and return its operands -/
def sub_terms : preform → Option (preterm × preterm) := sorry

/-- Find (t - s) inside a preform and replace it with variable k -/
@[simp] def sub_subst (x : preterm) (y : preterm) (k : ℕ) : preform → preform := sorry

end preform


/-- Preform which asserts that the value of variable k is
    the truncated difference between preterms t and s -/
def is_diff (t : preterm) (s : preterm) (k : ℕ) : preform :=
  preform.or (preform.eq t (preterm.add s (preterm.var 1 k)))
    (preform.and (preform.le t s) (preform.eq (preterm.var 1 k) (preterm.cst 0)))

theorem holds_is_diff {t : preterm} {s : preterm} {k : ℕ} {v : ℕ → ℕ} :
    v k = preterm.val v t - preterm.val v s → preform.holds v (is_diff t s k) :=
  sorry

/-- Helper function for sub_elim -/
def sub_elim_core (t : preterm) (s : preterm) (k : ℕ) (p : preform) : preform :=
  preform.and (preform.sub_subst t s k p) (is_diff t s k)

/-- Return de Brujin index of fresh variable that does not occur
    in any of the arguments -/
def sub_fresh_index (t : preterm) (s : preterm) (p : preform) : ℕ :=
  max (preform.fresh_index p) (max (preterm.fresh_index t) (preterm.fresh_index s))

/-- Return a new preform with all subtractions eliminated -/
def sub_elim (t : preterm) (s : preterm) (p : preform) : preform :=
  sub_elim_core t s (sub_fresh_index t s p) p

theorem sub_subst_equiv {k : ℕ} {x : preterm} {y : preterm} {v : ℕ → ℕ} (p : preform) :
    preform.fresh_index p ≤ k →
        (preform.holds (update k (preterm.val v x - preterm.val v y) v)
            (preform.sub_subst x y k p) ↔
          preform.holds v p) :=
  sorry

theorem sat_sub_elim {t : preterm} {s : preterm} {p : preform} :
    preform.sat p → preform.sat (sub_elim t s p) :=
  sorry

theorem unsat_of_unsat_sub_elim (t : preterm) (s : preterm) (p : preform) :
    preform.unsat (sub_elim t s p) → preform.unsat p :=
  mt sat_sub_elim

end Mathlib