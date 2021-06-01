/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.norm_num
import Mathlib.PostPort

universes u_1 l 

namespace Mathlib

/-!
# The `abel` tactic

Evaluate expressions in the language of additive, commutative monoids and groups.


-/

namespace tactic


namespace abel


def term {α : Type u_1} [add_comm_monoid α] (n : ℕ) (x : α) (a : α) : α := n •ℕ x + a

def termg {α : Type u_1} [add_comm_group α] (n : ℤ) (x : α) (a : α) : α := n •ℤ x + a

theorem const_add_term {α : Type u_1} [add_comm_monoid α] (k : α) (n : ℕ) (x : α) (a : α) (a' : α)
    (h : k + a = a') : k + term n x a = term n x a' :=
  sorry

theorem const_add_termg {α : Type u_1} [add_comm_group α] (k : α) (n : ℤ) (x : α) (a : α) (a' : α)
    (h : k + a = a') : k + termg n x a = termg n x a' :=
  sorry

theorem term_add_const {α : Type u_1} [add_comm_monoid α] (n : ℕ) (x : α) (a : α) (k : α) (a' : α)
    (h : a + k = a') : term n x a + k = term n x a' :=
  sorry

theorem term_add_constg {α : Type u_1} [add_comm_group α] (n : ℤ) (x : α) (a : α) (k : α) (a' : α)
    (h : a + k = a') : termg n x a + k = termg n x a' :=
  sorry

theorem term_add_term {α : Type u_1} [add_comm_monoid α] (n₁ : ℕ) (x : α) (a₁ : α) (n₂ : ℕ) (a₂ : α)
    (n' : ℕ) (a' : α) (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') :
    term n₁ x a₁ + term n₂ x a₂ = term n' x a' :=
  sorry

theorem term_add_termg {α : Type u_1} [add_comm_group α] (n₁ : ℤ) (x : α) (a₁ : α) (n₂ : ℤ) (a₂ : α)
    (n' : ℤ) (a' : α) (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') :
    termg n₁ x a₁ + termg n₂ x a₂ = termg n' x a' :=
  sorry

theorem zero_term {α : Type u_1} [add_comm_monoid α] (x : α) (a : α) : term 0 x a = a := sorry

theorem zero_termg {α : Type u_1} [add_comm_group α] (x : α) (a : α) : termg 0 x a = a := sorry

theorem term_neg {α : Type u_1} [add_comm_group α] (n : ℤ) (x : α) (a : α) (n' : ℤ) (a' : α)
    (h₁ : -n = n') (h₂ : -a = a') : -termg n x a = termg n' x a' :=
  sorry

def smul {α : Type u_1} [add_comm_monoid α] (n : ℕ) (x : α) : α := n •ℕ x

def smulg {α : Type u_1} [add_comm_group α] (n : ℤ) (x : α) : α := n •ℤ x

theorem zero_smul {α : Type u_1} [add_comm_monoid α] (c : ℕ) : smul c 0 = 0 := sorry

theorem zero_smulg {α : Type u_1} [add_comm_group α] (c : ℤ) : smulg c 0 = 0 := sorry

theorem term_smul {α : Type u_1} [add_comm_monoid α] (c : ℕ) (n : ℕ) (x : α) (a : α) (n' : ℕ)
    (a' : α) (h₁ : c * n = n') (h₂ : smul c a = a') : smul c (term n x a) = term n' x a' :=
  sorry

theorem term_smulg {α : Type u_1} [add_comm_group α] (c : ℤ) (n : ℤ) (x : α) (a : α) (n' : ℤ)
    (a' : α) (h₁ : c * n = n') (h₂ : smulg c a = a') : smulg c (termg n x a) = termg n' x a' :=
  sorry

theorem term_atom {α : Type u_1} [add_comm_monoid α] (x : α) : x = term 1 x 0 := sorry

theorem term_atomg {α : Type u_1} [add_comm_group α] (x : α) : x = termg 1 x 0 := sorry

theorem unfold_sub {α : Type u_1} [add_group α] (a : α) (b : α) (c : α) (h : a + -b = c) :
    a - b = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b = c)) (sub_eq_add_neg a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -b = c)) h)) (Eq.refl c))

theorem unfold_smul {α : Type u_1} [add_comm_monoid α] (n : ℕ) (x : α) (y : α) (h : smul n x = y) :
    n •ℕ x = y :=
  h

theorem unfold_smulg {α : Type u_1} [add_comm_group α] (n : ℕ) (x : α) (y : α)
    (h : smulg (Int.ofNat n) x = y) : n •ℕ x = y :=
  h

theorem unfold_gsmul {α : Type u_1} [add_comm_group α] (n : ℤ) (x : α) (y : α) (h : smulg n x = y) :
    n •ℤ x = y :=
  h

theorem subst_into_smul {α : Type u_1} [add_comm_monoid α] (l : ℕ) (r : α) (tl : ℕ) (tr : α) (t : α)
    (prl : l = tl) (prr : r = tr) (prt : smul tl tr = t) : smul l r = t :=
  sorry

theorem subst_into_smulg {α : Type u_1} [add_comm_group α] (l : ℤ) (r : α) (tl : ℤ) (tr : α) (t : α)
    (prl : l = tl) (prr : r = tr) (prt : smulg tl tr = t) : smulg l r = t :=
  sorry

inductive normalize_mode where
| raw : normalize_mode
| term : normalize_mode

protected instance normalize_mode.inhabited : Inhabited normalize_mode :=
  { default := normalize_mode.term }

end abel


namespace interactive


/-- Tactic for solving equations in the language of
*additive*, commutative monoids and groups.
This version of `abel` fails if the target is not an equality
that is provable by the axioms of commutative monoids/groups. -/
/--
Evaluate expressions in the language of *additive*, commutative monoids and groups.
It attempts to prove the goal outright if there is no `at`
specifier and the target is an equality, but if this
fails, it falls back to rewriting all monoid expressions into a normal form.
If there is an `at` specifier, it rewrites the given target into a normal form.
```lean
example {α : Type*} {a b : α} [add_comm_monoid α] : a + (b + a) = a + a + b := by abel
example {α : Type*} {a b : α} [add_comm_group α] : (a + b) - ((b + a) + a) = -a := by abel
example {α : Type*} {a b : α} [add_comm_group α] (hyp : a + a - a = b - b) : a = 0 :=
by { abel at hyp, exact hyp }
```
-/
end Mathlib