/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Fox Thomson.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.data.finset.basic
import Mathlib.tactic.rcases
import Mathlib.tactic.omega.default
import Mathlib.computability.language
import PostPort

universes u l 

namespace Mathlib

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regex's used in
computer science such as the POSIX standard.

TODO
* Show that this regular expressions and DFA/NFA's are equivalent.
* `attribute [pattern] has_mul.mul` has been added into this file, it could be moved.
-/

/--
This is the definition of regular expressions. The names used here is to mirror the definition
of a Kleene algebra (https://en.wikipedia.org/wiki/Kleene_algebra).
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings which match `P`
* `P + Q` (`plus P Q`) matches anything which match `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-/
inductive regular_expression (α : Type u) 
where
| zero : regular_expression α
| epsilon : regular_expression α
| char : α → regular_expression α
| plus : regular_expression α → regular_expression α → regular_expression α
| comp : regular_expression α → regular_expression α → regular_expression α
| star : regular_expression α → regular_expression α

namespace regular_expression


protected instance inhabited {α : Type u} : Inhabited (regular_expression α) :=
  { default := zero }

protected instance has_add {α : Type u} : Add (regular_expression α) :=
  { add := plus }

protected instance has_mul {α : Type u} : Mul (regular_expression α) :=
  { mul := comp }

protected instance has_one {α : Type u} : HasOne (regular_expression α) :=
  { one := epsilon }

protected instance has_zero {α : Type u} : HasZero (regular_expression α) :=
  { zero := zero }

@[simp] theorem zero_def {α : Type u} : zero = 0 :=
  rfl

@[simp] theorem one_def {α : Type u} : epsilon = 1 :=
  rfl

@[simp] theorem plus_def {α : Type u} (P : regular_expression α) (Q : regular_expression α) : plus P Q = P + Q :=
  rfl

@[simp] theorem comp_def {α : Type u} (P : regular_expression α) (Q : regular_expression α) : comp P Q = P * Q :=
  rfl

/-- `matches P` provides a language which contains all strings that `P` matches -/
def matches {α : Type u} : regular_expression α → language α :=
  sorry

@[simp] theorem matches_zero_def {α : Type u} : matches 0 = 0 :=
  rfl

@[simp] theorem matches_epsilon_def {α : Type u} : matches 1 = 1 :=
  rfl

@[simp] theorem matches_add_def {α : Type u} (P : regular_expression α) (Q : regular_expression α) : matches (P + Q) = matches P + matches Q :=
  rfl

@[simp] theorem matches_mul_def {α : Type u} (P : regular_expression α) (Q : regular_expression α) : matches (P * Q) = matches P * matches Q :=
  rfl

@[simp] theorem matches_star_def {α : Type u} (P : regular_expression α) : matches (star P) = language.star (matches P) :=
  rfl

/-- `match_epsilon P` is true if and only if `P` matches the empty string -/
def match_epsilon {α : Type u} : regular_expression α → Bool :=
  sorry

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv {α : Type u} [dec : DecidableEq α] : regular_expression α → α → regular_expression α :=
  sorry

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches`. -/
def rmatch {α : Type u} [dec : DecidableEq α] : regular_expression α → List α → Bool :=
  sorry

@[simp] theorem zero_rmatch {α : Type u} [dec : DecidableEq α] (x : List α) : rmatch 0 x = false := sorry

theorem one_rmatch_iff {α : Type u} [dec : DecidableEq α] (x : List α) : ↥(rmatch 1 x) ↔ x = [] := sorry

theorem char_rmatch_iff {α : Type u} [dec : DecidableEq α] (a : α) (x : List α) : ↥(rmatch (char a) x) ↔ x = [a] := sorry

theorem add_rmatch_iff {α : Type u} [dec : DecidableEq α] (P : regular_expression α) (Q : regular_expression α) (x : List α) : ↥(rmatch (P + Q) x) ↔ ↥(rmatch P x) ∨ ↥(rmatch Q x) := sorry

theorem mul_rmatch_iff {α : Type u} [dec : DecidableEq α] (P : regular_expression α) (Q : regular_expression α) (x : List α) : ↥(rmatch (P * Q) x) ↔ ∃ (t : List α), ∃ (u : List α), x = t ++ u ∧ ↥(rmatch P t) ∧ ↥(rmatch Q u) := sorry

theorem star_rmatch_iff {α : Type u} [dec : DecidableEq α] (P : regular_expression α) (x : List α) : ↥(rmatch (star P) x) ↔ ∃ (S : List (List α)), x = list.join S ∧ ∀ (t : List α), t ∈ S → t ≠ [] ∧ ↥(rmatch P t) := sorry

@[simp] theorem rmatch_iff_matches {α : Type u} [dec : DecidableEq α] (P : regular_expression α) (x : List α) : ↥(rmatch P x) ↔ x ∈ matches P := sorry

protected instance matches.decidable_pred {α : Type u} [dec : DecidableEq α] (P : regular_expression α) : decidable_pred (matches P) :=
  id fun (x : List α) => id (eq.mpr sorry (eq.decidable (rmatch P x) tt))

