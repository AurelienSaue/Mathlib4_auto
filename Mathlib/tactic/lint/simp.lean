/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.lint.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# Linter for simplification lemmas

This files defines several linters that prevent common mistakes when declaring simp lemmas:

 * `simp_nf` checks that the left-hand side of a simp lemma is not simplified by a different lemma.
 * `simp_var_head` checks that the head symbol of the left-hand side is not a variable.
 * `simp_comm` checks that commutativity lemmas are not marked as simplification lemmas.
-/

/-- `simp_lhs_rhs ty` returns the left-hand and right-hand side of a simp lemma with type `ty`. -/
-- We only detect a fixed set of simp relations here.

-- This is somewhat justified since for a custom simp relation R,

-- the simp lemma `R a b` is implicitly converted to `R a b ↔ true` as well.

/-- `simp_lhs ty` returns the left-hand side of a simp lemma with type `ty`. -/
/--
`simp_is_conditional_core ty` returns `none` if `ty` is a conditional simp
lemma, and `some lhs` otherwise.
-/
/--
`simp_is_conditional ty` returns true iff the simp lemma with type `ty` is conditional.
-/
/-- Checks whether two expressions are equal for the simplifier. That is,
they are reducibly-definitional equal, and they have the same head symbol. -/
/-- Reports declarations that are simp lemmas whose left-hand side is not in simp-normal form. -/
-- Sometimes, a definition is tagged @[simp] to add the equational lemmas to the simp set.

-- In this case, ignore the declaration if it is not a valid simp lemma by itself.

/--
This note gives you some tips to debug any errors that the simp-normal form linter raises
