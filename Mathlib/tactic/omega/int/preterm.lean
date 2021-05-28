/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.omega.term
import Mathlib.PostPort

universes l 

namespace Mathlib

/-
Linear integer arithmetic terms in pre-normalized form.
-/

namespace omega


namespace int


/-- The shadow syntax for arithmetic terms. All constants are reified to `cst`
(e.g., `-5` is reified to `cst -5`) and all other atomic terms are reified to
`exp` (e.g., `-5 * (gcd 14 -7)` is reified to `exp -5 \`(gcd 14 -7)`).
`exp` accepts a coefficient of type `int` as its first argument because
multiplication by constant is allowed by the omega test. -/
/-- Similar to `exprterm`, except that all exprs are now replaced with
de Brujin indices of type `nat`. This is akin to generalizing over
the terms represented by the said exprs. -/
inductive preterm 
where
| cst : ℤ → preterm
| var : ℤ → ℕ → preterm
| add : preterm → preterm → preterm

namespace preterm


/-- Preterm evaluation -/
@[simp] def val (v : ℕ → ℤ) : preterm → ℤ :=
  sorry

/-- Fresh de Brujin index not used by any variable in argument -/
def fresh_index : preterm → ℕ :=
  sorry

@[simp] def add_one (t : preterm) : preterm :=
  add t (cst 1)

def repr : preterm → string :=
  sorry

end preterm


/-- Return a term (which is in canonical form by definition)
    that is equivalent to the input preterm -/
@[simp] def canonize : preterm → term :=
  sorry

@[simp] theorem val_canonize {v : ℕ → ℤ} {t : preterm} : term.val v (canonize t) = preterm.val v t := sorry

