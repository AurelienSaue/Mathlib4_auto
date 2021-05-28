/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.omega.term
import PostPort

universes l 

namespace Mathlib

/-
Linear natural number arithmetic terms in pre-normalized form.
-/

namespace omega


namespace nat


/-- The shadow syntax for arithmetic terms. All constants are reified to `cst`
(e.g., `5` is reified to `cst 5`) and all other atomic terms are reified to
`exp` (e.g., `5 * (list.length l)` is reified to `exp 5 \`(list.length l)`).
`exp` accepts a coefficient of type `nat` as its first argument because
multiplication by constant is allowed by the omega test. -/
/-- Similar to `exprterm`, except that all exprs are now replaced with
de Brujin indices of type `nat`. This is akin to generalizing over
the terms represented by the said exprs. -/
inductive preterm 
where
| cst : ℕ → preterm
| var : ℕ → ℕ → preterm
| add : preterm → preterm → preterm
| sub : preterm → preterm → preterm

namespace preterm


/-- Helper tactic for proof by induction over preterms -/
/-- Preterm evaluation -/
def val (v : ℕ → ℕ) : preterm → ℕ :=
  sorry

@[simp] theorem val_const {v : ℕ → ℕ} {m : ℕ} : val v (cst m) = m :=
  rfl

@[simp] theorem val_var {v : ℕ → ℕ} {m : ℕ} {n : ℕ} : val v (var m n) = m * v n := sorry

@[simp] theorem val_add {v : ℕ → ℕ} {t : preterm} {s : preterm} : val v (add t s) = val v t + val v s :=
  rfl

@[simp] theorem val_sub {v : ℕ → ℕ} {t : preterm} {s : preterm} : val v (sub t s) = val v t - val v s :=
  rfl

/-- Fresh de Brujin index not used by any variable in argument -/
def fresh_index : preterm → ℕ :=
  sorry

/-- If variable assignments `v` and `w` agree on all variables that occur
in term `t`, the value of `t` under `v` and `w` are identical. -/
theorem val_constant (v : ℕ → ℕ) (w : ℕ → ℕ) (t : preterm) : (∀ (x : ℕ), x < fresh_index t → v x = w x) → val v t = val w t := sorry

def repr : preterm → string :=
  sorry

@[simp] def add_one (t : preterm) : preterm :=
  add t (cst 1)

/-- Preterm is free of subtractions -/
def sub_free : preterm → Prop :=
  sorry

end preterm


/-- Return a term (which is in canonical form by definition)
    that is equivalent to the input preterm -/
@[simp] def canonize : preterm → term :=
  sorry

@[simp] theorem val_canonize {v : ℕ → ℕ} {t : preterm} : preterm.sub_free t → term.val (fun (x : ℕ) => ↑(v x)) (canonize t) = ↑(preterm.val v t) := sorry

