/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.omega.coeffs
import PostPort

namespace Mathlib

/-
Normalized linear integer arithmetic terms.
-/

namespace omega


/-- Shadow syntax of normalized terms. The first element
    represents the constant term and the list represents
    the coefficients. -/
def term  :=
  ℤ × List ℤ

namespace term


/-- Evaluate a term using the valuation v. -/
@[simp] def val (v : ℕ → ℤ) : term → ℤ :=
  sorry

@[simp] def neg : term → term :=
  sorry

@[simp] def add : term → term → term :=
  sorry

@[simp] def sub : term → term → term :=
  sorry

@[simp] def mul (i : ℤ) : term → term :=
  sorry

@[simp] def div (i : ℤ) : term → term :=
  sorry

theorem val_neg {v : ℕ → ℤ} {t : term} : val v (neg t) = -val v t := sorry

@[simp] theorem val_sub {v : ℕ → ℤ} {t1 : term} {t2 : term} : val v (sub t1 t2) = val v t1 - val v t2 := sorry

@[simp] theorem val_add {v : ℕ → ℤ} {t1 : term} {t2 : term} : val v (add t1 t2) = val v t1 + val v t2 := sorry

@[simp] theorem val_mul {v : ℕ → ℤ} {i : ℤ} {t : term} : val v (mul i t) = i * val v t := sorry

theorem val_div {v : ℕ → ℤ} {i : ℤ} {b : ℤ} {as : List ℤ} : i ∣ b → (∀ (x : ℤ), x ∈ as → i ∣ x) → val v (div i (b, as)) = val v (b, as) / i := sorry

/-- Fresh de Brujin index not used by any variable ocurring in the term -/
def fresh_index (t : term) : ℕ :=
  list.length (prod.snd t)

def to_string (t : term) : string :=
  list.foldr (fun (_x : ℕ × ℤ) => sorry) (to_string (prod.fst t)) (list.enum (prod.snd t))

protected instance has_to_string : has_to_string term :=
  has_to_string.mk to_string

end term


/-- Fresh de Brujin index not used by any variable ocurring in the list of terms -/
def terms.fresh_index : List term → ℕ :=
  sorry

