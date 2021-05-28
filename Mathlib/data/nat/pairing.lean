/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

Elegant pairing function.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.sqrt
import Mathlib.data.set.lattice
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

namespace nat


/-- Pairing function for the natural numbers. -/
def mkpair (a : ℕ) (b : ℕ) : ℕ :=
  ite (a < b) (b * b + a) (a * a + a + b)

/-- Unpairing function for the natural numbers. -/
def unpair (n : ℕ) : ℕ × ℕ :=
  let s : ℕ := sqrt n;
  ite (n - s * s < s) (n - s * s, s) (s, n - s * s - s)

@[simp] theorem mkpair_unpair (n : ℕ) : mkpair (prod.fst (unpair n)) (prod.snd (unpair n)) = n := sorry

theorem mkpair_unpair' {n : ℕ} {a : ℕ} {b : ℕ} (H : unpair n = (a, b)) : mkpair a b = n := sorry

@[simp] theorem unpair_mkpair (a : ℕ) (b : ℕ) : unpair (mkpair a b) = (a, b) := sorry

theorem unpair_lt {n : ℕ} (n1 : 1 ≤ n) : prod.fst (unpair n) < n := sorry

theorem unpair_le_left (n : ℕ) : prod.fst (unpair n) ≤ n :=
  nat.cases_on n (idRhs (prod.fst (unpair 0) ≤ 0) (of_as_true trivial))
    fun (n : ℕ) => idRhs (prod.fst (unpair (n + 1)) ≤ n + 1) (le_of_lt (unpair_lt (succ_pos n)))

theorem le_mkpair_left (a : ℕ) (b : ℕ) : a ≤ mkpair a b := sorry

theorem le_mkpair_right (a : ℕ) (b : ℕ) : b ≤ mkpair a b := sorry

theorem unpair_le_right (n : ℕ) : prod.snd (unpair n) ≤ n := sorry

theorem mkpair_lt_mkpair_left {a₁ : ℕ} {a₂ : ℕ} (b : ℕ) (h : a₁ < a₂) : mkpair a₁ b < mkpair a₂ b := sorry

theorem mkpair_lt_mkpair_right (a : ℕ) {b₁ : ℕ} {b₂ : ℕ} (h : b₁ < b₂) : mkpair a b₁ < mkpair a b₂ := sorry

end nat


namespace set


theorem Union_unpair_prod {α : Type u_1} {β : Type u_2} {s : ℕ → set α} {t : ℕ → set β} : (Union fun (n : ℕ) => set.prod (s (prod.fst (nat.unpair n))) (t (prod.snd (nat.unpair n)))) =
  set.prod (Union fun (n : ℕ) => s n) (Union fun (n : ℕ) => t n) := sorry

