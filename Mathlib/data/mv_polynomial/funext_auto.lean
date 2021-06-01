/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.ring_division
import Mathlib.data.mv_polynomial.rename
import Mathlib.ring_theory.polynomial.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
## Function extensionality for multivariate polynomials

In this file we show that two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables.

# Main declaration

* `mv_polynomial.funext`: two polynomials `φ ψ : mv_polynomial σ R`
  over an infinite integral domain `R` are equal if `eval x φ = eval x ψ` for all `x : σ → R`.

-/

namespace mv_polynomial


/-- Two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables. -/
theorem funext {R : Type u_1} [integral_domain R] [infinite R] {σ : Type u_2}
    {p : mv_polynomial σ R} {q : mv_polynomial σ R}
    (h : ∀ (x : σ → R), coe_fn (eval x) p = coe_fn (eval x) q) : p = q :=
  sorry

theorem funext_iff {R : Type u_1} [integral_domain R] [infinite R] {σ : Type u_2}
    {p : mv_polynomial σ R} {q : mv_polynomial σ R} :
    p = q ↔ ∀ (x : σ → R), coe_fn (eval x) p = coe_fn (eval x) q :=
  sorry

end Mathlib