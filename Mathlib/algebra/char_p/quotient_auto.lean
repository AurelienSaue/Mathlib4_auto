/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.char_p.basic
import Mathlib.algebra.ring_quot
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Characteristic of quotients rings
-/

namespace char_p


theorem quotient (R : Type u) [comm_ring R] (p : ℕ) [hp1 : fact (nat.prime p)]
    (hp2 : ↑p ∈ nonunits R) : char_p (ideal.quotient (ideal.span (singleton ↑p))) p :=
  sorry

/-- If an ideal does not contain any coercions of natural numbers other than zero, then its quotient
inherits the characteristic of the underlying ring. -/
theorem quotient' {R : Type u_1} [comm_ring R] (p : ℕ) [char_p R p] (I : ideal R)
    (h : ∀ (x : ℕ), ↑x ∈ I → ↑x = 0) : char_p (ideal.quotient I) p :=
  sorry

end Mathlib