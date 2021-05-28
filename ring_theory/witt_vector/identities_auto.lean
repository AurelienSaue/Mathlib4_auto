/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.ring_theory.witt_vector.frobenius
import Mathlib.ring_theory.witt_vector.verschiebung
import Mathlib.ring_theory.witt_vector.mul_p
import PostPort

universes u_1 

namespace Mathlib

/-!
## Identities between operations on the ring of Witt vectors

In this file we derive common identities between the Frobenius and Verschiebung operators.

## Main declarations

* `frobenius_verschiebung`: the composition of Frobenius and Verschiebung is multiplication by `p`
* `verschiebung_mul_frobenius`: the “projection formula”: `V(x * F y) = V x * y`
-/

namespace witt_vector


/-- The composition of Frobenius and Verschiebung is multiplication by `p`. -/
theorem frobenius_verschiebung {p : ℕ} {R : Type u_1} [fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) : coe_fn frobenius (coe_fn verschiebung x) = x * ↑p := sorry

/-- Verschiebung is the same as multiplication by `p` on the ring of Witt vectors of `zmod p`. -/
theorem verschiebung_zmod {p : ℕ} [fact (nat.prime p)] (x : witt_vector p (zmod p)) : coe_fn verschiebung x = x * ↑p := sorry

theorem coeff_p_pow {p : ℕ} {R : Type u_1} [fact (nat.prime p)] [comm_ring R] [char_p R p] (i : ℕ) : coeff (↑p ^ i) i = 1 := sorry

/-- The “projection formula” for Frobenius and Verschiebung. -/
theorem verschiebung_mul_frobenius {p : ℕ} {R : Type u_1} [fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) (y : witt_vector p R) : coe_fn verschiebung (x * coe_fn frobenius y) = coe_fn verschiebung x * y := sorry

