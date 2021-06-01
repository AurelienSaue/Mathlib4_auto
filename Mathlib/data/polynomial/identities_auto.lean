/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.derivative
import Mathlib.PostPort

universes u_1 u 

namespace Mathlib

/-!
# Theory of univariate polynomials

The main def is `binom_expansion`.
-/

namespace polynomial


/- @TODO: pow_add_expansion and pow_sub_pow_factor are not specific to polynomials.
  These belong somewhere else. But not in group_power because they depend on tactic.ring_exp

Maybe use data.nat.choose to prove it.
 -/

def pow_add_expansion {R : Type u_1} [comm_semiring R] (x : R) (y : R) (n : ℕ) :
    Subtype fun (k : R) => (x + y) ^ n = x ^ n + ↑n * x ^ (n - 1) * y + k * y ^ bit0 1 :=
  sorry

def binom_expansion {R : Type u} [comm_ring R] (f : polynomial R) (x : R) (y : R) :
    Subtype
        fun (k : R) =>
          eval (x + y) f = eval x f + eval x (coe_fn derivative f) * y + k * y ^ bit0 1 :=
  { val := finsupp.sum f fun (e : ℕ) (a : R) => a * subtype.val (poly_binom_aux1 x y e a),
    property := sorry }

def pow_sub_pow_factor {R : Type u} [comm_ring R] (x : R) (y : R) (i : ℕ) :
    Subtype fun (z : R) => x ^ i - y ^ i = z * (x - y) :=
  sorry

def eval_sub_factor {R : Type u} [comm_ring R] (f : polynomial R) (x : R) (y : R) :
    Subtype fun (z : R) => eval x f - eval y f = z * (x - y) :=
  { val := finsupp.sum f fun (i : ℕ) (r : R) => r * subtype.val (pow_sub_pow_factor x y i),
    property := sorry }

end Mathlib