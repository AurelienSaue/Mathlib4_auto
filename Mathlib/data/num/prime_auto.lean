/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.num.lemmas
import Mathlib.data.nat.prime
import Mathlib.tactic.ring
import Mathlib.PostPort

namespace Mathlib

/-!
# Primality for binary natural numbers

This file defines versions of `nat.min_fac` and `nat.prime` for `num` and `pos_num`. As with other
`num` definitions, they are not intended for general use (`nat` should be used instead of `num` in
most cases) but they can be used in contexts where kernel computation is required, such as proofs
by `rfl` and `dec_trivial`, as well as in `#reduce`.

The default decidable instance for `nat.prime` is optimized for VM evaluation, so it should be
preferred within `#eval` or in tactic execution, while for proofs the `norm_num` tactic can be used
to construct primality and non-primality proofs more efficiently than kernel computation.

Nevertheless, sometimes proof by computational reflection requires natural number computations, and
`num` implements algorithms directly on binary natural numbers for this purpose.
-/

namespace pos_num


/-- Auxiliary function for computing the smallest prime factor of a `pos_num`. Unlike
`nat.min_fac_aux`, we use a natural number `fuel` variable that is set to an upper bound on the
number of iterations. It is initialized to the number `n` we are determining primality for. Even
though this is exponential in the input (since it is a `nat`, not a `num`), it will get lazily
evaluated during kernel reduction, so we will only require about `sqrt n` unfoldings, for the
`sqrt n` iterations of the loop. -/
def min_fac_aux (n : pos_num) : ℕ → pos_num → pos_num := sorry

theorem min_fac_aux_to_nat {fuel : ℕ} {n : pos_num} {k : pos_num}
    (h : nat.sqrt ↑n < fuel + ↑(bit1 k)) : ↑(min_fac_aux n fuel k) = nat.min_fac_aux ↑n ↑(bit1 k) :=
  sorry

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def min_fac : pos_num → pos_num := sorry

@[simp] theorem min_fac_to_nat (n : pos_num) : ↑(min_fac n) = nat.min_fac ↑n := sorry

/-- Primality predicate for a `pos_num`. -/
@[simp] def prime (n : pos_num) := nat.prime ↑n

protected instance decidable_prime : decidable_pred prime := sorry

end pos_num


namespace num


/-- Returns the smallest prime factor of `n ≠ 1`. -/
def min_fac : num → pos_num := sorry

@[simp] theorem min_fac_to_nat (n : num) : ↑(min_fac n) = nat.min_fac ↑n :=
  num.cases_on n (idRhs (↑(min_fac 0) = ↑(min_fac 0)) rfl)
    fun (n : pos_num) => idRhs (↑(pos_num.min_fac n) = nat.min_fac ↑n) (pos_num.min_fac_to_nat n)

/-- Primality predicate for a `num`. -/
@[simp] def prime (n : num) := nat.prime ↑n

protected instance decidable_prime : decidable_pred prime := sorry

end Mathlib