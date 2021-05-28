/-
Copyright (c) 2020 Johan Commelin and Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.witt_vector.basic
import Mathlib.ring_theory.witt_vector.is_poly
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!

# `init` and `tail`

Given a Witt vector `x`, we are sometimes interested
in its components before and after an index `n`.
This file defines those operations, proves that `init` is polynomial,
and shows how that polynomial interacts with `mv_polynomial.bind₁`.

## Main declarations

* `witt_vector.init n x`: the first `n` coefficients of `x`, as a Witt vector. All coefficients at
  indices ≥ `n` are 0.
* `witt_vector.tail n x`: the complementary part to `init`. All coefficients at indices < `n` are 0,
  otherwise they are the same as in `x`.
* `witt_vector.coeff_add_of_disjoint`: if `x` and `y` are Witt vectors such that for every `n`
  the `n`-th coefficient of `x` or of `y` is `0`, then the coefficients of `x + y`
  are just `x.coeff n + y.coeff n`.
-/

namespace tactic


namespace interactive


/--
`init_ring` is an auxiliary tactic that discharges goals factoring `init` over ring operations.
-/
end interactive


end tactic


namespace witt_vector


/-- `witt_vector.select P x`, for a predicate `P : ℕ → Prop` is the Witt vector
whose `n`-th coefficient is `x.coeff n` if `P n` is true, and `0` otherwise.
-/
def select {p : ℕ} {R : Type u_1} [comm_ring R] (P : ℕ → Prop) (x : witt_vector p R) : witt_vector p R :=
  mk p fun (n : ℕ) => ite (P n) (coeff x n) 0

/-- The polynomial that witnesses that `witt_vector.select` is a polynomial function.
`select_poly n` is `X n` if `P n` holds, and `0` otherwise. -/
def select_poly (P : ℕ → Prop) (n : ℕ) : mv_polynomial ℕ ℤ :=
  ite (P n) (mv_polynomial.X n) 0

theorem coeff_select {p : ℕ} {R : Type u_1} [comm_ring R] (P : ℕ → Prop) (x : witt_vector p R) (n : ℕ) : coeff (select P x) n = coe_fn (mv_polynomial.aeval (coeff x)) (select_poly P n) := sorry

theorem select_is_poly {p : ℕ} (P : ℕ → Prop) : is_poly p fun (R : Type u_1) (_Rcr : comm_ring R) (x : witt_vector p R) => select P x :=
  Exists.intro (select_poly P)
    (id fun (R : Type u_1) (_Rcr : comm_ring R) (x : witt_vector p R) => funext fun (i : ℕ) => coeff_select P x i)

theorem select_add_select_not {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] (P : ℕ → Prop) (x : witt_vector p R) : select P x + select (fun (i : ℕ) => ¬P i) x = x := sorry

theorem coeff_add_of_disjoint {p : ℕ} [hp : fact (nat.prime p)] (n : ℕ) {R : Type u_1} [comm_ring R] (x : witt_vector p R) (y : witt_vector p R) (h : ∀ (n : ℕ), coeff x n = 0 ∨ coeff y n = 0) : coeff (x + y) n = coeff x n + coeff y n := sorry

/-- `witt_vector.init n x` is the Witt vector of which the first `n` coefficients are those from `x`
and all other coefficients are `0`.
See `witt_vector.tail` for the complementary part.
-/
def init {p : ℕ} {R : Type u_1} [comm_ring R] (n : ℕ) : witt_vector p R → witt_vector p R :=
  select fun (i : ℕ) => i < n

/-- `witt_vector.tail n x` is the Witt vector of which the first `n` coefficients are `0`
and all other coefficients are those from `x`.
See `witt_vector.init` for the complementary part. -/
def tail {p : ℕ} {R : Type u_1} [comm_ring R] (n : ℕ) : witt_vector p R → witt_vector p R :=
  select fun (i : ℕ) => n ≤ i

@[simp] theorem init_add_tail {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] (x : witt_vector p R) (n : ℕ) : init n x + tail n x = x := sorry

@[simp] theorem init_init {p : ℕ} {R : Type u_1} [comm_ring R] (x : witt_vector p R) (n : ℕ) : init n (init n x) = init n x := sorry

theorem init_add {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] (x : witt_vector p R) (y : witt_vector p R) (n : ℕ) : init n (x + y) = init n (init n x + init n y) := sorry

theorem init_mul {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] (x : witt_vector p R) (y : witt_vector p R) (n : ℕ) : init n (x * y) = init n (init n x * init n y) := sorry

theorem init_neg {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] (x : witt_vector p R) (n : ℕ) : init n (-x) = init n (-init n x) := sorry

theorem init_sub {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] (x : witt_vector p R) (y : witt_vector p R) (n : ℕ) : init n (x - y) = init n (init n x - init n y) := sorry

/-- `witt_vector.init n x` is polynomial in the coefficients of `x`. -/
theorem init_is_poly (p : ℕ) (n : ℕ) : is_poly p fun (R : Type u_1) (_Rcr : comm_ring R) => init n :=
  select_is_poly fun (i : ℕ) => i < n

