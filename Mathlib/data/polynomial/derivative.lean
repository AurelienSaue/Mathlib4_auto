/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.eval
import Mathlib.PostPort

universes u u_1 y v 

namespace Mathlib

/-!
# The derivative map on polynomials

## Main definitions
 * `polynomial.derivative`: The formal derivative of polynomials, expressed as a linear map.

-/

namespace polynomial


/-- `derivative p` is the formal derivative of the polynomial `p` -/
def derivative {R : Type u} [semiring R] : linear_map R (polynomial R) (polynomial R) :=
  finsupp.total ℕ (polynomial R) R fun (n : ℕ) => coe_fn C ↑n * X ^ (n - 1)

theorem derivative_apply {R : Type u} [semiring R] (p : polynomial R) : coe_fn derivative p = finsupp.sum p fun (n : ℕ) (a : R) => coe_fn C (a * ↑n) * X ^ (n - 1) := sorry

theorem coeff_derivative {R : Type u} [semiring R] (p : polynomial R) (n : ℕ) : coeff (coe_fn derivative p) n = coeff p (n + 1) * (↑n + 1) := sorry

theorem derivative_zero {R : Type u} [semiring R] : coe_fn derivative 0 = 0 :=
  linear_map.map_zero derivative

theorem derivative_monomial {R : Type u} [semiring R] (a : R) (n : ℕ) : coe_fn derivative (coe_fn (monomial n) a) = coe_fn (monomial (n - 1)) (a * ↑n) := sorry

theorem derivative_C_mul_X_pow {R : Type u} [semiring R] (a : R) (n : ℕ) : coe_fn derivative (coe_fn C a * X ^ n) = coe_fn C (a * ↑n) * X ^ (n - 1) := sorry

@[simp] theorem derivative_X_pow {R : Type u} [semiring R] (n : ℕ) : coe_fn derivative (X ^ n) = ↑n * X ^ (n - 1) := sorry

@[simp] theorem derivative_C {R : Type u} [semiring R] {a : R} : coe_fn derivative (coe_fn C a) = 0 := sorry

@[simp] theorem derivative_X {R : Type u} [semiring R] : coe_fn derivative X = 1 := sorry

@[simp] theorem derivative_one {R : Type u} [semiring R] : coe_fn derivative 1 = 0 :=
  derivative_C

@[simp] theorem derivative_bit0 {R : Type u} [semiring R] {a : polynomial R} : coe_fn derivative (bit0 a) = bit0 (coe_fn derivative a) := sorry

@[simp] theorem derivative_bit1 {R : Type u} [semiring R] {a : polynomial R} : coe_fn derivative (bit1 a) = bit0 (coe_fn derivative a) := sorry

@[simp] theorem derivative_add {R : Type u} [semiring R] {f : polynomial R} {g : polynomial R} : coe_fn derivative (f + g) = coe_fn derivative f + coe_fn derivative g :=
  linear_map.map_add derivative f g

@[simp] theorem derivative_neg {R : Type u_1} [ring R] (f : polynomial R) : coe_fn derivative (-f) = -coe_fn derivative f :=
  linear_map.map_neg derivative f

@[simp] theorem derivative_sub {R : Type u_1} [ring R] (f : polynomial R) (g : polynomial R) : coe_fn derivative (f - g) = coe_fn derivative f - coe_fn derivative g :=
  linear_map.map_sub derivative f g

@[simp] theorem derivative_sum {R : Type u} {ι : Type y} [semiring R] {s : finset ι} {f : ι → polynomial R} : coe_fn derivative (finset.sum s fun (b : ι) => f b) = finset.sum s fun (b : ι) => coe_fn derivative (f b) :=
  linear_map.map_sum derivative

@[simp] theorem derivative_smul {R : Type u} [semiring R] (r : R) (p : polynomial R) : coe_fn derivative (r • p) = r • coe_fn derivative p :=
  linear_map.map_smul derivative r p

theorem derivative_eval {R : Type u} [comm_semiring R] (p : polynomial R) (x : R) : eval x (coe_fn derivative p) = finsupp.sum p fun (n : ℕ) (a : R) => a * ↑n * x ^ (n - 1) := sorry

@[simp] theorem derivative_mul {R : Type u} [comm_semiring R] {f : polynomial R} {g : polynomial R} : coe_fn derivative (f * g) = coe_fn derivative f * g + f * coe_fn derivative g := sorry

theorem derivative_pow_succ {R : Type u} [comm_semiring R] (p : polynomial R) (n : ℕ) : coe_fn derivative (p ^ (n + 1)) = (↑n + 1) * p ^ n * coe_fn derivative p := sorry

theorem derivative_pow {R : Type u} [comm_semiring R] (p : polynomial R) (n : ℕ) : coe_fn derivative (p ^ n) = ↑n * p ^ (n - 1) * coe_fn derivative p := sorry

theorem derivative_map {R : Type u} {S : Type v} [comm_semiring R] [comm_semiring S] (p : polynomial R) (f : R →+* S) : coe_fn derivative (map f p) = map f (coe_fn derivative p) := sorry

/-- Chain rule for formal derivative of polynomials. -/
theorem derivative_eval₂_C {R : Type u} [comm_semiring R] (p : polynomial R) (q : polynomial R) : coe_fn derivative (eval₂ C q p) = eval₂ C q (coe_fn derivative p) * coe_fn derivative q := sorry

theorem of_mem_support_derivative {R : Type u} [comm_semiring R] {p : polynomial R} {n : ℕ} (h : n ∈ finsupp.support (coe_fn derivative p)) : n + 1 ∈ finsupp.support p := sorry

theorem degree_derivative_lt {R : Type u} [comm_semiring R] {p : polynomial R} (hp : p ≠ 0) : degree (coe_fn derivative p) < degree p :=
  iff.mpr (finset.sup_lt_iff (iff.mpr bot_lt_iff_ne_bot (mt (iff.mp degree_eq_bot) hp)))
    fun (n : ℕ) (hp : n ∈ finsupp.support (coe_fn derivative p)) =>
      lt_of_lt_of_le (iff.mpr with_bot.some_lt_some (nat.lt_succ_self n)) (finset.le_sup (of_mem_support_derivative hp))

theorem nat_degree_derivative_lt {R : Type u} [comm_semiring R] {p : polynomial R} (hp : coe_fn derivative p ≠ 0) : nat_degree (coe_fn derivative p) < nat_degree p := sorry

theorem degree_derivative_le {R : Type u} [comm_semiring R] {p : polynomial R} : degree (coe_fn derivative p) ≤ degree p := sorry

theorem mem_support_derivative {R : Type u} [integral_domain R] [char_zero R] (p : polynomial R) (n : ℕ) : n ∈ finsupp.support (coe_fn derivative p) ↔ n + 1 ∈ finsupp.support p := sorry

@[simp] theorem degree_derivative_eq {R : Type u} [integral_domain R] [char_zero R] (p : polynomial R) (hp : 0 < nat_degree p) : degree (coe_fn derivative p) = ↑(nat_degree p - 1) := sorry

theorem nat_degree_eq_zero_of_derivative_eq_zero {R : Type u} [integral_domain R] [char_zero R] {f : polynomial R} (h : coe_fn derivative f = 0) : nat_degree f = 0 := sorry

