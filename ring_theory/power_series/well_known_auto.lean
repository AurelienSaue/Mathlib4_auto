/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.ring_theory.power_series.basic
import Mathlib.data.nat.parity
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Definition of well-known power series

In this file we define the following power series:

* `power_series.inv_units_sub`: given `u : units R`, this is the series for `1 / (u - x)`.
  It is given by `∑ n, x ^ n /ₚ u ^ (n + 1)`.

* `power_series.sin`, `power_series.cos`, `power_series.exp` : power series for sin, cosine, and
  exponential functions.
-/

namespace power_series


/-- The power series for `1 / (u - x)`. -/
def inv_units_sub {R : Type u_1} [ring R] (u : units R) : power_series R :=
  mk fun (n : ℕ) => 1 /ₚ u ^ (n + 1)

@[simp] theorem coeff_inv_units_sub {R : Type u_1} [ring R] (u : units R) (n : ℕ) : coe_fn (coeff R n) (inv_units_sub u) = 1 /ₚ u ^ (n + 1) :=
  coeff_mk n fun (n : ℕ) => 1 /ₚ u ^ (n + 1)

@[simp] theorem constant_coeff_inv_units_sub {R : Type u_1} [ring R] (u : units R) : coe_fn (constant_coeff R) (inv_units_sub u) = 1 /ₚ u := sorry

@[simp] theorem inv_units_sub_mul_X {R : Type u_1} [ring R] (u : units R) : inv_units_sub u * X = inv_units_sub u * coe_fn (C R) ↑u - 1 := sorry

@[simp] theorem inv_units_sub_mul_sub {R : Type u_1} [ring R] (u : units R) : inv_units_sub u * (coe_fn (C R) ↑u - X) = 1 := sorry

theorem map_inv_units_sub {R : Type u_1} {S : Type u_2} [ring R] [ring S] (f : R →+* S) (u : units R) : coe_fn (map f) (inv_units_sub u) = inv_units_sub (coe_fn (units.map ↑f) u) := sorry

/-- Power series for the exponential function at zero. -/
def exp (A : Type u_1) [ring A] [algebra ℚ A] : power_series A :=
  mk fun (n : ℕ) => coe_fn (algebra_map ℚ A) (1 / ↑(nat.factorial n))

/-- Power series for the sine function at zero. -/
def sin (A : Type u_1) [ring A] [algebra ℚ A] : power_series A :=
  mk fun (n : ℕ) => ite (even n) 0 (coe_fn (algebra_map ℚ A) ((-1) ^ (n / bit0 1) / ↑(nat.factorial n)))

/-- Power series for the cosine function at zero. -/
def cos (A : Type u_1) [ring A] [algebra ℚ A] : power_series A :=
  mk fun (n : ℕ) => ite (even n) (coe_fn (algebra_map ℚ A) ((-1) ^ (n / bit0 1) / ↑(nat.factorial n))) 0

@[simp] theorem coeff_exp {A : Type u_1} [ring A] [algebra ℚ A] (n : ℕ) : coe_fn (coeff A n) (exp A) = coe_fn (algebra_map ℚ A) (1 / ↑(nat.factorial n)) :=
  coeff_mk n fun (n : ℕ) => coe_fn (algebra_map ℚ A) (1 / ↑(nat.factorial n))

@[simp] theorem map_exp {A : Type u_1} {A' : Type u_2} [ring A] [ring A'] [algebra ℚ A] [algebra ℚ A'] (f : A →+* A') : coe_fn (map f) (exp A) = exp A' := sorry

@[simp] theorem map_sin {A : Type u_1} {A' : Type u_2} [ring A] [ring A'] [algebra ℚ A] [algebra ℚ A'] (f : A →+* A') : coe_fn (map f) (sin A) = sin A' := sorry

@[simp] theorem map_cos {A : Type u_1} {A' : Type u_2} [ring A] [ring A'] [algebra ℚ A] [algebra ℚ A'] (f : A →+* A') : coe_fn (map f) (cos A) = cos A' := sorry

