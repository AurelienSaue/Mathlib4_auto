/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.witt_vector.basic
import Mathlib.ring_theory.witt_vector.is_poly
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-! ## The Verschiebung operator -/

namespace witt_vector


-- unfortunately, without this attribute, some of the code breaks for reasons I don't understand

/--
`verschiebung_fun x` shifts the coefficients of `x` up by one,
by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verchiebung_fun x).coeff (i + 1)`.

`verschiebung_fun` is the underlying function of the additive monoid hom `witt_vector.verschiebung`.
-/
def verschiebung_fun {p : ℕ} {R : Type u_1} [comm_ring R] (x : witt_vector p R) : witt_vector p R :=
  mk p fun (n : ℕ) => ite (n = 0) 0 (coeff x (n - 1))

theorem verschiebung_fun_coeff {p : ℕ} {R : Type u_1} [comm_ring R] (x : witt_vector p R) (n : ℕ) : coeff (verschiebung_fun x) n = ite (n = 0) 0 (coeff x (n - 1)) := sorry

theorem verschiebung_fun_coeff_zero {p : ℕ} {R : Type u_1} [comm_ring R] (x : witt_vector p R) : coeff (verschiebung_fun x) 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coeff (verschiebung_fun x) 0 = 0)) (verschiebung_fun_coeff x 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ite (0 = 0) 0 (coeff x (0 - 1)) = 0)) (if_pos rfl))) (Eq.refl 0))

@[simp] theorem verschiebung_fun_coeff_succ {p : ℕ} {R : Type u_1} [comm_ring R] (x : witt_vector p R) (n : ℕ) : coeff (verschiebung_fun x) (Nat.succ n) = coeff x n :=
  rfl

theorem ghost_component_zero_verschiebung_fun {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) : coe_fn (ghost_component 0) (verschiebung_fun x) = 0 := sorry

theorem ghost_component_verschiebung_fun {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) (n : ℕ) : coe_fn (ghost_component (n + 1)) (verschiebung_fun x) = ↑p * coe_fn (ghost_component n) x := sorry

/--
The 0th Verschiebung polynomial is 0. For `n > 0`, the `n`th Verschiebung polynomial is the
variable `X (n-1)`.
-/
def verschiebung_poly (n : ℕ) : mv_polynomial ℕ ℤ :=
  ite (n = 0) 0 (mv_polynomial.X (n - 1))

@[simp] theorem verschiebung_poly_zero : verschiebung_poly 0 = 0 :=
  rfl

theorem aeval_verschiebung_poly' {p : ℕ} {R : Type u_1} [comm_ring R] (x : witt_vector p R) (n : ℕ) : coe_fn (mv_polynomial.aeval (coeff x)) (verschiebung_poly n) = coeff (verschiebung_fun x) n := sorry

/--
`witt_vector.verschiebung` has polynomial structure given by `witt_vector.verschiebung_poly`.
-/
theorem verschiebung_fun_is_poly (p : ℕ) : is_poly p fun (R : Type u_1) (_Rcr : comm_ring R) => verschiebung_fun := sorry

/--
`verschiebung x` shifts the coefficients of `x` up by one, by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verchiebung x).coeff (i + 1)`.

This is a additive monoid hom with underlying function `verschiebung_fun`.
-/
def verschiebung {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] : witt_vector p R →+ witt_vector p R :=
  add_monoid_hom.mk verschiebung_fun sorry sorry

/-- `witt_vector.verschiebung` is a polynomial function. -/
theorem verschiebung_is_poly {p : ℕ} [hp : fact (nat.prime p)] : is_poly p fun (R : Type u_1) (_Rcr : comm_ring R) => ⇑verschiebung :=
  verschiebung_fun_is_poly p

/-- verschiebung is a natural transformation -/
@[simp] theorem map_verschiebung {p : ℕ} {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)] [comm_ring R] [comm_ring S] (f : R →+* S) (x : witt_vector p R) : coe_fn (map f) (coe_fn verschiebung x) = coe_fn verschiebung (coe_fn (map f) x) := sorry

theorem ghost_component_zero_verschiebung {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) : coe_fn (ghost_component 0) (coe_fn verschiebung x) = 0 :=
  ghost_component_zero_verschiebung_fun x

theorem ghost_component_verschiebung {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) (n : ℕ) : coe_fn (ghost_component (n + 1)) (coe_fn verschiebung x) = ↑p * coe_fn (ghost_component n) x :=
  ghost_component_verschiebung_fun x n

@[simp] theorem verschiebung_coeff_zero {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) : coeff (coe_fn verschiebung x) 0 = 0 :=
  rfl

-- simp_nf complains if this is simp

theorem verschiebung_coeff_add_one {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) (n : ℕ) : coeff (coe_fn verschiebung x) (n + 1) = coeff x n :=
  rfl

@[simp] theorem verschiebung_coeff_succ {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) (n : ℕ) : coeff (coe_fn verschiebung x) (Nat.succ n) = coeff x n :=
  rfl

theorem aeval_verschiebung_poly {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) (n : ℕ) : coe_fn (mv_polynomial.aeval (coeff x)) (verschiebung_poly n) = coeff (coe_fn verschiebung x) n :=
  aeval_verschiebung_poly' x n

@[simp] theorem bind₁_verschiebung_poly_witt_polynomial {p : ℕ} [hp : fact (nat.prime p)] (n : ℕ) : coe_fn (mv_polynomial.bind₁ verschiebung_poly) (witt_polynomial p ℤ n) =
  ite (n = 0) 0 (↑p * witt_polynomial p ℤ (n - 1)) := sorry

