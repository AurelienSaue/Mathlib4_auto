/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Devon Tuma
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.polynomial.basic
import Mathlib.ring_theory.non_zero_divisors
import Mathlib.PostPort

universes u_3 u_4 u_1 u_2 

namespace Mathlib

/-- `scale_roots p s` is a polynomial with root `r * s` for each root `r` of `p`. -/
def scale_roots {R : Type u_3} [comm_ring R] (p : polynomial R) (s : R) : polynomial R :=
  finsupp.on_finset (finsupp.support p) (fun (i : ℕ) => polynomial.coeff p i * s ^ (polynomial.nat_degree p - i)) sorry

@[simp] theorem coeff_scale_roots {R : Type u_3} [comm_ring R] (p : polynomial R) (s : R) (i : ℕ) : polynomial.coeff (scale_roots p s) i = polynomial.coeff p i * s ^ (polynomial.nat_degree p - i) :=
  rfl

theorem coeff_scale_roots_nat_degree {R : Type u_3} [comm_ring R] (p : polynomial R) (s : R) : polynomial.coeff (scale_roots p s) (polynomial.nat_degree p) = polynomial.leading_coeff p := sorry

@[simp] theorem zero_scale_roots {R : Type u_3} [comm_ring R] (s : R) : scale_roots 0 s = 0 := sorry

theorem scale_roots_ne_zero {R : Type u_3} [comm_ring R] {p : polynomial R} (hp : p ≠ 0) (s : R) : scale_roots p s ≠ 0 := sorry

theorem support_scale_roots_le {R : Type u_3} [comm_ring R] (p : polynomial R) (s : R) : finsupp.support (scale_roots p s) ≤ finsupp.support p := sorry

theorem support_scale_roots_eq {R : Type u_3} [comm_ring R] (p : polynomial R) {s : R} (hs : s ∈ non_zero_divisors R) : finsupp.support (scale_roots p s) = finsupp.support p := sorry

@[simp] theorem degree_scale_roots {R : Type u_3} [comm_ring R] (p : polynomial R) {s : R} : polynomial.degree (scale_roots p s) = polynomial.degree p := sorry

@[simp] theorem nat_degree_scale_roots {R : Type u_3} [comm_ring R] (p : polynomial R) (s : R) : polynomial.nat_degree (scale_roots p s) = polynomial.nat_degree p := sorry

theorem monic_scale_roots_iff {R : Type u_3} [comm_ring R] {p : polynomial R} (s : R) : polynomial.monic (scale_roots p s) ↔ polynomial.monic p := sorry

theorem scale_roots_eval₂_eq_zero {R : Type u_3} {S : Type u_4} [comm_ring R] [comm_ring S] {p : polynomial S} (f : S →+* R) {r : R} {s : S} (hr : polynomial.eval₂ f r p = 0) : polynomial.eval₂ f (coe_fn f s * r) (scale_roots p s) = 0 := sorry

theorem scale_roots_aeval_eq_zero {R : Type u_3} {S : Type u_4} [comm_ring R] [comm_ring S] [algebra S R] {p : polynomial S} {r : R} {s : S} (hr : coe_fn (polynomial.aeval r) p = 0) : coe_fn (polynomial.aeval (coe_fn (algebra_map S R) s * r)) (scale_roots p s) = 0 :=
  scale_roots_eval₂_eq_zero (algebra_map S R) hr

theorem scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero {A : Type u_1} {K : Type u_2} [integral_domain A] [field K] {p : polynomial A} {f : A →+* K} (hf : function.injective ⇑f) {r : A} {s : A} (hr : polynomial.eval₂ f (coe_fn f r / coe_fn f s) p = 0) (hs : s ∈ non_zero_divisors A) : polynomial.eval₂ f (coe_fn f r) (scale_roots p s) = 0 := sorry

theorem scale_roots_aeval_eq_zero_of_aeval_div_eq_zero {A : Type u_1} {K : Type u_2} [integral_domain A] [field K] [algebra A K] (inj : function.injective ⇑(algebra_map A K)) {p : polynomial A} {r : A} {s : A} (hr : coe_fn (polynomial.aeval (coe_fn (algebra_map A K) r / coe_fn (algebra_map A K) s)) p = 0) (hs : s ∈ non_zero_divisors A) : coe_fn (polynomial.aeval (coe_fn (algebra_map A K) r)) (scale_roots p s) = 0 :=
  scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs

