/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.group_theory.submonoid.operations
import Mathlib.group_theory.submonoid.membership
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Non-zero divisors

In this file we define the submonoid `non_zero_divisors` of a `monoid_with_zero`.
-/

/-- The submonoid of non-zero-divisors of a `monoid_with_zero` `R`. -/
def non_zero_divisors (R : Type u_1) [monoid_with_zero R] : submonoid R :=
  submonoid.mk (set_of fun (x : R) => ∀ (z : R), z * x = 0 → z = 0) sorry sorry

theorem mul_mem_non_zero_divisors {R : Type u_1} [comm_ring R] {a : R} {b : R} : a * b ∈ non_zero_divisors R ↔ a ∈ non_zero_divisors R ∧ b ∈ non_zero_divisors R := sorry

theorem eq_zero_of_ne_zero_of_mul_right_eq_zero {A : Type u_2} [integral_domain A] {x : A} {y : A} (hnx : x ≠ 0) (hxy : y * x = 0) : y = 0 :=
  or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

theorem eq_zero_of_ne_zero_of_mul_left_eq_zero {A : Type u_2} [integral_domain A] {x : A} {y : A} (hnx : x ≠ 0) (hxy : x * y = 0) : y = 0 :=
  or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

theorem mem_non_zero_divisors_iff_ne_zero {A : Type u_2} [integral_domain A] {x : A} : x ∈ non_zero_divisors A ↔ x ≠ 0 := sorry

theorem map_ne_zero_of_mem_non_zero_divisors {R : Type u_1} [comm_ring R] [nontrivial R] {B : Type u_2} [ring B] {g : R →+* B} (hg : function.injective ⇑g) {x : ↥(non_zero_divisors R)} : coe_fn g ↑x ≠ 0 :=
  fun (h0 : coe_fn g ↑x = 0) =>
    one_ne_zero (subtype.property x 1 (Eq.symm (one_mul (subtype.val x)) ▸ hg (trans h0 (Eq.symm (ring_hom.map_zero g)))))

theorem map_mem_non_zero_divisors {A : Type u_2} [integral_domain A] {B : Type u_1} [integral_domain B] {g : A →+* B} (hg : function.injective ⇑g) {x : ↥(non_zero_divisors A)} : coe_fn g ↑x ∈ non_zero_divisors B :=
  fun (z : B) (hz : z * coe_fn g ↑x = 0) =>
    eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_non_zero_divisors hg) hz

theorem le_non_zero_divisors_of_domain {A : Type u_2} [integral_domain A] {M : submonoid A} (hM : ¬↑0 ∈ M) : M ≤ non_zero_divisors A :=
  fun (x : A) (hx : x ∈ M) (y : A) (hy : y * x = 0) =>
    or.rec_on (eq_zero_or_eq_zero_of_mul_eq_zero hy) (fun (h : y = 0) => h) fun (h : x = 0) => absurd (h ▸ hx) hM

theorem powers_le_non_zero_divisors_of_domain {A : Type u_2} [integral_domain A] {a : A} (ha : a ≠ 0) : submonoid.powers a ≤ non_zero_divisors A :=
  le_non_zero_divisors_of_domain
    fun (h : ↑0 ∈ submonoid.powers a) => absurd (Exists.rec_on h fun (_x : ℕ) (hn : a ^ _x = ↑0) => pow_eq_zero hn) ha

theorem map_le_non_zero_divisors_of_injective {A : Type u_2} [integral_domain A] {B : Type u_1} [integral_domain B] {f : A →+* B} (hf : function.injective ⇑f) {M : submonoid A} (hM : M ≤ non_zero_divisors A) : submonoid.map (↑f) M ≤ non_zero_divisors B := sorry

