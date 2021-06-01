/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.jacobson
import Mathlib.field_theory.algebraic_closure
import Mathlib.field_theory.mv_polynomial
import Mathlib.algebraic_geometry.prime_spectrum
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Nullstellensatz
This file establishes a version of Hilbert's classical Nullstellensatz for `mv_polynomial`s.
The main statement of the theorem is `vanishing_ideal_zero_locus_eq_radical`.

The statement is in terms of new definitions `vanishing_ideal` and `zero_locus`.
Mathlib already has versions of these in terms of the prime spectrum of a ring,
  but those are not well-suited for expressing this result.
Suggestions for better ways to state this theorem or organize things are welcome.

The machinery around `vanishing_ideal` and `zero_locus` is also minimal, I only added lemmas
  directly needed in this proof, since I'm not sure if they are the right approach.
-/

namespace mv_polynomial


/-- Set of points that are zeroes of all polynomials in an ideal -/
def zero_locus {k : Type u_1} [field k] {σ : Type u_2} (I : ideal (mv_polynomial σ k)) :
    set (σ → k) :=
  set_of fun (x : σ → k) => ∀ (p : mv_polynomial σ k), p ∈ I → coe_fn (eval x) p = 0

@[simp] theorem mem_zero_locus_iff {k : Type u_1} [field k] {σ : Type u_2}
    {I : ideal (mv_polynomial σ k)} {x : σ → k} :
    x ∈ zero_locus I ↔ ∀ (p : mv_polynomial σ k), p ∈ I → coe_fn (eval x) p = 0 :=
  iff.rfl

theorem zero_locus_anti_mono {k : Type u_1} [field k] {σ : Type u_2} {I : ideal (mv_polynomial σ k)}
    {J : ideal (mv_polynomial σ k)} (h : I ≤ J) : zero_locus J ≤ zero_locus I :=
  fun (x : σ → k) (hx : x ∈ zero_locus J) (p : mv_polynomial σ k) (hp : p ∈ I) => hx p (h hp)

theorem zero_locus_bot {k : Type u_1} [field k] {σ : Type u_2} : zero_locus ⊥ = ⊤ :=
  iff.mpr eq_top_iff
    fun (x : σ → k) (hx : x ∈ ⊤) (p : mv_polynomial σ k) (hp : p ∈ ⊥) =>
      trans (congr_arg (⇑(eval x)) (iff.mp ideal.mem_bot hp)) (ring_hom.map_zero (eval x))

theorem zero_locus_top {k : Type u_1} [field k] {σ : Type u_2} : zero_locus ⊤ = ⊥ :=
  iff.mpr eq_bot_iff
    fun (x : σ → k) (hx : x ∈ zero_locus ⊤) =>
      one_ne_zero (ring_hom.map_one (eval x) ▸ hx 1 submodule.mem_top)

/-- Ideal of polynomials with common zeroes at all elements of a set -/
def vanishing_ideal {k : Type u_1} [field k] {σ : Type u_2} (V : set (σ → k)) :
    ideal (mv_polynomial σ k) :=
  submodule.mk (set_of fun (p : mv_polynomial σ k) => ∀ (x : σ → k), x ∈ V → coe_fn (eval x) p = 0)
    sorry sorry sorry

@[simp] theorem mem_vanishing_ideal_iff {k : Type u_1} [field k] {σ : Type u_2} {V : set (σ → k)}
    {p : mv_polynomial σ k} :
    p ∈ vanishing_ideal V ↔ ∀ (x : σ → k), x ∈ V → coe_fn (eval x) p = 0 :=
  iff.rfl

theorem vanishing_ideal_anti_mono {k : Type u_1} [field k] {σ : Type u_2} {A : set (σ → k)}
    {B : set (σ → k)} (h : A ≤ B) : vanishing_ideal B ≤ vanishing_ideal A :=
  fun (p : mv_polynomial σ k) (hp : p ∈ vanishing_ideal B) (x : σ → k) (hx : x ∈ A) => hp x (h hx)

theorem vanishing_ideal_empty {k : Type u_1} [field k] {σ : Type u_2} : vanishing_ideal ∅ = ⊤ :=
  le_antisymm le_top
    fun (p : mv_polynomial σ k) (hp : p ∈ ⊤) (x : σ → k) (hx : x ∈ ∅) =>
      absurd hx (set.not_mem_empty x)

theorem le_vanishing_ideal_zero_locus {k : Type u_1} [field k] {σ : Type u_2}
    (I : ideal (mv_polynomial σ k)) : I ≤ vanishing_ideal (zero_locus I) :=
  fun (p : mv_polynomial σ k) (hp : p ∈ I) (x : σ → k) (hx : x ∈ zero_locus I) => hx p hp

theorem zero_locus_vanishing_ideal_le {k : Type u_1} [field k] {σ : Type u_2} (V : set (σ → k)) :
    V ≤ zero_locus (vanishing_ideal V) :=
  fun (V_1 : σ → k) (hV : V_1 ∈ V) (p : mv_polynomial σ k) (hp : p ∈ vanishing_ideal V) => hp V_1 hV

theorem zero_locus_vanishing_ideal_galois_connection {k : Type u_1} [field k] {σ : Type u_2} :
    galois_connection zero_locus vanishing_ideal :=
  fun (I : ideal (mv_polynomial σ k)) (V : order_dual (set (σ → k))) =>
    { mp :=
        fun (h : zero_locus I ≤ V) =>
          le_trans (le_vanishing_ideal_zero_locus I) (vanishing_ideal_anti_mono h),
      mpr :=
        fun (h : I ≤ vanishing_ideal V) =>
          le_trans (zero_locus_anti_mono h) (zero_locus_vanishing_ideal_le V) }

theorem mem_vanishing_ideal_singleton_iff {k : Type u_1} [field k] {σ : Type u_2} (x : σ → k)
    (p : mv_polynomial σ k) : p ∈ vanishing_ideal (singleton x) ↔ coe_fn (eval x) p = 0 :=
  { mp := fun (h : p ∈ vanishing_ideal (singleton x)) => h x rfl,
    mpr :=
      fun (hpx : coe_fn (eval x) p = 0) (y : σ → k) (hy : y ∈ singleton x) => Eq.symm hy ▸ hpx }

protected instance vanishing_ideal_singleton_is_maximal {k : Type u_1} [field k] {σ : Type u_2}
    {x : σ → k} : ideal.is_maximal (vanishing_ideal (singleton x)) :=
  sorry

theorem radical_le_vanishing_ideal_zero_locus {k : Type u_1} [field k] {σ : Type u_2}
    (I : ideal (mv_polynomial σ k)) : ideal.radical I ≤ vanishing_ideal (zero_locus I) :=
  sorry

/-- The point in the prime spectrum assosiated to a given point -/
def point_to_point {k : Type u_1} [field k] {σ : Type u_2} (x : σ → k) :
    prime_spectrum (mv_polynomial σ k) :=
  { val := vanishing_ideal (singleton x), property := sorry }

@[simp] theorem vanishing_ideal_point_to_point {k : Type u_1} [field k] {σ : Type u_2}
    (V : set (σ → k)) : prime_spectrum.vanishing_ideal (point_to_point '' V) = vanishing_ideal V :=
  sorry

theorem point_to_point_zero_locus_le {k : Type u_1} [field k] {σ : Type u_2}
    (I : ideal (mv_polynomial σ k)) :
    point_to_point '' zero_locus I ≤ prime_spectrum.zero_locus ↑I :=
  sorry

theorem is_maximal_iff_eq_vanishing_ideal_singleton {k : Type u_1} [field k] {σ : Type u_2}
    [is_alg_closed k] [fintype σ] (I : ideal (mv_polynomial σ k)) :
    ideal.is_maximal I ↔ ∃ (x : σ → k), I = vanishing_ideal (singleton x) :=
  sorry

/-- Main statement of the Nullstellensatz -/
@[simp] theorem vanishing_ideal_zero_locus_eq_radical {k : Type u_1} [field k] {σ : Type u_2}
    [is_alg_closed k] [fintype σ] (I : ideal (mv_polynomial σ k)) :
    vanishing_ideal (zero_locus I) = ideal.radical I :=
  sorry

@[simp] theorem is_prime.vanishing_ideal_zero_locus {k : Type u_1} [field k] {σ : Type u_2}
    [is_alg_closed k] [fintype σ] (P : ideal (mv_polynomial σ k)) [h : ideal.is_prime P] :
    vanishing_ideal (zero_locus P) = P :=
  trans (vanishing_ideal_zero_locus_eq_radical P) (ideal.is_prime.radical h)

end Mathlib