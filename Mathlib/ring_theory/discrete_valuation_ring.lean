/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.principal_ideal_domain
import Mathlib.order.conditionally_complete_lattice
import Mathlib.ring_theory.multiplicity
import Mathlib.ring_theory.valuation.basic
import Mathlib.PostPort

universes u l u_1 

namespace Mathlib

/-!
# Discrete valuation rings

This file defines discrete valuation rings (DVRs) and develops a basic interface
for them.

## Important definitions

There are various definitions of a DVR in the literature; we define a DVR to be a local PID
which is not a field (the first definition in Wikipedia) and prove that this is equivalent
to being a PID with a unique non-zero prime ideal (the definition in Serre's
book "Local Fields").

Let R be an integral domain, assumed to be a principal ideal ring and a local ring.

* `discrete_valuation_ring R` : a predicate expressing that R is a DVR

### Definitions

* `add_val R : R → ℕ` : the additive valuation on a DVR (sending 0 to 0 rather than the
     mathematically correct +∞).
TODO -- the multiplicative valuation, taking values in something
  like `with_zero (multiplicative ℤ)`?

## Implementation notes

It's a theorem that an element of a DVR is a uniformizer if and only if it's irreducible.
We do not hence define `uniformizer` at all, because we can use `irreducible` instead.

## Tags

discrete valuation ring
-/

/-- An integral domain is a *discrete valuation ring* (DVR) if it's a local PID which
  is not a field. -/
class discrete_valuation_ring (R : Type u) [integral_domain R] 
extends is_principal_ideal_ring R, local_ring R
where
  not_a_field' : local_ring.maximal_ideal R ≠ ⊥

namespace discrete_valuation_ring


theorem not_a_field (R : Type u) [integral_domain R] [discrete_valuation_ring R] : local_ring.maximal_ideal R ≠ ⊥ :=
  not_a_field'

/-- An element of a DVR is irreducible iff it is a uniformizer, that is, generates the
  maximal ideal of R -/
theorem irreducible_iff_uniformizer {R : Type u} [integral_domain R] [discrete_valuation_ring R] (ϖ : R) : irreducible ϖ ↔ local_ring.maximal_ideal R = ideal.span (singleton ϖ) := sorry

/-- Uniformisers exist in a DVR -/
theorem exists_irreducible (R : Type u) [integral_domain R] [discrete_valuation_ring R] : ∃ (ϖ : R), irreducible ϖ := sorry

/-- an integral domain is a DVR iff it's a PID with a unique non-zero prime ideal -/
theorem iff_pid_with_one_nonzero_prime (R : Type u) [integral_domain R] : discrete_valuation_ring R ↔ is_principal_ideal_ring R ∧ exists_unique fun (P : ideal R) => P ≠ ⊥ ∧ ideal.is_prime P := sorry

theorem associated_of_irreducible (R : Type u) [integral_domain R] [discrete_valuation_ring R] {a : R} {b : R} (ha : irreducible a) (hb : irreducible b) : associated a b := sorry

end discrete_valuation_ring


namespace discrete_valuation_ring


/-- Alternative characterisation of discrete valuation rings. -/
def has_unit_mul_pow_irreducible_factorization (R : Type u_1) [integral_domain R]  :=
  ∃ (p : R), irreducible p ∧ ∀ {x : R}, x ≠ 0 → ∃ (n : ℕ), associated (p ^ n) x

namespace has_unit_mul_pow_irreducible_factorization


theorem unique_irreducible {R : Type u_1} [integral_domain R] (hR : has_unit_mul_pow_irreducible_factorization R) {p : R} {q : R} (hp : irreducible p) (hq : irreducible q) : associated p q := sorry

/-- An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p` is a unique factorization domain.
See `discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization`. -/
theorem to_unique_factorization_monoid {R : Type u_1} [integral_domain R] (hR : has_unit_mul_pow_irreducible_factorization R) : unique_factorization_monoid R := sorry

theorem of_ufd_of_unique_irreducible {R : Type u_1} [integral_domain R] [unique_factorization_monoid R] (h₁ : ∃ (p : R), irreducible p) (h₂ : ∀ {p q : R}, irreducible p → irreducible q → associated p q) : has_unit_mul_pow_irreducible_factorization R := sorry

end has_unit_mul_pow_irreducible_factorization


theorem aux_pid_of_ufd_of_unique_irreducible (R : Type u) [integral_domain R] [unique_factorization_monoid R] (h₁ : ∃ (p : R), irreducible p) (h₂ : ∀ {p q : R}, irreducible p → irreducible q → associated p q) : is_principal_ideal_ring R := sorry

/--
A unique factorization domain with at least one irreducible element
in which all irreducible elements are associated
is a discrete valuation ring.
-/
theorem of_ufd_of_unique_irreducible {R : Type u} [integral_domain R] [unique_factorization_monoid R] (h₁ : ∃ (p : R), irreducible p) (h₂ : ∀ {p q : R}, irreducible p → irreducible q → associated p q) : discrete_valuation_ring R := sorry

/--
An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p`
is a discrete valuation ring.
-/
theorem of_has_unit_mul_pow_irreducible_factorization {R : Type u} [integral_domain R] (hR : has_unit_mul_pow_irreducible_factorization R) : discrete_valuation_ring R := sorry

theorem associated_pow_irreducible {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : irreducible ϖ) : ∃ (n : ℕ), associated x (ϖ ^ n) := sorry

theorem eq_unit_mul_pow_irreducible {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : irreducible ϖ) : ∃ (n : ℕ), ∃ (u : units R), x = ↑u * ϖ ^ n := sorry

theorem ideal_eq_span_pow_irreducible {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] {s : ideal R} (hs : s ≠ ⊥) {ϖ : R} (hirr : irreducible ϖ) : ∃ (n : ℕ), s = ideal.span (singleton (ϖ ^ n)) := sorry

theorem unit_mul_pow_congr_pow {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] {p : R} {q : R} (hp : irreducible p) (hq : irreducible q) (u : units R) (v : units R) (m : ℕ) (n : ℕ) (h : ↑u * p ^ m = ↑v * q ^ n) : m = n := sorry

theorem unit_mul_pow_congr_unit {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] {ϖ : R} (hirr : irreducible ϖ) (u : units R) (v : units R) (m : ℕ) (n : ℕ) (h : ↑u * ϖ ^ m = ↑v * ϖ ^ n) : u = v := sorry

/-!
## The additive valuation on a DVR
-/

/-- The `ℕ`-valued additive valuation on a DVR (returns junk at `0` rather than `+∞`) -/
def add_val (R : Type u) [integral_domain R] [discrete_valuation_ring R] : R → ℕ :=
  fun (r : R) => dite (r = 0) (fun (hr : r = 0) => 0) fun (hr : ¬r = 0) => classical.some sorry

theorem add_val_spec {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] {r : R} (hr : r ≠ 0) : let ϖ : R := classical.some (exists_irreducible R);
let n : ℕ := classical.some (associated_pow_irreducible hr (classical.some_spec (exists_irreducible R)));
associated r (ϖ ^ n) :=
  classical.some_spec (associated_pow_irreducible hr (classical.some_spec (exists_irreducible R)))

theorem add_val_def {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] (r : R) (u : units R) {ϖ : R} (hϖ : irreducible ϖ) (n : ℕ) (hr : r = ↑u * ϖ ^ n) : add_val R r = n := sorry

theorem add_val_def' {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] (u : units R) {ϖ : R} (hϖ : irreducible ϖ) (n : ℕ) : add_val R (↑u * ϖ ^ n) = n :=
  add_val_def (↑u * ϖ ^ n) u hϖ n rfl

@[simp] theorem add_val_zero {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] : add_val R 0 = 0 :=
  dif_pos rfl

@[simp] theorem add_val_one {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] : add_val R 1 = 0 := sorry

@[simp] theorem add_val_uniformizer {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] {ϖ : R} (hϖ : irreducible ϖ) : add_val R ϖ = 1 := sorry

@[simp] theorem add_val_mul {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] {a : R} {b : R} (ha : a ≠ 0) (hb : b ≠ 0) : add_val R (a * b) = add_val R a + add_val R b := sorry

theorem add_val_pow {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] (a : R) (n : ℕ) : add_val R (a ^ n) = n * add_val R a := sorry

theorem add_val_le_iff_dvd {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] {a : R} {b : R} (ha : a ≠ 0) (hb : b ≠ 0) : add_val R a ≤ add_val R b ↔ a ∣ b := sorry

theorem add_val_add {R : Type u_1} [integral_domain R] [discrete_valuation_ring R] {a : R} {b : R} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) : min (add_val R a) (add_val R b) ≤ add_val R (a + b) := sorry

