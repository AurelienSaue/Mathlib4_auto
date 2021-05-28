/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker

TODO: Provide a GCD monoid instance for `ℕ`, port GCD facts about nats
TODO: Generalize normalization monoids commutative (cancellative) monoids with or without zero
TODO: Generalize GCD monoid to not require normalization in all cases
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.associated
import Mathlib.PostPort

universes u_2 l u_1 

namespace Mathlib

/-!

# Monoids with normalization functions, `gcd`, and `lcm`

This file defines extra structures on `comm_cancel_monoid_with_zero`s, including `integral_domain`s.

## Main Definitions

* `normalization_monoid`
* `gcd_monoid`
* `gcd_monoid_of_exists_gcd`
* `gcd_monoid_of_exists_lcm`

## Implementation Notes

* `normalization_monoid` is defined by assigning to each element a `norm_unit` such that multiplying
by that unit normalizes the monoid, and `normalize` is an idempotent monoid homomorphism. This
definition as currently implemented does casework on `0`.

* `gcd_monoid` extends `normalization_monoid`, so the `gcd` and `lcm` are always normalized.
This makes `gcd`s of polynomials easier to work with, but excludes Euclidean domains, and monoids
without zero.

* `gcd_monoid_of_gcd` noncomputably constructs a `gcd_monoid` structure just from the `gcd`
  and its properties.

* `gcd_monoid_of_exists_gcd` noncomputably constructs a `gcd_monoid` structure just from a proof
  that any two elements have a (not necessarily normalized) `gcd`.

* `gcd_monoid_of_lcm` noncomputably constructs a `gcd_monoid` structure just from the `lcm`
  and its properties.

* `gcd_monoid_of_exists_lcm` noncomputably constructs a `gcd_monoid` structure just from a proof
  that any two elements have a (not necessarily normalized) `lcm`.

## TODO

* Provide a GCD monoid instance for `ℕ`, port GCD facts about nats, definition of coprime
* Generalize normalization monoids to commutative (cancellative) monoids with or without zero
* Generalize GCD monoid to not require normalization in all cases


## Tags

divisibility, gcd, lcm, normalize

-/

/-- Normalization monoid: multiplying with `norm_unit` gives a normal form for associated
elements. -/
class normalization_monoid (α : Type u_2) [nontrivial α] [comm_cancel_monoid_with_zero α] 
where
  norm_unit : α → units α
  norm_unit_zero : norm_unit 0 = 1
  norm_unit_mul : ∀ {a b : α}, a ≠ 0 → b ≠ 0 → norm_unit (a * b) = norm_unit a * norm_unit b
  norm_unit_coe_units : ∀ (u : units α), norm_unit ↑u = (u⁻¹)

@[simp] theorem norm_unit_one {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] : norm_unit 1 = 1 :=
  norm_unit_coe_units 1

/-- Chooses an element of each associate class, by multiplying by `norm_unit` -/
def normalize {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] : monoid_with_zero_hom α α :=
  monoid_with_zero_hom.mk (fun (x : α) => x * ↑(norm_unit x)) sorry sorry sorry

theorem associated_normalize {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] {x : α} : associated x (coe_fn normalize x) :=
  Exists.intro (norm_unit x) rfl

theorem normalize_associated {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] {x : α} : associated (coe_fn normalize x) x :=
  associated.symm associated_normalize

theorem associates.mk_normalize {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] {x : α} : associates.mk (coe_fn normalize x) = associates.mk x :=
  iff.mpr associates.mk_eq_mk_iff_associated normalize_associated

@[simp] theorem normalize_apply {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] {x : α} : coe_fn normalize x = x * ↑(norm_unit x) :=
  rfl

@[simp] theorem normalize_zero {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] : coe_fn normalize 0 = 0 :=
  monoid_with_zero_hom.map_zero normalize

@[simp] theorem normalize_one {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] : coe_fn normalize 1 = 1 :=
  monoid_with_zero_hom.map_one normalize

theorem normalize_coe_units {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] (u : units α) : coe_fn normalize ↑u = 1 := sorry

theorem normalize_eq_zero {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] {x : α} : coe_fn normalize x = 0 ↔ x = 0 :=
  { mp := fun (hx : coe_fn normalize x = 0) => iff.mp (associated_zero_iff_eq_zero x) (hx ▸ associated_normalize),
    mpr := fun (ᾰ : x = 0) => Eq._oldrec normalize_zero (Eq.symm ᾰ) }

theorem normalize_eq_one {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] {x : α} : coe_fn normalize x = 1 ↔ is_unit x := sorry

@[simp] theorem norm_unit_mul_norm_unit {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] (a : α) : norm_unit (a * ↑(norm_unit a)) = 1 := sorry

theorem normalize_idem {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] (x : α) : coe_fn normalize (coe_fn normalize x) = coe_fn normalize x := sorry

theorem normalize_eq_normalize {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] {a : α} {b : α} (hab : a ∣ b) (hba : b ∣ a) : coe_fn normalize a = coe_fn normalize b := sorry

theorem normalize_eq_normalize_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] {x : α} {y : α} : coe_fn normalize x = coe_fn normalize y ↔ x ∣ y ∧ y ∣ x := sorry

theorem dvd_antisymm_of_normalize_eq {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] {a : α} {b : α} (ha : coe_fn normalize a = a) (hb : coe_fn normalize b = b) (hab : a ∣ b) (hba : b ∣ a) : a = b :=
  ha ▸ hb ▸ normalize_eq_normalize hab hba

--can be proven by simp

theorem dvd_normalize_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] {a : α} {b : α} : a ∣ coe_fn normalize b ↔ a ∣ b :=
  units.dvd_mul_right

--can be proven by simp

theorem normalize_dvd_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] {a : α} {b : α} : coe_fn normalize a ∣ b ↔ a ∣ b :=
  units.mul_right_dvd

namespace comm_group_with_zero


protected instance normalization_monoid {α : Type u_1} [DecidableEq α] [comm_group_with_zero α] : normalization_monoid α :=
  normalization_monoid.mk (fun (x : α) => dite (x = 0) (fun (h : x = 0) => 1) fun (h : ¬x = 0) => units.mk0 x h⁻¹) sorry
    sorry sorry

@[simp] theorem coe_norm_unit {α : Type u_1} [DecidableEq α] [comm_group_with_zero α] {a : α} (h0 : a ≠ 0) : ↑(norm_unit a) = (a⁻¹) := sorry

end comm_group_with_zero


namespace associates


/-- Maps an element of `associates` back to the normalized element of its associate class -/
protected def out {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] : associates α → α :=
  quotient.lift ⇑normalize sorry

theorem out_mk {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] (a : α) : associates.out (associates.mk a) = coe_fn normalize a :=
  rfl

@[simp] theorem out_one {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] : associates.out 1 = 1 :=
  normalize_one

theorem out_mul {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] (a : associates α) (b : associates α) : associates.out (a * b) = associates.out a * associates.out b := sorry

theorem dvd_out_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] (a : α) (b : associates α) : a ∣ associates.out b ↔ associates.mk a ≤ b := sorry

theorem out_dvd_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] (a : α) (b : associates α) : associates.out b ∣ a ↔ b ≤ associates.mk a := sorry

@[simp] theorem out_top {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] : associates.out ⊤ = 0 :=
  normalize_zero

@[simp] theorem normalize_out {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] (a : associates α) : coe_fn normalize (associates.out a) = associates.out a :=
  quotient.induction_on a normalize_idem

end associates


/-- GCD monoid: a `comm_cancel_monoid_with_zero` with normalization and `gcd`
(greatest common divisor) and `lcm` (least common multiple) operations. In this setting `gcd` and
`lcm` form a bounded lattice on the associated elements where `gcd` is the infimum, `lcm` is the
supremum, `1` is bottom, and `0` is top. The type class focuses on `gcd` and we derive the
corresponding `lcm` facts from `gcd`.
-/
class gcd_monoid (α : Type u_2) [comm_cancel_monoid_with_zero α] [nontrivial α] 
extends normalization_monoid α
where
  gcd : α → α → α
  lcm : α → α → α
  gcd_dvd_left : ∀ (a b : α), gcd a b ∣ a
  gcd_dvd_right : ∀ (a b : α), gcd a b ∣ b
  dvd_gcd : ∀ {a b c : α}, a ∣ c → a ∣ b → a ∣ gcd c b
  normalize_gcd : ∀ (a b : α), coe_fn normalize (gcd a b) = gcd a b
  gcd_mul_lcm : ∀ (a b : α), gcd a b * lcm a b = coe_fn normalize (a * b)
  lcm_zero_left : ∀ (a : α), lcm 0 a = 0
  lcm_zero_right : ∀ (a : α), lcm a 0 = 0

@[simp] theorem normalize_gcd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) : coe_fn normalize (gcd a b) = gcd a b :=
  gcd_monoid.normalize_gcd

@[simp] theorem gcd_mul_lcm {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) : gcd a b * lcm a b = coe_fn normalize (a * b) :=
  gcd_monoid.gcd_mul_lcm

theorem dvd_gcd_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) (c : α) : a ∣ gcd b c ↔ a ∣ b ∧ a ∣ c := sorry

theorem gcd_comm {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) : gcd a b = gcd b a :=
  dvd_antisymm_of_normalize_eq (normalize_gcd a b) (normalize_gcd b a) (dvd_gcd (gcd_dvd_right a b) (gcd_dvd_left a b))
    (dvd_gcd (gcd_dvd_right b a) (gcd_dvd_left b a))

theorem gcd_assoc {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (m : α) (n : α) (k : α) : gcd (gcd m n) k = gcd m (gcd n k) := sorry

protected instance gcd_monoid.gcd.is_commutative {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] : is_commutative α gcd :=
  is_commutative.mk gcd_comm

protected instance gcd_monoid.gcd.is_associative {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] : is_associative α gcd :=
  is_associative.mk gcd_assoc

theorem gcd_eq_normalize {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} {b : α} {c : α} (habc : gcd a b ∣ c) (hcab : c ∣ gcd a b) : gcd a b = coe_fn normalize c :=
  normalize_gcd a b ▸ normalize_eq_normalize habc hcab

@[simp] theorem gcd_zero_left {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) : gcd 0 a = coe_fn normalize a :=
  gcd_eq_normalize (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero a) (dvd_refl a))

@[simp] theorem gcd_zero_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) : gcd a 0 = coe_fn normalize a :=
  gcd_eq_normalize (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero a))

@[simp] theorem gcd_eq_zero_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) : gcd a b = 0 ↔ a = 0 ∧ b = 0 := sorry

@[simp] theorem gcd_one_left {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) : gcd 1 a = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd 1 a) normalize_one (gcd_dvd_left 1 a) (one_dvd (gcd 1 a))

@[simp] theorem gcd_one_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) : gcd a 1 = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd a 1) normalize_one (gcd_dvd_right a 1) (one_dvd (gcd a 1))

theorem gcd_dvd_gcd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} {b : α} {c : α} {d : α} (hab : a ∣ b) (hcd : c ∣ d) : gcd a c ∣ gcd b d :=
  dvd_gcd (dvd.trans (gcd_dvd_left a c) hab) (dvd.trans (gcd_dvd_right a c) hcd)

@[simp] theorem gcd_same {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) : gcd a a = coe_fn normalize a :=
  gcd_eq_normalize (gcd_dvd_left a a) (dvd_gcd (dvd_refl a) (dvd_refl a))

@[simp] theorem gcd_mul_left {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) (c : α) : gcd (a * b) (a * c) = coe_fn normalize a * gcd b c := sorry

@[simp] theorem gcd_mul_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) (c : α) : gcd (b * a) (c * a) = gcd b c * coe_fn normalize a := sorry

theorem gcd_eq_left_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) (h : coe_fn normalize a = a) : gcd a b = a ↔ a ∣ b := sorry

theorem gcd_eq_right_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) (h : coe_fn normalize b = b) : gcd a b = b ↔ b ∣ a := sorry

theorem gcd_dvd_gcd_mul_left {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (m : α) (n : α) (k : α) : gcd m n ∣ gcd (k * m) n :=
  gcd_dvd_gcd (dvd_mul_left m k) (dvd_refl n)

theorem gcd_dvd_gcd_mul_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (m : α) (n : α) (k : α) : gcd m n ∣ gcd (m * k) n :=
  gcd_dvd_gcd (dvd_mul_right m k) (dvd_refl n)

theorem gcd_dvd_gcd_mul_left_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (m : α) (n : α) (k : α) : gcd m n ∣ gcd m (k * n) :=
  gcd_dvd_gcd (dvd_refl m) (dvd_mul_left n k)

theorem gcd_dvd_gcd_mul_right_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (m : α) (n : α) (k : α) : gcd m n ∣ gcd m (n * k) :=
  gcd_dvd_gcd (dvd_refl m) (dvd_mul_right n k)

theorem gcd_eq_of_associated_left {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {m : α} {n : α} (h : associated m n) (k : α) : gcd m k = gcd n k :=
  dvd_antisymm_of_normalize_eq (normalize_gcd m k) (normalize_gcd n k) (gcd_dvd_gcd (dvd_of_associated h) (dvd_refl k))
    (gcd_dvd_gcd (dvd_of_associated (associated.symm h)) (dvd_refl k))

theorem gcd_eq_of_associated_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {m : α} {n : α} (h : associated m n) (k : α) : gcd k m = gcd k n :=
  dvd_antisymm_of_normalize_eq (normalize_gcd k m) (normalize_gcd k n) (gcd_dvd_gcd (dvd_refl k) (dvd_of_associated h))
    (gcd_dvd_gcd (dvd_refl k) (dvd_of_associated (associated.symm h)))

theorem dvd_gcd_mul_of_dvd_mul {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {m : α} {n : α} {k : α} (H : k ∣ m * n) : k ∣ gcd k m * n := sorry

theorem dvd_mul_gcd_of_dvd_mul {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {m : α} {n : α} {k : α} (H : k ∣ m * n) : k ∣ m * gcd k n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (k ∣ m * gcd k n)) (mul_comm m (gcd k n))))
    (dvd_gcd_mul_of_dvd_mul (eq.mp (Eq._oldrec (Eq.refl (k ∣ m * n)) (mul_comm m n)) H))

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`.

 Note: In general, this representation is highly non-unique. -/
theorem exists_dvd_and_dvd_of_dvd_mul {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {m : α} {n : α} {k : α} (H : k ∣ m * n) : ∃ (d₁ : α), ∃ (hd₁ : d₁ ∣ m), ∃ (d₂ : α), ∃ (hd₂ : d₂ ∣ n), k = d₁ * d₂ := sorry

theorem gcd_mul_dvd_mul_gcd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (k : α) (m : α) (n : α) : gcd k (m * n) ∣ gcd k m * gcd k n := sorry

theorem gcd_pow_right_dvd_pow_gcd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} {b : α} {k : ℕ} : gcd a (b ^ k) ∣ gcd a b ^ k := sorry

theorem gcd_pow_left_dvd_pow_gcd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} {b : α} {k : ℕ} : gcd (a ^ k) b ∣ gcd a b ^ k :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd (a ^ k) b ∣ gcd a b ^ k)) (gcd_comm (a ^ k) b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd b (a ^ k) ∣ gcd a b ^ k)) (gcd_comm a b))) gcd_pow_right_dvd_pow_gcd)

theorem pow_dvd_of_mul_eq_pow {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} {b : α} {c : α} {d₁ : α} {d₂ : α} (ha : a ≠ 0) (hab : gcd a b = 1) {k : ℕ} (h : a * b = c ^ k) (hc : c = d₁ * d₂) (hd₁ : d₁ ∣ a) : d₁ ^ k ≠ 0 ∧ d₁ ^ k ∣ a := sorry

theorem exists_associated_pow_of_mul_eq_pow {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} {b : α} {c : α} (hab : gcd a b = 1) {k : ℕ} (h : a * b = c ^ k) : ∃ (d : α), associated (d ^ k) a := sorry

theorem lcm_dvd_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} {b : α} {c : α} : lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c := sorry

theorem dvd_lcm_left {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) : a ∣ lcm a b :=
  and.left (iff.mp lcm_dvd_iff (dvd_refl (lcm a b)))

theorem dvd_lcm_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) : b ∣ lcm a b :=
  and.right (iff.mp lcm_dvd_iff (dvd_refl (lcm a b)))

theorem lcm_dvd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} {b : α} {c : α} (hab : a ∣ b) (hcb : c ∣ b) : lcm a c ∣ b :=
  iff.mpr lcm_dvd_iff { left := hab, right := hcb }

@[simp] theorem lcm_eq_zero_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) : lcm a b = 0 ↔ a = 0 ∨ b = 0 := sorry

@[simp] theorem normalize_lcm {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) : coe_fn normalize (lcm a b) = lcm a b := sorry

theorem lcm_comm {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) : lcm a b = lcm b a :=
  dvd_antisymm_of_normalize_eq (normalize_lcm a b) (normalize_lcm b a) (lcm_dvd (dvd_lcm_right b a) (dvd_lcm_left b a))
    (lcm_dvd (dvd_lcm_right a b) (dvd_lcm_left a b))

theorem lcm_assoc {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (m : α) (n : α) (k : α) : lcm (lcm m n) k = lcm m (lcm n k) := sorry

protected instance gcd_monoid.lcm.is_commutative {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] : is_commutative α lcm :=
  is_commutative.mk lcm_comm

protected instance gcd_monoid.lcm.is_associative {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] : is_associative α lcm :=
  is_associative.mk lcm_assoc

theorem lcm_eq_normalize {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} {b : α} {c : α} (habc : lcm a b ∣ c) (hcab : c ∣ lcm a b) : lcm a b = coe_fn normalize c :=
  normalize_lcm a b ▸ normalize_eq_normalize habc hcab

theorem lcm_dvd_lcm {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} {b : α} {c : α} {d : α} (hab : a ∣ b) (hcd : c ∣ d) : lcm a c ∣ lcm b d :=
  lcm_dvd (dvd.trans hab (dvd_lcm_left b d)) (dvd.trans hcd (dvd_lcm_right b d))

@[simp] theorem lcm_units_coe_left {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (u : units α) (a : α) : lcm (↑u) a = coe_fn normalize a :=
  lcm_eq_normalize (lcm_dvd units.coe_dvd (dvd_refl a)) (dvd_lcm_right (↑u) a)

@[simp] theorem lcm_units_coe_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (u : units α) : lcm a ↑u = coe_fn normalize a :=
  Eq.trans (lcm_comm a ↑u) (lcm_units_coe_left u a)

@[simp] theorem lcm_one_left {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) : lcm 1 a = coe_fn normalize a :=
  lcm_units_coe_left 1 a

@[simp] theorem lcm_one_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) : lcm a 1 = coe_fn normalize a :=
  lcm_units_coe_right a 1

@[simp] theorem lcm_same {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) : lcm a a = coe_fn normalize a :=
  lcm_eq_normalize (lcm_dvd (dvd_refl a) (dvd_refl a)) (dvd_lcm_left a a)

@[simp] theorem lcm_eq_one_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) : lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1 := sorry

@[simp] theorem lcm_mul_left {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) (c : α) : lcm (a * b) (a * c) = coe_fn normalize a * lcm b c := sorry

@[simp] theorem lcm_mul_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) (c : α) : lcm (b * a) (c * a) = lcm b c * coe_fn normalize a := sorry

theorem lcm_eq_left_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) (h : coe_fn normalize a = a) : lcm a b = a ↔ b ∣ a := sorry

theorem lcm_eq_right_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (b : α) (h : coe_fn normalize b = b) : lcm a b = b ↔ a ∣ b := sorry

theorem lcm_dvd_lcm_mul_left {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (m : α) (n : α) (k : α) : lcm m n ∣ lcm (k * m) n :=
  lcm_dvd_lcm (dvd_mul_left m k) (dvd_refl n)

theorem lcm_dvd_lcm_mul_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (m : α) (n : α) (k : α) : lcm m n ∣ lcm (m * k) n :=
  lcm_dvd_lcm (dvd_mul_right m k) (dvd_refl n)

theorem lcm_dvd_lcm_mul_left_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (m : α) (n : α) (k : α) : lcm m n ∣ lcm m (k * n) :=
  lcm_dvd_lcm (dvd_refl m) (dvd_mul_left n k)

theorem lcm_dvd_lcm_mul_right_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (m : α) (n : α) (k : α) : lcm m n ∣ lcm m (n * k) :=
  lcm_dvd_lcm (dvd_refl m) (dvd_mul_right n k)

theorem lcm_eq_of_associated_left {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {m : α} {n : α} (h : associated m n) (k : α) : lcm m k = lcm n k :=
  dvd_antisymm_of_normalize_eq (normalize_lcm m k) (normalize_lcm n k) (lcm_dvd_lcm (dvd_of_associated h) (dvd_refl k))
    (lcm_dvd_lcm (dvd_of_associated (associated.symm h)) (dvd_refl k))

theorem lcm_eq_of_associated_right {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {m : α} {n : α} (h : associated m n) (k : α) : lcm k m = lcm k n :=
  dvd_antisymm_of_normalize_eq (normalize_lcm k m) (normalize_lcm k n) (lcm_dvd_lcm (dvd_refl k) (dvd_of_associated h))
    (lcm_dvd_lcm (dvd_refl k) (dvd_of_associated (associated.symm h)))

namespace gcd_monoid


theorem prime_of_irreducible {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {x : α} (hi : irreducible x) : prime x := sorry

theorem irreducible_iff_prime {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {p : α} : irreducible p ↔ prime p :=
  { mp := prime_of_irreducible, mpr := irreducible_of_prime }

end gcd_monoid


theorem units_eq_one {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique (units α)] (u : units α) : u = 1 :=
  subsingleton.elim u 1

protected instance normalization_monoid_of_unique_units {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique (units α)] [nontrivial α] : normalization_monoid α :=
  normalization_monoid.mk (fun (x : α) => 1) sorry sorry sorry

@[simp] theorem norm_unit_eq_one {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique (units α)] [nontrivial α] (x : α) : norm_unit x = 1 :=
  rfl

@[simp] theorem normalize_eq {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique (units α)] [nontrivial α] (x : α) : coe_fn normalize x = x :=
  mul_one x

theorem gcd_eq_of_dvd_sub_right {α : Type u_1} [integral_domain α] [gcd_monoid α] {a : α} {b : α} {c : α} (h : a ∣ b - c) : gcd a b = gcd a c := sorry

theorem gcd_eq_of_dvd_sub_left {α : Type u_1} [integral_domain α] [gcd_monoid α] {a : α} {b : α} {c : α} (h : a ∣ b - c) : gcd b a = gcd c a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd b a = gcd c a)) (gcd_comm b a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (gcd a b = gcd c a)) (gcd_comm c a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (gcd a b = gcd a c)) (gcd_eq_of_dvd_sub_right h))) (Eq.refl (gcd a c))))

/-- Define `normalization_monoid` on a structure from a `monoid_hom` inverse to `associates.mk`. -/
def normalization_monoid_of_monoid_hom_right_inverse {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [DecidableEq α] (f : associates α →* α) (hinv : function.right_inverse (⇑f) associates.mk) : normalization_monoid α :=
  normalization_monoid.mk (fun (a : α) => ite (a = 0) 1 (classical.some sorry)) sorry sorry sorry

/-- Define `gcd_monoid` on a structure just from the `gcd` and its properties. -/
def gcd_monoid_of_gcd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] [DecidableEq α] (gcd : α → α → α) (gcd_dvd_left : ∀ (a b : α), gcd a b ∣ a) (gcd_dvd_right : ∀ (a b : α), gcd a b ∣ b) (dvd_gcd : ∀ {a b c : α}, a ∣ c → a ∣ b → a ∣ gcd c b) (normalize_gcd : ∀ (a b : α), coe_fn normalize (gcd a b) = gcd a b) : gcd_monoid α :=
  gcd_monoid.mk norm_unit sorry sorry sorry gcd (fun (a b : α) => ite (a = 0) 0 (classical.some sorry)) gcd_dvd_left
    gcd_dvd_right sorry normalize_gcd sorry sorry sorry

/-- Define `gcd_monoid` on a structure just from the `lcm` and its properties. -/
def gcd_monoid_of_lcm {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] [DecidableEq α] (lcm : α → α → α) (dvd_lcm_left : ∀ (a b : α), a ∣ lcm a b) (dvd_lcm_right : ∀ (a b : α), b ∣ lcm a b) (lcm_dvd : ∀ {a b c : α}, c ∣ a → b ∣ a → lcm c b ∣ a) (normalize_lcm : ∀ (a b : α), coe_fn normalize (lcm a b) = lcm a b) : gcd_monoid α :=
  let exists_gcd : ∀ (a b : α), lcm a b ∣ coe_fn normalize (a * b) := sorry;
  gcd_monoid.mk norm_unit sorry sorry sorry
    (fun (a b : α) =>
      ite (a = 0) (coe_fn normalize b) (ite (b = 0) (coe_fn normalize a) (classical.some (exists_gcd a b))))
    lcm sorry sorry sorry sorry sorry sorry sorry

/-- Define a `gcd_monoid` structure on a monoid just from the existence of a `gcd`. -/
def gcd_monoid_of_exists_gcd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] [DecidableEq α] (h : ∀ (a b : α), ∃ (c : α), ∀ (d : α), d ∣ a ∧ d ∣ b ↔ d ∣ c) : gcd_monoid α :=
  gcd_monoid_of_gcd (fun (a b : α) => coe_fn normalize (classical.some (h a b))) sorry sorry sorry sorry

/-- Define a `gcd_monoid` structure on a monoid just from the existence of an `lcm`. -/
def gcd_monoid_of_exists_lcm {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α] [DecidableEq α] (h : ∀ (a b : α), ∃ (c : α), ∀ (d : α), a ∣ d ∧ b ∣ d ↔ c ∣ d) : gcd_monoid α :=
  gcd_monoid_of_lcm (fun (a b : α) => coe_fn normalize (classical.some (h a b))) sorry sorry sorry sorry

