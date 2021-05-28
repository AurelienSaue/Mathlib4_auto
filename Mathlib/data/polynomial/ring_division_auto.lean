/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker, Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.polynomial.basic
import Mathlib.data.polynomial.div
import Mathlib.data.polynomial.algebra_map
import Mathlib.data.set.finite
import PostPort

universes u v u_1 

namespace Mathlib

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $ R[X] $

-/

namespace polynomial


theorem nat_degree_pos_of_aeval_root {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] [algebra R S] {p : polynomial R} (hp : p ≠ 0) {z : S} (hz : coe_fn (aeval z) p = 0) (inj : ∀ (x : R), coe_fn (algebra_map R S) x = 0 → x = 0) : 0 < nat_degree p :=
  nat_degree_pos_of_eval₂_root hp (algebra_map R S) hz inj

theorem degree_pos_of_aeval_root {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] [algebra R S] {p : polynomial R} (hp : p ≠ 0) {z : S} (hz : coe_fn (aeval z) p = 0) (inj : ∀ (x : R), coe_fn (algebra_map R S) x = 0 → x = 0) : 0 < degree p :=
  iff.mp nat_degree_pos_iff_degree_pos (nat_degree_pos_of_aeval_root hp hz inj)

theorem aeval_mod_by_monic_eq_self_of_root {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] [algebra R S] {p : polynomial R} {q : polynomial R} (hq : monic q) {x : S} (hx : coe_fn (aeval x) q = 0) : coe_fn (aeval x) (p %ₘ q) = coe_fn (aeval x) p :=
  eval₂_mod_by_monic_eq_self_of_root hq hx

protected instance integral_domain {R : Type u} [integral_domain R] : integral_domain (polynomial R) :=
  integral_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul
    sorry comm_ring.one sorry sorry sorry sorry sorry sorry sorry

theorem nat_degree_mul {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} (hp : p ≠ 0) (hq : q ≠ 0) : nat_degree (p * q) = nat_degree p + nat_degree q := sorry

@[simp] theorem nat_degree_pow {R : Type u} [integral_domain R] (p : polynomial R) (n : ℕ) : nat_degree (p ^ n) = n * nat_degree p := sorry

theorem root_mul {R : Type u} {a : R} [integral_domain R] {p : polynomial R} {q : polynomial R} : is_root (p * q) a ↔ is_root p a ∨ is_root q a := sorry

theorem root_or_root_of_root_mul {R : Type u} {a : R} [integral_domain R] {p : polynomial R} {q : polynomial R} (h : is_root (p * q) a) : is_root p a ∨ is_root q a :=
  iff.mp root_mul h

theorem degree_le_mul_left {R : Type u} [integral_domain R] {q : polynomial R} (p : polynomial R) (hq : q ≠ 0) : degree p ≤ degree (p * q) := sorry

theorem nat_degree_le_of_dvd {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} (h1 : p ∣ q) (h2 : q ≠ 0) : nat_degree p ≤ nat_degree q := sorry

theorem degree_eq_zero_of_is_unit {R : Type u} [integral_domain R] {p : polynomial R} (h : is_unit p) : degree p = 0 := sorry

@[simp] theorem degree_coe_units {R : Type u} [integral_domain R] (u : units (polynomial R)) : degree ↑u = 0 :=
  degree_eq_zero_of_is_unit (Exists.intro u rfl)

theorem prime_X_sub_C {R : Type u} [integral_domain R] {r : R} : prime (X - coe_fn C r) := sorry

theorem prime_X {R : Type u} [integral_domain R] : prime X := sorry

theorem prime_of_degree_eq_one_of_monic {R : Type u} [integral_domain R] {p : polynomial R} (hp1 : degree p = 1) (hm : monic p) : prime p := sorry

theorem irreducible_X_sub_C {R : Type u} [integral_domain R] (r : R) : irreducible (X - coe_fn C r) :=
  irreducible_of_prime prime_X_sub_C

theorem irreducible_X {R : Type u} [integral_domain R] : irreducible X :=
  irreducible_of_prime prime_X

theorem irreducible_of_degree_eq_one_of_monic {R : Type u} [integral_domain R] {p : polynomial R} (hp1 : degree p = 1) (hm : monic p) : irreducible p :=
  irreducible_of_prime (prime_of_degree_eq_one_of_monic hp1 hm)

theorem eq_of_monic_of_associated {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} (hp : monic p) (hq : monic q) (hpq : associated p q) : p = q := sorry

@[simp] theorem root_multiplicity_zero {R : Type u} [integral_domain R] {x : R} : root_multiplicity x 0 = 0 :=
  dif_pos rfl

theorem root_multiplicity_eq_zero {R : Type u} [integral_domain R] {p : polynomial R} {x : R} (h : ¬is_root p x) : root_multiplicity x p = 0 := sorry

theorem root_multiplicity_pos {R : Type u} [integral_domain R] {p : polynomial R} (hp : p ≠ 0) {x : R} : 0 < root_multiplicity x p ↔ is_root p x := sorry

theorem root_multiplicity_mul {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} {x : R} (hpq : p * q ≠ 0) : root_multiplicity x (p * q) = root_multiplicity x p + root_multiplicity x q := sorry

theorem root_multiplicity_X_sub_C_self {R : Type u} [integral_domain R] {x : R} : root_multiplicity x (X - coe_fn C x) = 1 := sorry

theorem root_multiplicity_X_sub_C {R : Type u} [integral_domain R] {x : R} {y : R} : root_multiplicity x (X - coe_fn C y) = ite (x = y) 1 0 := sorry

/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
theorem root_multiplicity_X_sub_C_pow {R : Type u} [integral_domain R] (a : R) (n : ℕ) : root_multiplicity a ((X - coe_fn C a) ^ n) = n := sorry

/-- If `(X - a) ^ n` divides a polynomial `p` then the multiplicity of `a` as root of `p` is at
least `n`. -/
theorem root_multiplicity_of_dvd {R : Type u} [integral_domain R] {p : polynomial R} {a : R} {n : ℕ} (hzero : p ≠ 0) (h : (X - coe_fn C a) ^ n ∣ p) : n ≤ root_multiplicity a p := sorry

/-- The multiplicity of `p + q` is at least the minimum of the multiplicities. -/
theorem root_multiplicity_add {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} (a : R) (hzero : p + q ≠ 0) : min (root_multiplicity a p) (root_multiplicity a q) ≤ root_multiplicity a (p + q) :=
  root_multiplicity_of_dvd hzero (min_pow_dvd_add (pow_root_multiplicity_dvd p a) (pow_root_multiplicity_dvd q a))

theorem exists_multiset_roots {R : Type u} [integral_domain R] {p : polynomial R} (hp : p ≠ 0) : ∃ (s : multiset R), ↑(coe_fn multiset.card s) ≤ degree p ∧ ∀ (a : R), multiset.count a s = root_multiplicity a p := sorry

/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
def roots {R : Type u} [integral_domain R] (p : polynomial R) : multiset R :=
  dite (p = 0) (fun (h : p = 0) => ∅) fun (h : ¬p = 0) => classical.some (exists_multiset_roots h)

@[simp] theorem roots_zero {R : Type u} [integral_domain R] : roots 0 = 0 :=
  dif_pos rfl

theorem card_roots {R : Type u} [integral_domain R] {p : polynomial R} (hp0 : p ≠ 0) : ↑(coe_fn multiset.card (roots p)) ≤ degree p := sorry

theorem card_roots' {R : Type u} [integral_domain R] {p : polynomial R} (hp0 : p ≠ 0) : coe_fn multiset.card (roots p) ≤ nat_degree p :=
  iff.mp with_bot.coe_le_coe (le_trans (card_roots hp0) (le_of_eq (degree_eq_nat_degree hp0)))

theorem card_roots_sub_C {R : Type u} [integral_domain R] {p : polynomial R} {a : R} (hp0 : 0 < degree p) : ↑(coe_fn multiset.card (roots (p - coe_fn C a))) ≤ degree p := sorry

theorem card_roots_sub_C' {R : Type u} [integral_domain R] {p : polynomial R} {a : R} (hp0 : 0 < degree p) : coe_fn multiset.card (roots (p - coe_fn C a)) ≤ nat_degree p := sorry

@[simp] theorem count_roots {R : Type u} {a : R} [integral_domain R] {p : polynomial R} (hp : p ≠ 0) : multiset.count a (roots p) = root_multiplicity a p := sorry

@[simp] theorem mem_roots {R : Type u} {a : R} [integral_domain R] {p : polynomial R} (hp : p ≠ 0) : a ∈ roots p ↔ is_root p a := sorry

theorem eq_zero_of_infinite_is_root {R : Type u} [integral_domain R] (p : polynomial R) (h : set.infinite (set_of fun (x : R) => is_root p x)) : p = 0 := sorry

theorem eq_of_infinite_eval_eq {R : Type u_1} [integral_domain R] (p : polynomial R) (q : polynomial R) (h : set.infinite (set_of fun (x : R) => eval x p = eval x q)) : p = q := sorry

theorem roots_mul {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} (hpq : p * q ≠ 0) : roots (p * q) = roots p + roots q := sorry

@[simp] theorem mem_roots_sub_C {R : Type u} [integral_domain R] {p : polynomial R} {a : R} {x : R} (hp0 : 0 < degree p) : x ∈ roots (p - coe_fn C a) ↔ eval x p = a := sorry

@[simp] theorem roots_X_sub_C {R : Type u} [integral_domain R] (r : R) : roots (X - coe_fn C r) = r ::ₘ 0 := sorry

@[simp] theorem roots_C {R : Type u} [integral_domain R] (x : R) : roots (coe_fn C x) = 0 := sorry

@[simp] theorem roots_one {R : Type u} [integral_domain R] : roots 1 = ∅ :=
  roots_C 1

theorem roots_list_prod {R : Type u} [integral_domain R] (L : List (polynomial R)) : (∀ (p : polynomial R), p ∈ L → p ≠ 0) → roots (list.prod L) = multiset.bind (↑L) roots := sorry

theorem roots_multiset_prod {R : Type u} [integral_domain R] (m : multiset (polynomial R)) : (∀ (p : polynomial R), p ∈ m → p ≠ 0) → roots (multiset.prod m) = multiset.bind m roots := sorry

theorem roots_prod {R : Type u} [integral_domain R] {ι : Type u_1} (f : ι → polynomial R) (s : finset ι) : finset.prod s f ≠ 0 → roots (finset.prod s f) = multiset.bind (finset.val s) fun (i : ι) => roots (f i) := sorry

theorem roots_prod_X_sub_C {R : Type u} [integral_domain R] (s : finset R) : roots (finset.prod s fun (a : R) => X - coe_fn C a) = finset.val s := sorry

theorem card_roots_X_pow_sub_C {R : Type u} [integral_domain R] {n : ℕ} (hn : 0 < n) (a : R) : coe_fn multiset.card (roots (X ^ n - coe_fn C a)) ≤ n :=
  iff.mp with_bot.coe_le_coe (trans_rel_left LessEq (card_roots (X_pow_sub_C_ne_zero hn a)) (degree_X_pow_sub_C hn a))

/-- `nth_roots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nth_roots {R : Type u} [integral_domain R] (n : ℕ) (a : R) : multiset R :=
  roots (X ^ n - coe_fn C a)

@[simp] theorem mem_nth_roots {R : Type u} [integral_domain R] {n : ℕ} (hn : 0 < n) {a : R} {x : R} : x ∈ nth_roots n a ↔ x ^ n = a := sorry

@[simp] theorem nth_roots_zero {R : Type u} [integral_domain R] (r : R) : nth_roots 0 r = 0 := sorry

theorem card_nth_roots {R : Type u} [integral_domain R] (n : ℕ) (a : R) : coe_fn multiset.card (nth_roots n a) ≤ n := sorry

/-- The multiset `nth_roots ↑n (1 : R)` as a finset. -/
def nth_roots_finset (n : ℕ) (R : Type u_1) [integral_domain R] : finset R :=
  multiset.to_finset (nth_roots n 1)

@[simp] theorem mem_nth_roots_finset {R : Type u} [integral_domain R] {n : ℕ} (h : 0 < n) {x : R} : x ∈ nth_roots_finset n R ↔ x ^ n = 1 := sorry

theorem coeff_comp_degree_mul_degree {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} (hqd0 : nat_degree q ≠ 0) : coeff (comp p q) (nat_degree p * nat_degree q) = leading_coeff p * leading_coeff q ^ nat_degree p := sorry

theorem nat_degree_comp {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} : nat_degree (comp p q) = nat_degree p * nat_degree q := sorry

theorem leading_coeff_comp {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} (hq : nat_degree q ≠ 0) : leading_coeff (comp p q) = leading_coeff p * leading_coeff q ^ nat_degree p := sorry

theorem units_coeff_zero_smul {R : Type u} [integral_domain R] (c : units (polynomial R)) (p : polynomial R) : coeff (↑c) 0 • p = ↑c * p := sorry

@[simp] theorem nat_degree_coe_units {R : Type u} [integral_domain R] (u : units (polynomial R)) : nat_degree ↑u = 0 :=
  nat_degree_eq_of_degree_eq_some (degree_coe_units u)

theorem zero_of_eval_zero {R : Type u} [integral_domain R] [infinite R] (p : polynomial R) (h : ∀ (x : R), eval x p = 0) : p = 0 := sorry

theorem funext {R : Type u} [integral_domain R] [infinite R] {p : polynomial R} {q : polynomial R} (ext : ∀ (r : R), eval r p = eval r q) : p = q := sorry

theorem is_unit_iff {R : Type u} [integral_domain R] {f : polynomial R} : is_unit f ↔ ∃ (r : R), is_unit r ∧ coe_fn C r = f := sorry

theorem coeff_coe_units_zero_ne_zero {R : Type u} [integral_domain R] (u : units (polynomial R)) : coeff (↑u) 0 ≠ 0 := sorry

theorem degree_eq_degree_of_associated {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} (h : associated p q) : degree p = degree q := sorry

theorem degree_eq_one_of_irreducible_of_root {R : Type u} [integral_domain R] {p : polynomial R} (hi : irreducible p) {x : R} (hx : is_root p x) : degree p = 1 := sorry

/-- Division by a monic polynomial doesn't change the leading coefficient. -/
theorem leading_coeff_div_by_monic_of_monic {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} (hmonic : monic q) (hdegree : degree q ≤ degree p) : leading_coeff (p /ₘ q) = leading_coeff p := sorry

theorem eq_of_monic_of_dvd_of_nat_degree_le {R : Type u} [integral_domain R] {p : polynomial R} {q : polynomial R} (hp : monic p) (hq : monic q) (hdiv : p ∣ q) (hdeg : nat_degree q ≤ nat_degree p) : q = p := sorry

theorem is_unit_of_is_unit_leading_coeff_of_is_unit_map {R : Type u} {S : Type v} [semiring R] [integral_domain S] (φ : R →+* S) (f : polynomial R) (hf : is_unit (leading_coeff f)) (H : is_unit (map φ f)) : is_unit f := sorry

/--
A polynomial over an integral domain `R` is irreducible if it is monic and
  irreducible after mapping into an integral domain `S`.

A special case of this lemma is that a polynomial over `ℤ` is irreducible if
  it is monic and irreducible over `ℤ/pℤ` for some prime `p`.
-/
theorem monic.irreducible_of_irreducible_map {R : Type u} {S : Type v} [integral_domain R] [integral_domain S] (φ : R →+* S) (f : polynomial R) (h_mon : monic f) (h_irr : irreducible (map φ f)) : irreducible f := sorry

end polynomial


namespace is_integral_domain


/-- Lift evidence that `is_integral_domain R` to `is_integral_domain (polynomial R)`. -/
theorem polynomial {R : Type u_1} [comm_ring R] (h : is_integral_domain R) : is_integral_domain (polynomial R) :=
  integral_domain.to_is_integral_domain (polynomial R)

