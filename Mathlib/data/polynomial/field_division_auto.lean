/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.ring_division
import Mathlib.data.polynomial.derivative
import Mathlib.algebra.gcd_monoid
import Mathlib.PostPort

universes u y v u_1 

namespace Mathlib

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $ R[X] $

-/

namespace polynomial


protected instance normalization_monoid {R : Type u} [integral_domain R] [normalization_monoid R] :
    normalization_monoid (polynomial R) :=
  normalization_monoid.mk
    (fun (p : polynomial R) =>
      units.mk (coe_fn C ↑(norm_unit (leading_coeff p))) (coe_fn C ↑(norm_unit (leading_coeff p)⁻¹))
        sorry sorry)
    sorry sorry sorry

@[simp] theorem coe_norm_unit {R : Type u} [integral_domain R] [normalization_monoid R]
    {p : polynomial R} : ↑(norm_unit p) = coe_fn C ↑(norm_unit (leading_coeff p)) :=
  sorry

theorem leading_coeff_normalize {R : Type u} [integral_domain R] [normalization_monoid R]
    (p : polynomial R) : leading_coeff (coe_fn normalize p) = coe_fn normalize (leading_coeff p) :=
  sorry

theorem is_unit_iff_degree_eq_zero {R : Type u} [field R] {p : polynomial R} :
    is_unit p ↔ degree p = 0 :=
  sorry

theorem degree_pos_of_ne_zero_of_nonunit {R : Type u} [field R] {p : polynomial R} (hp0 : p ≠ 0)
    (hp : ¬is_unit p) : 0 < degree p :=
  sorry

theorem monic_mul_leading_coeff_inv {R : Type u} [field R] {p : polynomial R} (h : p ≠ 0) :
    monic (p * coe_fn C (leading_coeff p⁻¹)) :=
  sorry

theorem degree_mul_leading_coeff_inv {R : Type u} [field R] {q : polynomial R} (p : polynomial R)
    (h : q ≠ 0) : degree (p * coe_fn C (leading_coeff q⁻¹)) = degree p :=
  sorry

theorem irreducible_of_monic {R : Type u} [field R] {p : polynomial R} (hp1 : monic p)
    (hp2 : p ≠ 1) :
    irreducible p ↔ ∀ (f g : polynomial R), monic f → monic g → f * g = p → f = 1 ∨ g = 1 :=
  sorry

/-- Division of polynomials. See polynomial.div_by_monic for more details.-/
def div {R : Type u} [field R] (p : polynomial R) (q : polynomial R) : polynomial R :=
  coe_fn C (leading_coeff q⁻¹) * (p /ₘ (q * coe_fn C (leading_coeff q⁻¹)))

/-- Remainder of polynomial division, see the lemma `quotient_mul_add_remainder_eq_aux`.
See polynomial.mod_by_monic for more details. -/
def mod {R : Type u} [field R] (p : polynomial R) (q : polynomial R) : polynomial R :=
  p %ₘ (q * coe_fn C (leading_coeff q⁻¹))

protected instance has_div {R : Type u} [field R] : Div (polynomial R) := { div := div }

protected instance has_mod {R : Type u} [field R] : Mod (polynomial R) := { mod := mod }

theorem div_def {R : Type u} [field R] {p : polynomial R} {q : polynomial R} :
    p / q = coe_fn C (leading_coeff q⁻¹) * (p /ₘ (q * coe_fn C (leading_coeff q⁻¹))) :=
  rfl

theorem mod_def {R : Type u} [field R] {p : polynomial R} {q : polynomial R} :
    p % q = p %ₘ (q * coe_fn C (leading_coeff q⁻¹)) :=
  rfl

theorem mod_by_monic_eq_mod {R : Type u} [field R] {q : polynomial R} (p : polynomial R)
    (hq : monic q) : p %ₘ q = p % q :=
  sorry

theorem div_by_monic_eq_div {R : Type u} [field R] {q : polynomial R} (p : polynomial R)
    (hq : monic q) : p /ₘ q = p / q :=
  sorry

theorem mod_X_sub_C_eq_C_eval {R : Type u} [field R] (p : polynomial R) (a : R) :
    p % (X - coe_fn C a) = coe_fn C (eval a p) :=
  mod_by_monic_eq_mod p (monic_X_sub_C a) ▸ mod_by_monic_X_sub_C_eq_C_eval p a

theorem mul_div_eq_iff_is_root {R : Type u} {a : R} [field R] {p : polynomial R} :
    (X - coe_fn C a) * (p / (X - coe_fn C a)) = p ↔ is_root p a :=
  div_by_monic_eq_div p (monic_X_sub_C a) ▸ mul_div_by_monic_eq_iff_is_root

protected instance euclidean_domain {R : Type u} [field R] : euclidean_domain (polynomial R) :=
  euclidean_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub
    sorry sorry comm_ring.mul sorry comm_ring.one sorry sorry sorry sorry sorry sorry Div.div sorry
    Mod.mod quotient_mul_add_remainder_eq_aux (fun (p q : polynomial R) => degree p < degree q)
    sorry sorry sorry

theorem mod_eq_self_iff {R : Type u} [field R] {p : polynomial R} {q : polynomial R} (hq0 : q ≠ 0) :
    p % q = p ↔ degree p < degree q :=
  sorry

theorem div_eq_zero_iff {R : Type u} [field R] {p : polynomial R} {q : polynomial R} (hq0 : q ≠ 0) :
    p / q = 0 ↔ degree p < degree q :=
  sorry

theorem degree_add_div {R : Type u} [field R] {p : polynomial R} {q : polynomial R} (hq0 : q ≠ 0)
    (hpq : degree q ≤ degree p) : degree q + degree (p / q) = degree p :=
  sorry

theorem degree_div_le {R : Type u} [field R] (p : polynomial R) (q : polynomial R) :
    degree (p / q) ≤ degree p :=
  sorry

theorem degree_div_lt {R : Type u} [field R] {p : polynomial R} {q : polynomial R} (hp : p ≠ 0)
    (hq : 0 < degree q) : degree (p / q) < degree p :=
  sorry

@[simp] theorem degree_map {R : Type u} {k : Type y} [field R] [field k] (p : polynomial R)
    (f : R →+* k) : degree (map f p) = degree p :=
  degree_map_eq_of_injective (ring_hom.injective f) p

@[simp] theorem nat_degree_map {R : Type u} {k : Type y} [field R] {p : polynomial R} [field k]
    (f : R →+* k) : nat_degree (map f p) = nat_degree p :=
  nat_degree_eq_of_degree_eq (degree_map p f)

@[simp] theorem leading_coeff_map {R : Type u} {k : Type y} [field R] {p : polynomial R} [field k]
    (f : R →+* k) : leading_coeff (map f p) = coe_fn f (leading_coeff p) :=
  sorry

theorem monic_map_iff {R : Type u} {k : Type y} [field R] [field k] {f : R →+* k}
    {p : polynomial R} : monic (map f p) ↔ monic p :=
  sorry

theorem is_unit_map {R : Type u} {k : Type y} [field R] {p : polynomial R} [field k] (f : R →+* k) :
    is_unit (map f p) ↔ is_unit p :=
  sorry

theorem map_div {R : Type u} {k : Type y} [field R] {p : polynomial R} {q : polynomial R} [field k]
    (f : R →+* k) : map f (p / q) = map f p / map f q :=
  sorry

theorem map_mod {R : Type u} {k : Type y} [field R] {p : polynomial R} {q : polynomial R} [field k]
    (f : R →+* k) : map f (p % q) = map f p % map f q :=
  sorry

theorem gcd_map {R : Type u} {k : Type y} [field R] {p : polynomial R} {q : polynomial R} [field k]
    (f : R →+* k) : euclidean_domain.gcd (map f p) (map f q) = map f (euclidean_domain.gcd p q) :=
  sorry

theorem eval₂_gcd_eq_zero {R : Type u} {k : Type y} [field R] [comm_semiring k] {ϕ : R →+* k}
    {f : polynomial R} {g : polynomial R} {α : k} (hf : eval₂ ϕ α f = 0) (hg : eval₂ ϕ α g = 0) :
    eval₂ ϕ α (euclidean_domain.gcd f g) = 0 :=
  sorry

theorem eval_gcd_eq_zero {R : Type u} [field R] {f : polynomial R} {g : polynomial R} {α : R}
    (hf : eval α f = 0) (hg : eval α g = 0) : eval α (euclidean_domain.gcd f g) = 0 :=
  eval₂_gcd_eq_zero hf hg

theorem root_left_of_root_gcd {R : Type u} {k : Type y} [field R] [comm_semiring k] {ϕ : R →+* k}
    {f : polynomial R} {g : polynomial R} {α : k} (hα : eval₂ ϕ α (euclidean_domain.gcd f g) = 0) :
    eval₂ ϕ α f = 0 :=
  sorry

theorem root_right_of_root_gcd {R : Type u} {k : Type y} [field R] [comm_semiring k] {ϕ : R →+* k}
    {f : polynomial R} {g : polynomial R} {α : k} (hα : eval₂ ϕ α (euclidean_domain.gcd f g) = 0) :
    eval₂ ϕ α g = 0 :=
  sorry

theorem root_gcd_iff_root_left_right {R : Type u} {k : Type y} [field R] [comm_semiring k]
    {ϕ : R →+* k} {f : polynomial R} {g : polynomial R} {α : k} :
    eval₂ ϕ α (euclidean_domain.gcd f g) = 0 ↔ eval₂ ϕ α f = 0 ∧ eval₂ ϕ α g = 0 :=
  sorry

theorem is_root_gcd_iff_is_root_left_right {R : Type u} [field R] {f : polynomial R}
    {g : polynomial R} {α : R} : is_root (euclidean_domain.gcd f g) α ↔ is_root f α ∧ is_root g α :=
  root_gcd_iff_root_left_right

theorem is_coprime_map {R : Type u} {k : Type y} [field R] {p : polynomial R} {q : polynomial R}
    [field k] (f : R →+* k) : is_coprime (map f p) (map f q) ↔ is_coprime p q :=
  sorry

@[simp] theorem map_eq_zero {R : Type u} {S : Type v} [field R] {p : polynomial R} [semiring S]
    [nontrivial S] (f : R →+* S) : map f p = 0 ↔ p = 0 :=
  sorry

theorem map_ne_zero {R : Type u} {S : Type v} [field R] {p : polynomial R} [semiring S]
    [nontrivial S] {f : R →+* S} (hp : p ≠ 0) : map f p ≠ 0 :=
  mt (iff.mp (map_eq_zero f)) hp

theorem mem_roots_map {R : Type u} {k : Type y} [field R] {p : polynomial R} [field k] {f : R →+* k}
    {x : k} (hp : p ≠ 0) : x ∈ roots (map f p) ↔ eval₂ f x p = 0 :=
  sorry

theorem exists_root_of_degree_eq_one {R : Type u} [field R] {p : polynomial R} (h : degree p = 1) :
    ∃ (x : R), is_root p x :=
  sorry

theorem coeff_inv_units {R : Type u} [field R] (u : units (polynomial R)) (n : ℕ) :
    coeff (↑u) n⁻¹ = coeff (↑(u⁻¹)) n :=
  sorry

theorem monic_normalize {R : Type u} [field R] {p : polynomial R} (hp0 : p ≠ 0) :
    monic (coe_fn normalize p) :=
  sorry

theorem coe_norm_unit_of_ne_zero {R : Type u} [field R] {p : polynomial R} (hp : p ≠ 0) :
    ↑(norm_unit p) = coe_fn C (leading_coeff p⁻¹) :=
  sorry

theorem normalize_monic {R : Type u} [field R] {p : polynomial R} (h : monic p) :
    coe_fn normalize p = p :=
  sorry

theorem map_dvd_map' {R : Type u} {k : Type y} [field R] [field k] (f : R →+* k) {x : polynomial R}
    {y : polynomial R} : map f x ∣ map f y ↔ x ∣ y :=
  sorry

theorem degree_normalize {R : Type u} [field R] {p : polynomial R} :
    degree (coe_fn normalize p) = degree p :=
  sorry

theorem prime_of_degree_eq_one {R : Type u} [field R] {p : polynomial R} (hp1 : degree p = 1) :
    prime p :=
  sorry

theorem irreducible_of_degree_eq_one {R : Type u} [field R] {p : polynomial R}
    (hp1 : degree p = 1) : irreducible p :=
  irreducible_of_prime (prime_of_degree_eq_one hp1)

theorem not_irreducible_C {R : Type u} [field R] (x : R) : ¬irreducible (coe_fn C x) := sorry

theorem degree_pos_of_irreducible {R : Type u} [field R] {p : polynomial R} (hp : irreducible p) :
    0 < degree p :=
  lt_of_not_ge
    fun (hp0 : 0 ≥ degree p) =>
      (fun (this : p = coe_fn C (coeff p 0)) => not_irreducible_C (coeff p 0) (this ▸ hp))
        (eq_C_of_degree_le_zero hp0)

theorem pairwise_coprime_X_sub {α : Type u} [field α] {I : Type v} {s : I → α}
    (H : function.injective s) : pairwise (is_coprime on fun (i : I) => X - coe_fn C (s i)) :=
  sorry

/-- If `f` is a polynomial over a field, and `a : K` satisfies `f' a ≠ 0`,
then `f / (X - a)` is coprime with `X - a`.
Note that we do not assume `f a = 0`, because `f / (X - a) = (f - f a) / (X - a)`. -/
theorem is_coprime_of_is_root_of_eval_derivative_ne_zero {K : Type u_1} [field K] (f : polynomial K)
    (a : K) (hf' : eval a (coe_fn derivative f) ≠ 0) :
    is_coprime (X - coe_fn C a) (f /ₘ (X - coe_fn C a)) :=
  sorry

theorem prod_multiset_root_eq_finset_root {R : Type u} [field R] {p : polynomial R}
    (hzero : p ≠ 0) :
    multiset.prod (multiset.map (fun (a : R) => X - coe_fn C a) (roots p)) =
        finset.prod (multiset.to_finset (roots p))
          fun (a : R) => (fun (a : R) => (X - coe_fn C a) ^ root_multiplicity a p) a :=
  sorry

/-- The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`. -/
theorem prod_multiset_X_sub_C_dvd {R : Type u} [field R] (p : polynomial R) :
    multiset.prod (multiset.map (fun (a : R) => X - coe_fn C a) (roots p)) ∣ p :=
  sorry

theorem roots_C_mul {R : Type u} [field R] (p : polynomial R) {a : R} (hzero : a ≠ 0) :
    roots (coe_fn C a * p) = roots p :=
  sorry

theorem roots_normalize {R : Type u} [field R] {p : polynomial R} :
    roots (coe_fn normalize p) = roots p :=
  sorry

end Mathlib