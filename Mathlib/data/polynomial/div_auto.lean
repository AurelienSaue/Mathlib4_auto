/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.monic
import Mathlib.ring_theory.euclidean_domain
import Mathlib.ring_theory.multiplicity
import Mathlib.PostPort

universes u u_1 v 

namespace Mathlib

/-!
# Division of univariate polynomials

The main defs are `div_by_monic` and `mod_by_monic`.
The compatibility between these is given by `mod_by_monic_add_div`.
We also define `root_multiplicity`.
-/

namespace polynomial


/--
The coercion turning a `polynomial` into the function which reports the coefficient of a given
monomial `X^n`
-/
-- TODO we would like to completely remove this, but this requires fixing some proofs

def coeff_coe_to_fun {R : Type u} [semiring R] : has_coe_to_fun (polynomial R) :=
  finsupp.has_coe_to_fun

theorem apply_eq_coeff {R : Type u} {n : ℕ} [semiring R] {p : polynomial R} :
    coe_fn p n = coeff p n :=
  rfl

/-- `div_X p` return a polynomial `q` such that `q * X + C (p.coeff 0) = p`.
  It can be used in a semiring where the usual division algorithm is not possible -/
def div_X {R : Type u} [semiring R] (p : polynomial R) : polynomial R :=
  finsupp.mk
    (finset.mk
      (multiset.map (fun (n : ℕ) => n - 1)
        (finset.val (finset.filter (fun (_x : ℕ) => _x > 0) (finsupp.support p))))
      sorry)
    (fun (n : ℕ) => coeff p (n + 1)) sorry

theorem div_X_mul_X_add {R : Type u} [semiring R] (p : polynomial R) :
    div_X p * X + coe_fn C (coeff p 0) = p :=
  sorry

@[simp] theorem div_X_C {R : Type u} [semiring R] (a : R) : div_X (coe_fn C a) = 0 := sorry

theorem div_X_eq_zero_iff {R : Type u} [semiring R] {p : polynomial R} :
    div_X p = 0 ↔ p = coe_fn C (coeff p 0) :=
  sorry

theorem div_X_add {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} :
    div_X (p + q) = div_X p + div_X q :=
  sorry

theorem degree_div_X_lt {R : Type u} [semiring R] {p : polynomial R} (hp0 : p ≠ 0) :
    degree (div_X p) < degree p :=
  sorry

/-- An induction principle for polynomials, valued in Sort* instead of Prop. -/
def rec_on_horner {R : Type u} [semiring R] {M : polynomial R → Sort u_1} (p : polynomial R) :
    M 0 →
        ((p : polynomial R) → (a : R) → coeff p 0 = 0 → a ≠ 0 → M p → M (p + coe_fn C a)) →
          ((p : polynomial R) → p ≠ 0 → M p → M (p * X)) → M p :=
  sorry

theorem degree_pos_induction_on {R : Type u} [semiring R] {P : polynomial R → Prop}
    (p : polynomial R) (h0 : 0 < degree p) (hC : ∀ {a : R}, a ≠ 0 → P (coe_fn C a * X))
    (hX : ∀ {p : polynomial R}, 0 < degree p → P p → P (p * X))
    (hadd : ∀ {p : polynomial R} {a : R}, 0 < degree p → P p → P (p + coe_fn C a)) : P p :=
  sorry

theorem X_dvd_iff {α : Type u} [comm_semiring α] {f : polynomial α} : X ∣ f ↔ coeff f 0 = 0 := sorry

theorem multiplicity_finite_of_degree_pos_of_monic {R : Type u} [comm_semiring R] {p : polynomial R}
    {q : polynomial R} (hp : 0 < degree p) (hmp : monic p) (hq : q ≠ 0) : multiplicity.finite p q :=
  sorry

theorem div_wf_lemma {R : Type u} [ring R] {p : polynomial R} {q : polynomial R}
    (h : degree q ≤ degree p ∧ p ≠ 0) (hq : monic q) :
    degree (p - coe_fn C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) < degree p :=
  sorry

/-- See `div_by_monic`. -/
def div_mod_by_monic_aux {R : Type u} [ring R] (p : polynomial R) {q : polynomial R} :
    monic q → polynomial R × polynomial R :=
  sorry

/-- `div_by_monic` gives the quotient of `p` by a monic polynomial `q`. -/
def div_by_monic {R : Type u} [ring R] (p : polynomial R) (q : polynomial R) : polynomial R :=
  dite (monic q) (fun (hq : monic q) => prod.fst (div_mod_by_monic_aux p hq))
    fun (hq : ¬monic q) => 0

/-- `mod_by_monic` gives the remainder of `p` by a monic polynomial `q`. -/
def mod_by_monic {R : Type u} [ring R] (p : polynomial R) (q : polynomial R) : polynomial R :=
  dite (monic q) (fun (hq : monic q) => prod.snd (div_mod_by_monic_aux p hq))
    fun (hq : ¬monic q) => p

infixl:70 " /ₘ " => Mathlib.polynomial.div_by_monic

infixl:70 " %ₘ " => Mathlib.polynomial.mod_by_monic

theorem degree_mod_by_monic_lt {R : Type u} [ring R] (p : polynomial R) {q : polynomial R}
    (hq : monic q) (hq0 : q ≠ 0) : degree (p %ₘ q) < degree q :=
  sorry

@[simp] theorem zero_mod_by_monic {R : Type u} [ring R] (p : polynomial R) : 0 %ₘ p = 0 := sorry

@[simp] theorem zero_div_by_monic {R : Type u} [ring R] (p : polynomial R) : 0 /ₘ p = 0 := sorry

@[simp] theorem mod_by_monic_zero {R : Type u} [ring R] (p : polynomial R) : p %ₘ 0 = p := sorry

@[simp] theorem div_by_monic_zero {R : Type u} [ring R] (p : polynomial R) : p /ₘ 0 = 0 := sorry

theorem div_by_monic_eq_of_not_monic {R : Type u} [ring R] {q : polynomial R} (p : polynomial R)
    (hq : ¬monic q) : p /ₘ q = 0 :=
  dif_neg hq

theorem mod_by_monic_eq_of_not_monic {R : Type u} [ring R] {q : polynomial R} (p : polynomial R)
    (hq : ¬monic q) : p %ₘ q = p :=
  dif_neg hq

theorem mod_by_monic_eq_self_iff {R : Type u} [ring R] {p : polynomial R} {q : polynomial R}
    (hq : monic q) (hq0 : q ≠ 0) : p %ₘ q = p ↔ degree p < degree q :=
  sorry

theorem degree_mod_by_monic_le {R : Type u} [ring R] (p : polynomial R) {q : polynomial R}
    (hq : monic q) : degree (p %ₘ q) ≤ degree q :=
  sorry

theorem mod_by_monic_eq_sub_mul_div {R : Type u} [comm_ring R] (p : polynomial R) {q : polynomial R}
    (hq : monic q) : p %ₘ q = p - q * (p /ₘ q) :=
  sorry

theorem mod_by_monic_add_div {R : Type u} [comm_ring R] (p : polynomial R) {q : polynomial R}
    (hq : monic q) : p %ₘ q + q * (p /ₘ q) = p :=
  iff.mp eq_sub_iff_add_eq (mod_by_monic_eq_sub_mul_div p hq)

theorem div_by_monic_eq_zero_iff {R : Type u} [comm_ring R] {p : polynomial R} {q : polynomial R}
    (hq : monic q) (hq0 : q ≠ 0) : p /ₘ q = 0 ↔ degree p < degree q :=
  sorry

theorem degree_add_div_by_monic {R : Type u} [comm_ring R] {p : polynomial R} {q : polynomial R}
    (hq : monic q) (h : degree q ≤ degree p) : degree q + degree (p /ₘ q) = degree p :=
  sorry

theorem degree_div_by_monic_le {R : Type u} [comm_ring R] (p : polynomial R) (q : polynomial R) :
    degree (p /ₘ q) ≤ degree p :=
  sorry

theorem degree_div_by_monic_lt {R : Type u} [comm_ring R] (p : polynomial R) {q : polynomial R}
    (hq : monic q) (hp0 : p ≠ 0) (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
  sorry

theorem nat_degree_div_by_monic {R : Type u} [comm_ring R] (f : polynomial R) {g : polynomial R}
    (hg : monic g) : nat_degree (f /ₘ g) = nat_degree f - nat_degree g :=
  sorry

theorem div_mod_by_monic_unique {R : Type u} [comm_ring R] {f : polynomial R} {g : polynomial R}
    (q : polynomial R) (r : polynomial R) (hg : monic g) (h : r + g * q = f ∧ degree r < degree g) :
    f /ₘ g = q ∧ f %ₘ g = r :=
  sorry

theorem map_mod_div_by_monic {R : Type u} {S : Type v} [comm_ring R] {p : polynomial R}
    {q : polynomial R} [comm_ring S] (f : R →+* S) (hq : monic q) :
    map f (p /ₘ q) = map f p /ₘ map f q ∧ map f (p %ₘ q) = map f p %ₘ map f q :=
  sorry

theorem map_div_by_monic {R : Type u} {S : Type v} [comm_ring R] {p : polynomial R}
    {q : polynomial R} [comm_ring S] (f : R →+* S) (hq : monic q) :
    map f (p /ₘ q) = map f p /ₘ map f q :=
  and.left (map_mod_div_by_monic f hq)

theorem map_mod_by_monic {R : Type u} {S : Type v} [comm_ring R] {p : polynomial R}
    {q : polynomial R} [comm_ring S] (f : R →+* S) (hq : monic q) :
    map f (p %ₘ q) = map f p %ₘ map f q :=
  and.right (map_mod_div_by_monic f hq)

theorem dvd_iff_mod_by_monic_eq_zero {R : Type u} [comm_ring R] {p : polynomial R}
    {q : polynomial R} (hq : monic q) : p %ₘ q = 0 ↔ q ∣ p :=
  sorry

theorem map_dvd_map {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)
    (hf : function.injective ⇑f) {x : polynomial R} {y : polynomial R} (hx : monic x) :
    map f x ∣ map f y ↔ x ∣ y :=
  sorry

@[simp] theorem mod_by_monic_one {R : Type u} [comm_ring R] (p : polynomial R) : p %ₘ 1 = 0 := sorry

@[simp] theorem div_by_monic_one {R : Type u} [comm_ring R] (p : polynomial R) : p /ₘ 1 = p := sorry

@[simp] theorem mod_by_monic_X_sub_C_eq_C_eval {R : Type u} [comm_ring R] (p : polynomial R)
    (a : R) : p %ₘ (X - coe_fn C a) = coe_fn C (eval a p) :=
  sorry

theorem mul_div_by_monic_eq_iff_is_root {R : Type u} {a : R} [comm_ring R] {p : polynomial R} :
    (X - coe_fn C a) * (p /ₘ (X - coe_fn C a)) = p ↔ is_root p a :=
  sorry

theorem dvd_iff_is_root {R : Type u} {a : R} [comm_ring R] {p : polynomial R} :
    X - coe_fn C a ∣ p ↔ is_root p a :=
  sorry

theorem mod_by_monic_X {R : Type u} [comm_ring R] (p : polynomial R) :
    p %ₘ X = coe_fn C (eval 0 p) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (p %ₘ X = coe_fn C (eval 0 p)))
        (Eq.symm (mod_by_monic_X_sub_C_eq_C_eval p 0))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (p %ₘ X = p %ₘ (X - coe_fn C 0))) C_0))
      (eq.mpr (id (Eq._oldrec (Eq.refl (p %ₘ X = p %ₘ (X - 0))) (sub_zero X))) (Eq.refl (p %ₘ X))))

theorem eval₂_mod_by_monic_eq_self_of_root {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
    {f : R →+* S} {p : polynomial R} {q : polynomial R} (hq : monic q) {x : S}
    (hx : eval₂ f x q = 0) : eval₂ f x (p %ₘ q) = eval₂ f x p :=
  sorry

/-- An algorithm for deciding polynomial divisibility.
The algorithm is "compute `p %ₘ q` and compare to `0`". `
See `polynomial.mod_by_monic` for the algorithm that computes `%ₘ`.
 -/
def decidable_dvd_monic {R : Type u} [comm_ring R] {q : polynomial R} (p : polynomial R)
    (hq : monic q) : Decidable (q ∣ p) :=
  decidable_of_iff (p %ₘ q = 0) (dvd_iff_mod_by_monic_eq_zero hq)

theorem multiplicity_X_sub_C_finite {R : Type u} [comm_ring R] {p : polynomial R} (a : R)
    (h0 : p ≠ 0) : multiplicity.finite (X - coe_fn C a) p :=
  sorry

/-- The largest power of `X - C a` which divides `p`.
This is computable via the divisibility algorithm `decidable_dvd_monic`. -/
def root_multiplicity {R : Type u} [comm_ring R] (a : R) (p : polynomial R) : ℕ :=
  dite (p = 0) (fun (h0 : p = 0) => 0)
    fun (h0 : ¬p = 0) =>
      let I : decidable_pred fun (n : ℕ) => ¬(X - coe_fn C a) ^ (n + 1) ∣ p :=
        fun (n : ℕ) => not.decidable;
      nat.find (multiplicity_X_sub_C_finite a h0)

theorem root_multiplicity_eq_multiplicity {R : Type u} [comm_ring R] (p : polynomial R) (a : R) :
    root_multiplicity a p =
        dite (p = 0) (fun (h0 : p = 0) => 0)
          fun (h0 : ¬p = 0) =>
            roption.get (multiplicity (X - coe_fn C a) p) (multiplicity_X_sub_C_finite a h0) :=
  sorry

theorem pow_root_multiplicity_dvd {R : Type u} [comm_ring R] (p : polynomial R) (a : R) :
    (X - coe_fn C a) ^ root_multiplicity a p ∣ p :=
  sorry

theorem div_by_monic_mul_pow_root_multiplicity_eq {R : Type u} [comm_ring R] (p : polynomial R)
    (a : R) :
    p /ₘ (X - coe_fn C a) ^ root_multiplicity a p * (X - coe_fn C a) ^ root_multiplicity a p = p :=
  sorry

theorem eval_div_by_monic_pow_root_multiplicity_ne_zero {R : Type u} [comm_ring R]
    {p : polynomial R} (a : R) (hp : p ≠ 0) :
    eval a (p /ₘ (X - coe_fn C a) ^ root_multiplicity a p) ≠ 0 :=
  sorry

end Mathlib