/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.ring_theory.integral_closure
import Mathlib.data.polynomial.field_division
import Mathlib.ring_theory.polynomial.gauss_lemma
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Minimal polynomials

This file defines the minimal polynomial of an element `x` of an `A`-algebra `B`,
under the assumption that x is integral over `A`.

After stating the defining property we specialize to the setting of field extensions
and derive some well-known properties, amongst which the fact that minimal polynomials
are irreducible, and uniquely determined by their defining property.

-/

/-- Let `B` be an `A`-algebra, and `x` an element of `B` that is integral over `A`
so we have some term `hx : is_integral A x`.
The minimal polynomial `minpoly A x` of `x` is a monic polynomial of smallest degree
that has `x` as its root.
For instance, if `V` is a `K`-vector space for some field `K`, and `f : V →ₗ[K] V` then
the minimal polynomial of `f` is `minpoly f.is_integral`. -/
def minpoly (A : Type u_1) {B : Type u_2} [comm_ring A] [ring B] [algebra A B] (x : B) : polynomial A :=
  dite (is_integral A x)
    (fun (hx : is_integral A x) =>
      well_founded.min sorry (fun (p : polynomial A) => polynomial.monic p ∧ polynomial.eval₂ (algebra_map A B) x p = 0)
        hx)
    fun (hx : ¬is_integral A x) => 0

namespace minpoly


/--A minimal polynomial is monic.-/
theorem monic {A : Type u_1} {B : Type u_2} [comm_ring A] [ring B] [algebra A B] {x : B} (hx : is_integral A x) : polynomial.monic (minpoly A x) := sorry

/-- A minimal polynomial is nonzero. -/
theorem ne_zero {A : Type u_1} {B : Type u_2} [comm_ring A] [ring B] [algebra A B] {x : B} [nontrivial A] (hx : is_integral A x) : minpoly A x ≠ 0 :=
  polynomial.ne_zero_of_monic (monic hx)

theorem eq_zero {A : Type u_1} {B : Type u_2} [comm_ring A] [ring B] [algebra A B] {x : B} (hx : ¬is_integral A x) : minpoly A x = 0 :=
  dif_neg hx

/--An element is a root of its minimal polynomial.-/
@[simp] theorem aeval (A : Type u_1) {B : Type u_2} [comm_ring A] [ring B] [algebra A B] (x : B) : coe_fn (polynomial.aeval x) (minpoly A x) = 0 := sorry

theorem mem_range_of_degree_eq_one (A : Type u_1) {B : Type u_2} [comm_ring A] [ring B] [algebra A B] (x : B) (hx : polynomial.degree (minpoly A x) = 1) : x ∈ ring_hom.range (algebra_map A B) := sorry

/--The defining property of the minimal polynomial of an element x:
it is the monic polynomial with smallest degree that has x as its root.-/
theorem min (A : Type u_1) {B : Type u_2} [comm_ring A] [ring B] [algebra A B] (x : B) {p : polynomial A} (pmonic : polynomial.monic p) (hp : coe_fn (polynomial.aeval x) p = 0) : polynomial.degree (minpoly A x) ≤ polynomial.degree p := sorry

-- TODO(Commelin, Brasca): this is a duplicate

/-- If an element `x` is a root of a nonzero monic polynomial `p`,
then the degree of `p` is at least the degree of the minimal polynomial of `x`. -/
theorem degree_le_of_monic (A : Type u_1) {B : Type u_2} [comm_ring A] [ring B] [algebra A B] (x : B) {p : polynomial A} (hmonic : polynomial.monic p) (hp : coe_fn (polynomial.aeval x) p = 0) : polynomial.degree (minpoly A x) ≤ polynomial.degree p := sorry

/-- The degree of a minimal polynomial is positive. -/
theorem degree_pos {A : Type u_1} {B : Type u_2} [integral_domain A] [ring B] [algebra A B] [nontrivial B] {x : B} [nontrivial A] (hx : is_integral A x) : 0 < polynomial.degree (minpoly A x) := sorry

/-- If `B/A` is an injective ring extension, and `a` is an element of `A`,
then the minimal polynomial of `algebra_map A B a` is `X - C a`. -/
theorem eq_X_sub_C_of_algebra_map_inj {A : Type u_1} {B : Type u_2} [integral_domain A] [ring B] [algebra A B] [nontrivial B] [nontrivial A] (a : A) (hf : function.injective ⇑(algebra_map A B)) : minpoly A (coe_fn (algebra_map A B) a) = polynomial.X - coe_fn polynomial.C a := sorry

/-- A minimal polynomial is not a unit. -/
theorem not_is_unit (A : Type u_1) {B : Type u_2} [integral_domain A] [ring B] [algebra A B] [nontrivial B] (x : B) : ¬is_unit (minpoly A x) := sorry

/-- If `a` strictly divides the minimal polynomial of `x`, then `x` cannot be a root for `a`. -/
theorem aeval_ne_zero_of_dvd_not_unit_minpoly {A : Type u_1} {B : Type u_2} [integral_domain A] [domain B] [algebra A B] {x : B} {a : polynomial A} (hx : is_integral A x) (hamonic : polynomial.monic a) (hdvd : dvd_not_unit a (minpoly A x)) : coe_fn (polynomial.aeval x) a ≠ 0 := sorry

/--A minimal polynomial is irreducible.-/
theorem irreducible {A : Type u_1} {B : Type u_2} [integral_domain A] [domain B] [algebra A B] {x : B} (hx : is_integral A x) : irreducible (minpoly A x) := sorry

/-- If an element `x` is a root of a nonzero polynomial `p`,
then the degree of `p` is at least the degree of the minimal polynomial of `x`. -/
theorem degree_le_of_ne_zero (A : Type u_1) {B : Type u_2} [field A] [ring B] [algebra A B] (x : B) {p : polynomial A} (pnz : p ≠ 0) (hp : coe_fn (polynomial.aeval x) p = 0) : polynomial.degree (minpoly A x) ≤ polynomial.degree p := sorry

/-- The minimal polynomial of an element x is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has x as a root,
then this polynomial is equal to the minimal polynomial of x. -/
theorem unique (A : Type u_1) {B : Type u_2} [field A] [ring B] [algebra A B] (x : B) {p : polynomial A} (pmonic : polynomial.monic p) (hp : coe_fn (polynomial.aeval x) p = 0) (pmin : ∀ (q : polynomial A), polynomial.monic q → coe_fn (polynomial.aeval x) q = 0 → polynomial.degree p ≤ polynomial.degree q) : p = minpoly A x := sorry

/-- If an element x is a root of a polynomial p,
then the minimal polynomial of x divides p. -/
theorem dvd (A : Type u_1) {B : Type u_2} [field A] [ring B] [algebra A B] (x : B) {p : polynomial A} (hp : coe_fn (polynomial.aeval x) p = 0) : minpoly A x ∣ p := sorry

theorem dvd_map_of_is_scalar_tower (A : Type u_1) (K : Type u_2) {R : Type u_3} [comm_ring A] [field K] [comm_ring R] [algebra A K] [algebra A R] [algebra K R] [is_scalar_tower A K R] (x : R) : minpoly K x ∣ polynomial.map (algebra_map A K) (minpoly A x) := sorry

theorem unique' {A : Type u_1} {B : Type u_2} [field A] [ring B] [algebra A B] {x : B} [nontrivial B] {p : polynomial A} (hx : is_integral A x) (hp1 : irreducible p) (hp2 : coe_fn (polynomial.aeval x) p = 0) (hp3 : polynomial.monic p) : p = minpoly A x := sorry

/-- If `y` is the image of `x` in an extension, their minimal polynomials coincide.

We take `h : y = algebra_map L T x` as an argument because `rw h` typically fails
since `is_integral R y` depends on y.
-/
theorem eq_of_algebra_map_eq {K : Type u_1} {S : Type u_2} {T : Type u_3} [field K] [comm_ring S] [comm_ring T] [algebra K S] [algebra K T] [algebra S T] [is_scalar_tower K S T] (hST : function.injective ⇑(algebra_map S T)) {x : S} {y : T} (hx : is_integral K x) (h : y = coe_fn (algebra_map S T) x) : minpoly K x = minpoly K y := sorry

/-- For GCD domains, the minimal polynomial over the ring is the same as the minimal polynomial
over the fraction field. -/
theorem gcd_domain_eq_field_fractions {A : Type u_1} {K : Type u_2} {R : Type u_3} [integral_domain A] [gcd_monoid A] [field K] [integral_domain R] (f : fraction_map A K) [algebra (localization_map.codomain f) R] [algebra A R] [is_scalar_tower A (localization_map.codomain f) R] {x : R} (hx : is_integral A x) : minpoly (localization_map.codomain f) x = polynomial.map (localization_map.to_ring_hom f) (minpoly A x) := sorry

/-- The minimal polynomial over `ℤ` is the same as the minimal polynomial over `ℚ`. -/
--TODO use `gcd_domain_eq_field_fractions` directly when localizations are defined

-- in terms of algebras instead of `ring_hom`s

theorem over_int_eq_over_rat {A : Type u_1} [integral_domain A] {x : A} [hℚA : algebra ℚ A] (hx : is_integral ℤ x) : minpoly ℚ x = polynomial.map (int.cast_ring_hom ℚ) (minpoly ℤ x) := sorry

/-- For GCD domains, the minimal polynomial divides any primitive polynomial that has the integral
element as root. -/
theorem gcd_domain_dvd {A : Type u_1} {K : Type u_2} {R : Type u_3} [integral_domain A] [gcd_monoid A] [field K] [integral_domain R] (f : fraction_map A K) [algebra (localization_map.codomain f) R] [algebra A R] [is_scalar_tower A (localization_map.codomain f) R] {x : R} (hx : is_integral A x) {P : polynomial A} (hprim : polynomial.is_primitive P) (hroot : coe_fn (polynomial.aeval x) P = 0) : minpoly A x ∣ P := sorry

/-- The minimal polynomial over `ℤ` divides any primitive polynomial that has the integral element
as root. -/
-- TODO use `gcd_domain_dvd` directly when localizations are defined in terms of algebras

-- instead of `ring_hom`s

theorem integer_dvd {A : Type u_1} [integral_domain A] [algebra ℚ A] {x : A} (hx : is_integral ℤ x) {P : polynomial ℤ} (hprim : polynomial.is_primitive P) (hroot : coe_fn (polynomial.aeval x) P = 0) : minpoly ℤ x ∣ P := sorry

/-- If `B/K` is a nontrivial algebra over a field, and `x` is an element of `K`,
then the minimal polynomial of `algebra_map K B x` is `X - C x`. -/
theorem eq_X_sub_C {A : Type u_1} (B : Type u_2) [field A] [ring B] [algebra A B] [nontrivial B] (a : A) : minpoly A (coe_fn (algebra_map A B) a) = polynomial.X - coe_fn polynomial.C a :=
  eq_X_sub_C_of_algebra_map_inj a (ring_hom.injective (algebra_map A B))

theorem eq_X_sub_C' {A : Type u_1} [field A] (a : A) : minpoly A a = polynomial.X - coe_fn polynomial.C a :=
  eq_X_sub_C A a

/-- The minimal polynomial of `0` is `X`. -/
@[simp] theorem zero (A : Type u_1) (B : Type u_2) [field A] [ring B] [algebra A B] [nontrivial B] : minpoly A 0 = polynomial.X := sorry

/-- The minimal polynomial of `1` is `X - 1`. -/
@[simp] theorem one (A : Type u_1) (B : Type u_2) [field A] [ring B] [algebra A B] [nontrivial B] : minpoly A 1 = polynomial.X - 1 := sorry

/-- A minimal polynomial is prime. -/
theorem prime {A : Type u_1} {B : Type u_2} [field A] [domain B] [algebra A B] {x : B} (hx : is_integral A x) : prime (minpoly A x) := sorry

/-- If `L/K` is a field extension and an element `y` of `K` is a root of the minimal polynomial
of an element `x ∈ L`, then `y` maps to `x` under the field embedding. -/
theorem root {A : Type u_1} {B : Type u_2} [field A] [domain B] [algebra A B] {x : B} (hx : is_integral A x) {y : A} (h : polynomial.is_root (minpoly A x) y) : coe_fn (algebra_map A B) y = x := sorry

/--The constant coefficient of the minimal polynomial of `x` is `0` if and only if `x = 0`. -/
@[simp] theorem coeff_zero_eq_zero {A : Type u_1} {B : Type u_2} [field A] [domain B] [algebra A B] {x : B} (hx : is_integral A x) : polynomial.coeff (minpoly A x) 0 = 0 ↔ x = 0 := sorry

/--The minimal polynomial of a nonzero element has nonzero constant coefficient. -/
theorem coeff_zero_ne_zero {A : Type u_1} {B : Type u_2} [field A] [domain B] [algebra A B] {x : B} (hx : is_integral A x) (h : x ≠ 0) : polynomial.coeff (minpoly A x) 0 ≠ 0 := sorry

