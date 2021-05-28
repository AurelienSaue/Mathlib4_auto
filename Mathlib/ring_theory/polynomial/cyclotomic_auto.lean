/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Riccardo Brasca
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.field_theory.splitting_field
import Mathlib.ring_theory.roots_of_unity
import Mathlib.algebra.polynomial.big_operators
import Mathlib.number_theory.arithmetic_function
import Mathlib.data.polynomial.lifts
import Mathlib.analysis.complex.roots_of_unity
import Mathlib.field_theory.separable
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Cyclotomic polynomials.

For `n : ℕ` and an integral domain `R`, we define a modified version of the `n`-th cyclotomic
polynomial with coefficients in `R`, denoted `cyclotomic' n R`, as `∏ (X - μ)`, where `μ` varies
over the primitive `n`th roots of unity. If there is a primitive `n`th root of unity in `R` then
this the standard definition. We then define the standard cyclotomic polynomial `cyclotomic n R`
with coefficients in any ring `R`.

## Main definition

* `cyclotomic n R` : the `n`-th cyclotomic polynomial with coefficients in `R`.

## Main results

* `int_coeff_of_cycl` : If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K`
comes from a polynomial with integer coefficients.
* `deg_of_cyclotomic` : The degree of `cyclotomic n` is `totient n`.
* `prod_cyclotomic_eq_X_pow_sub_one` : `X ^ n - 1 = ∏ (cyclotomic i)`, where `i` divides `n`.
* `cyclotomic_eq_prod_X_pow_sub_one_pow_moebius` : The Möbius inversion formula for
  `cyclotomic n R` over an abstract fraction field for `polynomial R`.
* `cyclotomic.irreducible` : `cyclotomic n ℤ` is irreducible.

## Implementation details

Our definition of `cyclotomic' n R` makes sense in any integral domain `R`, but the interesting
results hold if there is a primitive `n`-th root of unity in `R`. In particular, our definition is
not the standard one unless there is a primitive `n`th root of unity in `R`. For example,
`cyclotomic' 3 ℤ = 1`, since there are no primitive cube roots of unity in `ℤ`. The main example is
`R = ℂ`, we decided to work in general since the difficulties are essentially the same.
To get the standard cyclotomic polynomials, we use `int_coeff_of_cycl`, with `R = ℂ`, to get a
polynomial with integer coefficients and then we map it to `polynomial R`, for any ring `R`.
To prove `cyclotomic.irreducible`, the irreducibility of `cyclotomic n ℤ`, we show in
`minpoly_primitive_root_eq_cyclotomic` that `cyclotomic n ℤ` is the minimal polynomial of
any `n`-th primitive root of unity `μ : K`, where `K` is a field of characteristic `0`.
-/

namespace polynomial


/-- The modified `n`-th cyclotomic polynomial with coefficients in `R`, it is the usual cyclotomic
polynomial if there is a primitive `n`-th root of unity in `R`. -/
def cyclotomic' (n : ℕ) (R : Type u_1) [integral_domain R] : polynomial R :=
  finset.prod (primitive_roots n R) fun (μ : R) => X - coe_fn C μ

/-- The zeroth modified cyclotomic polyomial is `1`. -/
@[simp] theorem cyclotomic'_zero (R : Type u_1) [integral_domain R] : cyclotomic' 0 R = 1 := sorry

/-- The first modified cyclotomic polyomial is `X - 1`. -/
@[simp] theorem cyclotomic'_one (R : Type u_1) [integral_domain R] : cyclotomic' 1 R = X - 1 := sorry

/-- The second modified cyclotomic polyomial is `X + 1` if the characteristic of `R` is not `2`. -/
@[simp] theorem cyclotomic'_two (R : Type u_1) [integral_domain R] (p : ℕ) [char_p R p] (hp : p ≠ bit0 1) : cyclotomic' (bit0 1) R = X + 1 := sorry

/-- `cyclotomic' n R` is monic. -/
theorem cyclotomic'.monic (n : ℕ) (R : Type u_1) [integral_domain R] : monic (cyclotomic' n R) :=
  monic_prod_of_monic (primitive_roots n R) (fun (μ : R) => X - coe_fn C μ)
    fun (z : R) (hz : z ∈ primitive_roots n R) => monic_X_sub_C z

/-- `cyclotomic' n R` is different from `0`. -/
theorem cyclotomic'_ne_zero (n : ℕ) (R : Type u_1) [integral_domain R] : cyclotomic' n R ≠ 0 :=
  monic.ne_zero (cyclotomic'.monic n R)

/-- The natural degree of `cyclotomic' n R` is `totient n` if there is a primitive root of
unity in `R`. -/
theorem nat_degree_cyclotomic' {R : Type u_1} [integral_domain R] {ζ : R} {n : ℕ} (h : is_primitive_root ζ n) : nat_degree (cyclotomic' n R) = nat.totient n := sorry

/-- The degree of `cyclotomic' n R` is `totient n` if there is a primitive root of unity in `R`. -/
theorem degree_cyclotomic' {R : Type u_1} [integral_domain R] {ζ : R} {n : ℕ} (h : is_primitive_root ζ n) : degree (cyclotomic' n R) = ↑(nat.totient n) := sorry

/-- The roots of `cyclotomic' n R` are the primitive `n`-th roots of unity. -/
theorem roots_of_cyclotomic (n : ℕ) (R : Type u_1) [integral_domain R] : roots (cyclotomic' n R) = finset.val (primitive_roots n R) := sorry

/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - 1 = ∏ (X - μ)`, where `μ`
varies over the `n`-th roots of unity. -/
theorem X_pow_sub_one_eq_prod {K : Type u_1} [field K] {ζ : K} {n : ℕ} (hpos : 0 < n) (h : is_primitive_root ζ n) : X ^ n - 1 = finset.prod (nth_roots_finset n K) fun (ζ : K) => X - coe_fn C ζ := sorry

/-- `cyclotomic' n K` splits. -/
theorem cyclotomic'_splits {K : Type u_1} [field K] (n : ℕ) : splits (ring_hom.id K) (cyclotomic' n K) :=
  splits_prod (ring_hom.id K)
    fun (z : K) (hz : z ∈ primitive_roots n K) =>
      eq.mpr (id (propext (iff_true_intro (splits_X_sub_C (ring_hom.id K))))) trivial

/-- If there is a primitive `n`-th root of unity in `K`, then `X ^ n - 1`splits. -/
theorem X_pow_sub_one_splits {K : Type u_1} [field K] {ζ : K} {n : ℕ} (h : is_primitive_root ζ n) : splits (ring_hom.id K) (X ^ n - coe_fn C 1) := sorry

/-- If there is a primitive `n`-th root of unity in `K`, then
`∏ i in nat.divisors n, cyclotomic' i K = X ^ n - 1`. -/
theorem prod_cyclotomic'_eq_X_pow_sub_one {K : Type u_1} [field K] {ζ : K} {n : ℕ} (hpos : 0 < n) (h : is_primitive_root ζ n) : (finset.prod (nat.divisors n) fun (i : ℕ) => cyclotomic' i K) = X ^ n - 1 := sorry

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic' n K = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic' i K)`. -/
theorem cyclotomic'_eq_X_pow_sub_one_div {K : Type u_1} [field K] {ζ : K} {n : ℕ} (hpos : 0 < n) (h : is_primitive_root ζ n) : cyclotomic' n K = (X ^ n - 1) /ₘ finset.prod (nat.proper_divisors n) fun (i : ℕ) => cyclotomic' i K := sorry

/-- If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K` comes from a
polynomial with integer coefficients. -/
theorem int_coeff_of_cyclotomic {K : Type u_1} [field K] {ζ : K} {n : ℕ} (h : is_primitive_root ζ n) : ∃ (P : polynomial ℤ), map (int.cast_ring_hom K) P = cyclotomic' n K ∧ degree P = degree (cyclotomic' n K) ∧ monic P := sorry

/-- If `K` is of characteristic `0` and there is a primitive `n`-th root of unity in `K`,
then `cyclotomic n K` comes from a unique polynomial with integer coefficients. -/
theorem unique_int_coeff_of_cycl {K : Type u_1} [field K] [char_zero K] {ζ : K} {n : ℕ+} (h : is_primitive_root ζ ↑n) : exists_unique fun (P : polynomial ℤ) => map (int.cast_ring_hom K) P = cyclotomic' (↑n) K := sorry

/-- The `n`-th cyclotomic polynomial with coefficients in `R`. -/
def cyclotomic (n : ℕ) (R : Type u_1) [ring R] : polynomial R :=
  dite (n = 0) (fun (h : n = 0) => 1) fun (h : ¬n = 0) => map (int.cast_ring_hom R) (classical.some sorry)

theorem int_cyclotomic_rw {n : ℕ} (h : n ≠ 0) : cyclotomic n ℤ = classical.some (int_coeff_of_cyclotomic (complex.is_primitive_root_exp n h)) := sorry

/-- `cyclotomic n R` comes from `cyclotomic n ℤ`. -/
theorem map_cyclotomic_int (n : ℕ) (R : Type u_1) [ring R] : map (int.cast_ring_hom R) (cyclotomic n ℤ) = cyclotomic n R := sorry

theorem int_cyclotomic_spec (n : ℕ) : map (int.cast_ring_hom ℂ) (cyclotomic n ℤ) = cyclotomic' n ℂ ∧
  degree (cyclotomic n ℤ) = degree (cyclotomic' n ℂ) ∧ monic (cyclotomic n ℤ) := sorry

theorem int_cyclotomic_unique {n : ℕ} {P : polynomial ℤ} (h : map (int.cast_ring_hom ℂ) P = cyclotomic' n ℂ) : P = cyclotomic n ℤ := sorry

/-- The definition of `cyclotomic n R` commutes with any ring homomorphism. -/
@[simp] theorem map_cyclotomic (n : ℕ) {R : Type u_1} {S : Type u_2} [ring R] [ring S] (f : R →+* S) : map f (cyclotomic n R) = cyclotomic n S := sorry

/-- The zeroth cyclotomic polyomial is `1`. -/
@[simp] theorem cyclotomic_zero (R : Type u_1) [ring R] : cyclotomic 0 R = 1 := sorry

/-- The first cyclotomic polyomial is `X - 1`. -/
@[simp] theorem cyclotomic_one (R : Type u_1) [ring R] : cyclotomic 1 R = X - 1 := sorry

/-- The second cyclotomic polyomial is `X + 1`. -/
@[simp] theorem cyclotomic_two (R : Type u_1) [ring R] : cyclotomic (bit0 1) R = X + 1 := sorry

/-- `cyclotomic n` is monic. -/
theorem cyclotomic.monic (n : ℕ) (R : Type u_1) [ring R] : monic (cyclotomic n R) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (monic (cyclotomic n R))) (Eq.symm (map_cyclotomic_int n R))))
    (monic_map (int.cast_ring_hom R) (and.right (and.right (int_cyclotomic_spec n))))

/-- `cyclotomic n R` is different from `0`. -/
theorem cyclotomic_ne_zero (n : ℕ) (R : Type u_1) [ring R] [nontrivial R] : cyclotomic n R ≠ 0 :=
  monic.ne_zero (cyclotomic.monic n R)

/-- The degree of `cyclotomic n` is `totient n`. -/
theorem degree_cyclotomic (n : ℕ) (R : Type u_1) [ring R] [nontrivial R] : degree (cyclotomic n R) = ↑(nat.totient n) := sorry

/-- The natural degree of `cyclotomic n` is `totient n`. -/
theorem nat_degree_cyclotomic (n : ℕ) (R : Type u_1) [ring R] [nontrivial R] : nat_degree (cyclotomic n R) = nat.totient n := sorry

/-- The degree of `cyclotomic n R` is positive. -/
theorem degree_cyclotomic_pos (n : ℕ) (R : Type u_1) (hpos : 0 < n) [ring R] [nontrivial R] : 0 < degree (cyclotomic n R) := sorry

/-- `∏ i in nat.divisors n, cyclotomic i R = X ^ n - 1`. -/
theorem prod_cyclotomic_eq_X_pow_sub_one {n : ℕ} (hpos : 0 < n) (R : Type u_1) [comm_ring R] : (finset.prod (nat.divisors n) fun (i : ℕ) => cyclotomic i R) = X ^ n - 1 := sorry

/-- `cyclotomic n R` can be expressed as a product in a fraction field of `polynomial R`
  using Möbius inversion. -/
theorem cyclotomic_eq_prod_X_pow_sub_one_pow_moebius {n : ℕ} (hpos : 0 < n) (R : Type u_1) [comm_ring R] [nontrivial R] {K : Type u_2} [field K] (f : fraction_map (polynomial R) K) : coe_fn (localization_map.to_map f) (cyclotomic n R) =
  finset.prod (nat.divisors_antidiagonal n)
    fun (i : ℕ × ℕ) =>
      coe_fn (localization_map.to_map f) (X ^ prod.snd i - 1) ^ coe_fn nat.arithmetic_function.moebius (prod.fst i) := sorry

/-- We have
`cyclotomic n R = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic i K)`. -/
theorem cyclotomic_eq_X_pow_sub_one_div {R : Type u_1} [comm_ring R] [nontrivial R] {n : ℕ} (hpos : 0 < n) : cyclotomic n R = (X ^ n - 1) /ₘ finset.prod (nat.proper_divisors n) fun (i : ℕ) => cyclotomic i R := sorry

/-- If `m` is a proper divisor of `n`, then `X ^ m - 1` divides
`∏ i in nat.proper_divisors n, cyclotomic i R`. -/
theorem X_pow_sub_one_dvd_prod_cyclotomic (R : Type u_1) [comm_ring R] {n : ℕ} {m : ℕ} (hpos : 0 < n) (hm : m ∣ n) (hdiff : m ≠ n) : X ^ m - 1 ∣ finset.prod (nat.proper_divisors n) fun (i : ℕ) => cyclotomic i R := sorry

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic n K = ∏ μ in primitive_roots n R, (X - C μ)`. In particular,
`cyclotomic n K = cyclotomic' n K` -/
theorem cyclotomic_eq_prod_X_sub_primitive_roots {K : Type u_1} [field K] {ζ : K} {n : ℕ} (h : is_primitive_root ζ n) : cyclotomic n K = finset.prod (primitive_roots n K) fun (μ : K) => X - coe_fn C μ := sorry

/-- Any `n`-th primitive root of unity is a root of `cyclotomic n ℤ`.-/
theorem is_root_cyclotomic {n : ℕ} {K : Type u_1} [field K] (hpos : 0 < n) {μ : K} (h : is_primitive_root μ n) : is_root (cyclotomic n K) μ := sorry

theorem eq_cyclotomic_iff {R : Type u_1} [comm_ring R] [nontrivial R] {n : ℕ} (hpos : 0 < n) (P : polynomial R) : P = cyclotomic n R ↔ (P * finset.prod (nat.proper_divisors n) fun (i : ℕ) => cyclotomic i R) = X ^ n - 1 := sorry

/-- If `p` is prime, then `cyclotomic p R = geom_series X p`. -/
theorem cyclotomic_eq_geom_series {R : Type u_1} [comm_ring R] [nontrivial R] {p : ℕ} (hp : nat.prime p) : cyclotomic p R = geom_series X p := sorry

/-- The constant term of `cyclotomic n R` is `1` if `2 ≤ n`. -/
theorem cyclotomic_coeff_zero (R : Type u_1) [comm_ring R] {n : ℕ} (hn : bit0 1 ≤ n) : coeff (cyclotomic n R) 0 = 1 := sorry

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, where `p` is a prime, then `a` and `p` are
coprime. -/
theorem coprime_of_root_cyclotomic {n : ℕ} (hpos : 0 < n) {p : ℕ} [hprime : fact (nat.prime p)] {a : ℕ} (hroot : is_root (cyclotomic n (zmod p)) (coe_fn (nat.cast_ring_hom (zmod p)) a)) : nat.coprime a p := sorry

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, then the multiplicative order of `a` modulo
`p` divides `n`. -/
theorem order_of_root_cyclotomic_dvd {n : ℕ} (hpos : 0 < n) {p : ℕ} [hprime : fact (nat.prime p)] {a : ℕ} (hroot : is_root (cyclotomic n (zmod p)) (coe_fn (nat.cast_ring_hom (zmod p)) a)) : order_of (zmod.unit_of_coprime a (coprime_of_root_cyclotomic hpos hroot)) ∣ n := sorry

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, where `p` is a prime that does not divide
`n`, then the multiplicative order of `a` modulo `p` is exactly `n`. -/
theorem order_of_root_cyclotomic {n : ℕ} (hpos : 0 < n) {p : ℕ} [hprime : fact (nat.prime p)] {a : ℕ} (hn : ¬p ∣ n) (hroot : is_root (cyclotomic n (zmod p)) (coe_fn (nat.cast_ring_hom (zmod p)) a)) : order_of (zmod.unit_of_coprime a (coprime_of_root_cyclotomic hpos hroot)) = n := sorry

end polynomial


/-- The minimal polynomial of a primitive `n`-th root of unity `μ` divides `cyclotomic n ℤ`. -/
theorem minpoly_primitive_root_dvd_cyclotomic {n : ℕ} {K : Type u_1} [field K] {μ : K} (h : is_primitive_root μ n) (hpos : 0 < n) [char_zero K] : minpoly ℤ μ ∣ polynomial.cyclotomic n ℤ := sorry

/-- `cyclotomic n ℤ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
theorem cyclotomic_eq_minpoly {n : ℕ} {K : Type u_1} [field K] {μ : K} (h : is_primitive_root μ n) (hpos : 0 < n) [char_zero K] : polynomial.cyclotomic n ℤ = minpoly ℤ μ := sorry

/-- `cyclotomic n ℤ` is irreducible. -/
theorem cyclotomic.irreducible {n : ℕ} (hpos : 0 < n) : irreducible (polynomial.cyclotomic n ℤ) := sorry

