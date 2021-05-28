/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

# Ring-theoretic supplement of data.polynomial.

## Main results
* `mv_polynomial.integral_domain`:
  If a ring is an integral domain, then so is its polynomial ring over finitely many variables.
* `polynomial.is_noetherian_ring`:
  Hilbert basis theorem, that if a ring is noetherian then so is its polynomial ring.
* `polynomial.wf_dvd_monoid`:
  If an integral domain is a `wf_dvd_monoid`, then so is its polynomial ring.
* `polynomial.unique_factorization_monoid`:
  If an integral domain is a `unique_factorization_monoid`, then so is its polynomial ring.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.char_p.basic
import Mathlib.data.mv_polynomial.comm_ring
import Mathlib.data.mv_polynomial.equiv
import Mathlib.data.polynomial.field_division
import Mathlib.ring_theory.principal_ideal_domain
import Mathlib.ring_theory.polynomial.content
import PostPort

universes u u_1 v w 

namespace Mathlib

namespace polynomial


protected instance char_p {R : Type u} [semiring R] (p : ℕ) [h : char_p R p] : char_p (polynomial R) p :=
  sorry

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`. -/
def degree_le (R : Type u) [comm_ring R] (n : with_bot ℕ) : submodule R (polynomial R) :=
  infi fun (k : ℕ) => infi fun (h : ↑k > n) => linear_map.ker (lcoeff R k)

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree < `n`. -/
def degree_lt (R : Type u) [comm_ring R] (n : ℕ) : submodule R (polynomial R) :=
  infi fun (k : ℕ) => infi fun (h : k ≥ n) => linear_map.ker (lcoeff R k)

theorem mem_degree_le {R : Type u} [comm_ring R] {n : with_bot ℕ} {f : polynomial R} : f ∈ degree_le R n ↔ degree f ≤ n := sorry

theorem degree_le_mono {R : Type u} [comm_ring R] {m : with_bot ℕ} {n : with_bot ℕ} (H : m ≤ n) : degree_le R m ≤ degree_le R n :=
  fun (f : polynomial R) (hf : f ∈ degree_le R m) => iff.mpr mem_degree_le (le_trans (iff.mp mem_degree_le hf) H)

theorem degree_le_eq_span_X_pow {R : Type u} [comm_ring R] {n : ℕ} : degree_le R ↑n = submodule.span R ↑(finset.image (fun (n : ℕ) => X ^ n) (finset.range (n + 1))) := sorry

theorem mem_degree_lt {R : Type u} [comm_ring R] {n : ℕ} {f : polynomial R} : f ∈ degree_lt R n ↔ degree f < ↑n := sorry

theorem degree_lt_mono {R : Type u} [comm_ring R] {m : ℕ} {n : ℕ} (H : m ≤ n) : degree_lt R m ≤ degree_lt R n :=
  fun (f : polynomial R) (hf : f ∈ degree_lt R m) =>
    iff.mpr mem_degree_lt (lt_of_lt_of_le (iff.mp mem_degree_lt hf) (iff.mpr with_bot.coe_le_coe H))

theorem degree_lt_eq_span_X_pow {R : Type u} [comm_ring R] {n : ℕ} : degree_lt R n = submodule.span R ↑(finset.image (fun (n : ℕ) => X ^ n) (finset.range n)) := sorry

/-- The first `n` coefficients on `degree_lt n` form a linear equivalence with `fin n → F`. -/
def degree_lt_equiv (F : Type u_1) [field F] (n : ℕ) : linear_equiv F (↥(degree_lt F n)) (fin n → F) :=
  linear_equiv.mk (fun (p : ↥(degree_lt F n)) (n_1 : fin n) => coeff ↑p ↑n_1) sorry sorry
    (fun (f : fin n → F) =>
      { val := finset.sum finset.univ fun (i : fin n) => coe_fn (monomial ↑i) (f i), property := sorry })
    sorry sorry

/-- Given a polynomial, return the polynomial whose coefficients are in
the ring closure of the original coefficients. -/
def restriction {R : Type u} [comm_ring R] (p : polynomial R) : polynomial ↥(ring.closure ↑(finsupp.frange p)) :=
  finsupp.mk (finsupp.support p) (fun (i : ℕ) => { val := finsupp.to_fun p i, property := sorry }) sorry

@[simp] theorem coeff_restriction {R : Type u} [comm_ring R] {p : polynomial R} {n : ℕ} : ↑(coeff (restriction p) n) = coeff p n :=
  rfl

@[simp] theorem coeff_restriction' {R : Type u} [comm_ring R] {p : polynomial R} {n : ℕ} : subtype.val (coeff (restriction p) n) = coeff p n :=
  rfl

@[simp] theorem map_restriction {R : Type u} [comm_ring R] (p : polynomial R) : map (algebra_map (↥(ring.closure ↑(finsupp.frange p))) R) (restriction p) = p := sorry

@[simp] theorem degree_restriction {R : Type u} [comm_ring R] {p : polynomial R} : degree (restriction p) = degree p :=
  rfl

@[simp] theorem nat_degree_restriction {R : Type u} [comm_ring R] {p : polynomial R} : nat_degree (restriction p) = nat_degree p :=
  rfl

@[simp] theorem monic_restriction {R : Type u} [comm_ring R] {p : polynomial R} : monic (restriction p) ↔ monic p :=
  { mp := fun (H : monic (restriction p)) => congr_arg subtype.val H, mpr := fun (H : monic p) => subtype.eq H }

@[simp] theorem restriction_zero {R : Type u} [comm_ring R] : restriction 0 = 0 :=
  rfl

@[simp] theorem restriction_one {R : Type u} [comm_ring R] : restriction 1 = 1 := sorry

theorem eval₂_restriction {R : Type u} [comm_ring R] {S : Type v} [ring S] {f : R →+* S} {x : S} {p : polynomial R} : eval₂ f x p = eval₂ (ring_hom.comp f (is_subring.subtype (ring.closure ↑(finsupp.frange p)))) x (restriction p) :=
  id (Eq.refl (finsupp.sum p fun (e : ℕ) (a : R) => coe_fn f a * x ^ e))

/-- Given a polynomial `p` and a subring `T` that contains the coefficients of `p`,
return the corresponding polynomial whose coefficients are in `T. -/
def to_subring {R : Type u} [comm_ring R] (p : polynomial R) (T : set R) [is_subring T] (hp : ↑(finsupp.frange p) ⊆ T) : polynomial ↥T :=
  finsupp.mk (finsupp.support p) (fun (i : ℕ) => { val := finsupp.to_fun p i, property := sorry }) sorry

@[simp] theorem coeff_to_subring {R : Type u} [comm_ring R] (p : polynomial R) (T : set R) [is_subring T] (hp : ↑(finsupp.frange p) ⊆ T) {n : ℕ} : ↑(coeff (to_subring p T hp) n) = coeff p n :=
  rfl

@[simp] theorem coeff_to_subring' {R : Type u} [comm_ring R] (p : polynomial R) (T : set R) [is_subring T] (hp : ↑(finsupp.frange p) ⊆ T) {n : ℕ} : subtype.val (coeff (to_subring p T hp) n) = coeff p n :=
  rfl

@[simp] theorem degree_to_subring {R : Type u} [comm_ring R] (p : polynomial R) (T : set R) [is_subring T] (hp : ↑(finsupp.frange p) ⊆ T) : degree (to_subring p T hp) = degree p :=
  rfl

@[simp] theorem nat_degree_to_subring {R : Type u} [comm_ring R] (p : polynomial R) (T : set R) [is_subring T] (hp : ↑(finsupp.frange p) ⊆ T) : nat_degree (to_subring p T hp) = nat_degree p :=
  rfl

@[simp] theorem monic_to_subring {R : Type u} [comm_ring R] (p : polynomial R) (T : set R) [is_subring T] (hp : ↑(finsupp.frange p) ⊆ T) : monic (to_subring p T hp) ↔ monic p :=
  { mp := fun (H : monic (to_subring p T hp)) => congr_arg subtype.val H, mpr := fun (H : monic p) => subtype.eq H }

@[simp] theorem to_subring_zero {R : Type u} [comm_ring R] (T : set R) [is_subring T] : to_subring 0 T (set.empty_subset T) = 0 :=
  rfl

@[simp] theorem to_subring_one {R : Type u} [comm_ring R] (T : set R) [is_subring T] : to_subring 1 T
    (set.subset.trans (iff.mpr finset.coe_subset finsupp.frange_single)
      (iff.mpr finset.singleton_subset_set_iff is_submonoid.one_mem)) =
  1 := sorry

@[simp] theorem map_to_subring {R : Type u} [comm_ring R] (p : polynomial R) (T : set R) [is_subring T] (hp : ↑(finsupp.frange p) ⊆ T) : map (is_subring.subtype T) (to_subring p T hp) = p :=
  ext fun (n : ℕ) => coeff_map (is_subring.subtype T) n

/-- Given a polynomial whose coefficients are in some subring, return
the corresponding polynomial whose coefificents are in the ambient ring. -/
def of_subring {R : Type u} [comm_ring R] (T : set R) [is_subring T] (p : polynomial ↥T) : polynomial R :=
  finsupp.mk (finsupp.support p) (subtype.val ∘ finsupp.to_fun p) sorry

@[simp] theorem frange_of_subring {R : Type u} [comm_ring R] (T : set R) [is_subring T] {p : polynomial ↥T} : ↑(finsupp.frange (of_subring T p)) ⊆ T := sorry

end polynomial


namespace ideal


/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself -/
theorem polynomial_mem_ideal_of_coeff_mem_ideal {R : Type u} [comm_ring R] (I : ideal (polynomial R)) (p : polynomial R) (hp : ∀ (n : ℕ), polynomial.coeff p n ∈ comap polynomial.C I) : p ∈ I :=
  polynomial.sum_C_mul_X_eq p ▸
    submodule.sum_mem I fun (n : ℕ) (hn : n ∈ finsupp.support p) => mul_mem_right I (polynomial.X ^ n) (hp n)

/-- The push-forward of an ideal `I` of `R` to `polynomial R` via inclusion
 is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_C_iff {R : Type u} [comm_ring R] {I : ideal R} {f : polynomial R} : f ∈ map polynomial.C I ↔ ∀ (n : ℕ), polynomial.coeff f n ∈ I := sorry

theorem quotient_map_C_eq_zero {R : Type u} [comm_ring R] {I : ideal R} (a : R) (H : a ∈ I) : coe_fn (ring_hom.comp (quotient.mk (map polynomial.C I)) polynomial.C) a = 0 := sorry

theorem eval₂_C_mk_eq_zero {R : Type u} [comm_ring R] {I : ideal R} (f : polynomial R) (H : f ∈ map polynomial.C I) : coe_fn (polynomial.eval₂_ring_hom (ring_hom.comp polynomial.C (quotient.mk I)) polynomial.X) f = 0 := sorry

/-- If `I` is an ideal of `R`, then the ring polynomials over the quotient ring `I.quotient` is
isomorphic to the quotient of `polynomial R` by the ideal `map C I`,
where `map C I` contains exactly the polynomials whose coefficients all lie in `I` -/
def polynomial_quotient_equiv_quotient_polynomial {R : Type u} [comm_ring R] (I : ideal R) : polynomial (quotient I) ≃+* quotient (map polynomial.C I) :=
  ring_equiv.mk
    ⇑(polynomial.eval₂_ring_hom
        (quotient.lift I (ring_hom.comp (quotient.mk (map polynomial.C I)) polynomial.C) quotient_map_C_eq_zero)
        (coe_fn (quotient.mk (map polynomial.C I)) polynomial.X))
    ⇑(quotient.lift (map polynomial.C I)
        (polynomial.eval₂_ring_hom (ring_hom.comp polynomial.C (quotient.mk I)) polynomial.X) eval₂_C_mk_eq_zero)
    sorry sorry sorry sorry

/-- If `P` is a prime ideal of `R`, then `R[x]/(P)` is an integral domain. -/
theorem is_integral_domain_map_C_quotient {R : Type u} [comm_ring R] {P : ideal R} (H : is_prime P) : is_integral_domain (quotient (map polynomial.C P)) :=
  ring_equiv.is_integral_domain (polynomial (quotient P))
    (integral_domain.to_is_integral_domain (polynomial (quotient P)))
    (ring_equiv.symm (polynomial_quotient_equiv_quotient_polynomial P))

/-- If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`. -/
theorem is_prime_map_C_of_is_prime {R : Type u} [comm_ring R] {P : ideal R} (H : is_prime P) : is_prime (map polynomial.C P) :=
  iff.mp (quotient.is_integral_domain_iff_prime (map polynomial.C P)) (is_integral_domain_map_C_quotient H)

/-- Given any ring `R` and an ideal `I` of `polynomial R`, we get a map `R → R[x] → R[x]/I`.
  If we let `R` be the image of `R` in `R[x]/I` then we also have a map `R[x] → R'[x]`.
  In particular we can map `I` across this map, to get `I'` and a new map `R' → R'[x] → R'[x]/I`.
  This theorem shows `I'` will not contain any non-zero constant polynomials
  -/
theorem eq_zero_of_polynomial_mem_map_range {R : Type u} [comm_ring R] (I : ideal (polynomial R)) (x : ↥(ring_hom.range (ring_hom.comp (quotient.mk I) polynomial.C))) (hx : coe_fn polynomial.C x ∈
  map (polynomial.map_ring_hom (ring_hom.range_restrict (ring_hom.comp (quotient.mk I) polynomial.C))) I) : x = 0 := sorry

/-- `polynomial R` is never a field for any ring `R`. -/
theorem polynomial_not_is_field {R : Type u} [comm_ring R] : ¬is_field (polynomial R) := sorry

/-- The only constant in a maximal ideal over a field is `0`. -/
theorem eq_zero_of_constant_mem_of_maximal {R : Type u} [comm_ring R] (hR : is_field R) (I : ideal (polynomial R)) [hI : is_maximal I] (x : R) (hx : coe_fn polynomial.C x ∈ I) : x = 0 := sorry

/-- Transport an ideal of `R[X]` to an `R`-submodule of `R[X]`. -/
def of_polynomial {R : Type u} [comm_ring R] (I : ideal (polynomial R)) : submodule R (polynomial R) :=
  submodule.mk (submodule.carrier I) sorry sorry sorry

theorem mem_of_polynomial {R : Type u} [comm_ring R] {I : ideal (polynomial R)} (x : polynomial R) : x ∈ of_polynomial I ↔ x ∈ I :=
  iff.rfl

/-- Given an ideal `I` of `R[X]`, make the `R`-submodule of `I`
consisting of polynomials of degree ≤ `n`. -/
def degree_le {R : Type u} [comm_ring R] (I : ideal (polynomial R)) (n : with_bot ℕ) : submodule R (polynomial R) :=
  polynomial.degree_le R n ⊓ of_polynomial I

/-- Given an ideal `I` of `R[X]`, make the ideal in `R` of
leading coefficients of polynomials in `I` with degree ≤ `n`. -/
def leading_coeff_nth {R : Type u} [comm_ring R] (I : ideal (polynomial R)) (n : ℕ) : ideal R :=
  submodule.map (polynomial.lcoeff R n) (degree_le I ↑n)

theorem mem_leading_coeff_nth {R : Type u} [comm_ring R] (I : ideal (polynomial R)) (n : ℕ) (x : R) : x ∈ leading_coeff_nth I n ↔
  ∃ (p : polynomial R), ∃ (H : p ∈ I), polynomial.degree p ≤ ↑n ∧ polynomial.leading_coeff p = x := sorry

theorem mem_leading_coeff_nth_zero {R : Type u} [comm_ring R] (I : ideal (polynomial R)) (x : R) : x ∈ leading_coeff_nth I 0 ↔ coe_fn polynomial.C x ∈ I := sorry

theorem leading_coeff_nth_mono {R : Type u} [comm_ring R] (I : ideal (polynomial R)) {m : ℕ} {n : ℕ} (H : m ≤ n) : leading_coeff_nth I m ≤ leading_coeff_nth I n := sorry

/-- Given an ideal `I` in `R[X]`, make the ideal in `R` of the
leading coefficients in `I`. -/
def leading_coeff {R : Type u} [comm_ring R] (I : ideal (polynomial R)) : ideal R :=
  supr fun (n : ℕ) => leading_coeff_nth I n

theorem mem_leading_coeff {R : Type u} [comm_ring R] (I : ideal (polynomial R)) (x : R) : x ∈ leading_coeff I ↔ ∃ (p : polynomial R), ∃ (H : p ∈ I), polynomial.leading_coeff p = x := sorry

theorem is_fg_degree_le {R : Type u} [comm_ring R] (I : ideal (polynomial R)) [is_noetherian_ring R] (n : ℕ) : submodule.fg (degree_le I ↑n) := sorry

end ideal


namespace polynomial


protected instance wf_dvd_monoid {R : Type u_1} [integral_domain R] [wf_dvd_monoid R] : wf_dvd_monoid (polynomial R) := sorry

end polynomial


/-- Hilbert basis theorem: a polynomial ring over a noetherian ring is a noetherian ring. -/
protected instance polynomial.is_noetherian_ring {R : Type u} [comm_ring R] [is_noetherian_ring R] : is_noetherian_ring (polynomial R) := sorry

namespace polynomial


theorem exists_irreducible_of_degree_pos {R : Type u} [integral_domain R] [wf_dvd_monoid R] {f : polynomial R} (hf : 0 < degree f) : ∃ (g : polynomial R), irreducible g ∧ g ∣ f :=
  wf_dvd_monoid.exists_irreducible_factor (fun (huf : is_unit f) => ne_of_gt hf (degree_eq_zero_of_is_unit huf))
    fun (hf0 : f = 0) => not_lt_of_lt hf (Eq.symm hf0 ▸ Eq.symm degree_zero ▸ with_bot.bot_lt_coe 0)

theorem exists_irreducible_of_nat_degree_pos {R : Type u} [integral_domain R] [wf_dvd_monoid R] {f : polynomial R} (hf : 0 < nat_degree f) : ∃ (g : polynomial R), irreducible g ∧ g ∣ f := sorry

theorem exists_irreducible_of_nat_degree_ne_zero {R : Type u} [integral_domain R] [wf_dvd_monoid R] {f : polynomial R} (hf : nat_degree f ≠ 0) : ∃ (g : polynomial R), irreducible g ∧ g ∣ f :=
  exists_irreducible_of_nat_degree_pos (nat.pos_of_ne_zero hf)

theorem linear_independent_powers_iff_eval₂ {R : Type u} {M : Type w} [comm_ring R] [add_comm_group M] [module R M] (f : linear_map R M M) (v : M) : (linear_independent R fun (n : ℕ) => coe_fn (f ^ n) v) ↔ ∀ (p : polynomial R), coe_fn (coe_fn (aeval f) p) v = 0 → p = 0 := sorry

theorem disjoint_ker_aeval_of_coprime {R : Type u} {M : Type w} [comm_ring R] [add_comm_group M] [module R M] (f : linear_map R M M) {p : polynomial R} {q : polynomial R} (hpq : is_coprime p q) : disjoint (linear_map.ker (coe_fn (aeval f) p)) (linear_map.ker (coe_fn (aeval f) q)) := sorry

theorem sup_aeval_range_eq_top_of_coprime {R : Type u} {M : Type w} [comm_ring R] [add_comm_group M] [module R M] (f : linear_map R M M) {p : polynomial R} {q : polynomial R} (hpq : is_coprime p q) : linear_map.range (coe_fn (aeval f) p) ⊔ linear_map.range (coe_fn (aeval f) q) = ⊤ := sorry

theorem sup_ker_aeval_le_ker_aeval_mul {R : Type u} {M : Type w} [comm_ring R] [add_comm_group M] [module R M] {f : linear_map R M M} {p : polynomial R} {q : polynomial R} : linear_map.ker (coe_fn (aeval f) p) ⊔ linear_map.ker (coe_fn (aeval f) q) ≤ linear_map.ker (coe_fn (aeval f) (p * q)) := sorry

theorem sup_ker_aeval_eq_ker_aeval_mul_of_coprime {R : Type u} {M : Type w} [comm_ring R] [add_comm_group M] [module R M] (f : linear_map R M M) {p : polynomial R} {q : polynomial R} (hpq : is_coprime p q) : linear_map.ker (coe_fn (aeval f) p) ⊔ linear_map.ker (coe_fn (aeval f) q) = linear_map.ker (coe_fn (aeval f) (p * q)) := sorry

end polynomial


namespace mv_polynomial


theorem is_noetherian_ring_fin_0 {R : Type u} [comm_ring R] [is_noetherian_ring R] : is_noetherian_ring (mv_polynomial (fin 0) R) :=
  is_noetherian_ring_of_ring_equiv R
    (ring_equiv.trans (ring_equiv.symm (pempty_ring_equiv R)) (ring_equiv_of_equiv R (equiv.symm fin_zero_equiv')))

theorem is_noetherian_ring_fin {R : Type u} [comm_ring R] [is_noetherian_ring R] {n : ℕ} : is_noetherian_ring (mv_polynomial (fin n) R) := sorry

/-- The multivariate polynomial ring in finitely many variables over a noetherian ring
is itself a noetherian ring. -/
protected instance is_noetherian_ring {R : Type u} {σ : Type v} [comm_ring R] [fintype σ] [is_noetherian_ring R] : is_noetherian_ring (mv_polynomial σ R) :=
  trunc.induction_on (fintype.equiv_fin σ)
    fun (e : σ ≃ fin (fintype.card σ)) =>
      is_noetherian_ring_of_ring_equiv (mv_polynomial (fin (fintype.card σ)) R) (ring_equiv_of_equiv R (equiv.symm e))

theorem is_integral_domain_fin_zero (R : Type u) [comm_ring R] (hR : is_integral_domain R) : is_integral_domain (mv_polynomial (fin 0) R) :=
  ring_equiv.is_integral_domain R hR (ring_equiv.trans (ring_equiv_of_equiv R fin_zero_equiv') (pempty_ring_equiv R))

/-- Auxilliary lemma:
Multivariate polynomials over an integral domain
with variables indexed by `fin n` form an integral domain.
This fact is proven inductively,
and then used to prove the general case without any finiteness hypotheses.
See `mv_polynomial.integral_domain` for the general case. -/
theorem is_integral_domain_fin (R : Type u) [comm_ring R] (hR : is_integral_domain R) (n : ℕ) : is_integral_domain (mv_polynomial (fin n) R) := sorry

theorem is_integral_domain_fintype (R : Type u) (σ : Type v) [comm_ring R] [fintype σ] (hR : is_integral_domain R) : is_integral_domain (mv_polynomial σ R) := sorry

/-- Auxilliary definition:
Multivariate polynomials in finitely many variables over an integral domain form an integral domain.
This fact is proven by transport of structure from the `mv_polynomial.integral_domain_fin`,
and then used to prove the general case without finiteness hypotheses.
See `mv_polynomial.integral_domain` for the general case. -/
def integral_domain_fintype (R : Type u) (σ : Type v) [integral_domain R] [fintype σ] : integral_domain (mv_polynomial σ R) :=
  is_integral_domain.to_integral_domain (mv_polynomial σ R) sorry

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {R : Type u} [integral_domain R] {σ : Type v} (p : mv_polynomial σ R) (q : mv_polynomial σ R) (h : p * q = 0) : p = 0 ∨ q = 0 := sorry

/-- The multivariate polynomial ring over an integral domain is an integral domain. -/
protected instance integral_domain {R : Type u} {σ : Type v} [integral_domain R] : integral_domain (mv_polynomial σ R) :=
  integral_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul
    sorry comm_ring.one sorry sorry sorry sorry sorry sorry mv_polynomial.eq_zero_or_eq_zero_of_mul_eq_zero

theorem map_mv_polynomial_eq_eval₂ {R : Type u} {σ : Type v} [comm_ring R] {S : Type u_1} [comm_ring S] [fintype σ] (ϕ : mv_polynomial σ R →+* S) (p : mv_polynomial σ R) : coe_fn ϕ p = eval₂ (ring_hom.comp ϕ C) (fun (s : σ) => coe_fn ϕ (X s)) p := sorry

end mv_polynomial


namespace polynomial


protected instance unique_factorization_monoid {D : Type u} [integral_domain D] [unique_factorization_monoid D] : unique_factorization_monoid (polynomial D) :=
  Mathlib.ufm_of_gcd_of_wf_dvd_monoid

