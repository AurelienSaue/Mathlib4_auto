/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.polynomial.big_operators
import Mathlib.field_theory.minpoly
import Mathlib.field_theory.splitting_field
import Mathlib.field_theory.tower
import Mathlib.algebra.squarefree
import Mathlib.PostPort

universes u u_1 v u_2 u_3 

namespace Mathlib

/-!

# Separable polynomials

We define a polynomial to be separable if it is coprime with its derivative. We prove basic
properties about separable polynomials here.

## Main definitions

* `polynomial.separable f`: a polynomial `f` is separable iff it is coprime with its derivative.
* `polynomial.expand R p f`: expand the polynomial `f` with coefficients in a
  commutative semiring `R` by a factor of p, so `expand R p (∑ aₙ xⁿ)` is `∑ aₙ xⁿᵖ`.
* `polynomial.contract p f`: the opposite of `expand`, so it sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`.

-/

namespace polynomial


/-- A polynomial is separable iff it is coprime with its derivative. -/
def separable {R : Type u} [comm_semiring R] (f : polynomial R) :=
  is_coprime f (coe_fn derivative f)

theorem separable_def {R : Type u} [comm_semiring R] (f : polynomial R) : separable f ↔ is_coprime f (coe_fn derivative f) :=
  iff.rfl

theorem separable_def' {R : Type u} [comm_semiring R] (f : polynomial R) : separable f ↔ ∃ (a : polynomial R), ∃ (b : polynomial R), a * f + b * coe_fn derivative f = 1 :=
  iff.rfl

theorem separable_one {R : Type u} [comm_semiring R] : separable 1 :=
  is_coprime_one_left

theorem separable_X_add_C {R : Type u} [comm_semiring R] (a : R) : separable (X + coe_fn C a) := sorry

theorem separable_X {R : Type u} [comm_semiring R] : separable X :=
  eq.mpr (id (Eq._oldrec (Eq.refl (separable X)) (propext (separable_def X))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime X (coe_fn derivative X))) derivative_X)) is_coprime_one_right)

theorem separable_C {R : Type u} [comm_semiring R] (r : R) : separable (coe_fn C r) ↔ is_unit r := sorry

theorem separable.of_mul_left {R : Type u} [comm_semiring R] {f : polynomial R} {g : polynomial R} (h : separable (f * g)) : separable f := sorry

theorem separable.of_mul_right {R : Type u} [comm_semiring R] {f : polynomial R} {g : polynomial R} (h : separable (f * g)) : separable g :=
  separable.of_mul_left (eq.mp (Eq._oldrec (Eq.refl (separable (f * g))) (mul_comm f g)) h)

theorem separable.of_dvd {R : Type u} [comm_semiring R] {f : polynomial R} {g : polynomial R} (hf : separable f) (hfg : g ∣ f) : separable g :=
  Exists.dcases_on hfg
    fun (f' : polynomial R) (hfg_h : f = g * f') =>
      Eq._oldrec (fun (hf : separable (g * f')) => separable.of_mul_left hf) (Eq.symm hfg_h) hf

theorem separable_gcd_left {F : Type u_1} [field F] {f : polynomial F} (hf : separable f) (g : polynomial F) : separable (euclidean_domain.gcd f g) :=
  separable.of_dvd hf (euclidean_domain.gcd_dvd_left f g)

theorem separable_gcd_right {F : Type u_1} [field F] {g : polynomial F} (f : polynomial F) (hg : separable g) : separable (euclidean_domain.gcd f g) :=
  separable.of_dvd hg (euclidean_domain.gcd_dvd_right f g)

theorem separable.is_coprime {R : Type u} [comm_semiring R] {f : polynomial R} {g : polynomial R} (h : separable (f * g)) : is_coprime f g := sorry

theorem separable.of_pow' {R : Type u} [comm_semiring R] {f : polynomial R} {n : ℕ} (h : separable (f ^ n)) : is_unit f ∨ separable f ∧ n = 1 ∨ n = 0 := sorry

theorem separable.of_pow {R : Type u} [comm_semiring R] {f : polynomial R} (hf : ¬is_unit f) {n : ℕ} (hn : n ≠ 0) (hfs : separable (f ^ n)) : separable f ∧ n = 1 :=
  or.resolve_right (or.resolve_left (separable.of_pow' hfs) hf) hn

theorem separable.map {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S] {p : polynomial R} (h : separable p) {f : R →+* S} : separable (map f p) := sorry

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`. -/
def expand (R : Type u) [comm_semiring R] (p : ℕ) : alg_hom R (polynomial R) (polynomial R) :=
  alg_hom.mk (ring_hom.to_fun (eval₂_ring_hom C (X ^ p))) sorry sorry sorry sorry sorry

theorem coe_expand (R : Type u) [comm_semiring R] (p : ℕ) : ⇑(expand R p) = eval₂ C (X ^ p) :=
  rfl

theorem expand_eq_sum {R : Type u} [comm_semiring R] (p : ℕ) {f : polynomial R} : coe_fn (expand R p) f = finsupp.sum f fun (e : ℕ) (a : R) => coe_fn C a * (X ^ p) ^ e :=
  id (Eq.refl (finsupp.sum f fun (e : ℕ) (a : R) => coe_fn C a * (X ^ p) ^ e))

@[simp] theorem expand_C {R : Type u} [comm_semiring R] (p : ℕ) (r : R) : coe_fn (expand R p) (coe_fn C r) = coe_fn C r :=
  eval₂_C C (X ^ p)

@[simp] theorem expand_X {R : Type u} [comm_semiring R] (p : ℕ) : coe_fn (expand R p) X = X ^ p :=
  eval₂_X C (X ^ p)

@[simp] theorem expand_monomial {R : Type u} [comm_semiring R] (p : ℕ) (q : ℕ) (r : R) : coe_fn (expand R p) (coe_fn (monomial q) r) = coe_fn (monomial (q * p)) r := sorry

theorem expand_expand {R : Type u} [comm_semiring R] (p : ℕ) (q : ℕ) (f : polynomial R) : coe_fn (expand R p) (coe_fn (expand R q) f) = coe_fn (expand R (p * q)) f := sorry

theorem expand_mul {R : Type u} [comm_semiring R] (p : ℕ) (q : ℕ) (f : polynomial R) : coe_fn (expand R (p * q)) f = coe_fn (expand R p) (coe_fn (expand R q) f) :=
  Eq.symm (expand_expand p q f)

@[simp] theorem expand_one {R : Type u} [comm_semiring R] (f : polynomial R) : coe_fn (expand R 1) f = f := sorry

theorem expand_pow {R : Type u} [comm_semiring R] (p : ℕ) (q : ℕ) (f : polynomial R) : coe_fn (expand R (p ^ q)) f = nat.iterate (⇑(expand R p)) q f := sorry

theorem derivative_expand {R : Type u} [comm_semiring R] (p : ℕ) (f : polynomial R) : coe_fn derivative (coe_fn (expand R p) f) = coe_fn (expand R p) (coe_fn derivative f) * (↑p * X ^ (p - 1)) := sorry

theorem coeff_expand {R : Type u} [comm_semiring R] {p : ℕ} (hp : 0 < p) (f : polynomial R) (n : ℕ) : coeff (coe_fn (expand R p) f) n = ite (p ∣ n) (coeff f (n / p)) 0 := sorry

@[simp] theorem coeff_expand_mul {R : Type u} [comm_semiring R] {p : ℕ} (hp : 0 < p) (f : polynomial R) (n : ℕ) : coeff (coe_fn (expand R p) f) (n * p) = coeff f n := sorry

@[simp] theorem coeff_expand_mul' {R : Type u} [comm_semiring R] {p : ℕ} (hp : 0 < p) (f : polynomial R) (n : ℕ) : coeff (coe_fn (expand R p) f) (p * n) = coeff f n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coeff (coe_fn (expand R p) f) (p * n) = coeff f n)) (mul_comm p n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coeff (coe_fn (expand R p) f) (n * p) = coeff f n)) (coeff_expand_mul hp f n)))
      (Eq.refl (coeff f n)))

theorem expand_eq_map_domain {R : Type u} [comm_semiring R] (p : ℕ) (f : polynomial R) : coe_fn (expand R p) f = finsupp.map_domain (fun (_x : ℕ) => _x * p) f := sorry

theorem expand_inj {R : Type u} [comm_semiring R] {p : ℕ} (hp : 0 < p) {f : polynomial R} {g : polynomial R} : coe_fn (expand R p) f = coe_fn (expand R p) g ↔ f = g := sorry

theorem expand_eq_zero {R : Type u} [comm_semiring R] {p : ℕ} (hp : 0 < p) {f : polynomial R} : coe_fn (expand R p) f = 0 ↔ f = 0 := sorry

theorem expand_eq_C {R : Type u} [comm_semiring R] {p : ℕ} (hp : 0 < p) {f : polynomial R} {r : R} : coe_fn (expand R p) f = coe_fn C r ↔ f = coe_fn C r := sorry

theorem nat_degree_expand {R : Type u} [comm_semiring R] (p : ℕ) (f : polynomial R) : nat_degree (coe_fn (expand R p) f) = nat_degree f * p := sorry

theorem map_expand {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S] {p : ℕ} (hp : 0 < p) {f : R →+* S} {q : polynomial R} : map f (coe_fn (expand R p) q) = coe_fn (expand S p) (map f q) := sorry

theorem separable_X_sub_C {R : Type u} [comm_ring R] {x : R} : separable (X - coe_fn C x) := sorry

theorem separable.mul {R : Type u} [comm_ring R] {f : polynomial R} {g : polynomial R} (hf : separable f) (hg : separable g) (h : is_coprime f g) : separable (f * g) := sorry

theorem separable_prod' {R : Type u} [comm_ring R] {ι : Type u_1} {f : ι → polynomial R} {s : finset ι} : (∀ (x : ι), x ∈ s → ∀ (y : ι), y ∈ s → x ≠ y → is_coprime (f x) (f y)) →
  (∀ (x : ι), x ∈ s → separable (f x)) → separable (finset.prod s fun (x : ι) => f x) := sorry

theorem separable_prod {R : Type u} [comm_ring R] {ι : Type u_1} [fintype ι] {f : ι → polynomial R} (h1 : pairwise (is_coprime on f)) (h2 : ∀ (x : ι), separable (f x)) : separable (finset.prod finset.univ fun (x : ι) => f x) :=
  separable_prod' (fun (x : ι) (hx : x ∈ finset.univ) (y : ι) (hy : y ∈ finset.univ) (hxy : x ≠ y) => h1 x y hxy)
    fun (x : ι) (hx : x ∈ finset.univ) => h2 x

theorem separable.inj_of_prod_X_sub_C {R : Type u} [comm_ring R] [nontrivial R] {ι : Type u_1} {f : ι → R} {s : finset ι} (hfs : separable (finset.prod s fun (i : ι) => X - coe_fn C (f i))) {x : ι} {y : ι} (hx : x ∈ s) (hy : y ∈ s) (hfxy : f x = f y) : x = y := sorry

theorem separable.injective_of_prod_X_sub_C {R : Type u} [comm_ring R] [nontrivial R] {ι : Type u_1} [fintype ι] {f : ι → R} (hfs : separable (finset.prod finset.univ fun (i : ι) => X - coe_fn C (f i))) : function.injective f :=
  fun (x y : ι) (hfxy : f x = f y) => separable.inj_of_prod_X_sub_C hfs (finset.mem_univ x) (finset.mem_univ y) hfxy

theorem is_unit_of_self_mul_dvd_separable {R : Type u} [comm_ring R] {p : polynomial R} {q : polynomial R} (hp : separable p) (hq : q * q ∣ p) : is_unit q := sorry

theorem is_local_ring_hom_expand (R : Type u) [integral_domain R] {p : ℕ} (hp : 0 < p) : is_local_ring_hom ↑(expand R p) := sorry

theorem separable_iff_derivative_ne_zero {F : Type u} [field F] {f : polynomial F} (hf : irreducible f) : separable f ↔ coe_fn derivative f ≠ 0 := sorry

theorem separable_map {F : Type u} [field F] {K : Type v} [field K] (f : F →+* K) {p : polynomial F} : separable (map f p) ↔ separable p := sorry

/-- The opposite of `expand`: sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`. -/
def contract {F : Type u} [field F] (p : ℕ) [hp : fact (nat.prime p)] (f : polynomial F) : polynomial F :=
  finsupp.mk (finset.preimage (finsupp.support f) (fun (_x : ℕ) => _x * p) sorry) (fun (n : ℕ) => coeff f (n * p)) sorry

theorem coeff_contract {F : Type u} [field F] (p : ℕ) [hp : fact (nat.prime p)] (f : polynomial F) (n : ℕ) : coeff (contract p f) n = coeff f (n * p) :=
  rfl

theorem of_irreducible_expand {F : Type u} [field F] (p : ℕ) [hp : fact (nat.prime p)] {f : polynomial F} (hf : irreducible (coe_fn (expand F p) f)) : irreducible f :=
  of_irreducible_map (↑(expand F p)) hf

theorem of_irreducible_expand_pow {F : Type u} [field F] (p : ℕ) [hp : fact (nat.prime p)] {f : polynomial F} {n : ℕ} : irreducible (coe_fn (expand F (p ^ n)) f) → irreducible f := sorry

theorem expand_char {F : Type u} [field F] (p : ℕ) [hp : fact (nat.prime p)] [HF : char_p F p] (f : polynomial F) : map (frobenius F p) (coe_fn (expand F p) f) = f ^ p := sorry

theorem map_expand_pow_char {F : Type u} [field F] (p : ℕ) [hp : fact (nat.prime p)] [HF : char_p F p] (f : polynomial F) (n : ℕ) : map (frobenius F p ^ n) (coe_fn (expand F (p ^ n)) f) = f ^ p ^ n := sorry

theorem expand_contract {F : Type u} [field F] (p : ℕ) [hp : fact (nat.prime p)] [HF : char_p F p] {f : polynomial F} (hf : coe_fn derivative f = 0) : coe_fn (expand F p) (contract p f) = f := sorry

theorem separable_or {F : Type u} [field F] (p : ℕ) [hp : fact (nat.prime p)] [HF : char_p F p] {f : polynomial F} (hf : irreducible f) : separable f ∨ ¬separable f ∧ ∃ (g : polynomial F), irreducible g ∧ coe_fn (expand F p) g = f := sorry

theorem exists_separable_of_irreducible {F : Type u} [field F] (p : ℕ) [hp : fact (nat.prime p)] [HF : char_p F p] {f : polynomial F} (hf : irreducible f) (hf0 : f ≠ 0) : ∃ (n : ℕ), ∃ (g : polynomial F), separable g ∧ coe_fn (expand F (p ^ n)) g = f := sorry

theorem is_unit_or_eq_zero_of_separable_expand {F : Type u} [field F] (p : ℕ) [hp : fact (nat.prime p)] [HF : char_p F p] {f : polynomial F} (n : ℕ) (hf : separable (coe_fn (expand F (p ^ n)) f)) : is_unit f ∨ n = 0 := sorry

theorem unique_separable_of_irreducible {F : Type u} [field F] (p : ℕ) [hp : fact (nat.prime p)] [HF : char_p F p] {f : polynomial F} (hf : irreducible f) (hf0 : f ≠ 0) (n₁ : ℕ) (g₁ : polynomial F) (hg₁ : separable g₁) (hgf₁ : coe_fn (expand F (p ^ n₁)) g₁ = f) (n₂ : ℕ) (g₂ : polynomial F) (hg₂ : separable g₂) (hgf₂ : coe_fn (expand F (p ^ n₂)) g₂ = f) : n₁ = n₂ ∧ g₁ = g₂ := sorry

theorem separable_prod_X_sub_C_iff' {F : Type u} [field F] {ι : Type u_1} {f : ι → F} {s : finset ι} : separable (finset.prod s fun (i : ι) => X - coe_fn C (f i)) ↔ ∀ (x : ι), x ∈ s → ∀ (y : ι), y ∈ s → f x = f y → x = y := sorry

theorem separable_prod_X_sub_C_iff {F : Type u} [field F] {ι : Type u_1} [fintype ι] {f : ι → F} : separable (finset.prod finset.univ fun (i : ι) => X - coe_fn C (f i)) ↔ function.injective f := sorry

theorem not_unit_X_sub_C {F : Type u} [field F] (a : F) : ¬is_unit (X - coe_fn C a) := sorry

theorem nodup_of_separable_prod {F : Type u} [field F] {s : multiset F} (hs : separable (multiset.prod (multiset.map (fun (a : F) => X - coe_fn C a) s))) : multiset.nodup s := sorry

theorem multiplicity_le_one_of_separable {F : Type u} [field F] {p : polynomial F} {q : polynomial F} (hq : ¬is_unit q) (hsep : separable p) : multiplicity q p ≤ 1 := sorry

theorem separable.squarefree {F : Type u} [field F] {p : polynomial F} (hsep : separable p) : squarefree p := sorry

/--If `n ≠ 0` in `F`, then ` X ^ n - a` is separable for any `a ≠ 0`. -/
theorem separable_X_pow_sub_C {F : Type u} [field F] {n : ℕ} (a : F) (hn : ↑n ≠ 0) (ha : a ≠ 0) : separable (X ^ n - coe_fn C a) := sorry

/--If `n ≠ 0` in `F`, then ` X ^ n - a` is squarefree for any `a ≠ 0`. -/
theorem squarefree_X_pow_sub_C {F : Type u} [field F] {n : ℕ} (a : F) (hn : ↑n ≠ 0) (ha : a ≠ 0) : squarefree (X ^ n - coe_fn C a) :=
  separable.squarefree (separable_X_pow_sub_C a hn ha)

theorem root_multiplicity_le_one_of_separable {F : Type u} [field F] {p : polynomial F} (hp : p ≠ 0) (hsep : separable p) (x : F) : root_multiplicity x p ≤ 1 := sorry

theorem count_roots_le_one {F : Type u} [field F] {p : polynomial F} (hsep : separable p) (x : F) : multiset.count x (roots p) ≤ 1 := sorry

theorem nodup_roots {F : Type u} [field F] {p : polynomial F} (hsep : separable p) : multiset.nodup (roots p) :=
  iff.mpr multiset.nodup_iff_count_le_one (count_roots_le_one hsep)

theorem eq_X_sub_C_of_separable_of_root_eq {F : Type u} [field F] {K : Type v} [field K] {i : F →+* K} {x : F} {h : polynomial F} (h_ne_zero : h ≠ 0) (h_sep : separable h) (h_root : eval x h = 0) (h_splits : splits i h) (h_roots : ∀ (y : K), y ∈ roots (map i h) → y = coe_fn i x) : h = coe_fn C (leading_coeff h) * (X - coe_fn C x) := sorry

end polynomial


theorem irreducible.separable {F : Type u} [field F] [char_zero F] {f : polynomial F} (hf : irreducible f) : polynomial.separable f := sorry

-- TODO: refactor to allow transcendental extensions?

-- See: https://en.wikipedia.org/wiki/Separable_extension#Separability_of_transcendental_extensions

/-- Typeclass for separable field extension: `K` is a separable field extension of `F` iff
the minimal polynomial of every `x : K` is separable. -/
def is_separable (F : Type u_1) (K : Type u_2) [field F] [field K] [algebra F K] :=
  ∀ (x : K), is_integral F x ∧ polynomial.separable (minpoly F x)

protected instance is_separable_self (F : Type u_1) [field F] : is_separable F F :=
  fun (x : F) =>
    { left := is_integral_algebra_map,
      right :=
        eq.mpr (id (Eq._oldrec (Eq.refl (polynomial.separable (minpoly F x))) (minpoly.eq_X_sub_C' x)))
          polynomial.separable_X_sub_C }

theorem is_separable_tower_top_of_is_separable (F : Type u_1) (K : Type u_2) (E : Type u_3) [field F] [field K] [field E] [algebra F K] [algebra F E] [algebra K E] [is_scalar_tower F K E] [h : is_separable F E] : is_separable K E := sorry

theorem is_separable_tower_bot_of_is_separable (F : Type u_1) (K : Type u_2) (E : Type u_3) [field F] [field K] [field E] [algebra F K] [algebra F E] [algebra K E] [is_scalar_tower F K E] [h : is_separable F E] : is_separable F K := sorry

theorem is_separable.of_alg_hom (F : Type u_1) {E : Type u_3} [field F] [field E] [algebra F E] (E' : Type u_2) [field E'] [algebra F E'] (f : alg_hom F E E') [is_separable F E'] : is_separable F E :=
  let _inst : algebra E E' := ring_hom.to_algebra (alg_hom.to_ring_hom f);
  is_separable_tower_bot_of_is_separable F E E'

