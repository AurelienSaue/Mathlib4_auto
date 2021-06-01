/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.eval
import Mathlib.algebra.algebra.tower
import Mathlib.PostPort

universes u z u_1 u_2 u_3 v 

namespace Mathlib

/-!
# Theory of univariate polynomials

We show that `polynomial A` is an R-algebra when `A` is an R-algebra.
We promote `eval₂` to an algebra hom in `aeval`.
-/

namespace polynomial


/-- Note that this instance also provides `algebra R (polynomial R)`. -/
protected instance algebra_of_algebra {R : Type u} {A : Type z} [comm_semiring R] [semiring A]
    [algebra R A] : algebra R (polynomial A) :=
  add_monoid_algebra.algebra

theorem algebra_map_apply {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A]
    (r : R) : coe_fn (algebra_map R (polynomial A)) r = coe_fn C (coe_fn (algebra_map R A) r) :=
  rfl

/--
When we have `[comm_ring R]`, the function `C` is the same as `algebra_map R (polynomial R)`.

(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebra_map` is not available.)
-/
theorem C_eq_algebra_map {R : Type u_1} [comm_ring R] (r : R) :
    coe_fn C r = coe_fn (algebra_map R (polynomial R)) r :=
  rfl

@[simp] theorem alg_hom_eval₂_algebra_map {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R]
    [ring A] [ring B] [algebra R A] [algebra R B] (p : polynomial R) (f : alg_hom R A B) (a : A) :
    coe_fn f (eval₂ (algebra_map R A) a p) = eval₂ (algebra_map R B) (coe_fn f a) p :=
  sorry

@[simp] theorem eval₂_algebra_map_X {R : Type u_1} {A : Type u_2} [comm_ring R] [ring A]
    [algebra R A] (p : polynomial R) (f : alg_hom R (polynomial R) A) :
    eval₂ (algebra_map R A) (coe_fn f X) p = coe_fn f p :=
  sorry

@[simp] theorem ring_hom_eval₂_algebra_map_int {R : Type u_1} {S : Type u_2} [ring R] [ring S]
    (p : polynomial ℤ) (f : R →+* S) (r : R) :
    coe_fn f (eval₂ (algebra_map ℤ R) r p) = eval₂ (algebra_map ℤ S) (coe_fn f r) p :=
  alg_hom_eval₂_algebra_map p (ring_hom.to_int_alg_hom f) r

@[simp] theorem eval₂_algebra_map_int_X {R : Type u_1} [ring R] (p : polynomial ℤ)
    (f : polynomial ℤ →+* R) : eval₂ (algebra_map ℤ R) (coe_fn f X) p = coe_fn f p :=
  sorry

-- Unfortunately `f.to_int_alg_hom` doesn't work here, as typeclasses don't match up correctly.

theorem eval₂_comp {R : Type u} {S : Type v} [comm_semiring R] {p : polynomial R} {q : polynomial R}
    [comm_semiring S] (f : R →+* S) {x : S} : eval₂ f x (comp p q) = eval₂ f (eval₂ f x q) p :=
  sorry

theorem eval_comp {R : Type u} {a : R} [comm_semiring R] {p : polynomial R} {q : polynomial R} :
    eval a (comp p q) = eval (eval a q) p :=
  eval₂_comp (ring_hom.id R)

protected instance comp.is_semiring_hom {R : Type u} [comm_semiring R] {p : polynomial R} :
    is_semiring_hom fun (q : polynomial R) => comp q p :=
  eq.mpr
    (id
      ((fun (f f_1 : polynomial R → polynomial R) (e_3 : f = f_1) => congr_arg is_semiring_hom e_3)
        (fun (q : polynomial R) => comp q p) (fun (q : polynomial R) => eval₂ C p q)
        (funext fun (q : polynomial R) => comp.equations._eqn_1 q p)))
    (eval₂.is_semiring_hom C p)

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`. -/
def aeval {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A] (x : A) :
    alg_hom R (polynomial R) A :=
  alg_hom.mk (ring_hom.to_fun (eval₂_ring_hom' (algebra_map R A) x sorry)) sorry sorry sorry sorry
    sorry

theorem alg_hom_ext {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A]
    {f : alg_hom R (polynomial R) A} {g : alg_hom R (polynomial R) A}
    (h : coe_fn f X = coe_fn g X) : f = g :=
  add_monoid_algebra.alg_hom_ext' (monoid_hom.ext_mnat h)

theorem aeval_def {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A] (x : A)
    (p : polynomial R) : coe_fn (aeval x) p = eval₂ (algebra_map R A) x p :=
  rfl

@[simp] theorem aeval_zero {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A]
    (x : A) : coe_fn (aeval x) 0 = 0 :=
  alg_hom.map_zero (aeval x)

@[simp] theorem aeval_X {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A]
    (x : A) : coe_fn (aeval x) X = x :=
  eval₂_X (algebra_map R A) x

@[simp] theorem aeval_C {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A]
    (x : A) (r : R) : coe_fn (aeval x) (coe_fn C r) = coe_fn (algebra_map R A) r :=
  eval₂_C (algebra_map R A) x

theorem aeval_monomial {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A]
    (x : A) {n : ℕ} {r : R} :
    coe_fn (aeval x) (coe_fn (monomial n) r) = coe_fn (algebra_map R A) r * x ^ n :=
  eval₂_monomial (algebra_map R A) x

@[simp] theorem aeval_X_pow {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A]
    (x : A) {n : ℕ} : coe_fn (aeval x) (X ^ n) = x ^ n :=
  eval₂_X_pow (algebra_map R A) x

@[simp] theorem aeval_add {R : Type u} {A : Type z} [comm_semiring R] {p : polynomial R}
    {q : polynomial R} [semiring A] [algebra R A] (x : A) :
    coe_fn (aeval x) (p + q) = coe_fn (aeval x) p + coe_fn (aeval x) q :=
  alg_hom.map_add (aeval x) p q

@[simp] theorem aeval_one {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A]
    (x : A) : coe_fn (aeval x) 1 = 1 :=
  alg_hom.map_one (aeval x)

@[simp] theorem aeval_bit0 {R : Type u} {A : Type z} [comm_semiring R] {p : polynomial R}
    [semiring A] [algebra R A] (x : A) : coe_fn (aeval x) (bit0 p) = bit0 (coe_fn (aeval x) p) :=
  alg_hom.map_bit0 (aeval x) p

@[simp] theorem aeval_bit1 {R : Type u} {A : Type z} [comm_semiring R] {p : polynomial R}
    [semiring A] [algebra R A] (x : A) : coe_fn (aeval x) (bit1 p) = bit1 (coe_fn (aeval x) p) :=
  alg_hom.map_bit1 (aeval x) p

@[simp] theorem aeval_nat_cast {R : Type u} {A : Type z} [comm_semiring R] [semiring A]
    [algebra R A] (x : A) (n : ℕ) : coe_fn (aeval x) ↑n = ↑n :=
  alg_hom.map_nat_cast (aeval x) n

theorem aeval_mul {R : Type u} {A : Type z} [comm_semiring R] {p : polynomial R} {q : polynomial R}
    [semiring A] [algebra R A] (x : A) :
    coe_fn (aeval x) (p * q) = coe_fn (aeval x) p * coe_fn (aeval x) q :=
  alg_hom.map_mul (aeval x) p q

theorem aeval_comp {R : Type u} [comm_semiring R] {p : polynomial R} {q : polynomial R}
    {A : Type u_1} [comm_semiring A] [algebra R A] (x : A) :
    coe_fn (aeval x) (comp p q) = coe_fn (aeval (coe_fn (aeval x) q)) p :=
  eval₂_comp (algebra_map R A)

@[simp] theorem aeval_map {R : Type u} [comm_semiring R] {B : Type u_1} [semiring B] [algebra R B]
    {A : Type u_2} [comm_semiring A] [algebra R A] [algebra A B] [is_scalar_tower R A B] (b : B)
    (p : polynomial R) : coe_fn (aeval b) (map (algebra_map R A) p) = coe_fn (aeval b) p :=
  sorry

theorem eval_unique {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A]
    (φ : alg_hom R (polynomial R) A) (p : polynomial R) :
    coe_fn φ p = eval₂ (algebra_map R A) (coe_fn φ X) p :=
  sorry

theorem aeval_alg_hom {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A]
    {B : Type u_1} [semiring B] [algebra R B] (f : alg_hom R A B) (x : A) :
    aeval (coe_fn f x) = alg_hom.comp f (aeval x) :=
  sorry

theorem aeval_alg_hom_apply {R : Type u} {A : Type z} [comm_semiring R] [semiring A] [algebra R A]
    {B : Type u_1} [semiring B] [algebra R B] (f : alg_hom R A B) (x : A) (p : polynomial R) :
    coe_fn (aeval (coe_fn f x)) p = coe_fn f (coe_fn (aeval x) p) :=
  iff.mp alg_hom.ext_iff (aeval_alg_hom f x) p

@[simp] theorem coe_aeval_eq_eval {R : Type u} [comm_semiring R] (r : R) : ⇑(aeval r) = eval r :=
  rfl

theorem coeff_zero_eq_aeval_zero {R : Type u} [comm_semiring R] (p : polynomial R) :
    coeff p 0 = coe_fn (aeval 0) p :=
  sorry

theorem pow_comp {R : Type u} [comm_semiring R] (p : polynomial R) (q : polynomial R) (k : ℕ) :
    comp (p ^ k) q = comp p q ^ k :=
  sorry

theorem is_root_of_eval₂_map_eq_zero {R : Type u} {S : Type v} [comm_semiring R] {p : polynomial R}
    [comm_ring S] {f : R →+* S} (hf : function.injective ⇑f) {r : R} :
    eval₂ f (coe_fn f r) p = 0 → is_root p r :=
  sorry

theorem is_root_of_aeval_algebra_map_eq_zero {R : Type u} {S : Type v} [comm_semiring R]
    [comm_ring S] [algebra R S] {p : polynomial R} (inj : function.injective ⇑(algebra_map R S))
    {r : R} (hr : coe_fn (aeval (coe_fn (algebra_map R S) r)) p = 0) : is_root p r :=
  is_root_of_eval₂_map_eq_zero inj hr

theorem dvd_term_of_dvd_eval_of_dvd_terms {S : Type v} [comm_ring S] {z : S} {p : S}
    {f : polynomial S} (i : ℕ) (dvd_eval : p ∣ eval z f)
    (dvd_terms : ∀ (j : ℕ), j ≠ i → p ∣ coeff f j * z ^ j) : p ∣ coeff f i * z ^ i :=
  sorry

theorem dvd_term_of_is_root_of_dvd_terms {S : Type v} [comm_ring S] {r : S} {p : S}
    {f : polynomial S} (i : ℕ) (hr : is_root f r) (h : ∀ (j : ℕ), j ≠ i → p ∣ coeff f j * r ^ j) :
    p ∣ coeff f i * r ^ i :=
  dvd_term_of_dvd_eval_of_dvd_terms i (Eq.symm hr ▸ dvd_zero p) h

theorem aeval_eq_sum_range {R : Type u} {S : Type v} [comm_semiring R] [comm_ring S] [algebra R S]
    {p : polynomial R} (x : S) :
    coe_fn (aeval x) p =
        finset.sum (finset.range (nat_degree p + 1)) fun (i : ℕ) => coeff p i • x ^ i :=
  sorry

theorem aeval_eq_sum_range' {R : Type u} {S : Type v} [comm_semiring R] [comm_ring S] [algebra R S]
    {p : polynomial R} {n : ℕ} (hn : nat_degree p < n) (x : S) :
    coe_fn (aeval x) p = finset.sum (finset.range n) fun (i : ℕ) => coeff p i • x ^ i :=
  sorry

/--
The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - monomial 0 r)` is sent to zero
when evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
theorem eval_mul_X_sub_C {R : Type u} [ring R] {p : polynomial R} (r : R) :
    eval r (p * (X - coe_fn C r)) = 0 :=
  sorry

theorem not_is_unit_X_sub_C {R : Type u} [ring R] [nontrivial R] {r : R} :
    ¬is_unit (X - coe_fn C r) :=
  sorry

theorem aeval_endomorphism {R : Type u} {M : Type u_1} [comm_ring R] [add_comm_group M] [module R M]
    (f : linear_map R M M) (v : M) (p : polynomial R) :
    coe_fn (coe_fn (aeval f) p) v = finsupp.sum p fun (n : ℕ) (b : R) => b • coe_fn (f ^ n) v :=
  sorry

end Mathlib