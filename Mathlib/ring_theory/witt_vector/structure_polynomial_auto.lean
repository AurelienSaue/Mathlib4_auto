/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.matrix.notation
import Mathlib.field_theory.mv_polynomial
import Mathlib.field_theory.finite.polynomial
import Mathlib.number_theory.basic
import Mathlib.ring_theory.witt_vector.witt_polynomial
import PostPort

universes u_2 u_1 

namespace Mathlib

/-!
# Witt structure polynomials

In this file we prove the main theorem that makes the whole theory of Witt vectors work.
Briefly, consider a polynomial `Φ : mv_polynomial idx ℤ` over the integers,
with polynomials variables indexed by an arbitrary type `idx`.

Then there exists a unique family of polynomials `φ : ℕ → mv_polynomial (idx × ℕ) Φ`
such that for all `n : ℕ` we have (`witt_structure_int_exists_unique`)
```
bind₁ φ (witt_polynomial p ℤ n) = bind₁ (λ i, (rename (prod.mk i) (witt_polynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

N.b.: As far as we know, these polynomials do not have a name in the literature,
so we have decided to call them the “Witt structure polynomials”. See `witt_structure_int`.

## Special cases

With the main result of this file in place, we apply it to certain special polynomials.
For example, by taking `Φ = X tt + X ff` resp. `Φ = X tt * X ff`
we obtain families of polynomials `witt_add` resp. `witt_mul`
(with type `ℕ → mv_polynomial (bool × ℕ) ℤ`) that will be used in later files to define the
addition and multiplication on the ring of Witt vectors.

## Outline of the proof

The proof of `witt_structure_int_exists_unique` is rather technical, and takes up most of this file.

We start by proving the analogous version for polynomials with rational coefficients,
instead of integer coefficients.
In this case, the solution is rather easy,
since the Witt polynomials form a faithful change of coordinates
in the polynomial ring `mv_polynomial ℕ ℚ`.
We therefore obtain a family of polynomials `witt_structure_rat Φ`
for every `Φ : mv_polynomial idx ℚ`.

If `Φ` has integer coefficients, then the polynomials `witt_structure_rat Φ n` do so as well.
Proving this claim is the essential core of this file, and culminates in
`map_witt_structure_int`, which proves that upon mapping the coefficients
of `witt_structure_int Φ n` from the integers to the rationals,
one obtains `witt_structure_rat Φ n`.
Ultimately, the proof of `map_witt_structure_int` relies on
```
dvd_sub_pow_of_dvd_sub {R : Type*} [comm_ring R] {p : ℕ} {a b : R} :
    (p : R) ∣ a - b → ∀ (k : ℕ), (p : R) ^ (k + 1) ∣ a ^ p ^ k - b ^ p ^ k
```

## Main results

* `witt_structure_rat Φ`: the family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℚ`
  associated with `Φ : mv_polynomial idx ℚ` and satisfying the property explained above.
* `witt_structure_rat_prop`: the proof that `witt_structure_rat` indeed satisfies the property.
* `witt_structure_int Φ`: the family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℤ`
  associated with `Φ : mv_polynomial idx ℤ` and satisfying the property explained above.
* `map_witt_structure_int`: the proof that the integral polynomials `with_structure_int Φ`
  are equal to `witt_structure_rat Φ` when mapped to polynomials with rational coefficients.
* `witt_structure_int_prop`: the proof that `witt_structure_int` indeed satisfies the property.
* Five families of polynomials that will be used to define the ring structure
  on the ring of Witt vectors:
  - `witt_vector.witt_zero`
  - `witt_vector.witt_one`
  - `witt_vector.witt_add`
  - `witt_vector.witt_mul`
  - `witt_vector.witt_neg`
  (We also define `witt_vector.witt_sub`, and later we will prove that it describes subtraction,
  which is defined as `λ a b, a + -b`. See `witt_vector.sub_coeff` for this proof.)

-/

-- This lemma reduces a bundled morphism to a "mere" function,

-- and consequently the simplifier cannot use a lot of powerful simp-lemmas.

-- We disable this locally, and probably it should be disabled globally in mathlib.

/-- `witt_structure_rat Φ` is a family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℚ`
that are uniquely characterised by the property that
```
bind₁ (witt_structure_rat p Φ) (witt_polynomial p ℚ n) =
bind₁ (λ i, (rename (prod.mk i) (witt_polynomial p ℚ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `witt_structure_rat Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

See `witt_structure_rat_prop` for this property,
and `witt_structure_rat_exists_unique` for the fact that `witt_structure_rat`
gives the unique family of polynomials with this property.

These polynomials turn out to have integral coefficients,
but it requires some effort to show this.
See `witt_structure_int` for the version with integral coefficients,
and `map_witt_structure_int` for the fact that it is equal to `witt_structure_rat`
when mapped to polynomials over the rationals. -/
def witt_structure_rat (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℚ) (n : ℕ) : mv_polynomial (idx × ℕ) ℚ :=
  coe_fn
    (mv_polynomial.bind₁
      fun (k : ℕ) =>
        coe_fn (mv_polynomial.bind₁ fun (i : idx) => coe_fn (mv_polynomial.rename (Prod.mk i)) (witt_polynomial p ℚ k)) Φ)
    (X_in_terms_of_W p ℚ n)

theorem witt_structure_rat_prop (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℚ) (n : ℕ) : coe_fn (mv_polynomial.bind₁ (witt_structure_rat p Φ)) (witt_polynomial p ℚ n) =
  coe_fn (mv_polynomial.bind₁ fun (i : idx) => coe_fn (mv_polynomial.rename (Prod.mk i)) (witt_polynomial p ℚ n)) Φ := sorry

theorem witt_structure_rat_exists_unique (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℚ) : exists_unique
  fun (φ : ℕ → mv_polynomial (idx × ℕ) ℚ) =>
    ∀ (n : ℕ),
      coe_fn (mv_polynomial.bind₁ φ) (witt_polynomial p ℚ n) =
        coe_fn (mv_polynomial.bind₁ fun (i : idx) => coe_fn (mv_polynomial.rename (Prod.mk i)) (witt_polynomial p ℚ n))
          Φ := sorry

theorem witt_structure_rat_rec_aux (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℚ) (n : ℕ) : witt_structure_rat p Φ n * coe_fn mv_polynomial.C (↑p ^ n) =
  coe_fn
      (mv_polynomial.bind₁ fun (b : idx) => coe_fn (mv_polynomial.rename fun (i : ℕ) => (b, i)) (witt_polynomial p ℚ n))
      Φ -
    finset.sum (finset.range n) fun (i : ℕ) => coe_fn mv_polynomial.C (↑p ^ i) * witt_structure_rat p Φ i ^ p ^ (n - i) := sorry

/-- Write `witt_structure_rat p φ n` in terms of `witt_structure_rat p φ i` for `i < n`. -/
theorem witt_structure_rat_rec (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℚ) (n : ℕ) : witt_structure_rat p Φ n =
  coe_fn mv_polynomial.C (1 / ↑p ^ n) *
    (coe_fn
        (mv_polynomial.bind₁
          fun (b : idx) => coe_fn (mv_polynomial.rename fun (i : ℕ) => (b, i)) (witt_polynomial p ℚ n))
        Φ -
      finset.sum (finset.range n)
        fun (i : ℕ) => coe_fn mv_polynomial.C (↑p ^ i) * witt_structure_rat p Φ i ^ p ^ (n - i)) := sorry

/-- `witt_structure_int Φ` is a family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℚ`
that are uniquely characterised by the property that
```
bind₁ (witt_structure_int p Φ) (witt_polynomial p ℚ n) =
bind₁ (λ i, (rename (prod.mk i) (witt_polynomial p ℚ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `witt_structure_int Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

See `witt_structure_int_prop` for this property,
and `witt_structure_int_exists_unique` for the fact that `witt_structure_int`
gives the unique family of polynomials with this property. -/
def witt_structure_int (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℤ) (n : ℕ) : mv_polynomial (idx × ℕ) ℤ :=
  finsupp.map_range rat.num sorry (witt_structure_rat p (coe_fn (mv_polynomial.map (int.cast_ring_hom ℚ)) Φ) n)

theorem bind₁_rename_expand_witt_polynomial {p : ℕ} {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℤ) (n : ℕ) (IH : ∀ (m : ℕ),
  m < n + 1 →
    coe_fn (mv_polynomial.map (int.cast_ring_hom ℚ)) (witt_structure_int p Φ m) =
      witt_structure_rat p (coe_fn (mv_polynomial.map (int.cast_ring_hom ℚ)) Φ) m) : coe_fn
    (mv_polynomial.bind₁
      fun (b : idx) =>
        coe_fn (mv_polynomial.rename fun (i : ℕ) => (b, i)) (coe_fn (mv_polynomial.expand p) (witt_polynomial p ℤ n)))
    Φ =
  coe_fn (mv_polynomial.bind₁ fun (i : ℕ) => coe_fn (mv_polynomial.expand p) (witt_structure_int p Φ i))
    (witt_polynomial p ℤ n) := sorry

theorem C_p_pow_dvd_bind₁_rename_witt_polynomial_sub_sum {p : ℕ} {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℤ) (n : ℕ) (IH : ∀ (m : ℕ),
  m < n →
    coe_fn (mv_polynomial.map (int.cast_ring_hom ℚ)) (witt_structure_int p Φ m) =
      witt_structure_rat p (coe_fn (mv_polynomial.map (int.cast_ring_hom ℚ)) Φ) m) : coe_fn mv_polynomial.C ↑(p ^ n) ∣
  coe_fn
      (mv_polynomial.bind₁ fun (b : idx) => coe_fn (mv_polynomial.rename fun (i : ℕ) => (b, i)) (witt_polynomial p ℤ n))
      Φ -
    finset.sum (finset.range n) fun (i : ℕ) => coe_fn mv_polynomial.C (↑p ^ i) * witt_structure_int p Φ i ^ p ^ (n - i) := sorry

@[simp] theorem map_witt_structure_int (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℤ) (n : ℕ) : coe_fn (mv_polynomial.map (int.cast_ring_hom ℚ)) (witt_structure_int p Φ n) =
  witt_structure_rat p (coe_fn (mv_polynomial.map (int.cast_ring_hom ℚ)) Φ) n := sorry

theorem witt_structure_int_prop (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℤ) (n : ℕ) : coe_fn (mv_polynomial.bind₁ (witt_structure_int p Φ)) (witt_polynomial p ℤ n) =
  coe_fn (mv_polynomial.bind₁ fun (i : idx) => coe_fn (mv_polynomial.rename (Prod.mk i)) (witt_polynomial p ℤ n)) Φ := sorry

theorem eq_witt_structure_int (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℤ) (φ : ℕ → mv_polynomial (idx × ℕ) ℤ) (h : ∀ (n : ℕ),
  coe_fn (mv_polynomial.bind₁ φ) (witt_polynomial p ℤ n) =
    coe_fn (mv_polynomial.bind₁ fun (i : idx) => coe_fn (mv_polynomial.rename (Prod.mk i)) (witt_polynomial p ℤ n)) Φ) : φ = witt_structure_int p Φ := sorry

theorem witt_structure_int_exists_unique (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℤ) : exists_unique
  fun (φ : ℕ → mv_polynomial (idx × ℕ) ℤ) =>
    ∀ (n : ℕ),
      coe_fn (mv_polynomial.bind₁ φ) (witt_polynomial p ℤ n) =
        coe_fn (mv_polynomial.bind₁ fun (i : idx) => coe_fn (mv_polynomial.rename (Prod.mk i)) (witt_polynomial p ℤ n))
          Φ :=
  Exists.intro (witt_structure_int p Φ) { left := witt_structure_int_prop p Φ, right := eq_witt_structure_int p Φ }

theorem witt_structure_prop (p : ℕ) {R : Type u_1} {idx : Type u_2} [comm_ring R] [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℤ) (n : ℕ) : coe_fn (mv_polynomial.aeval fun (i : ℕ) => coe_fn (mv_polynomial.map (int.cast_ring_hom R)) (witt_structure_int p Φ i))
    (witt_polynomial p ℤ n) =
  coe_fn (mv_polynomial.aeval fun (i : idx) => coe_fn (mv_polynomial.rename (Prod.mk i)) (witt_polynomial p R n)) Φ := sorry

theorem witt_structure_int_rename (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] {σ : Type u_1} (Φ : mv_polynomial idx ℤ) (f : idx → σ) (n : ℕ) : witt_structure_int p (coe_fn (mv_polynomial.rename f) Φ) n =
  coe_fn (mv_polynomial.rename (prod.map f id)) (witt_structure_int p Φ n) := sorry

@[simp] theorem constant_coeff_witt_structure_rat_zero (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℚ) : coe_fn mv_polynomial.constant_coeff (witt_structure_rat p Φ 0) = coe_fn mv_polynomial.constant_coeff Φ := sorry

theorem constant_coeff_witt_structure_rat (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℚ) (h : coe_fn mv_polynomial.constant_coeff Φ = 0) (n : ℕ) : coe_fn mv_polynomial.constant_coeff (witt_structure_rat p Φ n) = 0 := sorry

@[simp] theorem constant_coeff_witt_structure_int_zero (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℤ) : coe_fn mv_polynomial.constant_coeff (witt_structure_int p Φ 0) = coe_fn mv_polynomial.constant_coeff Φ := sorry

theorem constant_coeff_witt_structure_int (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] (Φ : mv_polynomial idx ℤ) (h : coe_fn mv_polynomial.constant_coeff Φ = 0) (n : ℕ) : coe_fn mv_polynomial.constant_coeff (witt_structure_int p Φ n) = 0 := sorry

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.

-- for our applications `idx` is always finite.

theorem witt_structure_rat_vars (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] [fintype idx] (Φ : mv_polynomial idx ℚ) (n : ℕ) : mv_polynomial.vars (witt_structure_rat p Φ n) ⊆ finset.product finset.univ (finset.range (n + 1)) := sorry

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.

-- for our applications `idx` is always finite.

theorem witt_structure_int_vars (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)] [fintype idx] (Φ : mv_polynomial idx ℤ) (n : ℕ) : mv_polynomial.vars (witt_structure_int p Φ n) ⊆ finset.product finset.univ (finset.range (n + 1)) := sorry

