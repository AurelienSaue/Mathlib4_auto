/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.big_operators.ring
import Mathlib.number_theory.divisors
import Mathlib.algebra.squarefree
import Mathlib.algebra.invertible
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Arithmetic Functions and Dirichlet Convolution

This file defines arithmetic functions, which are functions from `ℕ` to a specified type that map 0
to 0. In the literature, they are often instead defined as functions from `ℕ+`. These arithmetic
functions are endowed with a multiplication, given by Dirichlet convolution, and pointwise addition,
to form the Dirichlet ring.

## Main Definitions
 * `arithmetic_function R` consists of functions `f : ℕ → R` such that `f 0 = 0`.
 * An arithmetic function `f` `is_multiplicative` when `x.coprime y → f (x * y) = f x * f y`.
 * The pointwise operations `pmul` and `ppow` differ from the multiplication
  and power instances on `arithmetic_function R`, which use Dirichlet multiplication.
 * `ζ` is the arithmetic function such that `ζ x = 1` for `0 < x`.
 * `σ k` is the arithmetic function such that `σ k x = ∑ y in divisors x, y ^ k` for `0 < x`.
 * `pow k` is the arithmetic function such that `pow k x = x ^ k` for `0 < x`.
 * `id` is the identity arithmetic function on `ℕ`.
 * `ω n` is the number of distinct prime factors of `n`.
 * `Ω n` is the number of prime factors of `n` counted with multiplicity.
 * `μ` is the Möbius function.

## Main Results
 * Several forms of Möbius inversion:
 * `sum_eq_iff_sum_mul_moebius_eq` for functions to a `comm_ring`
 * `sum_eq_iff_sum_smul_moebius_eq` for functions to an `add_comm_group`
 * `prod_eq_iff_prod_pow_moebius_eq` for functions to a `comm_group`
 * `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` for functions to a `comm_group_with_zero`

## Notation
The arithmetic functions `ζ` and `σ` have Greek letter names, which are localized notation in
the namespace `arithmetic_function`.

## Tags
arithmetic functions, dirichlet convolution, divisors

-/

namespace nat


/-- An arithmetic function is a function from `ℕ` that maps 0 to 0. In the literature, they are
  often instead defined as functions from `ℕ+`. Multiplication on `arithmetic_functions` is by
  Dirichlet convolution. -/
def arithmetic_function (R : Type u_1) [HasZero R] :=
  zero_hom ℕ R

namespace arithmetic_function


@[simp] theorem to_fun_eq {R : Type u_1} [HasZero R] (f : arithmetic_function R) : zero_hom.to_fun f = ⇑f :=
  rfl

@[simp] theorem map_zero {R : Type u_1} [HasZero R] {f : arithmetic_function R} : coe_fn f 0 = 0 :=
  zero_hom.map_zero' f

theorem coe_inj {R : Type u_1} [HasZero R] {f : arithmetic_function R} {g : arithmetic_function R} : ⇑f = ⇑g ↔ f = g :=
  { mp := fun (h : ⇑f = ⇑g) => zero_hom.coe_inj h, mpr := fun (h : f = g) => h ▸ rfl }

@[simp] theorem zero_apply {R : Type u_1} [HasZero R] {x : ℕ} : coe_fn 0 x = 0 :=
  zero_hom.zero_apply x

theorem ext {R : Type u_1} [HasZero R] {f : arithmetic_function R} {g : arithmetic_function R} (h : ∀ (x : ℕ), coe_fn f x = coe_fn g x) : f = g :=
  zero_hom.ext h

theorem ext_iff {R : Type u_1} [HasZero R] {f : arithmetic_function R} {g : arithmetic_function R} : f = g ↔ ∀ (x : ℕ), coe_fn f x = coe_fn g x :=
  zero_hom.ext_iff

protected instance has_one {R : Type u_1} [HasZero R] [HasOne R] : HasOne (arithmetic_function R) :=
  { one := zero_hom.mk (fun (x : ℕ) => ite (x = 1) 1 0) sorry }

@[simp] theorem one_one {R : Type u_1} [HasZero R] [HasOne R] : coe_fn 1 1 = 1 :=
  rfl

@[simp] theorem one_apply_ne {R : Type u_1} [HasZero R] [HasOne R] {x : ℕ} (h : x ≠ 1) : coe_fn 1 x = 0 :=
  if_neg h

protected instance nat_coe {R : Type u_1} [HasZero R] [HasOne R] [Add R] : has_coe (arithmetic_function ℕ) (arithmetic_function R) :=
  has_coe.mk fun (f : arithmetic_function ℕ) => zero_hom.mk ↑⇑f sorry

@[simp] theorem nat_coe_nat (f : arithmetic_function ℕ) : ↑f = f :=
  ext fun (_x : ℕ) => cast_id (coe_fn f _x)

@[simp] theorem nat_coe_apply {R : Type u_1} [HasZero R] [HasOne R] [Add R] {f : arithmetic_function ℕ} {x : ℕ} : coe_fn (↑f) x = ↑(coe_fn f x) :=
  rfl

protected instance int_coe {R : Type u_1} [HasZero R] [HasOne R] [Add R] [Neg R] : has_coe (arithmetic_function ℤ) (arithmetic_function R) :=
  has_coe.mk fun (f : arithmetic_function ℤ) => zero_hom.mk ↑⇑f sorry

@[simp] theorem int_coe_int (f : arithmetic_function ℤ) : ↑f = f :=
  ext fun (_x : ℕ) => int.cast_id (coe_fn f _x)

@[simp] theorem int_coe_apply {R : Type u_1} [HasZero R] [HasOne R] [Add R] [Neg R] {f : arithmetic_function ℤ} {x : ℕ} : coe_fn (↑f) x = ↑(coe_fn f x) :=
  rfl

@[simp] theorem coe_coe {R : Type u_1} [HasZero R] [HasOne R] [Add R] [Neg R] {f : arithmetic_function ℕ} : ↑↑f = ↑f := sorry

protected instance has_add {R : Type u_1} [add_monoid R] : Add (arithmetic_function R) :=
  { add := fun (f g : arithmetic_function R) => zero_hom.mk (fun (n : ℕ) => coe_fn f n + coe_fn g n) sorry }

@[simp] theorem add_apply {R : Type u_1} [add_monoid R] {f : arithmetic_function R} {g : arithmetic_function R} {n : ℕ} : coe_fn (f + g) n = coe_fn f n + coe_fn g n :=
  rfl

protected instance add_monoid {R : Type u_1} [add_monoid R] : add_monoid (arithmetic_function R) :=
  add_monoid.mk Add.add sorry 0 sorry sorry

protected instance add_comm_monoid {R : Type u_1} [add_comm_monoid R] : add_comm_monoid (arithmetic_function R) :=
  add_comm_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry sorry

protected instance add_group {R : Type u_1} [add_group R] : add_group (arithmetic_function R) :=
  add_group.mk add_monoid.add sorry add_monoid.zero sorry sorry
    (fun (f : arithmetic_function R) => zero_hom.mk (fun (n : ℕ) => -coe_fn f n) sorry)
    (sub_neg_monoid.sub._default add_monoid.add sorry add_monoid.zero sorry sorry
      fun (f : arithmetic_function R) => zero_hom.mk (fun (n : ℕ) => -coe_fn f n) sorry)
    sorry

protected instance add_comm_group {R : Type u_1} [add_comm_group R] : add_comm_group (arithmetic_function R) :=
  add_comm_group.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry add_group.neg add_group.sub sorry sorry

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
protected instance has_scalar {R : Type u_1} {M : Type u_2} [HasZero R] [add_comm_monoid M] [has_scalar R M] : has_scalar (arithmetic_function R) (arithmetic_function M) :=
  has_scalar.mk
    fun (f : arithmetic_function R) (g : arithmetic_function M) =>
      zero_hom.mk
        (fun (n : ℕ) =>
          finset.sum (divisors_antidiagonal n) fun (x : ℕ × ℕ) => coe_fn f (prod.fst x) • coe_fn g (prod.snd x))
        sorry

@[simp] theorem smul_apply {R : Type u_1} {M : Type u_2} [HasZero R] [add_comm_monoid M] [has_scalar R M] {f : arithmetic_function R} {g : arithmetic_function M} {n : ℕ} : coe_fn (f • g) n = finset.sum (divisors_antidiagonal n) fun (x : ℕ × ℕ) => coe_fn f (prod.fst x) • coe_fn g (prod.snd x) :=
  rfl

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
protected instance has_mul {R : Type u_1} [semiring R] : Mul (arithmetic_function R) :=
  { mul := has_scalar.smul }

@[simp] theorem mul_apply {R : Type u_1} [semiring R] {f : arithmetic_function R} {g : arithmetic_function R} {n : ℕ} : coe_fn (f * g) n = finset.sum (divisors_antidiagonal n) fun (x : ℕ × ℕ) => coe_fn f (prod.fst x) * coe_fn g (prod.snd x) :=
  rfl

theorem mul_smul' {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] (f : arithmetic_function R) (g : arithmetic_function R) (h : arithmetic_function M) : (f * g) • h = f • g • h := sorry

theorem one_smul' {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] (b : arithmetic_function M) : 1 • b = b := sorry

protected instance monoid {R : Type u_1} [semiring R] : monoid (arithmetic_function R) :=
  monoid.mk Mul.mul sorry 1 sorry sorry

protected instance semiring {R : Type u_1} [semiring R] : semiring (arithmetic_function R) :=
  semiring.mk Add.add sorry 0 sorry sorry sorry Mul.mul sorry monoid.one sorry sorry sorry sorry sorry sorry

protected instance comm_semiring {R : Type u_1} [comm_semiring R] : comm_semiring (arithmetic_function R) :=
  comm_semiring.mk semiring.add sorry semiring.zero sorry sorry sorry semiring.mul sorry semiring.one sorry sorry sorry
    sorry sorry sorry sorry

protected instance comm_ring {R : Type u_1} [comm_ring R] : comm_ring (arithmetic_function R) :=
  comm_ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    comm_semiring.mul sorry comm_semiring.one sorry sorry sorry sorry sorry

protected instance semimodule {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] : semimodule (arithmetic_function R) (arithmetic_function M) :=
  semimodule.mk sorry sorry

/-- `ζ 0 = 0`, otherwise `ζ x = 1`. The Dirichlet Series is the Riemann ζ.  -/
def zeta : arithmetic_function ℕ :=
  zero_hom.mk (fun (x : ℕ) => ite (x = 0) 0 1) sorry

@[simp] theorem zeta_apply {x : ℕ} : coe_fn zeta x = ite (x = 0) 0 1 :=
  rfl

theorem zeta_apply_ne {x : ℕ} (h : x ≠ 0) : coe_fn zeta x = 1 :=
  if_neg h

@[simp] theorem coe_zeta_mul_apply {R : Type u_1} [semiring R] {f : arithmetic_function R} {x : ℕ} : coe_fn (↑zeta * f) x = finset.sum (divisors x) fun (i : ℕ) => coe_fn f i := sorry

theorem coe_zeta_smul_apply {R : Type u_1} {M : Type u_2} [comm_ring R] [add_comm_group M] [module R M] {f : arithmetic_function M} {x : ℕ} : coe_fn (↑zeta • f) x = finset.sum (divisors x) fun (i : ℕ) => coe_fn f i := sorry

@[simp] theorem coe_mul_zeta_apply {R : Type u_1} [semiring R] {f : arithmetic_function R} {x : ℕ} : coe_fn (f * ↑zeta) x = finset.sum (divisors x) fun (i : ℕ) => coe_fn f i := sorry

theorem zeta_mul_apply {f : arithmetic_function ℕ} {x : ℕ} : coe_fn (zeta * f) x = finset.sum (divisors x) fun (i : ℕ) => coe_fn f i := sorry

theorem mul_zeta_apply {f : arithmetic_function ℕ} {x : ℕ} : coe_fn (f * zeta) x = finset.sum (divisors x) fun (i : ℕ) => coe_fn f i := sorry

/-- This is the pointwise product of `arithmetic_function`s. -/
def pmul {R : Type u_1} [mul_zero_class R] (f : arithmetic_function R) (g : arithmetic_function R) : arithmetic_function R :=
  zero_hom.mk (fun (x : ℕ) => coe_fn f x * coe_fn g x) sorry

@[simp] theorem pmul_apply {R : Type u_1} [mul_zero_class R] {f : arithmetic_function R} {g : arithmetic_function R} {x : ℕ} : coe_fn (pmul f g) x = coe_fn f x * coe_fn g x :=
  rfl

theorem pmul_comm {R : Type u_1} [comm_monoid_with_zero R] (f : arithmetic_function R) (g : arithmetic_function R) : pmul f g = pmul g f := sorry

@[simp] theorem pmul_zeta {R : Type u_1} [semiring R] (f : arithmetic_function R) : pmul f ↑zeta = f := sorry

@[simp] theorem zeta_pmul {R : Type u_1} [semiring R] (f : arithmetic_function R) : pmul (↑zeta) f = f := sorry

/-- This is the pointwise power of `arithmetic_function`s. -/
def ppow {R : Type u_1} [semiring R] (f : arithmetic_function R) (k : ℕ) : arithmetic_function R :=
  dite (k = 0) (fun (h0 : k = 0) => ↑zeta) fun (h0 : ¬k = 0) => zero_hom.mk (fun (x : ℕ) => coe_fn f x ^ k) sorry

@[simp] theorem ppow_zero {R : Type u_1} [semiring R] {f : arithmetic_function R} : ppow f 0 = ↑zeta := sorry

@[simp] theorem ppow_apply {R : Type u_1} [semiring R] {f : arithmetic_function R} {k : ℕ} {x : ℕ} (kpos : 0 < k) : coe_fn (ppow f k) x = coe_fn f x ^ k := sorry

theorem ppow_succ {R : Type u_1} [semiring R] {f : arithmetic_function R} {k : ℕ} : ppow f (k + 1) = pmul f (ppow f k) := sorry

theorem ppow_succ' {R : Type u_1} [semiring R] {f : arithmetic_function R} {k : ℕ} {kpos : 0 < k} : ppow f (k + 1) = pmul (ppow f k) f := sorry

/-- Multiplicative functions -/
def is_multiplicative {R : Type u_1} [monoid_with_zero R] (f : arithmetic_function R) :=
  coe_fn f 1 = 1 ∧ ∀ {m n : ℕ}, coprime m n → coe_fn f (m * n) = coe_fn f m * coe_fn f n

namespace is_multiplicative


@[simp] theorem map_one {R : Type u_1} [monoid_with_zero R] {f : arithmetic_function R} (h : is_multiplicative f) : coe_fn f 1 = 1 :=
  and.left h

@[simp] theorem map_mul_of_coprime {R : Type u_1} [monoid_with_zero R] {f : arithmetic_function R} (hf : is_multiplicative f) {m : ℕ} {n : ℕ} (h : coprime m n) : coe_fn f (m * n) = coe_fn f m * coe_fn f n :=
  and.right hf m n h

theorem nat_cast {R : Type u_1} {f : arithmetic_function ℕ} [semiring R] (h : is_multiplicative f) : is_multiplicative ↑f := sorry

theorem int_cast {R : Type u_1} {f : arithmetic_function ℤ} [ring R] (h : is_multiplicative f) : is_multiplicative ↑f := sorry

theorem mul {R : Type u_1} [comm_semiring R] {f : arithmetic_function R} {g : arithmetic_function R} (hf : is_multiplicative f) (hg : is_multiplicative g) : is_multiplicative (f * g) := sorry

theorem pmul {R : Type u_1} [comm_semiring R] {f : arithmetic_function R} {g : arithmetic_function R} (hf : is_multiplicative f) (hg : is_multiplicative g) : is_multiplicative (pmul f g) := sorry

end is_multiplicative


/-- The identity on `ℕ` as an `arithmetic_function`.  -/
def id : arithmetic_function ℕ :=
  zero_hom.mk id sorry

@[simp] theorem id_apply {x : ℕ} : coe_fn id x = x :=
  rfl

/-- `pow k n = n ^ k`, except `pow 0 0 = 0`. -/
def pow (k : ℕ) : arithmetic_function ℕ :=
  ppow id k

@[simp] theorem pow_apply {k : ℕ} {n : ℕ} : coe_fn (pow k) n = ite (k = 0 ∧ n = 0) 0 (n ^ k) := sorry

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def sigma (k : ℕ) : arithmetic_function ℕ :=
  zero_hom.mk (fun (n : ℕ) => finset.sum (divisors n) fun (d : ℕ) => d ^ k) sorry

@[simp] theorem sigma_apply {k : ℕ} {n : ℕ} : coe_fn (sigma k) n = finset.sum (divisors n) fun (d : ℕ) => d ^ k :=
  rfl

theorem sigma_one_apply {n : ℕ} : coe_fn (sigma 1) n = finset.sum (divisors n) fun (d : ℕ) => d := sorry

theorem zeta_mul_pow_eq_sigma {k : ℕ} : zeta * pow k = sigma k := sorry

theorem is_multiplicative_zeta : is_multiplicative zeta := sorry

theorem is_multiplicative_id : is_multiplicative id :=
  { left := rfl, right := fun (_x _x_1 : ℕ) (_x_2 : coprime _x _x_1) => rfl }

theorem is_multiplicative.ppow {R : Type u_1} [comm_semiring R] {f : arithmetic_function R} (hf : is_multiplicative f) {k : ℕ} : is_multiplicative (ppow f k) := sorry

theorem is_multiplicative_pow {k : ℕ} : is_multiplicative (pow k) :=
  is_multiplicative.ppow is_multiplicative_id

theorem is_multiplicative_sigma {k : ℕ} : is_multiplicative (sigma k) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_multiplicative (sigma k))) (Eq.symm zeta_mul_pow_eq_sigma)))
    (is_multiplicative.mul is_multiplicative_zeta is_multiplicative_pow)

/-- `Ω n` is the number of prime factors of `n`. -/
def card_factors : arithmetic_function ℕ :=
  zero_hom.mk (fun (n : ℕ) => list.length (factors n)) sorry

theorem card_factors_apply {n : ℕ} : coe_fn card_factors n = list.length (factors n) :=
  rfl

@[simp] theorem card_factors_one : coe_fn card_factors 1 = 0 :=
  rfl

theorem card_factors_eq_one_iff_prime {n : ℕ} : coe_fn card_factors n = 1 ↔ prime n := sorry

theorem card_factors_mul {m : ℕ} {n : ℕ} (m0 : m ≠ 0) (n0 : n ≠ 0) : coe_fn card_factors (m * n) = coe_fn card_factors m + coe_fn card_factors n := sorry

theorem card_factors_multiset_prod {s : multiset ℕ} (h0 : multiset.prod s ≠ 0) : coe_fn card_factors (multiset.prod s) = multiset.sum (multiset.map (⇑card_factors) s) := sorry

/-- `ω n` is the number of distinct prime factors of `n`. -/
def card_distinct_factors : arithmetic_function ℕ :=
  zero_hom.mk (fun (n : ℕ) => list.length (list.erase_dup (factors n))) sorry

@[simp] theorem card_distinct_factors_zero : coe_fn card_distinct_factors 0 = 0 :=
  rfl

theorem card_distinct_factors_apply {n : ℕ} : coe_fn card_distinct_factors n = list.length (list.erase_dup (factors n)) :=
  rfl

theorem card_distinct_factors_eq_card_factors_iff_squarefree {n : ℕ} (h0 : n ≠ 0) : coe_fn card_distinct_factors n = coe_fn card_factors n ↔ squarefree n := sorry

/-- `μ` is the Möbius function. If `n` is squarefree with an even number of distinct prime factors,
  `μ n = 1`. If `n` is squarefree with an odd number of distinct prime factors, `μ n = -1`.
  If `n` is not squarefree, `μ n = 0`. -/
def moebius : arithmetic_function ℤ :=
  zero_hom.mk (fun (n : ℕ) => ite (squarefree n) ((-1) ^ coe_fn card_factors n) 0) sorry

@[simp] theorem moebius_apply_of_squarefree {n : ℕ} (h : squarefree n) : coe_fn moebius n = (-1) ^ coe_fn card_factors n :=
  if_pos h

@[simp] theorem moebius_eq_zero_of_not_squarefree {n : ℕ} (h : ¬squarefree n) : coe_fn moebius n = 0 :=
  if_neg h

theorem moebius_ne_zero_iff_squarefree {n : ℕ} : coe_fn moebius n ≠ 0 ↔ squarefree n := sorry

theorem moebius_ne_zero_iff_eq_or {n : ℕ} : coe_fn moebius n ≠ 0 ↔ coe_fn moebius n = 1 ∨ coe_fn moebius n = -1 := sorry

@[simp] theorem coe_moebius_mul_coe_zeta {R : Type u_1} [comm_ring R] : ↑moebius * ↑zeta = 1 := sorry

@[simp] theorem coe_zeta_mul_coe_moebius {R : Type u_1} [comm_ring R] : ↑zeta * ↑moebius = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑zeta * ↑moebius = 1)) (mul_comm ↑zeta ↑moebius)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑moebius * ↑zeta = 1)) (coe_moebius_mul_coe_zeta R _inst_1))) (Eq.refl 1))

@[simp] theorem moebius_mul_coe_zeta : moebius * ↑zeta = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (moebius * ↑zeta = 1)) (Eq.symm (int_coe_int moebius))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑moebius * ↑zeta = 1)) (coe_moebius_mul_coe_zeta ℤ int.comm_ring))) (Eq.refl 1))

@[simp] theorem coe_zeta_mul_moebius : ↑zeta * moebius = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑zeta * moebius = 1)) (Eq.symm (int_coe_int moebius))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑zeta * ↑moebius = 1)) (coe_zeta_mul_coe_moebius ℤ int.comm_ring))) (Eq.refl 1))

protected instance zeta.invertible {R : Type u_1} [comm_ring R] : invertible ↑zeta :=
  invertible.mk (↑moebius) (coe_moebius_mul_coe_zeta R _inst_1) (coe_zeta_mul_coe_moebius R _inst_1)

/-- A unit in `arithmetic_function R` that evaluates to `ζ`, with inverse `μ`. -/
def zeta_unit {R : Type u_1} [comm_ring R] : units (arithmetic_function R) :=
  units.mk (↑zeta) (↑moebius) (coe_zeta_mul_coe_moebius R _inst_1) (coe_moebius_mul_coe_zeta R _inst_1)

@[simp] theorem coe_zeta_unit {R : Type u_1} [comm_ring R] : ↑(zeta_unit R _inst_1) = ↑zeta :=
  rfl

@[simp] theorem inv_zeta_unit {R : Type u_1} [comm_ring R] : ↑(zeta_unit R _inst_1⁻¹) = ↑moebius :=
  rfl

/-- Möbius inversion for functions to an `add_comm_group`. -/
theorem sum_eq_iff_sum_smul_moebius_eq {R : Type u_1} [add_comm_group R] {f : ℕ → R} {g : ℕ → R} : (∀ (n : ℕ), 0 < n → (finset.sum (divisors n) fun (i : ℕ) => f i) = g n) ↔
  ∀ (n : ℕ),
    0 < n → (finset.sum (divisors_antidiagonal n) fun (x : ℕ × ℕ) => coe_fn moebius (prod.fst x) • g (prod.snd x)) = f n := sorry

/-- Möbius inversion for functions to a `comm_ring`. -/
theorem sum_eq_iff_sum_mul_moebius_eq {R : Type u_1} [comm_ring R] {f : ℕ → R} {g : ℕ → R} : (∀ (n : ℕ), 0 < n → (finset.sum (divisors n) fun (i : ℕ) => f i) = g n) ↔
  ∀ (n : ℕ),
    0 < n →
      (finset.sum (divisors_antidiagonal n) fun (x : ℕ × ℕ) => ↑(coe_fn moebius (prod.fst x)) * g (prod.snd x)) = f n := sorry

/-- Möbius inversion for functions to a `comm_group`. -/
theorem prod_eq_iff_prod_pow_moebius_eq {R : Type u_1} [comm_group R] {f : ℕ → R} {g : ℕ → R} : (∀ (n : ℕ), 0 < n → (finset.prod (divisors n) fun (i : ℕ) => f i) = g n) ↔
  ∀ (n : ℕ),
    0 < n →
      (finset.prod (divisors_antidiagonal n) fun (x : ℕ × ℕ) => g (prod.snd x) ^ coe_fn moebius (prod.fst x)) = f n :=
  sum_eq_iff_sum_smul_moebius_eq (additive R) additive.add_comm_group (fun (i : ℕ) => f i) fun (n : ℕ) => g n

/-- Möbius inversion for functions to a `comm_group_with_zero`. -/
theorem prod_eq_iff_prod_pow_moebius_eq_of_nonzero {R : Type u_1} [comm_group_with_zero R] {f : ℕ → R} {g : ℕ → R} (hf : ∀ (n : ℕ), 0 < n → f n ≠ 0) (hg : ∀ (n : ℕ), 0 < n → g n ≠ 0) : (∀ (n : ℕ), 0 < n → (finset.prod (divisors n) fun (i : ℕ) => f i) = g n) ↔
  ∀ (n : ℕ),
    0 < n →
      (finset.prod (divisors_antidiagonal n) fun (x : ℕ × ℕ) => g (prod.snd x) ^ coe_fn moebius (prod.fst x)) = f n := sorry

