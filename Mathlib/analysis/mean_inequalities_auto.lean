/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.convex.specific_functions
import Mathlib.analysis.special_functions.pow
import Mathlib.data.real.conjugate_exponents
import Mathlib.tactic.nth_rewrite.default
import Mathlib.measure_theory.integration
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Mean value inequalities

In this file we prove several inequalities, including AM-GM inequality, Young's inequality,
Hölder inequality, and Minkowski inequality.

## Main theorems

### AM-GM inequality:

The inequality says that the geometric mean of a tuple of non-negative numbers is less than or equal
to their arithmetic mean. We prove the weighted version of this inequality: if $w$ and $z$
are two non-negative vectors and $\sum_{i\in s} w_i=1$, then
$$
\prod_{i\in s} z_i^{w_i} ≤ \sum_{i\in s} w_iz_i.
$$
The classical version is a special case of this inequality for $w_i=\frac{1}{n}$.

We prove a few versions of this inequality. Each of the following lemmas comes in two versions:
a version for real-valued non-negative functions is in the `real` namespace, and a version for
`nnreal`-valued functions is in the `nnreal` namespace.

- `geom_mean_le_arith_mean_weighted` : weighted version for functions on `finset`s;
- `geom_mean_le_arith_mean2_weighted` : weighted version for two numbers;
- `geom_mean_le_arith_mean3_weighted` : weighted version for three numbers;
- `geom_mean_le_arith_mean4_weighted` : weighted version for four numbers.

### Generalized mean inequality

The inequality says that for two non-negative vectors $w$ and $z$ with $\sum_{i\in s} w_i=1$
and $p ≤ q$ we have
$$
\sqrt[p]{\sum_{i\in s} w_i z_i^p} ≤ \sqrt[q]{\sum_{i\in s} w_i z_i^q}.
$$

Currently we only prove this inequality for $p=1$. As in the rest of `mathlib`, we provide
different theorems for natural exponents (`pow_arith_mean_le_arith_mean_pow`), integer exponents
(`fpow_arith_mean_le_arith_mean_fpow`), and real exponents (`rpow_arith_mean_le_arith_mean_rpow` and
`arith_mean_le_rpow_mean`). In the first two cases we prove
$$
\left(\sum_{i\in s} w_i z_i\right)^n ≤ \sum_{i\in s} w_i z_i^n
$$
in order to avoid using real exponents. For real exponents we prove both this and standard versions.

### Young's inequality

Young's inequality says that for non-negative numbers `a`, `b`, `p`, `q` such that
$\frac{1}{p}+\frac{1}{q}=1$ we have
$$
ab ≤ \frac{a^p}{p} + \frac{b^q}{q}.
$$

This inequality is a special case of the AM-GM inequality. It can be used to prove Hölder's
inequality (see below) but we use a different proof.

### Hölder's inequality

The inequality says that for two conjugate exponents `p` and `q` (i.e., for two positive numbers
such that $\frac{1}{p}+\frac{1}{q}=1$) and any two non-negative vectors their inner product is
less than or equal to the product of the $L_p$ norm of the first vector and the $L_q$ norm of the
second vector:
$$
\sum_{i\in s} a_ib_i ≤ \sqrt[p]{\sum_{i\in s} a_i^p}\sqrt[q]{\sum_{i\in s} b_i^q}.
$$

We give versions of this result in `real`, `nnreal` and `ennreal`.

There are at least two short proofs of this inequality. In one proof we prenormalize both vectors,
then apply Young's inequality to each $a_ib_i$. We use a different proof deducing this inequality
from the generalized mean inequality for well-chosen vectors and weights.

Hölder's inequality for the Lebesgue integral of ennreal and nnreal functions: we prove
`∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q` conjugate real exponents
and `α→(e)nnreal` functions in two cases,
* `ennreal.lintegral_mul_le_Lp_mul_Lq` : ennreal functions,
* `nnreal.lintegral_mul_le_Lp_mul_Lq`  : nnreal functions.

### Minkowski's inequality

The inequality says that for `p ≥ 1` the function
$$
\|a\|_p=\sqrt[p]{\sum_{i\in s} a_i^p}
$$
satisfies the triangle inequality $\|a+b\|_p\le \|a\|_p+\|b\|_p$.

We give versions of this result in `real`, `nnreal` and `ennreal`.

We deduce this inequality from Hölder's inequality. Namely, Hölder inequality implies that $\|a\|_p$
is the maximum of the inner product $\sum_{i\in s}a_ib_i$ over `b` such that $\|b\|_q\le 1$. Now
Minkowski's inequality follows from the fact that the maximum value of the sum of two functions is
less than or equal to the sum of the maximum values of the summands.

Minkowski's inequality for the Lebesgue integral of measurable functions with `ennreal` values:
we prove `(∫ (f + g)^p ∂μ) ^ (1/p) ≤ (∫ f^p ∂μ) ^ (1/p) + (∫ g^p ∂μ) ^ (1/p)` for `1 ≤ p`.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `strict_convex_on` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.
- prove integral versions of these inequalities.

-/

namespace real


/-- AM-GM inequality: the geometric mean is less than or equal to the arithmetic mean, weighted
version for real-valued nonnegative functions. -/
theorem geom_mean_le_arith_mean_weighted {ι : Type u} (s : finset ι) (w : ι → ℝ) (z : ι → ℝ)
    (hw : ∀ (i : ι), i ∈ s → 0 ≤ w i) (hw' : (finset.sum s fun (i : ι) => w i) = 1)
    (hz : ∀ (i : ι), i ∈ s → 0 ≤ z i) :
    (finset.prod s fun (i : ι) => z i ^ w i) ≤ finset.sum s fun (i : ι) => w i * z i :=
  sorry

theorem pow_arith_mean_le_arith_mean_pow {ι : Type u} (s : finset ι) (w : ι → ℝ) (z : ι → ℝ)
    (hw : ∀ (i : ι), i ∈ s → 0 ≤ w i) (hw' : (finset.sum s fun (i : ι) => w i) = 1)
    (hz : ∀ (i : ι), i ∈ s → 0 ≤ z i) (n : ℕ) :
    (finset.sum s fun (i : ι) => w i * z i) ^ n ≤ finset.sum s fun (i : ι) => w i * z i ^ n :=
  convex_on.map_sum_le (convex_on_pow n) hw hw' hz

theorem pow_arith_mean_le_arith_mean_pow_of_even {ι : Type u} (s : finset ι) (w : ι → ℝ) (z : ι → ℝ)
    (hw : ∀ (i : ι), i ∈ s → 0 ≤ w i) (hw' : (finset.sum s fun (i : ι) => w i) = 1) {n : ℕ}
    (hn : even n) :
    (finset.sum s fun (i : ι) => w i * z i) ^ n ≤ finset.sum s fun (i : ι) => w i * z i ^ n :=
  convex_on.map_sum_le (convex_on_pow_of_even hn) hw hw' fun (_x : ι) (_x : _x ∈ s) => trivial

theorem fpow_arith_mean_le_arith_mean_fpow {ι : Type u} (s : finset ι) (w : ι → ℝ) (z : ι → ℝ)
    (hw : ∀ (i : ι), i ∈ s → 0 ≤ w i) (hw' : (finset.sum s fun (i : ι) => w i) = 1)
    (hz : ∀ (i : ι), i ∈ s → 0 < z i) (m : ℤ) :
    (finset.sum s fun (i : ι) => w i * z i) ^ m ≤ finset.sum s fun (i : ι) => w i * z i ^ m :=
  convex_on.map_sum_le (convex_on_fpow m) hw hw' hz

theorem rpow_arith_mean_le_arith_mean_rpow {ι : Type u} (s : finset ι) (w : ι → ℝ) (z : ι → ℝ)
    (hw : ∀ (i : ι), i ∈ s → 0 ≤ w i) (hw' : (finset.sum s fun (i : ι) => w i) = 1)
    (hz : ∀ (i : ι), i ∈ s → 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
    (finset.sum s fun (i : ι) => w i * z i) ^ p ≤ finset.sum s fun (i : ι) => w i * z i ^ p :=
  convex_on.map_sum_le (convex_on_rpow hp) hw hw' hz

theorem arith_mean_le_rpow_mean {ι : Type u} (s : finset ι) (w : ι → ℝ) (z : ι → ℝ)
    (hw : ∀ (i : ι), i ∈ s → 0 ≤ w i) (hw' : (finset.sum s fun (i : ι) => w i) = 1)
    (hz : ∀ (i : ι), i ∈ s → 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
    (finset.sum s fun (i : ι) => w i * z i) ≤
        (finset.sum s fun (i : ι) => w i * z i ^ p) ^ (1 / p) :=
  sorry

end real


namespace nnreal


/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for `nnreal`-valued functions. -/
theorem geom_mean_le_arith_mean_weighted {ι : Type u} (s : finset ι) (w : ι → nnreal)
    (z : ι → nnreal) (hw' : (finset.sum s fun (i : ι) => w i) = 1) :
    (finset.prod s fun (i : ι) => z i ^ ↑(w i)) ≤ finset.sum s fun (i : ι) => w i * z i :=
  sorry

/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for two `nnreal` numbers. -/
theorem geom_mean_le_arith_mean2_weighted (w₁ : nnreal) (w₂ : nnreal) (p₁ : nnreal) (p₂ : nnreal) :
    w₁ + w₂ = 1 → p₁ ^ ↑w₁ * p₂ ^ ↑w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
  sorry

theorem geom_mean_le_arith_mean3_weighted (w₁ : nnreal) (w₂ : nnreal) (w₃ : nnreal) (p₁ : nnreal)
    (p₂ : nnreal) (p₃ : nnreal) :
    w₁ + w₂ + w₃ = 1 → p₁ ^ ↑w₁ * p₂ ^ ↑w₂ * p₃ ^ ↑w₃ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
  sorry

theorem geom_mean_le_arith_mean4_weighted (w₁ : nnreal) (w₂ : nnreal) (w₃ : nnreal) (w₄ : nnreal)
    (p₁ : nnreal) (p₂ : nnreal) (p₃ : nnreal) (p₄ : nnreal) :
    w₁ + w₂ + w₃ + w₄ = 1 →
        p₁ ^ ↑w₁ * p₂ ^ ↑w₂ * p₃ ^ ↑w₃ * p₄ ^ ↑w₄ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
  sorry

/-- Weighted generalized mean inequality, version sums over finite sets, with `ℝ≥0`-valued
functions and natural exponent. -/
theorem pow_arith_mean_le_arith_mean_pow {ι : Type u} (s : finset ι) (w : ι → nnreal)
    (z : ι → nnreal) (hw' : (finset.sum s fun (i : ι) => w i) = 1) (n : ℕ) :
    (finset.sum s fun (i : ι) => w i * z i) ^ n ≤ finset.sum s fun (i : ι) => w i * z i ^ n :=
  sorry

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
theorem rpow_arith_mean_le_arith_mean_rpow {ι : Type u} (s : finset ι) (w : ι → nnreal)
    (z : ι → nnreal) (hw' : (finset.sum s fun (i : ι) => w i) = 1) {p : ℝ} (hp : 1 ≤ p) :
    (finset.sum s fun (i : ι) => w i * z i) ^ p ≤ finset.sum s fun (i : ι) => w i * z i ^ p :=
  sorry

/-- Weighted generalized mean inequality, version for two elements of `ℝ≥0` and real exponents. -/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ : nnreal) (w₂ : nnreal) (z₁ : nnreal) (z₂ : nnreal)
    (hw' : w₁ + w₂ = 1) {p : ℝ} (hp : 1 ≤ p) :
    (w₁ * z₁ + w₂ * z₂) ^ p ≤ w₁ * z₁ ^ p + w₂ * z₂ ^ p :=
  sorry

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
theorem arith_mean_le_rpow_mean {ι : Type u} (s : finset ι) (w : ι → nnreal) (z : ι → nnreal)
    (hw' : (finset.sum s fun (i : ι) => w i) = 1) {p : ℝ} (hp : 1 ≤ p) :
    (finset.sum s fun (i : ι) => w i * z i) ≤
        (finset.sum s fun (i : ι) => w i * z i ^ p) ^ (1 / p) :=
  sorry

end nnreal


namespace ennreal


/-- Weighted generalized mean inequality, version for sums over finite sets, with `ennreal`-valued
functions and real exponents. -/
theorem rpow_arith_mean_le_arith_mean_rpow {ι : Type u} (s : finset ι) (w : ι → ennreal)
    (z : ι → ennreal) (hw' : (finset.sum s fun (i : ι) => w i) = 1) {p : ℝ} (hp : 1 ≤ p) :
    (finset.sum s fun (i : ι) => w i * z i) ^ p ≤ finset.sum s fun (i : ι) => w i * z i ^ p :=
  sorry

/-- Weighted generalized mean inequality, version for two elements of `ennreal` and real
exponents. -/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ : ennreal) (w₂ : ennreal) (z₁ : ennreal)
    (z₂ : ennreal) (hw' : w₁ + w₂ = 1) {p : ℝ} (hp : 1 ≤ p) :
    (w₁ * z₁ + w₂ * z₂) ^ p ≤ w₁ * z₁ ^ p + w₂ * z₂ ^ p :=
  sorry

end ennreal


namespace real


theorem geom_mean_le_arith_mean2_weighted {w₁ : ℝ} {w₂ : ℝ} {p₁ : ℝ} {p₂ : ℝ} (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
  nnreal.geom_mean_le_arith_mean2_weighted { val := w₁, property := hw₁ }
    { val := w₂, property := hw₂ } { val := p₁, property := hp₁ } { val := p₂, property := hp₂ }
    (iff.mp nnreal.coe_eq hw)

theorem geom_mean_le_arith_mean3_weighted {w₁ : ℝ} {w₂ : ℝ} {w₃ : ℝ} {p₁ : ℝ} {p₂ : ℝ} {p₃ : ℝ}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hw : w₁ + w₂ + w₃ = 1) : p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
  nnreal.geom_mean_le_arith_mean3_weighted { val := w₁, property := hw₁ }
    { val := w₂, property := hw₂ } { val := w₃, property := hw₃ } { val := p₁, property := hp₁ }
    { val := p₂, property := hp₂ } { val := p₃, property := hp₃ } (iff.mp nnreal.coe_eq hw)

theorem geom_mean_le_arith_mean4_weighted {w₁ : ℝ} {w₂ : ℝ} {w₃ : ℝ} {w₄ : ℝ} {p₁ : ℝ} {p₂ : ℝ}
    {p₃ : ℝ} {p₄ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hw₄ : 0 ≤ w₄) (hp₁ : 0 ≤ p₁)
    (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hp₄ : 0 ≤ p₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ * p₄ ^ w₄ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
  nnreal.geom_mean_le_arith_mean4_weighted { val := w₁, property := hw₁ }
    { val := w₂, property := hw₂ } { val := w₃, property := hw₃ } { val := w₄, property := hw₄ }
    { val := p₁, property := hp₁ } { val := p₂, property := hp₂ } { val := p₃, property := hp₃ }
    { val := p₄, property := hp₄ } (iff.mp nnreal.coe_eq hw)

/-- Young's inequality, a version for nonnegative real numbers. -/
theorem young_inequality_of_nonneg {a : ℝ} {b : ℝ} {p : ℝ} {q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpq : is_conjugate_exponent p q) : a * b ≤ a ^ p / p + b ^ q / q :=
  sorry

/-- Young's inequality, a version for arbitrary real numbers. -/
theorem young_inequality (a : ℝ) (b : ℝ) {p : ℝ} {q : ℝ} (hpq : is_conjugate_exponent p q) :
    a * b ≤ abs a ^ p / p + abs b ^ q / q :=
  le_trans (trans_rel_left LessEq (le_abs_self (a * b)) (abs_mul a b))
    (young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq)

end real


namespace nnreal


/-- Young's inequality, `ℝ≥0` version. We use `{p q : ℝ≥0}` in order to avoid constructing
witnesses of `0 ≤ p` and `0 ≤ q` for the denominators.  -/
theorem young_inequality (a : nnreal) (b : nnreal) {p : nnreal} {q : nnreal} (hp : 1 < p)
    (hpq : 1 / p + 1 / q = 1) : a * b ≤ a ^ ↑p / p + b ^ ↑q / q :=
  real.young_inequality_of_nonneg (coe_nonneg a) (coe_nonneg b)
    (real.is_conjugate_exponent.mk hp (iff.mpr nnreal.coe_eq hpq))

/-- Young's inequality, `ℝ≥0` version with real conjugate exponents. -/
theorem young_inequality_real (a : nnreal) (b : nnreal) {p : ℝ} {q : ℝ}
    (hpq : real.is_conjugate_exponent p q) :
    a * b ≤ a ^ p / nnreal.of_real p + b ^ q / nnreal.of_real q :=
  sorry

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0`-valued functions. -/
theorem inner_le_Lp_mul_Lq {ι : Type u} (s : finset ι) (f : ι → nnreal) (g : ι → nnreal) {p : ℝ}
    {q : ℝ} (hpq : real.is_conjugate_exponent p q) :
    (finset.sum s fun (i : ι) => f i * g i) ≤
        (finset.sum s fun (i : ι) => f i ^ p) ^ (1 / p) *
          (finset.sum s fun (i : ι) => g i ^ q) ^ (1 / q) :=
  sorry

/-- The `L_p` seminorm of a vector `f` is the greatest value of the inner product
`∑ i in s, f i * g i` over functions `g` of `L_q` seminorm less than or equal to one. -/
theorem is_greatest_Lp {ι : Type u} (s : finset ι) (f : ι → nnreal) {p : ℝ} {q : ℝ}
    (hpq : real.is_conjugate_exponent p q) :
    is_greatest
        ((fun (g : ι → nnreal) => finset.sum s fun (i : ι) => f i * g i) ''
          set_of fun (g : ι → nnreal) => (finset.sum s fun (i : ι) => g i ^ q) ≤ 1)
        ((finset.sum s fun (i : ι) => f i ^ p) ^ (1 / p)) :=
  sorry

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `nnreal`-valued functions. -/
theorem Lp_add_le {ι : Type u} (s : finset ι) (f : ι → nnreal) (g : ι → nnreal) {p : ℝ}
    (hp : 1 ≤ p) :
    (finset.sum s fun (i : ι) => (f i + g i) ^ p) ^ (1 / p) ≤
        (finset.sum s fun (i : ι) => f i ^ p) ^ (1 / p) +
          (finset.sum s fun (i : ι) => g i ^ p) ^ (1 / p) :=
  sorry

end nnreal


namespace real


/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued functions. -/
theorem inner_le_Lp_mul_Lq {ι : Type u} (s : finset ι) (f : ι → ℝ) (g : ι → ℝ) {p : ℝ} {q : ℝ}
    (hpq : is_conjugate_exponent p q) :
    (finset.sum s fun (i : ι) => f i * g i) ≤
        (finset.sum s fun (i : ι) => abs (f i) ^ p) ^ (1 / p) *
          (finset.sum s fun (i : ι) => abs (g i) ^ q) ^ (1 / q) :=
  sorry

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `real`-valued functions. -/
theorem Lp_add_le {ι : Type u} (s : finset ι) (f : ι → ℝ) (g : ι → ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (finset.sum s fun (i : ι) => abs (f i + g i) ^ p) ^ (1 / p) ≤
        (finset.sum s fun (i : ι) => abs (f i) ^ p) ^ (1 / p) +
          (finset.sum s fun (i : ι) => abs (g i) ^ p) ^ (1 / p) :=
  sorry

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued nonnegative functions. -/
theorem inner_le_Lp_mul_Lq_of_nonneg {ι : Type u} (s : finset ι) {f : ι → ℝ} {g : ι → ℝ} {p : ℝ}
    {q : ℝ} (hpq : is_conjugate_exponent p q) (hf : ∀ (i : ι), i ∈ s → 0 ≤ f i)
    (hg : ∀ (i : ι), i ∈ s → 0 ≤ g i) :
    (finset.sum s fun (i : ι) => f i * g i) ≤
        (finset.sum s fun (i : ι) => f i ^ p) ^ (1 / p) *
          (finset.sum s fun (i : ι) => g i ^ q) ^ (1 / q) :=
  sorry

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `real`-valued nonnegative
functions. -/
theorem Lp_add_le_of_nonneg {ι : Type u} (s : finset ι) {f : ι → ℝ} {g : ι → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : ∀ (i : ι), i ∈ s → 0 ≤ f i) (hg : ∀ (i : ι), i ∈ s → 0 ≤ g i) :
    (finset.sum s fun (i : ι) => (f i + g i) ^ p) ^ (1 / p) ≤
        (finset.sum s fun (i : ι) => f i ^ p) ^ (1 / p) +
          (finset.sum s fun (i : ι) => g i ^ p) ^ (1 / p) :=
  sorry

end real


namespace ennreal


/-- Young's inequality, `ennreal` version with real conjugate exponents. -/
theorem young_inequality (a : ennreal) (b : ennreal) {p : ℝ} {q : ℝ}
    (hpq : real.is_conjugate_exponent p q) :
    a * b ≤ a ^ p / ennreal.of_real p + b ^ q / ennreal.of_real q :=
  sorry

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ennreal`-valued functions. -/
theorem inner_le_Lp_mul_Lq {ι : Type u} (s : finset ι) (f : ι → ennreal) (g : ι → ennreal) {p : ℝ}
    {q : ℝ} (hpq : real.is_conjugate_exponent p q) :
    (finset.sum s fun (i : ι) => f i * g i) ≤
        (finset.sum s fun (i : ι) => f i ^ p) ^ (1 / p) *
          (finset.sum s fun (i : ι) => g i ^ q) ^ (1 / q) :=
  sorry

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ennreal` valued nonnegative
functions. -/
theorem Lp_add_le {ι : Type u} (s : finset ι) (f : ι → ennreal) (g : ι → ennreal) {p : ℝ}
    (hp : 1 ≤ p) :
    (finset.sum s fun (i : ι) => (f i + g i) ^ p) ^ (1 / p) ≤
        (finset.sum s fun (i : ι) => f i ^ p) ^ (1 / p) +
          (finset.sum s fun (i : ι) => g i ^ p) ^ (1 / p) :=
  sorry

theorem add_rpow_le_rpow_add {p : ℝ} (a : ennreal) (b : ennreal) (hp1 : 1 ≤ p) :
    a ^ p + b ^ p ≤ (a + b) ^ p :=
  sorry

theorem rpow_add_rpow_le_add {p : ℝ} (a : ennreal) (b : ennreal) (hp1 : 1 ≤ p) :
    (a ^ p + b ^ p) ^ (1 / p) ≤ a + b :=
  sorry

theorem rpow_add_rpow_le {p : ℝ} {q : ℝ} (a : ennreal) (b : ennreal) (hp_pos : 0 < p)
    (hpq : p ≤ q) : (a ^ q + b ^ q) ^ (1 / q) ≤ (a ^ p + b ^ p) ^ (1 / p) :=
  sorry

theorem rpow_add_le_add_rpow {p : ℝ} (a : ennreal) (b : ennreal) (hp_pos : 0 < p) (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p :=
  sorry

end ennreal


/-!
### Hölder's inequality for the Lebesgue integral of ennreal and nnreal functions

We prove `∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q`
conjugate real exponents and `α→(e)nnreal` functions in several cases, the first two being useful
only to prove the more general results:
* `ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one` : ennreal functions for which the
    integrals on the right are equal to 1,
* `ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top` : ennreal functions for which the
    integrals on the right are neither ⊤ nor 0,
* `ennreal.lintegral_mul_le_Lp_mul_Lq` : ennreal functions,
* `nnreal.lintegral_mul_le_Lp_mul_Lq`  : nnreal functions.
-/

namespace ennreal


theorem lintegral_mul_le_one_of_lintegral_rpow_eq_one {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {p : ℝ} {q : ℝ} (hpq : real.is_conjugate_exponent p q)
    {f : α → ennreal} {g : α → ennreal} (hf : ae_measurable f) (hg : ae_measurable g)
    (hf_norm : (measure_theory.lintegral μ fun (a : α) => f a ^ p) = 1)
    (hg_norm : (measure_theory.lintegral μ fun (a : α) => g a ^ q) = 1) :
    (measure_theory.lintegral μ fun (a : α) => Mul.mul f g a) ≤ 1 :=
  sorry

/-- Function multiplied by the inverse of its p-seminorm `(∫⁻ f^p ∂μ) ^ 1/p`-/
def fun_mul_inv_snorm {α : Type u_1} [measurable_space α] (f : α → ennreal) (p : ℝ)
    (μ : measure_theory.measure α) : α → ennreal :=
  fun (a : α) => f a * ((measure_theory.lintegral μ fun (c : α) => f c ^ p) ^ (1 / p)⁻¹)

theorem fun_eq_fun_mul_inv_snorm_mul_snorm {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {p : ℝ} (f : α → ennreal)
    (hf_nonzero : (measure_theory.lintegral μ fun (a : α) => f a ^ p) ≠ 0)
    (hf_top : (measure_theory.lintegral μ fun (a : α) => f a ^ p) ≠ ⊤) {a : α} :
    f a =
        fun_mul_inv_snorm f p μ a * (measure_theory.lintegral μ fun (a : α) => f a ^ p) ^ (1 / p) :=
  sorry

theorem fun_mul_inv_snorm_rpow {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α}
    {p : ℝ} (hp0 : 0 < p) {f : α → ennreal} {a : α} :
    fun_mul_inv_snorm f p μ a ^ p =
        f a ^ p * ((measure_theory.lintegral μ fun (c : α) => f c ^ p)⁻¹) :=
  sorry

theorem lintegral_rpow_fun_mul_inv_snorm_eq_one {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {p : ℝ} (hp0_lt : 0 < p) {f : α → ennreal} (hf : ae_measurable f)
    (hf_nonzero : (measure_theory.lintegral μ fun (a : α) => f a ^ p) ≠ 0)
    (hf_top : (measure_theory.lintegral μ fun (a : α) => f a ^ p) ≠ ⊤) :
    (measure_theory.lintegral μ fun (c : α) => fun_mul_inv_snorm f p μ c ^ p) = 1 :=
  sorry

/-- Hölder's inequality in case of finite non-zero integrals -/
theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {p : ℝ} {q : ℝ} (hpq : real.is_conjugate_exponent p q)
    {f : α → ennreal} {g : α → ennreal} (hf : ae_measurable f) (hg : ae_measurable g)
    (hf_nontop : (measure_theory.lintegral μ fun (a : α) => f a ^ p) ≠ ⊤)
    (hg_nontop : (measure_theory.lintegral μ fun (a : α) => g a ^ q) ≠ ⊤)
    (hf_nonzero : (measure_theory.lintegral μ fun (a : α) => f a ^ p) ≠ 0)
    (hg_nonzero : (measure_theory.lintegral μ fun (a : α) => g a ^ q) ≠ 0) :
    (measure_theory.lintegral μ fun (a : α) => Mul.mul f g a) ≤
        (measure_theory.lintegral μ fun (a : α) => f a ^ p) ^ (1 / p) *
          (measure_theory.lintegral μ fun (a : α) => g a ^ q) ^ (1 / q) :=
  sorry

theorem ae_eq_zero_of_lintegral_rpow_eq_zero {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {p : ℝ} (hp0_lt : 0 < p) {f : α → ennreal} (hf : ae_measurable f)
    (hf_zero : (measure_theory.lintegral μ fun (a : α) => f a ^ p) = 0) :
    filter.eventually_eq (measure_theory.measure.ae μ) f 0 :=
  sorry

theorem lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {p : ℝ} (hp0_lt : 0 < p) {f : α → ennreal} {g : α → ennreal}
    (hf : ae_measurable f) (hf_zero : (measure_theory.lintegral μ fun (a : α) => f a ^ p) = 0) :
    (measure_theory.lintegral μ fun (a : α) => Mul.mul f g a) = 0 :=
  sorry

theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {p : ℝ} {q : ℝ} (hp0_lt : 0 < p) (hq0 : 0 ≤ q) {f : α → ennreal}
    {g : α → ennreal} (hf_top : (measure_theory.lintegral μ fun (a : α) => f a ^ p) = ⊤)
    (hg_nonzero : (measure_theory.lintegral μ fun (a : α) => g a ^ q) ≠ 0) :
    (measure_theory.lintegral μ fun (a : α) => Mul.mul f g a) ≤
        (measure_theory.lintegral μ fun (a : α) => f a ^ p) ^ (1 / p) *
          (measure_theory.lintegral μ fun (a : α) => g a ^ q) ^ (1 / q) :=
  sorry

/-- Hölder's inequality for functions `α → ennreal`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem lintegral_mul_le_Lp_mul_Lq {α : Type u_1} [measurable_space α]
    (μ : measure_theory.measure α) {p : ℝ} {q : ℝ} (hpq : real.is_conjugate_exponent p q)
    {f : α → ennreal} {g : α → ennreal} (hf : ae_measurable f) (hg : ae_measurable g) :
    (measure_theory.lintegral μ fun (a : α) => Mul.mul f g a) ≤
        (measure_theory.lintegral μ fun (a : α) => f a ^ p) ^ (1 / p) *
          (measure_theory.lintegral μ fun (a : α) => g a ^ q) ^ (1 / q) :=
  sorry

theorem lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {p : ℝ} {f : α → ennreal} {g : α → ennreal}
    (hf : ae_measurable f) (hf_top : (measure_theory.lintegral μ fun (a : α) => f a ^ p) < ⊤)
    (hg : ae_measurable g) (hg_top : (measure_theory.lintegral μ fun (a : α) => g a ^ p) < ⊤)
    (hp1 : 1 ≤ p) : (measure_theory.lintegral μ fun (a : α) => Add.add f g a ^ p) < ⊤ :=
  sorry

theorem lintegral_Lp_mul_le_Lq_mul_Lr {α : Type u_1} [measurable_space α] {p : ℝ} {q : ℝ} {r : ℝ}
    (hp0_lt : 0 < p) (hpq : p < q) (hpqr : 1 / p = 1 / q + 1 / r) (μ : measure_theory.measure α)
    {f : α → ennreal} {g : α → ennreal} (hf : ae_measurable f) (hg : ae_measurable g) :
    (measure_theory.lintegral μ fun (a : α) => Mul.mul f g a ^ p) ^ (1 / p) ≤
        (measure_theory.lintegral μ fun (a : α) => f a ^ q) ^ (1 / q) *
          (measure_theory.lintegral μ fun (a : α) => g a ^ r) ^ (1 / r) :=
  sorry

theorem lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {p : ℝ} {q : ℝ} (hpq : real.is_conjugate_exponent p q)
    {f : α → ennreal} {g : α → ennreal} (hf : ae_measurable f) (hg : ae_measurable g)
    (hf_top : (measure_theory.lintegral μ fun (a : α) => f a ^ p) ≠ ⊤) :
    (measure_theory.lintegral μ fun (a : α) => f a * g a ^ (p - 1)) ≤
        (measure_theory.lintegral μ fun (a : α) => f a ^ p) ^ (1 / p) *
          (measure_theory.lintegral μ fun (a : α) => g a ^ p) ^ (1 / q) :=
  sorry

theorem lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {p : ℝ} {q : ℝ} (hpq : real.is_conjugate_exponent p q)
    {f : α → ennreal} {g : α → ennreal} (hf : ae_measurable f)
    (hf_top : (measure_theory.lintegral μ fun (a : α) => f a ^ p) ≠ ⊤) (hg : ae_measurable g)
    (hg_top : (measure_theory.lintegral μ fun (a : α) => g a ^ p) ≠ ⊤) :
    (measure_theory.lintegral μ fun (a : α) => Add.add f g a ^ p) ≤
        ((measure_theory.lintegral μ fun (a : α) => f a ^ p) ^ (1 / p) +
            (measure_theory.lintegral μ fun (a : α) => g a ^ p) ^ (1 / p)) *
          (measure_theory.lintegral μ fun (a : α) => (f a + g a) ^ p) ^ (1 / q) :=
  sorry

/-- Minkowski's inequality for functions `α → ennreal`: the `ℒp` seminorm of the sum of two
functions is bounded by the sum of their `ℒp` seminorms. -/
theorem lintegral_Lp_add_le {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α}
    {p : ℝ} {f : α → ennreal} {g : α → ennreal} (hf : ae_measurable f) (hg : ae_measurable g)
    (hp1 : 1 ≤ p) :
    (measure_theory.lintegral μ fun (a : α) => Add.add f g a ^ p) ^ (1 / p) ≤
        (measure_theory.lintegral μ fun (a : α) => f a ^ p) ^ (1 / p) +
          (measure_theory.lintegral μ fun (a : α) => g a ^ p) ^ (1 / p) :=
  sorry

end ennreal


/-- Hölder's inequality for functions `α → ℝ≥0`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem nnreal.lintegral_mul_le_Lp_mul_Lq {α : Type u_1} [measurable_space α]
    {μ : measure_theory.measure α} {p : ℝ} {q : ℝ} (hpq : real.is_conjugate_exponent p q)
    {f : α → nnreal} {g : α → nnreal} (hf : ae_measurable f) (hg : ae_measurable g) :
    (measure_theory.lintegral μ fun (a : α) => ↑(Mul.mul f g a)) ≤
        (measure_theory.lintegral μ fun (a : α) => ↑(f a) ^ p) ^ (1 / p) *
          (measure_theory.lintegral μ fun (a : α) => ↑(g a) ^ q) ^ (1 / q) :=
  sorry

end Mathlib