/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.calculus.formal_multilinear_series
import Mathlib.analysis.specific_limits
import PostPort

universes u_1 u_2 u_3 l 

namespace Mathlib

/-!
# Analytic functions

A function is analytic in one dimension around `0` if it can be written as a converging power series
`Σ pₙ zⁿ`. This definition can be extended to any dimension (even in infinite dimension) by
requiring that `pₙ` is a continuous `n`-multilinear map. In general, `pₙ` is not unique (in two
dimensions, taking `p₂ (x, y) (x', y') = x y'` or `y x'` gives the same map when applied to a
vector `(x, y) (x, y)`). A way to guarantee uniqueness is to take a symmetric `pₙ`, but this is not
always possible in nonzero characteristic (in characteristic 2, the previous example has no
symmetric representative). Therefore, we do not insist on symmetry or uniqueness in the definition,
and we only require the existence of a converging series.

The general framework is important to say that the exponential map on bounded operators on a Banach
space is analytic, as well as the inverse on invertible operators.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `p.radius`: the largest `r : ennreal` such that `∥p n∥ * r^n` grows subexponentially, defined as
  a liminf.
* `p.le_radius_of_bound`, `p.le_radius_of_bound_nnreal`, `p.le_radius_of_is_O`: if `∥p n∥ * r ^ n`
  is bounded above, then `r ≤ p.radius`;
* `p.is_o_of_lt_radius`, `p.norm_mul_pow_le_mul_pow_of_lt_radius`, `p.is_o_one_of_lt_radius`,
  `p.norm_mul_pow_le_of_lt_radius`, `p.nnnorm_mul_pow_le_of_lt_radius`: if `r < p.radius`, then
  `∥p n∥ * r ^ n` tends to zero exponentially;
* `p.lt_radius_of_is_O`: if `r ≠ 0` and `∥p n∥ * r ^ n = O(a ^ n)` for some `-1 < a < 1`, then
  `r < p.radius`;
* `p.partial_sum n x`: the sum `∑_{i = 0}^{n-1} pᵢ xⁱ`.
* `p.sum x`: the sum `∑'_{i = 0}^{∞} pᵢ xⁱ`.

Additionally, let `f` be a function from `E` to `F`.

* `has_fpower_series_on_ball f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₙ yⁿ`.
* `has_fpower_series_at f p x`: on some ball of center `x` with positive radius, holds
  `has_fpower_series_on_ball f p x r`.
* `analytic_at 𝕜 f x`: there exists a power series `p` such that holds
  `has_fpower_series_at f p x`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `has_fpower_series_on_ball.continuous_on` and `has_fpower_series_at.continuous_at` and
  `analytic_at.continuous_at`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `formal_multilinear_series.has_fpower_series_on_ball`.
* If a function admits a power series in a ball, then it is analytic at any point `y` of this ball,
  and the power series there can be expressed in terms of the initial power series `p` as
  `p.change_origin y`. See `has_fpower_series_on_ball.change_origin`. It follows in particular that
  the set of points at which a given function is analytic is open, see `is_open_analytic_at`.

## Implementation details

We only introduce the radius of convergence of a power series, as `p.radius`.
For a power series in finitely many dimensions, there is a finer (directional, coordinate-dependent)
notion, describing the polydisk of convergence. This notion is more specific, and not necessary to
build the general theory. We do not define it here.
-/

/-! ### The radius of a formal multilinear series -/

namespace formal_multilinear_series


/-- The radius of a formal multilinear series is the largest `r` such that the sum `Σ pₙ yⁿ`
converges for all `∥y∥ < r`. -/
def radius {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) : ennreal :=
  supr fun (r : nnreal) => supr fun (C : ℝ) => supr fun (hr : ∀ (n : ℕ), norm (p n) * ↑r ^ n ≤ C) => ↑r

/-- If `∥pₙ∥ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) (C : ℝ) {r : nnreal} (h : ∀ (n : ℕ), norm (p n) * ↑r ^ n ≤ C) : ↑r ≤ radius p :=
  le_supr_of_le r (le_supr_of_le C (le_supr (fun (_x : ∀ (n : ℕ), norm (p n) * ↑r ^ n ≤ C) => ↑r) h))

/-- If `∥pₙ∥ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound_nnreal {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) (C : nnreal) {r : nnreal} (h : ∀ (n : ℕ), nnnorm (p n) * r ^ n ≤ C) : ↑r ≤ radius p := sorry

/-- If `∥pₙ∥ rⁿ = O(1)`, as `n → ∞`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_is_O {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {r : nnreal} (h : asymptotics.is_O (fun (n : ℕ) => norm (p n) * ↑r ^ n) (fun (n : ℕ) => 1) filter.at_top) : ↑r ≤ radius p :=
  exists.elim (iff.mp asymptotics.is_O_one_nat_at_top_iff h)
    fun (C : ℝ) (hC : ∀ (n : ℕ), norm (norm (p n) * ↑r ^ n) ≤ C) =>
      le_radius_of_bound p C fun (n : ℕ) => has_le.le.trans (le_abs_self (norm (p n) * ↑r ^ n)) (hC n)

theorem radius_eq_top_of_forall_nnreal_is_O {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) (h : ∀ (r : nnreal), asymptotics.is_O (fun (n : ℕ) => norm (p n) * ↑r ^ n) (fun (n : ℕ) => 1) filter.at_top) : radius p = ⊤ :=
  ennreal.eq_top_of_forall_nnreal_le fun (r : nnreal) => le_radius_of_is_O p (h r)

theorem radius_eq_top_of_eventually_eq_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) (h : filter.eventually (fun (n : ℕ) => p n = 0) filter.at_top) : radius p = ⊤ := sorry

theorem radius_eq_top_of_forall_image_add_eq_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) (n : ℕ) (hn : ∀ (m : ℕ), p (m + n) = 0) : radius p = ⊤ :=
  radius_eq_top_of_eventually_eq_zero p
    (iff.mpr filter.mem_at_top_sets (Exists.intro n fun (k : ℕ) (hk : k ≥ n) => nat.sub_add_cancel hk ▸ hn (k - n)))

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` tends to zero exponentially:
for some `0 < a < 1`, `∥p n∥ rⁿ = o(aⁿ)`. -/
theorem is_o_of_lt_radius {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {r : nnreal} (h : ↑r < radius p) : ∃ (a : ℝ), ∃ (H : a ∈ set.Ioo 0 1), asymptotics.is_o (fun (n : ℕ) => norm (p n) * ↑r ^ n) (pow a) filter.at_top := sorry

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ = o(1)`. -/
theorem is_o_one_of_lt_radius {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {r : nnreal} (h : ↑r < radius p) : asymptotics.is_o (fun (n : ℕ) => norm (p n) * ↑r ^ n) (fun (_x : ℕ) => 1) filter.at_top := sorry

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` tends to zero exponentially:
for some `0 < a < 1` and `C > 0`,  `∥p n∥ * r ^ n ≤ C * a ^ n`. -/
theorem norm_mul_pow_le_mul_pow_of_lt_radius {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {r : nnreal} (h : ↑r < radius p) : ∃ (a : ℝ), ∃ (H : a ∈ set.Ioo 0 1), ∃ (C : ℝ), ∃ (H : C > 0), ∀ (n : ℕ), norm (p n) * ↑r ^ n ≤ C * a ^ n := sorry

/-- If `r ≠ 0` and `∥pₙ∥ rⁿ = O(aⁿ)` for some `-1 < a < 1`, then `r < p.radius`. -/
theorem lt_radius_of_is_O {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {r : nnreal} (h₀ : r ≠ 0) {a : ℝ} (ha : a ∈ set.Ioo (-1) 1) (hp : asymptotics.is_O (fun (n : ℕ) => norm (p n) * ↑r ^ n) (pow a) filter.at_top) : ↑r < radius p := sorry

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem norm_mul_pow_le_of_lt_radius {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {r : nnreal} (h : ↑r < radius p) : ∃ (C : ℝ), ∃ (H : C > 0), ∀ (n : ℕ), norm (p n) * ↑r ^ n ≤ C := sorry

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem norm_le_div_pow_of_pos_of_lt_radius {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {r : nnreal} (h0 : 0 < r) (h : ↑r < radius p) : ∃ (C : ℝ), ∃ (H : C > 0), ∀ (n : ℕ), norm (p n) ≤ C / ↑r ^ n := sorry

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem nnnorm_mul_pow_le_of_lt_radius {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {r : nnreal} (h : ↑r < radius p) : ∃ (C : nnreal), ∃ (H : C > 0), ∀ (n : ℕ), nnnorm (p n) * r ^ n ≤ C := sorry

/-- The radius of the sum of two formal series is at least the minimum of their two radii. -/
theorem min_radius_le_radius_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) (q : formal_multilinear_series 𝕜 E F) : min (radius p) (radius q) ≤ radius (p + q) := sorry

@[simp] theorem radius_neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) : radius (-p) = radius p := sorry

/-- Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A
priori, it only behaves well when `∥x∥ < p.radius`. -/
protected def sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) (x : E) : F :=
  tsum fun (n : ℕ) => coe_fn (p n) fun (i : fin n) => x

/-- Given a formal multilinear series `p` and a vector `x`, then `p.partial_sum n x` is the sum
`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/
def partial_sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) (n : ℕ) (x : E) : F :=
  finset.sum (finset.range n) fun (k : ℕ) => coe_fn (p k) fun (i : fin k) => x

/-- The partial sums of a formal multilinear series are continuous. -/
theorem partial_sum_continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) (n : ℕ) : continuous (partial_sum p n) := sorry

end formal_multilinear_series


/-! ### Expanding a function as a power series -/

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series on the ball of radius `r > 0` around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `∥y∥ < r`.
-/
structure has_fpower_series_on_ball {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (p : formal_multilinear_series 𝕜 E F) (x : E) (r : ennreal) 
where
  r_le : r ≤ formal_multilinear_series.radius p
  r_pos : 0 < r
  has_sum : ∀ {y : E}, y ∈ emetric.ball 0 r → has_sum (fun (n : ℕ) => coe_fn (p n) fun (i : fin n) => y) (f (x + y))

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a neighborhood of `0`. -/
def has_fpower_series_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (p : formal_multilinear_series 𝕜 E F) (x : E)  :=
  ∃ (r : ennreal), has_fpower_series_on_ball f p x r

/-- Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a convergent power
series expansion around `x`. -/
def analytic_at (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (x : E)  :=
  ∃ (p : formal_multilinear_series 𝕜 E F), has_fpower_series_at f p x

theorem has_fpower_series_on_ball.has_fpower_series_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} (hf : has_fpower_series_on_ball f p x r) : has_fpower_series_at f p x :=
  Exists.intro r hf

theorem has_fpower_series_at.analytic_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} (hf : has_fpower_series_at f p x) : analytic_at 𝕜 f x :=
  Exists.intro p hf

theorem has_fpower_series_on_ball.analytic_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} (hf : has_fpower_series_on_ball f p x r) : analytic_at 𝕜 f x :=
  has_fpower_series_at.analytic_at (has_fpower_series_on_ball.has_fpower_series_at hf)

theorem has_fpower_series_on_ball.has_sum_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} (hf : has_fpower_series_on_ball f p x r) {y : E} (hy : y ∈ emetric.ball x r) : has_sum (fun (n : ℕ) => coe_fn (p n) fun (i : fin n) => y - x) (f y) := sorry

theorem has_fpower_series_on_ball.radius_pos {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} (hf : has_fpower_series_on_ball f p x r) : 0 < formal_multilinear_series.radius p :=
  lt_of_lt_of_le (has_fpower_series_on_ball.r_pos hf) (has_fpower_series_on_ball.r_le hf)

theorem has_fpower_series_at.radius_pos {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} (hf : has_fpower_series_at f p x) : 0 < formal_multilinear_series.radius p := sorry

theorem has_fpower_series_on_ball.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} {r' : ennreal} (hf : has_fpower_series_on_ball f p x r) (r'_pos : 0 < r') (hr : r' ≤ r) : has_fpower_series_on_ball f p x r' :=
  has_fpower_series_on_ball.mk (le_trans hr (has_fpower_series_on_ball.r_le hf)) r'_pos
    fun (y : E) (hy : y ∈ emetric.ball 0 r') => has_fpower_series_on_ball.has_sum hf (emetric.ball_subset_ball hr hy)

protected theorem has_fpower_series_at.eventually {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} (hf : has_fpower_series_at f p x) : filter.eventually (fun (r : ennreal) => has_fpower_series_on_ball f p x r) (nhds_within 0 (set.Ioi 0)) := sorry

theorem has_fpower_series_on_ball.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {g : E → F} {pf : formal_multilinear_series 𝕜 E F} {pg : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} (hf : has_fpower_series_on_ball f pf x r) (hg : has_fpower_series_on_ball g pg x r) : has_fpower_series_on_ball (f + g) (pf + pg) x r := sorry

theorem has_fpower_series_at.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {g : E → F} {pf : formal_multilinear_series 𝕜 E F} {pg : formal_multilinear_series 𝕜 E F} {x : E} (hf : has_fpower_series_at f pf x) (hg : has_fpower_series_at g pg x) : has_fpower_series_at (f + g) (pf + pg) x := sorry

theorem analytic_at.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {g : E → F} {x : E} (hf : analytic_at 𝕜 f x) (hg : analytic_at 𝕜 g x) : analytic_at 𝕜 (f + g) x := sorry

theorem has_fpower_series_on_ball.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {pf : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} (hf : has_fpower_series_on_ball f pf x r) : has_fpower_series_on_ball (-f) (-pf) x r := sorry

theorem has_fpower_series_at.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {pf : formal_multilinear_series 𝕜 E F} {x : E} (hf : has_fpower_series_at f pf x) : has_fpower_series_at (-f) (-pf) x := sorry

theorem analytic_at.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} (hf : analytic_at 𝕜 f x) : analytic_at 𝕜 (-f) x := sorry

theorem has_fpower_series_on_ball.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {g : E → F} {pf : formal_multilinear_series 𝕜 E F} {pg : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} (hf : has_fpower_series_on_ball f pf x r) (hg : has_fpower_series_on_ball g pg x r) : has_fpower_series_on_ball (f - g) (pf - pg) x r := sorry

theorem has_fpower_series_at.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {g : E → F} {pf : formal_multilinear_series 𝕜 E F} {pg : formal_multilinear_series 𝕜 E F} {x : E} (hf : has_fpower_series_at f pf x) (hg : has_fpower_series_at g pg x) : has_fpower_series_at (f - g) (pf - pg) x := sorry

theorem analytic_at.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {g : E → F} {x : E} (hf : analytic_at 𝕜 f x) (hg : analytic_at 𝕜 g x) : analytic_at 𝕜 (f - g) x := sorry

theorem has_fpower_series_on_ball.coeff_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {pf : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} (hf : has_fpower_series_on_ball f pf x r) (v : fin 0 → E) : coe_fn (pf 0) v = f x := sorry

theorem has_fpower_series_at.coeff_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {pf : formal_multilinear_series 𝕜 E F} {x : E} (hf : has_fpower_series_at f pf x) (v : fin 0 → E) : coe_fn (pf 0) v = f x := sorry

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `∥y∥` and `n`. See also
`has_fpower_series_on_ball.uniform_geometric_approx` for a weaker version. -/
theorem has_fpower_series_on_ball.uniform_geometric_approx' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} {r' : nnreal} (hf : has_fpower_series_on_ball f p x r) (h : ↑r' < r) : ∃ (a : ℝ),
  ∃ (H : a ∈ set.Ioo 0 1),
    ∃ (C : ℝ),
      ∃ (H : C > 0),
        ∀ (y : E),
          y ∈ metric.ball 0 ↑r' →
            ∀ (n : ℕ), norm (f (x + y) - formal_multilinear_series.partial_sum p n y) ≤ C * (a * (norm y / ↑r')) ^ n := sorry

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence. -/
theorem has_fpower_series_on_ball.uniform_geometric_approx {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} {r' : nnreal} (hf : has_fpower_series_on_ball f p x r) (h : ↑r' < r) : ∃ (a : ℝ),
  ∃ (H : a ∈ set.Ioo 0 1),
    ∃ (C : ℝ),
      ∃ (H : C > 0),
        ∀ (y : E),
          y ∈ metric.ball 0 ↑r' → ∀ (n : ℕ), norm (f (x + y) - formal_multilinear_series.partial_sum p n y) ≤ C * a ^ n := sorry

/-- Taylor formula for an analytic function, `is_O` version. -/
theorem has_fpower_series_at.is_O_sub_partial_sum_pow {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} (hf : has_fpower_series_at f p x) (n : ℕ) : asymptotics.is_O (fun (y : E) => f (x + y) - formal_multilinear_series.partial_sum p n y) (fun (y : E) => norm y ^ n)
  (nhds 0) := sorry

-- hack to speed up simp when dealing with complicated types

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ∥y - x∥ ∥z - x∥) * ∥y - z∥`. This lemma formulates this property using `is_O` and
`filter.principal` on `E × E`. -/
theorem has_fpower_series_on_ball.is_O_image_sub_image_sub_deriv_principal {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} {r' : ennreal} (hf : has_fpower_series_on_ball f p x r) (hr : r' < r) : asymptotics.is_O
  (fun (y : E × E) => f (prod.fst y) - f (prod.snd y) - coe_fn (p 1) fun (_x : fin 1) => prod.fst y - prod.snd y)
  (fun (y : E × E) => norm (y - (x, x)) * norm (prod.fst y - prod.snd y)) (filter.principal (emetric.ball (x, x) r')) := sorry

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ∥y - x∥ ∥z - x∥) * ∥y - z∥`. -/
theorem has_fpower_series_on_ball.image_sub_sub_deriv_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} {r' : ennreal} (hf : has_fpower_series_on_ball f p x r) (hr : r' < r) : ∃ (C : ℝ),
  ∀ (y z : E),
    y ∈ emetric.ball x r' →
      z ∈ emetric.ball x r' →
        norm (f y - f z - coe_fn (p 1) fun (_x : fin 1) => y - z) ≤ C * max (norm (y - x)) (norm (z - x)) * norm (y - z) := sorry

/-- If `f` has formal power series `∑ n, pₙ` at `x`, then
`f y - f z - p 1 (λ _, y - z) = O(∥(y, z) - (x, x)∥ * ∥y - z∥)` as `(y, z) → (x, x)`.
In particular, `f` is strictly differentiable at `x`. -/
theorem has_fpower_series_at.is_O_image_sub_norm_mul_norm_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} (hf : has_fpower_series_at f p x) : asymptotics.is_O
  (fun (y : E × E) => f (prod.fst y) - f (prod.snd y) - coe_fn (p 1) fun (_x : fin 1) => prod.fst y - prod.snd y)
  (fun (y : E × E) => norm (y - (x, x)) * norm (prod.fst y - prod.snd y)) (nhds (x, x)) := sorry

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f (x + y)`
is the uniform limit of `p.partial_sum n y` there. -/
theorem has_fpower_series_on_ball.tendsto_uniformly_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} {r' : nnreal} (hf : has_fpower_series_on_ball f p x r) (h : ↑r' < r) : tendsto_uniformly_on (fun (n : ℕ) (y : E) => formal_multilinear_series.partial_sum p n y) (fun (y : E) => f (x + y))
  filter.at_top (metric.ball 0 ↑r') := sorry

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partial_sum n y` there. -/
theorem has_fpower_series_on_ball.tendsto_locally_uniformly_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} (hf : has_fpower_series_on_ball f p x r) : tendsto_locally_uniformly_on (fun (n : ℕ) (y : E) => formal_multilinear_series.partial_sum p n y)
  (fun (y : E) => f (x + y)) filter.at_top (emetric.ball 0 r) := sorry

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partial_sum n (y - x)` there. -/
theorem has_fpower_series_on_ball.tendsto_uniformly_on' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} {r' : nnreal} (hf : has_fpower_series_on_ball f p x r) (h : ↑r' < r) : tendsto_uniformly_on (fun (n : ℕ) (y : E) => formal_multilinear_series.partial_sum p n (y - x)) f filter.at_top
  (metric.ball x ↑r') := sorry

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the  partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partial_sum n (y - x)` there. -/
theorem has_fpower_series_on_ball.tendsto_locally_uniformly_on' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} (hf : has_fpower_series_on_ball f p x r) : tendsto_locally_uniformly_on (fun (n : ℕ) (y : E) => formal_multilinear_series.partial_sum p n (y - x)) f filter.at_top
  (emetric.ball x r) := sorry

/-- If a function admits a power series expansion on a disk, then it is continuous there. -/
theorem has_fpower_series_on_ball.continuous_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} (hf : has_fpower_series_on_ball f p x r) : continuous_on f (emetric.ball x r) := sorry

theorem has_fpower_series_at.continuous_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} (hf : has_fpower_series_at f p x) : continuous_at f x := sorry

theorem analytic_at.continuous_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} (hf : analytic_at 𝕜 f x) : continuous_at f x := sorry

/-- In a complete space, the sum of a converging power series `p` admits `p` as a power series.
This is not totally obvious as we need to check the convergence of the series. -/
theorem formal_multilinear_series.has_fpower_series_on_ball {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F] (p : formal_multilinear_series 𝕜 E F) (h : 0 < formal_multilinear_series.radius p) : has_fpower_series_on_ball (formal_multilinear_series.sum p) p 0 (formal_multilinear_series.radius p) := sorry

theorem has_fpower_series_on_ball.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {r : ennreal} [complete_space F] (h : has_fpower_series_on_ball f p x r) {y : E} (hy : y ∈ emetric.ball 0 r) : f (x + y) = formal_multilinear_series.sum p y := sorry

/-- The sum of a converging power series is continuous in its disk of convergence. -/
theorem formal_multilinear_series.continuous_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {p : formal_multilinear_series 𝕜 E F} [complete_space F] : continuous_on (formal_multilinear_series.sum p) (emetric.ball 0 (formal_multilinear_series.radius p)) := sorry

/-!
### Changing origin in a power series

If a function is analytic in a disk `D(x, R)`, then it is analytic in any disk contained in that
one. Indeed, one can write
$$
f (x + y + z) = \sum_{n} p_n (y + z)^n = \sum_{n, k} \binom{n}{k} p_n y^{n-k} z^k
= \sum_{k} \Bigl(\sum_{n} \binom{n}{k} p_n y^{n-k}\Bigr) z^k.
$$
The corresponding power series has thus a `k`-th coefficient equal to
$\sum_{n} \binom{n}{k} p_n y^{n-k}$. In the general case where `pₙ` is a multilinear map, this has
to be interpreted suitably: instead of having a binomial coefficient, one should sum over all
possible subsets `s` of `fin n` of cardinal `k`, and attribute `z` to the indices in `s` and
`y` to the indices outside of `s`.

In this paragraph, we implement this. The new power series is called `p.change_origin y`. Then, we
check its convergence and the fact that its sum coincides with the original sum. The outcome of this
discussion is that the set of points where a function is analytic is open.
-/

namespace formal_multilinear_series


/--
Changing the origin of a formal multilinear series `p`, so that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense.

Here, we don't use the bracket notation `⟨n, s, hs⟩` in place of the argument `i` in the lambda,
as this leads to a bad definition with auxiliary `_match` statements,
but we will try to use pattern matching in lambdas as much as possible in the proofs below
to increase readability.
-/
def change_origin {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) (x : E) : formal_multilinear_series 𝕜 E F :=
  fun (k : ℕ) =>
    tsum
      fun (i : sigma fun (n : ℕ) => Subtype fun (s : finset (fin n)) => finset.card s = k) =>
        continuous_multilinear_map.restr (p (sigma.fst i)) ↑(sigma.snd i) sorry x

/-- Auxiliary lemma controlling the summability of the sequence appearing in the definition of
`p.change_origin`, first version. -/
-- Note here and below it is necessary to use `@` and provide implicit arguments using `_`,

-- so that it is possible to use pattern matching in the lambda.

-- Overall this seems a good trade-off in readability.

theorem change_origin_summable_aux1 {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {x : E} {r : nnreal} (h : ↑(nnnorm x) + ↑r < radius p) : summable
  fun (_x : sigma fun (n : ℕ) => finset (fin n)) =>
    (fun (_a : sigma fun (n : ℕ) => finset (fin n)) =>
        sigma.cases_on _a
          fun (fst : ℕ) (snd : finset (fin fst)) =>
            idRhs ℝ (norm (p fst) * norm x ^ (fst - finset.card snd) * ↑r ^ finset.card snd))
      _x := sorry

/-- Auxiliary lemma controlling the summability of the sequence appearing in the definition of
`p.change_origin`, second version. -/
theorem change_origin_summable_aux2 {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {x : E} {r : nnreal} (h : ↑(nnnorm x) + ↑r < radius p) : summable
  fun (_x : sigma fun (k : ℕ) => sigma fun (n : ℕ) => Subtype fun (s : finset (fin n)) => finset.card s = k) =>
    (fun (_a : sigma fun (k : ℕ) => sigma fun (n : ℕ) => Subtype fun (s : finset (fin n)) => finset.card s = k) =>
        sigma.cases_on _a
          fun (fst : ℕ) (snd : sigma fun (n : ℕ) => Subtype fun (s : finset (fin n)) => finset.card s = fst) =>
            sigma.cases_on snd
              fun (snd_fst : ℕ) (snd_snd : Subtype fun (s : finset (fin snd_fst)) => finset.card s = fst) =>
                subtype.cases_on snd_snd
                  fun (snd_snd_val : finset (fin snd_fst)) (snd_snd_property : finset.card snd_snd_val = fst) =>
                    idRhs ℝ
                      (norm (continuous_multilinear_map.restr (p snd_fst) snd_snd_val snd_snd_property x) * ↑r ^ fst))
      _x := sorry

/-- An auxiliary definition for `change_origin_radius`. -/
def change_origin_summable_aux_j (k : ℕ) : (sigma fun (n : ℕ) => Subtype fun (s : finset (fin n)) => finset.card s = k) →
  sigma fun (k : ℕ) => sigma fun (n : ℕ) => Subtype fun (s : finset (fin n)) => finset.card s = k :=
  fun (_x : sigma fun (n : ℕ) => Subtype fun (s : finset (fin n)) => finset.card s = k) => sorry

theorem change_origin_summable_aux_j_injective (k : ℕ) : function.injective (change_origin_summable_aux_j k) := sorry

/-- Auxiliary lemma controlling the summability of the sequence appearing in the definition of
`p.change_origin`, third version. -/
theorem change_origin_summable_aux3 {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {x : E} (k : ℕ) (h : ↑(nnnorm x) < radius p) : summable
  fun (_x : sigma fun (n : ℕ) => Subtype fun (s : finset (fin n)) => finset.card s = k) =>
    (fun (_a : sigma fun (n : ℕ) => Subtype fun (s : finset (fin n)) => finset.card s = k) =>
        sigma.cases_on _a
          fun (fst : ℕ) (snd : Subtype fun (s : finset (fin fst)) => finset.card s = k) =>
            subtype.cases_on snd
              fun (snd_val : finset (fin fst)) (snd_property : finset.card snd_val = k) =>
                idRhs ℝ (norm (continuous_multilinear_map.restr (p fst) snd_val snd_property x)))
      _x := sorry

-- FIXME this causes a deterministic timeout with `-T50000`

/-- The radius of convergence of `p.change_origin x` is at least `p.radius - ∥x∥`. In other words,
`p.change_origin x` is well defined on the largest ball contained in the original ball of
convergence.-/
theorem change_origin_radius {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {x : E} : radius p - ↑(nnnorm x) ≤ radius (change_origin p x) := sorry

-- From this point on, assume that the space is complete, to make sure that series that converge

-- in norm also converge in `F`.

/-- The `k`-th coefficient of `p.change_origin` is the sum of a summable series. -/
theorem change_origin_has_sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {x : E} [complete_space F] (k : ℕ) (h : ↑(nnnorm x) < radius p) : has_sum
  (fun (i : sigma fun (n : ℕ) => Subtype fun (s : finset (fin n)) => finset.card s = k) =>
    continuous_multilinear_map.restr (p (sigma.fst i)) (subtype.val (sigma.snd i)) (subtype.property (sigma.snd i)) x)
  (change_origin p x k) := sorry

/-- Summing the series `p.change_origin x` at a point `y` gives back `p (x + y)`-/
theorem change_origin_eval {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {x : E} {y : E} [complete_space F] (h : ↑(nnnorm x) + ↑(nnnorm y) < radius p) : has_sum (fun (k : ℕ) => coe_fn (change_origin p x k) fun (i : fin k) => y) (formal_multilinear_series.sum p (x + y)) := sorry

end formal_multilinear_series


/-- If a function admits a power series expansion `p` on a ball `B (x, r)`, then it also admits a
power series on any subball of this ball (even with a different center), given by `p.change_origin`.
-/
theorem has_fpower_series_on_ball.change_origin {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {y : E} {r : ennreal} (hf : has_fpower_series_on_ball f p x r) (h : ↑(nnnorm y) < r) : has_fpower_series_on_ball f (formal_multilinear_series.change_origin p y) (x + y) (r - ↑(nnnorm y)) := sorry

theorem has_fpower_series_on_ball.analytic_at_of_mem {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x : E} {y : E} {r : ennreal} (hf : has_fpower_series_on_ball f p x r) (h : y ∈ emetric.ball x r) : analytic_at 𝕜 f y := sorry

theorem is_open_analytic_at (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space F] (f : E → F) : is_open (set_of fun (x : E) => analytic_at 𝕜 f x) := sorry

