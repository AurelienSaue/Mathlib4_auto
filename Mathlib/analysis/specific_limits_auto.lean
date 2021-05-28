/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.geom_sum
import Mathlib.order.filter.archimedean
import Mathlib.order.iterate
import Mathlib.topology.instances.ennreal
import Mathlib.tactic.ring_exp
import Mathlib.analysis.asymptotics
import PostPort

universes u_1 u_4 

namespace Mathlib

/-!
# A collection of specific limit computations
-/

theorem tendsto_norm_at_top_at_top : filter.tendsto norm filter.at_top filter.at_top :=
  filter.tendsto_abs_at_top_at_top

theorem summable_of_absolute_convergence_real {f : ℕ → ℝ} : (∃ (r : ℝ),
    filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => abs (f i)) filter.at_top (nhds r)) →
  summable f := sorry

theorem tendsto_inverse_at_top_nhds_0_nat : filter.tendsto (fun (n : ℕ) => ↑n⁻¹) filter.at_top (nhds 0) :=
  filter.tendsto.comp tendsto_inv_at_top_zero tendsto_coe_nat_at_top_at_top

theorem tendsto_const_div_at_top_nhds_0_nat (C : ℝ) : filter.tendsto (fun (n : ℕ) => C / ↑n) filter.at_top (nhds 0) := sorry

theorem nnreal.tendsto_inverse_at_top_nhds_0_nat : filter.tendsto (fun (n : ℕ) => ↑n⁻¹) filter.at_top (nhds 0) := sorry

theorem nnreal.tendsto_const_div_at_top_nhds_0_nat (C : nnreal) : filter.tendsto (fun (n : ℕ) => C / ↑n) filter.at_top (nhds 0) := sorry

theorem tendsto_one_div_add_at_top_nhds_0_nat : filter.tendsto (fun (n : ℕ) => 1 / (↑n + 1)) filter.at_top (nhds 0) := sorry

/-! ### Powers -/

theorem tendsto_add_one_pow_at_top_at_top_of_pos {α : Type u_1} [linear_ordered_semiring α] [archimedean α] {r : α} (h : 0 < r) : filter.tendsto (fun (n : ℕ) => (r + 1) ^ n) filter.at_top filter.at_top :=
  filter.tendsto_at_top_at_top_of_monotone' (fun (n m : ℕ) => pow_le_pow (le_add_of_nonneg_left (le_of_lt h)))
    (iff.mpr not_bdd_above_iff fun (x : α) => iff.mpr set.exists_range_iff (add_one_pow_unbounded_of_pos x h))

theorem tendsto_pow_at_top_at_top_of_one_lt {α : Type u_1} [linear_ordered_ring α] [archimedean α] {r : α} (h : 1 < r) : filter.tendsto (fun (n : ℕ) => r ^ n) filter.at_top filter.at_top :=
  sub_add_cancel r 1 ▸ tendsto_add_one_pow_at_top_at_top_of_pos (iff.mpr sub_pos h)

theorem nat.tendsto_pow_at_top_at_top_of_one_lt {m : ℕ} (h : 1 < m) : filter.tendsto (fun (n : ℕ) => m ^ n) filter.at_top filter.at_top :=
  nat.sub_add_cancel (le_of_lt h) ▸ tendsto_add_one_pow_at_top_at_top_of_pos (nat.sub_pos_of_lt h)

theorem tendsto_norm_zero' {𝕜 : Type u_1} [normed_group 𝕜] : filter.tendsto norm (nhds_within 0 (set_of fun (x : 𝕜) => x ≠ 0)) (nhds_within 0 (set.Ioi 0)) :=
  filter.tendsto.inf tendsto_norm_zero
    (iff.mpr filter.tendsto_principal_principal
      fun (x : 𝕜) (hx : x ∈ set_of fun (x : 𝕜) => x ≠ 0) => iff.mpr norm_pos_iff hx)

theorem normed_field.tendsto_norm_inverse_nhds_within_0_at_top {𝕜 : Type u_1} [normed_field 𝕜] : filter.tendsto (fun (x : 𝕜) => norm (x⁻¹)) (nhds_within 0 (set_of fun (x : 𝕜) => x ≠ 0)) filter.at_top :=
  filter.tendsto.congr (fun (x : 𝕜) => Eq.symm (normed_field.norm_inv x))
    (filter.tendsto.comp tendsto_inv_zero_at_top tendsto_norm_zero')

theorem tendsto_pow_at_top_nhds_0_of_lt_1 {𝕜 : Type u_1} [linear_ordered_field 𝕜] [archimedean 𝕜] [topological_space 𝕜] [order_topology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) : filter.tendsto (fun (n : ℕ) => r ^ n) filter.at_top (nhds 0) := sorry

theorem tendsto_pow_at_top_nhds_within_0_of_lt_1 {𝕜 : Type u_1} [linear_ordered_field 𝕜] [archimedean 𝕜] [topological_space 𝕜] [order_topology 𝕜] {r : 𝕜} (h₁ : 0 < r) (h₂ : r < 1) : filter.tendsto (fun (n : ℕ) => r ^ n) filter.at_top (nhds_within 0 (set.Ioi 0)) :=
  iff.mpr filter.tendsto_inf
    { left := tendsto_pow_at_top_nhds_0_of_lt_1 (has_lt.lt.le h₁) h₂,
      right := iff.mpr filter.tendsto_principal (filter.eventually_of_forall fun (n : ℕ) => pow_pos h₁ n) }

theorem is_o_pow_pow_of_lt_left {r₁ : ℝ} {r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) : asymptotics.is_o (fun (n : ℕ) => r₁ ^ n) (fun (n : ℕ) => r₂ ^ n) filter.at_top := sorry

theorem is_O_pow_pow_of_le_left {r₁ : ℝ} {r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) : asymptotics.is_O (fun (n : ℕ) => r₁ ^ n) (fun (n : ℕ) => r₂ ^ n) filter.at_top :=
  or.elim (has_le.le.eq_or_lt h₂) (fun (h : r₁ = r₂) => h ▸ asymptotics.is_O_refl (fun (n : ℕ) => r₁ ^ n) filter.at_top)
    fun (h : r₁ < r₂) => asymptotics.is_o.is_O (is_o_pow_pow_of_lt_left h₁ h)

theorem is_o_pow_pow_of_abs_lt_left {r₁ : ℝ} {r₂ : ℝ} (h : abs r₁ < abs r₂) : asymptotics.is_o (fun (n : ℕ) => r₁ ^ n) (fun (n : ℕ) => r₂ ^ n) filter.at_top :=
  asymptotics.is_o.of_norm_right
    (asymptotics.is_o.of_norm_left
      (asymptotics.is_o.congr (pow_abs r₁) (pow_abs r₂) (is_o_pow_pow_of_lt_left (abs_nonneg r₁) h)))

/-- Various statements equivalent to the fact that `f n` grows exponentially slower than `R ^ n`.

* 0: $f n = o(a ^ n)$ for some $-R < a < R$;
* 1: $f n = o(a ^ n)$ for some $0 < a < R$;
* 2: $f n = O(a ^ n)$ for some $-R < a < R$;
* 3: $f n = O(a ^ n)$ for some $0 < a < R$;
* 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|f n| ≤ Ca^n$
     for all `n`;
* 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for all `n`;
* 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;
* 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`.

NB: For backwards compatibility, if you add more items to the list, please append them at the end of
the list. -/
theorem tfae_exists_lt_is_o_pow (f : ℕ → ℝ) (R : ℝ) : tfae
  [∃ (a : ℝ), ∃ (H : a ∈ set.Ioo (-R) R), asymptotics.is_o f (pow a) filter.at_top,
    ∃ (a : ℝ), ∃ (H : a ∈ set.Ioo 0 R), asymptotics.is_o f (pow a) filter.at_top,
    ∃ (a : ℝ), ∃ (H : a ∈ set.Ioo (-R) R), asymptotics.is_O f (pow a) filter.at_top,
    ∃ (a : ℝ), ∃ (H : a ∈ set.Ioo 0 R), asymptotics.is_O f (pow a) filter.at_top,
    ∃ (a : ℝ), ∃ (H : a < R), ∃ (C : ℝ), ∃ (h₀ : 0 < C ∨ 0 < R), ∀ (n : ℕ), abs (f n) ≤ C * a ^ n,
    ∃ (a : ℝ), ∃ (H : a ∈ set.Ioo 0 R), ∃ (C : ℝ), ∃ (H : C > 0), ∀ (n : ℕ), abs (f n) ≤ C * a ^ n,
    ∃ (a : ℝ), ∃ (H : a < R), filter.eventually (fun (n : ℕ) => abs (f n) ≤ a ^ n) filter.at_top,
    ∃ (a : ℝ), ∃ (H : a ∈ set.Ioo 0 R), filter.eventually (fun (n : ℕ) => abs (f n) ≤ a ^ n) filter.at_top] := sorry

theorem uniformity_basis_dist_pow_of_lt_1 {α : Type u_1} [metric_space α] {r : ℝ} (h₀ : 0 < r) (h₁ : r < 1) : filter.has_basis (uniformity α) (fun (k : ℕ) => True)
  fun (k : ℕ) => set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) < r ^ k :=
  metric.mk_uniformity_basis (fun (i : ℕ) (_x : True) => pow_pos h₀ i)
    fun (ε : ℝ) (ε0 : 0 < ε) =>
      Exists.imp (fun (k : ℕ) (hk : r ^ k < ε) => Exists.intro trivial (has_lt.lt.le hk)) (exists_pow_lt_of_lt_one ε0 h₁)

theorem geom_lt {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) (h : ∀ (k : ℕ), k < n → c * u k < u (k + 1)) : c ^ n * u 0 < u n := sorry

theorem geom_le {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ (k : ℕ), k < n → c * u k ≤ u (k + 1)) : c ^ n * u 0 ≤ u n := sorry

/-- For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`. -/
theorem is_o_pow_const_const_pow_of_one_lt {R : Type u_1} [normed_ring R] (k : ℕ) {r : ℝ} (hr : 1 < r) : asymptotics.is_o (fun (n : ℕ) => ↑n ^ k) (fun (n : ℕ) => r ^ n) filter.at_top := sorry

/-- For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`. -/
theorem is_o_coe_const_pow_of_one_lt {R : Type u_1} [normed_ring R] {r : ℝ} (hr : 1 < r) : asymptotics.is_o coe (fun (n : ℕ) => r ^ n) filter.at_top := sorry

/-- If `∥r₁∥ < r₂`, then for any naturak `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as `n → ∞`. -/
theorem is_o_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type u_1} [normed_ring R] (k : ℕ) {r₁ : R} {r₂ : ℝ} (h : norm r₁ < r₂) : asymptotics.is_o (fun (n : ℕ) => ↑n ^ k * r₁ ^ n) (fun (n : ℕ) => r₂ ^ n) filter.at_top := sorry

theorem tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) : filter.tendsto (fun (n : ℕ) => ↑n ^ k / r ^ n) filter.at_top (nhds 0) :=
  asymptotics.is_o.tendsto_0 (is_o_pow_const_const_pow_of_one_lt k hr)

/-- If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`. -/
theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : ℕ) {r : ℝ} (hr : abs r < 1) : filter.tendsto (fun (n : ℕ) => ↑n ^ k * r ^ n) filter.at_top (nhds 0) := sorry

/-- If a sequence `v` of real numbers satisfies `k * v n ≤ v (n+1)` with `1 < k`,
then it goes to +∞. -/
theorem tendsto_at_top_of_geom_le {v : ℕ → ℝ} {c : ℝ} (h₀ : 0 < v 0) (hc : 1 < c) (hu : ∀ (n : ℕ), c * v n ≤ v (n + 1)) : filter.tendsto v filter.at_top filter.at_top :=
  filter.tendsto_at_top_mono
    (fun (n : ℕ) => geom_le (has_le.le.trans zero_le_one (has_lt.lt.le hc)) n fun (k : ℕ) (hk : k < n) => hu k)
    (filter.tendsto.at_top_mul_const h₀ (tendsto_pow_at_top_at_top_of_one_lt hc))

theorem nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : nnreal} (hr : r < 1) : filter.tendsto (fun (n : ℕ) => r ^ n) filter.at_top (nhds 0) := sorry

theorem ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : ennreal} (hr : r < 1) : filter.tendsto (fun (n : ℕ) => r ^ n) filter.at_top (nhds 0) := sorry

/-- In a normed ring, the powers of an element x with `∥x∥ < 1` tend to zero. -/
theorem tendsto_pow_at_top_nhds_0_of_norm_lt_1 {R : Type u_1} [normed_ring R] {x : R} (h : norm x < 1) : filter.tendsto (fun (n : ℕ) => x ^ n) filter.at_top (nhds 0) :=
  squeeze_zero_norm' (eventually_norm_pow_le x) (tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg x) h)

theorem tendsto_pow_at_top_nhds_0_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : filter.tendsto (fun (n : ℕ) => r ^ n) filter.at_top (nhds 0) :=
  tendsto_pow_at_top_nhds_0_of_norm_lt_1 h

/-! ### Geometric series-/

theorem has_sum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : has_sum (fun (n : ℕ) => r ^ n) (1 - r⁻¹) := sorry

theorem summable_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : summable fun (n : ℕ) => r ^ n :=
  Exists.intro (1 - r⁻¹) (has_sum_geometric_of_lt_1 h₁ h₂)

theorem tsum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : (tsum fun (n : ℕ) => r ^ n) = (1 - r⁻¹) :=
  has_sum.tsum_eq (has_sum_geometric_of_lt_1 h₁ h₂)

theorem has_sum_geometric_two : has_sum (fun (n : ℕ) => (1 / bit0 1) ^ n) (bit0 1) := sorry

theorem summable_geometric_two : summable fun (n : ℕ) => (1 / bit0 1) ^ n :=
  Exists.intro (bit0 1) has_sum_geometric_two

theorem tsum_geometric_two : (tsum fun (n : ℕ) => (1 / bit0 1) ^ n) = bit0 1 :=
  has_sum.tsum_eq has_sum_geometric_two

theorem sum_geometric_two_le (n : ℕ) : (finset.sum (finset.range n) fun (i : ℕ) => (1 / bit0 1) ^ i) ≤ bit0 1 := sorry

theorem has_sum_geometric_two' (a : ℝ) : has_sum (fun (n : ℕ) => a / bit0 1 / bit0 1 ^ n) a := sorry

theorem summable_geometric_two' (a : ℝ) : summable fun (n : ℕ) => a / bit0 1 / bit0 1 ^ n :=
  Exists.intro a (has_sum_geometric_two' a)

theorem tsum_geometric_two' (a : ℝ) : (tsum fun (n : ℕ) => a / bit0 1 / bit0 1 ^ n) = a :=
  has_sum.tsum_eq (has_sum_geometric_two' a)

theorem nnreal.has_sum_geometric {r : nnreal} (hr : r < 1) : has_sum (fun (n : ℕ) => r ^ n) (1 - r⁻¹) := sorry

theorem nnreal.summable_geometric {r : nnreal} (hr : r < 1) : summable fun (n : ℕ) => r ^ n :=
  Exists.intro (1 - r⁻¹) (nnreal.has_sum_geometric hr)

theorem tsum_geometric_nnreal {r : nnreal} (hr : r < 1) : (tsum fun (n : ℕ) => r ^ n) = (1 - r⁻¹) :=
  has_sum.tsum_eq (nnreal.has_sum_geometric hr)

/-- The series `pow r` converges to `(1-r)⁻¹`. For `r < 1` the RHS is a finite number,
and for `1 ≤ r` the RHS equals `∞`. -/
theorem ennreal.tsum_geometric (r : ennreal) : (tsum fun (n : ℕ) => r ^ n) = (1 - r⁻¹) := sorry

theorem has_sum_geometric_of_norm_lt_1 {K : Type u_4} [normed_field K] {ξ : K} (h : norm ξ < 1) : has_sum (fun (n : ℕ) => ξ ^ n) (1 - ξ⁻¹) := sorry

theorem summable_geometric_of_norm_lt_1 {K : Type u_4} [normed_field K] {ξ : K} (h : norm ξ < 1) : summable fun (n : ℕ) => ξ ^ n :=
  Exists.intro (1 - ξ⁻¹) (has_sum_geometric_of_norm_lt_1 h)

theorem tsum_geometric_of_norm_lt_1 {K : Type u_4} [normed_field K] {ξ : K} (h : norm ξ < 1) : (tsum fun (n : ℕ) => ξ ^ n) = (1 - ξ⁻¹) :=
  has_sum.tsum_eq (has_sum_geometric_of_norm_lt_1 h)

theorem has_sum_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : has_sum (fun (n : ℕ) => r ^ n) (1 - r⁻¹) :=
  has_sum_geometric_of_norm_lt_1 h

theorem summable_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : summable fun (n : ℕ) => r ^ n :=
  summable_geometric_of_norm_lt_1 h

theorem tsum_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : (tsum fun (n : ℕ) => r ^ n) = (1 - r⁻¹) :=
  tsum_geometric_of_norm_lt_1 h

/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp] theorem summable_geometric_iff_norm_lt_1 {K : Type u_4} [normed_field K] {ξ : K} : (summable fun (n : ℕ) => ξ ^ n) ↔ norm ξ < 1 := sorry

theorem summable_norm_pow_mul_geometric_of_norm_lt_1 {R : Type u_1} [normed_ring R] (k : ℕ) {r : R} (hr : norm r < 1) : summable fun (n : ℕ) => norm (↑n ^ k * r ^ n) := sorry

theorem summable_pow_mul_geometric_of_norm_lt_1 {R : Type u_1} [normed_ring R] [complete_space R] (k : ℕ) {r : R} (hr : norm r < 1) : summable fun (n : ℕ) => ↑n ^ k * r ^ n :=
  summable_of_summable_norm (summable_norm_pow_mul_geometric_of_norm_lt_1 k hr)

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `has_sum` version. -/
theorem has_sum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type u_1} [normed_field 𝕜] [complete_space 𝕜] {r : 𝕜} (hr : norm r < 1) : has_sum (fun (n : ℕ) => ↑n * r ^ n) (r / (1 - r) ^ bit0 1) := sorry

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`. -/
theorem tsum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type u_1} [normed_field 𝕜] [complete_space 𝕜] {r : 𝕜} (hr : norm r < 1) : (tsum fun (n : ℕ) => ↑n * r ^ n) = r / (1 - r) ^ bit0 1 :=
  has_sum.tsum_eq (has_sum_coe_mul_geometric_of_norm_lt_1 hr)

/-!
### Sequences with geometrically decaying distance in metric spaces

In this paragraph, we discuss sequences in metric spaces or emetric spaces for which the distance
between two consecutive terms decays geometrically. We show that such sequences are Cauchy
sequences, and bound their distances to the limit. We also discuss series with geometrically
decaying terms.
-/

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, `C ≠ ∞`, `r < 1`,
then `f` is a Cauchy sequence.-/
theorem cauchy_seq_of_edist_le_geometric {α : Type u_1} [emetric_space α] (r : ennreal) (C : ennreal) (hr : r < 1) (hC : C ≠ ⊤) {f : ℕ → α} (hu : ∀ (n : ℕ), edist (f n) (f (n + 1)) ≤ C * r ^ n) : cauchy_seq f := sorry

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
theorem edist_le_of_edist_le_geometric_of_tendsto {α : Type u_1} [emetric_space α] (r : ennreal) (C : ennreal) {f : ℕ → α} (hu : ∀ (n : ℕ), edist (f n) (f (n + 1)) ≤ C * r ^ n) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) (n : ℕ) : edist (f n) a ≤ C * r ^ n / (1 - r) := sorry

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
theorem edist_le_of_edist_le_geometric_of_tendsto₀ {α : Type u_1} [emetric_space α] (r : ennreal) (C : ennreal) {f : ℕ → α} (hu : ∀ (n : ℕ), edist (f n) (f (n + 1)) ≤ C * r ^ n) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) : edist (f 0) a ≤ C / (1 - r) := sorry

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then `f` is a Cauchy sequence.-/
theorem cauchy_seq_of_edist_le_geometric_two {α : Type u_1} [emetric_space α] (C : ennreal) (hC : C ≠ ⊤) {f : ℕ → α} (hu : ∀ (n : ℕ), edist (f n) (f (n + 1)) ≤ C / bit0 1 ^ n) : cauchy_seq f := sorry

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f n` to the limit of `f` is bounded above by `2 * C * 2^-n`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto {α : Type u_1} [emetric_space α] (C : ennreal) {f : ℕ → α} (hu : ∀ (n : ℕ), edist (f n) (f (n + 1)) ≤ C / bit0 1 ^ n) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) (n : ℕ) : edist (f n) a ≤ bit0 1 * C / bit0 1 ^ n := sorry

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f 0` to the limit of `f` is bounded above by `2 * C`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto₀ {α : Type u_1} [emetric_space α] (C : ennreal) {f : ℕ → α} (hu : ∀ (n : ℕ), edist (f n) (f (n + 1)) ≤ C / bit0 1 ^ n) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) : edist (f 0) a ≤ bit0 1 * C := sorry

theorem aux_has_sum_of_le_geometric {α : Type u_1} [metric_space α] {r : ℝ} {C : ℝ} (hr : r < 1) {f : ℕ → α} (hu : ∀ (n : ℕ), dist (f n) (f (n + 1)) ≤ C * r ^ n) : has_sum (fun (n : ℕ) => C * r ^ n) (C / (1 - r)) := sorry

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence.
Note that this lemma does not assume `0 ≤ C` or `0 ≤ r`. -/
theorem cauchy_seq_of_le_geometric {α : Type u_1} [metric_space α] (r : ℝ) (C : ℝ) (hr : r < 1) {f : ℕ → α} (hu : ∀ (n : ℕ), dist (f n) (f (n + 1)) ≤ C * r ^ n) : cauchy_seq f :=
  cauchy_seq_of_dist_le_of_summable (fun (n : ℕ) => C * r ^ n) hu
    (Exists.intro (C / (1 - r)) (aux_has_sum_of_le_geometric hr hu))

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto₀ {α : Type u_1} [metric_space α] (r : ℝ) (C : ℝ) (hr : r < 1) {f : ℕ → α} (hu : ∀ (n : ℕ), dist (f n) (f (n + 1)) ≤ C * r ^ n) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) : dist (f 0) a ≤ C / (1 - r) :=
  has_sum.tsum_eq (aux_has_sum_of_le_geometric hr hu) ▸
    dist_le_tsum_of_dist_le_of_tendsto₀ (fun (b : ℕ) => C * r ^ b) hu
      (Exists.intro (C / (1 - r)) (aux_has_sum_of_le_geometric hr hu)) ha

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto {α : Type u_1} [metric_space α] (r : ℝ) (C : ℝ) (hr : r < 1) {f : ℕ → α} (hu : ∀ (n : ℕ), dist (f n) (f (n + 1)) ≤ C * r ^ n) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) (n : ℕ) : dist (f n) a ≤ C * r ^ n / (1 - r) := sorry

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then `f` is a Cauchy sequence. -/
theorem cauchy_seq_of_le_geometric_two {α : Type u_1} [metric_space α] (C : ℝ) {f : ℕ → α} (hu₂ : ∀ (n : ℕ), dist (f n) (f (n + 1)) ≤ C / bit0 1 / bit0 1 ^ n) : cauchy_seq f :=
  cauchy_seq_of_dist_le_of_summable (fun (n : ℕ) => C / bit0 1 / bit0 1 ^ n) hu₂
    (Exists.intro C (has_sum_geometric_two' C))

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C`. -/
theorem dist_le_of_le_geometric_two_of_tendsto₀ {α : Type u_1} [metric_space α] (C : ℝ) {f : ℕ → α} (hu₂ : ∀ (n : ℕ), dist (f n) (f (n + 1)) ≤ C / bit0 1 / bit0 1 ^ n) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) : dist (f 0) a ≤ C :=
  tsum_geometric_two' C ▸
    dist_le_tsum_of_dist_le_of_tendsto₀ (fun (n : ℕ) => C / bit0 1 / bit0 1 ^ n) hu₂ (summable_geometric_two' C) ha

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C / 2^n`. -/
theorem dist_le_of_le_geometric_two_of_tendsto {α : Type u_1} [metric_space α] (C : ℝ) {f : ℕ → α} (hu₂ : ∀ (n : ℕ), dist (f n) (f (n + 1)) ≤ C / bit0 1 / bit0 1 ^ n) {a : α} (ha : filter.tendsto f filter.at_top (nhds a)) (n : ℕ) : dist (f n) a ≤ C / bit0 1 ^ n := sorry

theorem dist_partial_sum_le_of_le_geometric {α : Type u_1} [normed_group α] {r : ℝ} {C : ℝ} {f : ℕ → α} (hf : ∀ (n : ℕ), norm (f n) ≤ C * r ^ n) (n : ℕ) : dist (finset.sum (finset.range n) fun (i : ℕ) => f i) (finset.sum (finset.range (n + 1)) fun (i : ℕ) => f i) ≤ C * r ^ n := sorry

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
theorem cauchy_seq_finset_of_geometric_bound {α : Type u_1} [normed_group α] {r : ℝ} {C : ℝ} {f : ℕ → α} (hr : r < 1) (hf : ∀ (n : ℕ), norm (f n) ≤ C * r ^ n) : cauchy_seq fun (s : finset ℕ) => finset.sum s fun (x : ℕ) => f x :=
  cauchy_seq_finset_of_norm_bounded (fun (n : ℕ) => C * r ^ n)
    (has_sum.summable (aux_has_sum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf))) hf

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
theorem norm_sub_le_of_geometric_bound_of_has_sum {α : Type u_1} [normed_group α] {r : ℝ} {C : ℝ} {f : ℕ → α} (hr : r < 1) (hf : ∀ (n : ℕ), norm (f n) ≤ C * r ^ n) {a : α} (ha : has_sum f a) (n : ℕ) : norm ((finset.sum (finset.range n) fun (x : ℕ) => f x) - a) ≤ C * r ^ n / (1 - r) := sorry

/-- A geometric series in a complete normed ring is summable.
Proved above (same name, different namespace) for not-necessarily-complete normed fields. -/
theorem normed_ring.summable_geometric_of_norm_lt_1 {R : Type u_4} [normed_ring R] [complete_space R] (x : R) (h : norm x < 1) : summable fun (n : ℕ) => x ^ n := sorry

/-- Bound for the sum of a geometric series in a normed ring.  This formula does not assume that the
normed ring satisfies the axiom `∥1∥ = 1`. -/
theorem normed_ring.tsum_geometric_of_norm_lt_1 {R : Type u_4} [normed_ring R] [complete_space R] (x : R) (h : norm x < 1) : norm (tsum fun (n : ℕ) => x ^ n) ≤ norm 1 - 1 + (1 - norm x⁻¹) := sorry

theorem geom_series_mul_neg {R : Type u_4} [normed_ring R] [complete_space R] (x : R) (h : norm x < 1) : (tsum fun (i : ℕ) => x ^ i) * (1 - x) = 1 := sorry

theorem mul_neg_geom_series {R : Type u_4} [normed_ring R] [complete_space R] (x : R) (h : norm x < 1) : ((1 - x) * tsum fun (i : ℕ) => x ^ i) = 1 := sorry

/-! ### Positive sequences with small sums on encodable types -/

/-- For any positive `ε`, define on an encodable type a positive sequence with sum less than `ε` -/
def pos_sum_of_encodable {ε : ℝ} (hε : 0 < ε) (ι : Type u_1) [encodable ι] : Subtype fun (ε' : ι → ℝ) => (∀ (i : ι), 0 < ε' i) ∧ ∃ (c : ℝ), has_sum ε' c ∧ c ≤ ε :=
  let f : ℕ → ℝ := fun (n : ℕ) => ε / bit0 1 / bit0 1 ^ n;
  { val := f ∘ encodable.encode, property := sorry }

namespace nnreal


theorem exists_pos_sum_of_encodable {ε : nnreal} (hε : 0 < ε) (ι : Type u_1) [encodable ι] : ∃ (ε' : ι → nnreal), (∀ (i : ι), 0 < ε' i) ∧ ∃ (c : nnreal), has_sum ε' c ∧ c < ε := sorry

end nnreal


namespace ennreal


theorem exists_pos_sum_of_encodable {ε : ennreal} (hε : 0 < ε) (ι : Type u_1) [encodable ι] : ∃ (ε' : ι → nnreal), (∀ (i : ι), 0 < ε' i) ∧ (tsum fun (i : ι) => ↑(ε' i)) < ε := sorry

end ennreal


/-!
### Factorial
-/

theorem factorial_tendsto_at_top : filter.tendsto nat.factorial filter.at_top filter.at_top :=
  filter.tendsto_at_top_at_top_of_monotone nat.monotone_factorial fun (n : ℕ) => Exists.intro n (nat.self_le_factorial n)

theorem tendsto_factorial_div_pow_self_at_top : filter.tendsto (fun (n : ℕ) => ↑(nat.factorial n) / ↑n ^ n) filter.at_top (nhds 0) := sorry

