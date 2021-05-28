/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.set_integral
import Mathlib.measure_theory.lebesgue_measure
import Mathlib.analysis.calculus.fderiv_measurable
import Mathlib.analysis.calculus.extend_deriv
import Mathlib.PostPort

universes u_1 u_4 u_3 u_2 u_6 l 

namespace Mathlib

/-!
# Integral over an interval

In this file we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ` if `a ≤ b`
and `-∫ x in Ioc b a, f x ∂μ` if `b ≤ a`. We prove a few simple properties and many versions
of the first part of the
[fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus).
Recall that it states that the function `(u, v) ↦ ∫ x in u..v, f x` has derivative
`(δu, δv) ↦ δv • f b - δu • f a` at `(a, b)` provided that `f` is continuous at `a` and `b`.

## Main statements

### FTC-1 for Lebesgue measure

We prove several versions of FTC-1, all in the `interval_integral` namespace. Many of them follow
the naming scheme `integral_has(_strict?)_(f?)deriv(_within?)_at(_of_tendsto_ae?)(_right|_left?)`.
They formulate FTC in terms of `has(_strict?)_(f?)deriv(_within?)_at`.
Let us explain the meaning of each part of the name:

* `_strict` means that the theorem is about strict differentiability;
* `f` means that the theorem is about differentiability in both endpoints; incompatible with
  `_right|_left`;
* `_within` means that the theorem is about one-sided derivatives, see below for details;
* `_of_tendsto_ae` means that instead of continuity the theorem assumes that `f` has a finite limit
  almost surely as `x` tends to `a` and/or `b`;
* `_right` or `_left` mean that the theorem is about differentiability in the right (resp., left)
  endpoint.

We also reformulate these theorems in terms of `(f?)deriv(_within?)`. These theorems are named
`(f?)deriv(_within?)_integral(_of_tendsto_ae?)(_right|_left?)` with the same meaning of parts of the
name.

### One-sided derivatives

Theorem `integral_has_fderiv_within_at_of_tendsto_ae` states that `(u, v) ↦ ∫ x in u..v, f x` has a
derivative `(δu, δv) ↦ δv • cb - δu • ca` within the set `s × t` at `(a, b)` provided that `f` tends
to `ca` (resp., `cb`) almost surely at `la` (resp., `lb`), where possible values of `s`, `t`, and
corresponding filters `la`, `lb` are given in the following table.

| `s`     | `la`         | `t`     | `lb`         |
| ------- | ----         | ---     | ----         |
| `Iic a` | `𝓝[Iic a] a` | `Iic b` | `𝓝[Iic b] b` |
| `Ici a` | `𝓝[Ioi a] a` | `Ici b` | `𝓝[Ioi b] b` |
| `{a}`   | `⊥`          | `{b}`   | `⊥`          |
| `univ`  | `𝓝 a`        | `univ`  | `𝓝 b`        |

We use a typeclass `FTC_filter` to make Lean automatically find `la`/`lb` based on `s`/`t`. This way
we can formulate one theorem instead of `16` (or `8` if we leave only non-trivial ones not covered
by `integral_has_deriv_within_at_of_tendsto_ae_(left|right)` and
`integral_has_fderiv_at_of_tendsto_ae`). Similarly,
`integral_has_deriv_within_at_of_tendsto_ae_right` works for both one-sided derivatives using the
same typeclass to find an appropriate filter.

### FTC for a locally finite measure

Before proving FTC for the Lebesgue measure, we prove a few statements that can be seen as FTC for
any measure. The most general of them,
`measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae`, states the following. Let `(la, la')`
be an `FTC_filter` pair of filters around `a` (i.e., `FTC_filter a la la'`) and let `(lb, lb')` be
an `FTC_filter` pair of filters around `b`. If `f` has finite limits `ca` and `cb` almost surely at
`la'` and `lb'`, respectively, then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)` as `ua` and `va` tend to `la` while
`ub` and `vb` tend to `lb`.

## Implementation notes

### Avoiding `if`, `min`, and `max`

In order to avoid `if`s in the definition, we define `interval_integrable f μ a b` as
`integrable_on f (Ioc a b) μ ∧ integrable_on f (Ioc b a) μ`. For any `a`, `b` one of these
intervals is empty and the other coincides with `Ioc (min a b) (max a b)`.

Similarly, we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`.
Again, for any `a`, `b` one of these integrals is zero, and the other gives the expected result.

This way some properties can be translated from integrals over sets without dealing with
the cases `a ≤ b` and `b ≤ a` separately.

### Choice of the interval

We use integral over `Ioc (min a b) (max a b)` instead of one of the other three possible
intervals with the same endpoints for two reasons:

* this way `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ` holds whenever
  `f` is integrable on each interval; in particular, it works even if the measure `μ` has an atom
  at `b`; this rules out `Ioo` and `Icc` intervals;
* with this definition for a probability measure `μ`, the integral `∫ x in a..b, 1 ∂μ` equals
  the difference $F_μ(b)-F_μ(a)$, where $F_μ(a)=μ(-∞, a]$ is the
  [cumulative distribution function](https://en.wikipedia.org/wiki/Cumulative_distribution_function)
  of `μ`.

### `FTC_filter` class

As explained above, many theorems in this file rely on the typeclass
`FTC_filter (a : α) (l l' : filter α)` to avoid code duplication. This typeclass combines four
assumptions:

- `pure a ≤ l`;
- `l' ≤ 𝓝 a`;
- `l'` has a basis of measurable sets;
- if `u n` and `v n` tend to `l`, then for any `s ∈ l'`, `Ioc (u n) (v n)` is eventually included
  in `s`.

This typeclass has exactly four “real” instances: `(a, pure a, ⊥)`, `(a, 𝓝[Ici a] a, 𝓝[Ioi a] a)`,
`(a, 𝓝[Iic a] a, 𝓝[Iic a] a)`, `(a, 𝓝 a, 𝓝 a)`, and two instances that are equal to the first and
last “real” instances: `(a, 𝓝[{a}] a, ⊥)` and `(a, 𝓝[univ] a, 𝓝[univ] a)`. While the difference
between `Ici a` and `Ioi a` doesn't matter for theorems about Lebesgue measure, it becomes important
in the versions of FTC about any locally finite measure if this measure has an atom at one of the
endpoints.

## Tags

integral, fundamental theorem of calculus
 -/

/-!
### Integrability at an interval
-/

/-- A function `f` is called *interval integrable* with respect to a measure `μ` on an unordered
interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One of these
intervals is always empty, so this property is equivalent to `f` being integrable on
`(min a b, max a b]`. -/
def interval_integrable {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] (f : α → E) (μ : measure_theory.measure α) (a : α) (b : α)  :=
  measure_theory.integrable_on f (set.Ioc a b) ∧ measure_theory.integrable_on f (set.Ioc b a)

theorem measure_theory.integrable.interval_integrable {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] {f : α → E} {μ : measure_theory.measure α} (hf : measure_theory.integrable f) {a : α} {b : α} : interval_integrable f μ a b :=
  { left := measure_theory.integrable.integrable_on hf, right := measure_theory.integrable.integrable_on hf }

namespace interval_integrable


theorem symm {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] {f : α → E} {a : α} {b : α} {μ : measure_theory.measure α} (h : interval_integrable f μ a b) : interval_integrable f μ b a :=
  and.symm h

theorem refl {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] {f : α → E} {a : α} {μ : measure_theory.measure α} : interval_integrable f μ a a := sorry

theorem trans {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] {f : α → E} {a : α} {b : α} {c : α} {μ : measure_theory.measure α} (hab : interval_integrable f μ a b) (hbc : interval_integrable f μ b c) : interval_integrable f μ a c := sorry

theorem neg {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] {f : α → E} {a : α} {b : α} {μ : measure_theory.measure α} [borel_space E] (h : interval_integrable f μ a b) : interval_integrable (-f) μ a b :=
  { left := measure_theory.integrable.neg (and.left h), right := measure_theory.integrable.neg (and.right h) }

protected theorem ae_measurable {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] {f : α → E} {a : α} {b : α} {μ : measure_theory.measure α} (h : interval_integrable f μ a b) : ae_measurable f :=
  measure_theory.integrable.ae_measurable (and.left h)

protected theorem ae_measurable' {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] {f : α → E} {a : α} {b : α} {μ : measure_theory.measure α} (h : interval_integrable f μ a b) : ae_measurable f :=
  measure_theory.integrable.ae_measurable (and.right h)

theorem smul {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [borel_space E] [normed_field 𝕜] [normed_space 𝕜 E] {f : α → E} {a : α} {b : α} {μ : measure_theory.measure α} (h : interval_integrable f μ a b) (r : 𝕜) : interval_integrable (r • f) μ a b :=
  { left := measure_theory.integrable.smul r (and.left h), right := measure_theory.integrable.smul r (and.right h) }

theorem add {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [borel_space E] {f : α → E} {g : α → E} {a : α} {b : α} {μ : measure_theory.measure α} [topological_space.second_countable_topology E] (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) : interval_integrable (f + g) μ a b :=
  { left := measure_theory.integrable.add (and.left hf) (and.left hg),
    right := measure_theory.integrable.add (and.right hf) (and.right hg) }

theorem sub {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [borel_space E] {f : α → E} {g : α → E} {a : α} {b : α} {μ : measure_theory.measure α} [topological_space.second_countable_topology E] (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) : interval_integrable (f - g) μ a b :=
  { left := measure_theory.integrable.sub (and.left hf) (and.left hg),
    right := measure_theory.integrable.sub (and.right hf) (and.right hg) }

end interval_integrable


theorem continuous_on.interval_integrable {E : Type u_4} [measurable_space E] [normed_group E] {μ : measure_theory.measure ℝ} [measure_theory.locally_finite_measure μ] [borel_space E] {u : ℝ → E} {a : ℝ} {b : ℝ} (hu : continuous_on u (set.interval a b)) : interval_integrable u μ a b := sorry

theorem continuous_on.interval_integrable_of_Icc {E : Type u_4} [measurable_space E] [normed_group E] {μ : measure_theory.measure ℝ} [measure_theory.locally_finite_measure μ] [borel_space E] {u : ℝ → E} {a : ℝ} {b : ℝ} (h : a ≤ b) (hu : continuous_on u (set.Icc a b)) : interval_integrable u μ a b :=
  continuous_on.interval_integrable (Eq.symm (set.interval_of_le h) ▸ hu)

/-- A continuous function on `ℝ` is `interval_integrable` with respect to any locally finite measure
`ν` on ℝ. -/
theorem continuous.interval_integrable {E : Type u_4} [measurable_space E] [normed_group E] {μ : measure_theory.measure ℝ} [measure_theory.locally_finite_measure μ] [borel_space E] {u : ℝ → E} (hu : continuous u) (a : ℝ) (b : ℝ) : interval_integrable u μ a b :=
  continuous_on.interval_integrable (continuous.continuous_on hu)

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : α → E` has a finite limit at `l' ⊓ μ.ae`. Then `f` is interval integrable on
`u..v` provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply tendsto.eventually_interval_integrable_ae` will generate goals `filter α` and
`tendsto_Ixx_class Ioc ?m_1 l'`. -/
theorem filter.tendsto.eventually_interval_integrable_ae {α : Type u_1} {β : Type u_2} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] {f : α → E} {μ : measure_theory.measure α} {l : filter α} {l' : filter α} (hfm : measurable_at_filter f l') [filter.tendsto_Ixx_class set.Ioc l l'] [filter.is_measurably_generated l'] (hμ : measure_theory.measure.finite_at_filter μ l') {c : E} (hf : filter.tendsto f (l' ⊓ measure_theory.measure.ae μ) (nhds c)) {u : β → α} {v : β → α} {lt : filter β} (hu : filter.tendsto u lt l) (hv : filter.tendsto v lt l) : filter.eventually (fun (t : β) => interval_integrable f μ (u t) (v t)) lt := sorry

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : α → E` has a finite limit at `l`. Then `f` is interval integrable on `u..v`
provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply tendsto.eventually_interval_integrable_ae` will generate goals `filter α` and
`tendsto_Ixx_class Ioc ?m_1 l'`. -/
theorem filter.tendsto.eventually_interval_integrable {α : Type u_1} {β : Type u_2} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] {f : α → E} {μ : measure_theory.measure α} {l : filter α} {l' : filter α} (hfm : measurable_at_filter f l') [filter.tendsto_Ixx_class set.Ioc l l'] [filter.is_measurably_generated l'] (hμ : measure_theory.measure.finite_at_filter μ l') {c : E} (hf : filter.tendsto f l' (nhds c)) {u : β → α} {v : β → α} {lt : filter β} (hu : filter.tendsto u lt l) (hv : filter.tendsto v lt l) : filter.eventually (fun (t : β) => interval_integrable f μ (u t) (v t)) lt :=
  filter.tendsto.eventually_interval_integrable_ae hfm hμ (filter.tendsto.mono_left hf inf_le_left) hu hv

/-!
### Interval integral: definition and basic properties

In this section we define `∫ x in a..b, f x ∂μ` as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`
and prove some basic properties.
-/

/-- The interval integral `∫ x in a..b, f x ∂μ` is defined
as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`. -/
def interval_integral {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] (f : α → E) (a : α) (b : α) (μ : measure_theory.measure α) : E :=
  (measure_theory.integral (measure_theory.measure.restrict μ (set.Ioc a b)) fun (x : α) => f x) -
    measure_theory.integral (measure_theory.measure.restrict μ (set.Ioc b a)) fun (x : α) => f x

namespace interval_integral


@[simp] theorem integral_zero {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {μ : measure_theory.measure α} : interval_integral (fun (x : α) => 0) a b μ = 0 := sorry

theorem integral_of_le {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {f : α → E} {μ : measure_theory.measure α} (h : a ≤ b) : interval_integral (fun (x : α) => f x) a b μ =
  measure_theory.integral (measure_theory.measure.restrict μ (set.Ioc a b)) fun (x : α) => f x := sorry

@[simp] theorem integral_same {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {f : α → E} {μ : measure_theory.measure α} : interval_integral (fun (x : α) => f x) a a μ = 0 :=
  sub_self
    (measure_theory.integral (measure_theory.measure.restrict μ (set.Ioc a a)) fun (x : α) => (fun (x : α) => f x) x)

theorem integral_symm {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : α → E} {μ : measure_theory.measure α} (a : α) (b : α) : interval_integral (fun (x : α) => f x) b a μ = -interval_integral (fun (x : α) => f x) a b μ := sorry

theorem integral_of_ge {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {f : α → E} {μ : measure_theory.measure α} (h : b ≤ a) : interval_integral (fun (x : α) => f x) a b μ =
  -measure_theory.integral (measure_theory.measure.restrict μ (set.Ioc b a)) fun (x : α) => f x := sorry

theorem integral_cases {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {μ : measure_theory.measure α} (f : α → E) (a : α) (b : α) : interval_integral (fun (x : α) => f x) a b μ ∈
  insert (measure_theory.integral (measure_theory.measure.restrict μ (set.Ioc (min a b) (max a b))) fun (x : α) => f x)
    (singleton
      (-measure_theory.integral (measure_theory.measure.restrict μ (set.Ioc (min a b) (max a b))) fun (x : α) => f x)) := sorry

theorem integral_non_ae_measurable {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {μ : measure_theory.measure α} {f : α → E} {a : α} {b : α} (h : a < b) (hf : ¬ae_measurable f) : interval_integral (fun (x : α) => f x) a b μ = 0 := sorry

theorem norm_integral_eq_norm_integral_Ioc {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {f : α → E} {μ : measure_theory.measure α} : norm (interval_integral (fun (x : α) => f x) a b μ) =
  norm (measure_theory.integral (measure_theory.measure.restrict μ (set.Ioc (min a b) (max a b))) fun (x : α) => f x) := sorry

theorem norm_integral_le_integral_norm_Ioc {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {f : α → E} {μ : measure_theory.measure α} : norm (interval_integral (fun (x : α) => f x) a b μ) ≤
  measure_theory.integral (measure_theory.measure.restrict μ (set.Ioc (min a b) (max a b))) fun (x : α) => norm (f x) :=
  trans_rel_right LessEq norm_integral_eq_norm_integral_Ioc (measure_theory.norm_integral_le_integral_norm f)

theorem norm_integral_le_abs_integral_norm {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {f : α → E} {μ : measure_theory.measure α} : norm (interval_integral (fun (x : α) => f x) a b μ) ≤ abs (interval_integral (fun (x : α) => norm (f x)) a b μ) := sorry

theorem norm_integral_le_of_norm_le_const_ae {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : ℝ} {b : ℝ} {C : ℝ} {f : ℝ → E} (h : filter.eventually (fun (x : ℝ) => x ∈ set.Ioc (min a b) (max a b) → norm (f x) ≤ C) (measure_theory.measure.ae volume)) : norm (interval_integral (fun (x : ℝ) => f x) a b volume) ≤ C * abs (b - a) := sorry

theorem norm_integral_le_of_norm_le_const {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : ℝ} {b : ℝ} {C : ℝ} {f : ℝ → E} (h : ∀ (x : ℝ), x ∈ set.Ioc (min a b) (max a b) → norm (f x) ≤ C) : norm (interval_integral (fun (x : ℝ) => f x) a b volume) ≤ C * abs (b - a) :=
  norm_integral_le_of_norm_le_const_ae (filter.eventually_of_forall h)

theorem integral_add {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {f : α → E} {g : α → E} {μ : measure_theory.measure α} (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) : interval_integral (fun (x : α) => f x + g x) a b μ =
  interval_integral (fun (x : α) => f x) a b μ + interval_integral (fun (x : α) => g x) a b μ := sorry

@[simp] theorem integral_neg {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {f : α → E} {μ : measure_theory.measure α} : interval_integral (fun (x : α) => -f x) a b μ = -interval_integral (fun (x : α) => f x) a b μ := sorry

theorem integral_sub {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {f : α → E} {g : α → E} {μ : measure_theory.measure α} (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) : interval_integral (fun (x : α) => f x - g x) a b μ =
  interval_integral (fun (x : α) => f x) a b μ - interval_integral (fun (x : α) => g x) a b μ := sorry

theorem integral_smul {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {f : α → E} {μ : measure_theory.measure α} (r : ℝ) : interval_integral (fun (x : α) => r • f x) a b μ = r • interval_integral (fun (x : α) => f x) a b μ := sorry

theorem integral_const' {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {μ : measure_theory.measure α} (c : E) : interval_integral (fun (x : α) => c) a b μ =
  (ennreal.to_real (coe_fn μ (set.Ioc a b)) - ennreal.to_real (coe_fn μ (set.Ioc b a))) • c := sorry

theorem integral_const {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : ℝ} {b : ℝ} (c : E) : interval_integral (fun (x : ℝ) => c) a b volume = (b - a) • c := sorry

theorem integral_smul_measure {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {f : α → E} {μ : measure_theory.measure α} (c : ennreal) : interval_integral (fun (x : α) => f x) a b (c • μ) = ennreal.to_real c • interval_integral (fun (x : α) => f x) a b μ := sorry

theorem integral_comp_add_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] (a : ℝ) (b : ℝ) (c : ℝ) (f : ℝ → E) (hfm : ae_measurable f) : interval_integral (fun (x : ℝ) => f (x + c)) a b volume = interval_integral (fun (x : ℝ) => f x) (a + c) (b + c) volume := sorry

theorem integral_comp_mul_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {c : ℝ} (hc : 0 < c) (a : ℝ) (b : ℝ) (f : ℝ → E) (hfm : ae_measurable f) : interval_integral (fun (x : ℝ) => f (x * c)) a b volume =
  c⁻¹ • interval_integral (fun (x : ℝ) => f x) (a * c) (b * c) volume := sorry

theorem integral_comp_neg {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] (a : ℝ) (b : ℝ) (f : ℝ → E) (hfm : ae_measurable f) : interval_integral (fun (x : ℝ) => f (-x)) a b volume = interval_integral (fun (x : ℝ) => f x) (-b) (-a) volume := sorry

/-!
### Integral is an additive function of the interval

In this section we prove that `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ`
as well as a few other identities trivially equivalent to this one. We also prove that
`∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ` provided that `support f ⊆ Ioc a b`.
-/

/-- If two functions are equal in the relevant interval, their interval integrals are also equal. -/
theorem integral_congr {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {μ : measure_theory.measure α} [topological_space α] [opens_measurable_space α] [order_closed_topology α] {a : α} {b : α} {f : α → E} {g : α → E} (h : set.eq_on f g (set.interval a b)) : interval_integral (fun (x : α) => f x) a b μ = interval_integral (fun (x : α) => g x) a b μ := sorry

theorem integral_add_adjacent_intervals_cancel {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {c : α} {f : α → E} {μ : measure_theory.measure α} [topological_space α] [opens_measurable_space α] [order_closed_topology α] (hab : interval_integrable f μ a b) (hbc : interval_integrable f μ b c) : interval_integral (fun (x : α) => f x) a b μ + interval_integral (fun (x : α) => f x) b c μ +
    interval_integral (fun (x : α) => f x) c a μ =
  0 := sorry

theorem integral_add_adjacent_intervals {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {c : α} {f : α → E} {μ : measure_theory.measure α} [topological_space α] [opens_measurable_space α] [order_closed_topology α] (hab : interval_integrable f μ a b) (hbc : interval_integrable f μ b c) : interval_integral (fun (x : α) => f x) a b μ + interval_integral (fun (x : α) => f x) b c μ =
  interval_integral (fun (x : α) => f x) a c μ := sorry

theorem integral_interval_sub_left {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {c : α} {f : α → E} {μ : measure_theory.measure α} [topological_space α] [opens_measurable_space α] [order_closed_topology α] (hab : interval_integrable f μ a b) (hac : interval_integrable f μ a c) : interval_integral (fun (x : α) => f x) a b μ - interval_integral (fun (x : α) => f x) a c μ =
  interval_integral (fun (x : α) => f x) c b μ :=
  sub_eq_of_eq_add'
    (Eq.symm (integral_add_adjacent_intervals hac (interval_integrable.trans (interval_integrable.symm hac) hab)))

theorem integral_interval_add_interval_comm {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {c : α} {d : α} {f : α → E} {μ : measure_theory.measure α} [topological_space α] [opens_measurable_space α] [order_closed_topology α] (hab : interval_integrable f μ a b) (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) : interval_integral (fun (x : α) => f x) a b μ + interval_integral (fun (x : α) => f x) c d μ =
  interval_integral (fun (x : α) => f x) a d μ + interval_integral (fun (x : α) => f x) c b μ := sorry

theorem integral_interval_sub_interval_comm {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {c : α} {d : α} {f : α → E} {μ : measure_theory.measure α} [topological_space α] [opens_measurable_space α] [order_closed_topology α] (hab : interval_integrable f μ a b) (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) : interval_integral (fun (x : α) => f x) a b μ - interval_integral (fun (x : α) => f x) c d μ =
  interval_integral (fun (x : α) => f x) a c μ - interval_integral (fun (x : α) => f x) b d μ := sorry

theorem integral_interval_sub_interval_comm' {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {c : α} {d : α} {f : α → E} {μ : measure_theory.measure α} [topological_space α] [opens_measurable_space α] [order_closed_topology α] (hab : interval_integrable f μ a b) (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) : interval_integral (fun (x : α) => f x) a b μ - interval_integral (fun (x : α) => f x) c d μ =
  interval_integral (fun (x : α) => f x) d b μ - interval_integral (fun (x : α) => f x) c a μ := sorry

theorem integral_Iic_sub_Iic {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {f : α → E} {μ : measure_theory.measure α} [topological_space α] [opens_measurable_space α] [order_closed_topology α] (ha : measure_theory.integrable_on f (set.Iic a)) (hb : measure_theory.integrable_on f (set.Iic b)) : ((measure_theory.integral (measure_theory.measure.restrict μ (set.Iic b)) fun (x : α) => f x) -
    measure_theory.integral (measure_theory.measure.restrict μ (set.Iic a)) fun (x : α) => f x) =
  interval_integral (fun (x : α) => f x) a b μ := sorry

/-- If `μ` is a finite measure then `∫ x in a..b, c ∂μ = (μ (Iic b) - μ (Iic a)) • c`. -/
theorem integral_const_of_cdf {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {a : α} {b : α} {μ : measure_theory.measure α} [topological_space α] [opens_measurable_space α] [order_closed_topology α] [measure_theory.finite_measure μ] (c : E) : interval_integral (fun (x : α) => c) a b μ =
  (ennreal.to_real (coe_fn μ (set.Iic b)) - ennreal.to_real (coe_fn μ (set.Iic a))) • c := sorry

theorem integral_eq_integral_of_support_subset {α : Type u_1} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {μ : measure_theory.measure α} [topological_space α] [opens_measurable_space α] [order_closed_topology α] {f : α → E} {a : α} {b : α} (h : function.support f ⊆ set.Ioc a b) : interval_integral (fun (x : α) => f x) a b μ = measure_theory.integral μ fun (x : α) => f x := sorry

theorem integral_eq_zero_iff_of_le_of_nonneg_ae {f : ℝ → ℝ} {a : ℝ} {b : ℝ} (hab : a ≤ b) (hf : filter.eventually_le (measure_theory.measure.ae (measure_theory.measure.restrict volume (set.Ioc a b))) 0 f) (hfi : interval_integrable f volume a b) : interval_integral (fun (x : ℝ) => f x) a b volume = 0 ↔
  filter.eventually_eq (measure_theory.measure.ae (measure_theory.measure.restrict volume (set.Ioc a b))) f 0 := sorry

theorem integral_eq_zero_iff_of_nonneg_ae {f : ℝ → ℝ} {a : ℝ} {b : ℝ} (hf : filter.eventually_le (measure_theory.measure.ae (measure_theory.measure.restrict volume (set.Ioc a b ∪ set.Ioc b a))) 0
  f) (hfi : interval_integrable f volume a b) : interval_integral (fun (x : ℝ) => f x) a b volume = 0 ↔
  filter.eventually_eq (measure_theory.measure.ae (measure_theory.measure.restrict volume (set.Ioc a b ∪ set.Ioc b a)))
    f 0 := sorry

theorem integral_pos_iff_support_of_nonneg_ae' {f : ℝ → ℝ} {a : ℝ} {b : ℝ} (hf : filter.eventually_le (measure_theory.measure.ae (measure_theory.measure.restrict volume (set.Ioc a b ∪ set.Ioc b a))) 0
  f) (hfi : interval_integrable f volume a b) : 0 < interval_integral (fun (x : ℝ) => f x) a b volume ↔ a < b ∧ 0 < coe_fn volume (function.support f ∩ set.Ioc a b) := sorry

theorem integral_pos_iff_support_of_nonneg_ae {f : ℝ → ℝ} {a : ℝ} {b : ℝ} (hf : filter.eventually_le (measure_theory.measure.ae volume) 0 f) (hfi : interval_integrable f volume a b) : 0 < interval_integral (fun (x : ℝ) => f x) a b volume ↔ a < b ∧ 0 < coe_fn volume (function.support f ∩ set.Ioc a b) :=
  integral_pos_iff_support_of_nonneg_ae' (measure_theory.ae_mono measure_theory.measure.restrict_le_self hf) hfi

/-!
### Fundamental theorem of calculus, part 1, for any measure

In this section we prove a few lemmas that can be seen as versions of FTC-1 for interval integrals
w.r.t. any measure. Many theorems are formulated for one or two pairs of filters related by
`FTC_filter a l l'`. This typeclass has exactly four “real” instances: `(a, pure a, ⊥)`,
`(a, 𝓝[Ici a] a, 𝓝[Ioi a] a)`, `(a, 𝓝[Iic a] a, 𝓝[Iic a] a)`, `(a, 𝓝 a, 𝓝 a)`, and two instances
that are equal to the first and last “real” instances: `(a, 𝓝[{a}] a, ⊥)` and
`(a, 𝓝[univ] a, 𝓝[univ] a)`.  We use this approach to avoid repeating arguments in many very similar
cases.  Lean can automatically find both `a` and `l'` based on `l`.

The most general theorem `measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae` can be seen
as a generalization of lemma `integral_has_strict_fderiv_at` below which states strict
differentiability of `∫ x in u..v, f x` in `(u, v)` at `(a, b)` for a measurable function `f` that
is integrable on `a..b` and is continuous at `a` and `b`. The lemma is generalized in three
directions: first, `measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae` deals with any
locally finite measure `μ`; second, it works for one-sided limits/derivatives; third, it assumes
only that `f` has finite limits almost surely at `a` and `b`.

Namely, let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`FTC_filter`s around `a`; let `(lb, lb')` be a pair of `FTC_filter`s around `b`. Suppose that `f`
has finite limits `ca` and `cb` at `la' ⊓ μ.ae` and `lb' ⊓ μ.ae`, respectively.  Then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This theorem is formulated with integral of constants instead of measures in the right hand sides
for two reasons: first, this way we avoid `min`/`max` in the statements; second, often it is
possible to write better `simp` lemmas for these integrals, see `integral_const` and
`integral_const_of_cdf`.

In the next subsection we apply this theorem to prove various theorems about differentiability
of the integral w.r.t. Lebesgue measure. -/

/-- An auxiliary typeclass for the Fundamental theorem of calculus, part 1. It is used to formulate
theorems that work simultaneously for left and right one-sided derivatives of `∫ x in u..v, f x`.
There are four instances: `(a, pure a, ⊥)`, `(a, 𝓝[Ici a], 𝓝[Ioi a])`,
`(a, 𝓝[Iic a], 𝓝[Iic a])`, and `(a, 𝓝 a, 𝓝 a)`. -/
class FTC_filter {β : Type u_6} [linear_order β] [measurable_space β] [topological_space β] (a : outParam β) (outer : filter β) (inner : outParam (filter β)) 
extends filter.tendsto_Ixx_class set.Ioc outer inner
where
  pure_le : pure a ≤ outer
  le_nhds : inner ≤ nhds a
  meas_gen : filter.is_measurably_generated inner

/- The `dangerous_instance` linter doesn't take `out_param`s into account, so it thinks that
`FTC_filter.to_tendsto_Ixx_class` is dangerous. Disable this linter using `nolint`.
-/

namespace FTC_filter


protected instance pure {β : Type u_2} [linear_order β] [measurable_space β] [topological_space β] (a : β) : FTC_filter a (pure a) ⊥ :=
  mk (le_refl (pure a)) bot_le

protected instance nhds_within_singleton {β : Type u_2} [linear_order β] [measurable_space β] [topological_space β] (a : β) : FTC_filter a (nhds_within a (singleton a)) ⊥ :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (FTC_filter a (nhds_within a (singleton a)) ⊥))
        (nhds_within.equations._eqn_1 a (singleton a))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (FTC_filter a (nhds a ⊓ filter.principal (singleton a)) ⊥)) (filter.principal_singleton a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (FTC_filter a (nhds a ⊓ pure a) ⊥)) (iff.mpr inf_eq_right (pure_le_nhds a))))
        (FTC_filter.pure a)))

theorem finite_at_inner {β : Type u_2} [linear_order β] [measurable_space β] [topological_space β] {a : β} (l : filter β) {l' : outParam (filter β)} [h : FTC_filter a l l'] {μ : measure_theory.measure β} [measure_theory.locally_finite_measure μ] : measure_theory.measure.finite_at_filter μ l' :=
  measure_theory.measure.finite_at_filter.filter_mono (le_nhds l) (measure_theory.measure.finite_at_nhds μ a)

protected instance nhds {β : Type u_2} [linear_order β] [measurable_space β] [topological_space β] [opens_measurable_space β] [order_topology β] (a : β) : FTC_filter a (nhds a) (nhds a) :=
  mk (pure_le_nhds a) (le_refl (nhds a))

protected instance nhds_univ {β : Type u_2} [linear_order β] [measurable_space β] [topological_space β] [opens_measurable_space β] [order_topology β] (a : β) : FTC_filter a (nhds_within a set.univ) (nhds a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (FTC_filter a (nhds_within a set.univ) (nhds a))) (nhds_within_univ a)))
    (FTC_filter.nhds a)

protected instance nhds_left {β : Type u_2} [linear_order β] [measurable_space β] [topological_space β] [opens_measurable_space β] [order_topology β] (a : β) : FTC_filter a (nhds_within a (set.Iic a)) (nhds_within a (set.Iic a)) :=
  mk (pure_le_nhds_within set.right_mem_Iic) inf_le_left

protected instance nhds_right {β : Type u_2} [linear_order β] [measurable_space β] [topological_space β] [opens_measurable_space β] [order_topology β] (a : β) : FTC_filter a (nhds_within a (set.Ici a)) (nhds_within a (set.Ioi a)) :=
  mk (pure_le_nhds_within set.left_mem_Ici) inf_le_left

end FTC_filter


/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, where `μ` is a measure
finite at `l'`, then `∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both
`u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae` for a version assuming
`[FTC_filter a l l']` and `[locally_finite_measure μ]`. If `l` is one of `𝓝[Ici a] a`,
`𝓝[Iic a] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae' {α : Type u_1} {β : Type u_2} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : α → E} {c : E} {l : filter α} {l' : filter α} {lt : filter β} {μ : measure_theory.measure α} {u : β → α} {v : β → α} [filter.is_measurably_generated l'] [filter.tendsto_Ixx_class set.Ioc l l'] (hfm : measurable_at_filter f l') (hf : filter.tendsto f (l' ⊓ measure_theory.measure.ae μ) (nhds c)) (hl : measure_theory.measure.finite_at_filter μ l') (hu : filter.tendsto u lt l) (hv : filter.tendsto v lt l) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : α) => f x) (u t) (v t) μ - interval_integral (fun (x : α) => c) (u t) (v t) μ)
  (fun (t : β) => interval_integral (fun (x : α) => 1) (u t) (v t) μ) lt := sorry

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both
`u` and `v` tend to `l` so that `u ≤ v`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_le` for a version assuming
`[FTC_filter a l l']` and `[locally_finite_measure μ]`. If `l` is one of `𝓝[Ici a] a`,
`𝓝[Iic a] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' {α : Type u_1} {β : Type u_2} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : α → E} {c : E} {l : filter α} {l' : filter α} {lt : filter β} {μ : measure_theory.measure α} {u : β → α} {v : β → α} [filter.is_measurably_generated l'] [filter.tendsto_Ixx_class set.Ioc l l'] (hfm : measurable_at_filter f l') (hf : filter.tendsto f (l' ⊓ measure_theory.measure.ae μ) (nhds c)) (hl : measure_theory.measure.finite_at_filter μ l') (hu : filter.tendsto u lt l) (hv : filter.tendsto v lt l) (huv : filter.eventually_le lt u v) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : α) => f x) (u t) (v t) μ - ennreal.to_real (coe_fn μ (set.Ioc (u t) (v t))) • c)
  (fun (t : β) => ennreal.to_real (coe_fn μ (set.Ioc (u t) (v t)))) lt := sorry

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both
`u` and `v` tend to `l` so that `v ≤ u`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge` for a version assuming
`[FTC_filter a l l']` and `[locally_finite_measure μ]`. If `l` is one of `𝓝[Ici a] a`,
`𝓝[Iic a] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge' {α : Type u_1} {β : Type u_2} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : α → E} {c : E} {l : filter α} {l' : filter α} {lt : filter β} {μ : measure_theory.measure α} {u : β → α} {v : β → α} [filter.is_measurably_generated l'] [filter.tendsto_Ixx_class set.Ioc l l'] (hfm : measurable_at_filter f l') (hf : filter.tendsto f (l' ⊓ measure_theory.measure.ae μ) (nhds c)) (hl : measure_theory.measure.finite_at_filter μ l') (hu : filter.tendsto u lt l) (hv : filter.tendsto v lt l) (huv : filter.eventually_le lt v u) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : α) => f x) (u t) (v t) μ + ennreal.to_real (coe_fn μ (set.Ioc (v t) (u t))) • c)
  (fun (t : β) => ennreal.to_real (coe_fn μ (set.Ioc (v t) (u t)))) lt := sorry

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae'` for a version that also works, e.g., for
`l = l' = at_top`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae {α : Type u_1} {β : Type u_2} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : α → E} {a : α} {c : E} {l : filter α} {l' : filter α} {lt : filter β} {μ : measure_theory.measure α} {u : β → α} {v : β → α} [topological_space α] [measure_theory.locally_finite_measure μ] [FTC_filter a l l'] (hfm : measurable_at_filter f l') (hf : filter.tendsto f (l' ⊓ measure_theory.measure.ae μ) (nhds c)) (hu : filter.tendsto u lt l) (hv : filter.tendsto v lt l) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : α) => f x) (u t) (v t) μ - interval_integral (fun (x : α) => c) (u t) (v t) μ)
  (fun (t : β) => interval_integral (fun (x : α) => 1) (u t) (v t) μ) lt :=
  measure_integral_sub_linear_is_o_of_tendsto_ae' hfm hf (FTC_filter.finite_at_inner l) hu hv

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_le'` for a version that also works,
e.g., for `l = l' = at_top`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae_of_le {α : Type u_1} {β : Type u_2} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : α → E} {a : α} {c : E} {l : filter α} {l' : filter α} {lt : filter β} {μ : measure_theory.measure α} {u : β → α} {v : β → α} [topological_space α] [measure_theory.locally_finite_measure μ] [FTC_filter a l l'] (hfm : measurable_at_filter f l') (hf : filter.tendsto f (l' ⊓ measure_theory.measure.ae μ) (nhds c)) (hu : filter.tendsto u lt l) (hv : filter.tendsto v lt l) (huv : filter.eventually_le lt u v) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : α) => f x) (u t) (v t) μ - ennreal.to_real (coe_fn μ (set.Ioc (u t) (v t))) • c)
  (fun (t : β) => ennreal.to_real (coe_fn μ (set.Ioc (u t) (v t)))) lt :=
  measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' hfm hf (FTC_filter.finite_at_inner l) hu hv huv

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge'` for a version that also works,
e.g., for `l = l' = at_top`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge {α : Type u_1} {β : Type u_2} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : α → E} {a : α} {c : E} {l : filter α} {l' : filter α} {lt : filter β} {μ : measure_theory.measure α} {u : β → α} {v : β → α} [topological_space α] [measure_theory.locally_finite_measure μ] [FTC_filter a l l'] (hfm : measurable_at_filter f l') (hf : filter.tendsto f (l' ⊓ measure_theory.measure.ae μ) (nhds c)) (hu : filter.tendsto u lt l) (hv : filter.tendsto v lt l) (huv : filter.eventually_le lt v u) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : α) => f x) (u t) (v t) μ + ennreal.to_real (coe_fn μ (set.Ioc (v t) (u t))) • c)
  (fun (t : β) => ennreal.to_real (coe_fn μ (set.Ioc (v t) (u t)))) lt :=
  measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge' hfm hf (FTC_filter.finite_at_inner l) hu hv huv

/-- Fundamental theorem of calculus-1, strict derivative in both limits for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of `FTC_filter`s
around `a`; let `(lb, lb')` be a pair of `FTC_filter`s around `b`. Suppose that `f` has finite
limits `ca` and `cb` at `la' ⊓ μ.ae` and `lb' ⊓ μ.ae`, respectively.
Then `∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ =
  ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
    o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.
-/
theorem measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae {α : Type u_1} {β : Type u_2} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : α → E} {a : α} {b : α} {ca : E} {cb : E} {la : filter α} {la' : filter α} {lb : filter α} {lb' : filter α} {lt : filter β} {μ : measure_theory.measure α} {ua : β → α} {va : β → α} {ub : β → α} {vb : β → α} [topological_space α] [order_topology α] [borel_space α] [FTC_filter a la la'] [FTC_filter b lb lb'] [measure_theory.locally_finite_measure μ] (hab : interval_integrable f μ a b) (hmeas_a : measurable_at_filter f la') (hmeas_b : measurable_at_filter f lb') (ha_lim : filter.tendsto f (la' ⊓ measure_theory.measure.ae μ) (nhds ca)) (hb_lim : filter.tendsto f (lb' ⊓ measure_theory.measure.ae μ) (nhds cb)) (hua : filter.tendsto ua lt la) (hva : filter.tendsto va lt la) (hub : filter.tendsto ub lt lb) (hvb : filter.tendsto vb lt lb) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : α) => f x) (va t) (vb t) μ - interval_integral (fun (x : α) => f x) (ua t) (ub t) μ -
      (interval_integral (fun (x : α) => cb) (ub t) (vb t) μ - interval_integral (fun (x : α) => ca) (ua t) (va t) μ))
  (fun (t : β) =>
    norm (interval_integral (fun (x : α) => 1) (ua t) (va t) μ) +
      norm (interval_integral (fun (x : α) => 1) (ub t) (vb t) μ))
  lt := sorry

/-- Fundamental theorem of calculus-1, strict derivative in right endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(lb, lb')` be a pair of `FTC_filter`s
around `b`. Suppose that `f` has a finite limit `c` at `lb' ⊓ μ.ae`.

Then `∫ x in a..v, f x ∂μ - ∫ x in a..u, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)`
as `u` and `v` tend to `lb`.
-/
theorem measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right {α : Type u_1} {β : Type u_2} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : α → E} {a : α} {b : α} {c : E} {lb : filter α} {lb' : filter α} {lt : filter β} {μ : measure_theory.measure α} {u : β → α} {v : β → α} [topological_space α] [order_topology α] [borel_space α] [FTC_filter b lb lb'] [measure_theory.locally_finite_measure μ] (hab : interval_integrable f μ a b) (hmeas : measurable_at_filter f lb') (hf : filter.tendsto f (lb' ⊓ measure_theory.measure.ae μ) (nhds c)) (hu : filter.tendsto u lt lb) (hv : filter.tendsto v lt lb) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : α) => f x) a (v t) μ - interval_integral (fun (x : α) => f x) a (u t) μ -
      interval_integral (fun (x : α) => c) (u t) (v t) μ)
  (fun (t : β) => interval_integral (fun (x : α) => 1) (u t) (v t) μ) lt := sorry

/-- Fundamental theorem of calculus-1, strict derivative in left endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of `FTC_filter`s
around `a`. Suppose that `f` has a finite limit `c` at `la' ⊓ μ.ae`.

Then `∫ x in v..b, f x ∂μ - ∫ x in u..b, f x ∂μ = -∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)`
as `u` and `v` tend to `la`.
-/
theorem measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left {α : Type u_1} {β : Type u_2} {E : Type u_4} [linear_order α] [measurable_space α] [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : α → E} {a : α} {b : α} {c : E} {la : filter α} {la' : filter α} {lt : filter β} {μ : measure_theory.measure α} {u : β → α} {v : β → α} [topological_space α] [order_topology α] [borel_space α] [FTC_filter a la la'] [measure_theory.locally_finite_measure μ] (hab : interval_integrable f μ a b) (hmeas : measurable_at_filter f la') (hf : filter.tendsto f (la' ⊓ measure_theory.measure.ae μ) (nhds c)) (hu : filter.tendsto u lt la) (hv : filter.tendsto v lt la) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : α) => f x) (v t) b μ - interval_integral (fun (x : α) => f x) (u t) b μ +
      interval_integral (fun (x : α) => c) (u t) (v t) μ)
  (fun (t : β) => interval_integral (fun (x : α) => 1) (u t) (v t) μ) lt := sorry

/-!
### Fundamental theorem of calculus-1 for Lebesgue measure

In this section we restate theorems from the previous section for Lebesgue measure.
In particular, we prove that `∫ x in u..v, f x` is strictly differentiable in `(u, v)`
at `(a, b)` provided that `f` is integrable on `a..b` and is continuous at `a` and `b`.
-/

/-!
#### Auxiliary `is_o` statements

In this section we prove several lemmas that can be interpreted as strict differentiability of
`(u, v) ↦ ∫ x in u..v, f x ∂μ` in `u` and/or `v` at a filter. The statements use `is_o` because
we have no definition of `has_strict_(f)deriv_at_filter` in the library.
-/

/-- Fundamental theorem of calculus-1, local version. If `f` has a finite limit `c` almost surely at
`l'`, where `(l, l')` is an `FTC_filter` pair around `a`, then
`∫ x in u..v, f x ∂μ = (v - u) • c + o (v - u)` as both `u` and `v` tend to `l`. -/
theorem integral_sub_linear_is_o_of_tendsto_ae {β : Type u_2} {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {l : filter ℝ} {l' : filter ℝ} {lt : filter β} {a : ℝ} [FTC_filter a l l'] (hfm : measurable_at_filter f l') (hf : filter.tendsto f (l' ⊓ measure_theory.measure.ae volume) (nhds c)) {u : β → ℝ} {v : β → ℝ} (hu : filter.tendsto u lt l) (hv : filter.tendsto v lt l) : asymptotics.is_o (fun (t : β) => interval_integral (fun (x : ℝ) => f x) (u t) (v t) volume - (v t - u t) • c) (v - u) lt := sorry

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `FTC_filter` pair around
`a`, and `(lb, lb')` is an `FTC_filter` pair around `b`, and `f` has finite limits `ca` and `cb`
almost surely at `la'` and `lb'`, respectively, then
`(∫ x in va..vb, f x) - ∫ x in ua..ub, f x = (vb - ub) • cb - (va - ua) • ca +
  o(∥va - ua∥ + ∥vb - ub∥)` as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This lemma could've been formulated using `has_strict_fderiv_at_filter` if we had this
definition. -/
theorem integral_sub_integral_sub_linear_is_o_of_tendsto_ae {β : Type u_2} {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {ca : E} {cb : E} {la : filter ℝ} {la' : filter ℝ} {lb : filter ℝ} {lb' : filter ℝ} {lt : filter β} {a : ℝ} {b : ℝ} {ua : β → ℝ} {ub : β → ℝ} {va : β → ℝ} {vb : β → ℝ} [FTC_filter a la la'] [FTC_filter b lb lb'] (hab : interval_integrable f volume a b) (hmeas_a : measurable_at_filter f la') (hmeas_b : measurable_at_filter f lb') (ha_lim : filter.tendsto f (la' ⊓ measure_theory.measure.ae volume) (nhds ca)) (hb_lim : filter.tendsto f (lb' ⊓ measure_theory.measure.ae volume) (nhds cb)) (hua : filter.tendsto ua lt la) (hva : filter.tendsto va lt la) (hub : filter.tendsto ub lt lb) (hvb : filter.tendsto vb lt lb) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : ℝ) => f x) (va t) (vb t) volume -
        interval_integral (fun (x : ℝ) => f x) (ua t) (ub t) volume -
      ((vb t - ub t) • cb - (va t - ua t) • ca))
  (fun (t : β) => norm (va t - ua t) + norm (vb t - ub t)) lt := sorry

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(lb, lb')` is an `FTC_filter` pair
around `b`, and `f` has a finite limit `c` almost surely at `lb'`, then
`(∫ x in a..v, f x) - ∫ x in a..u, f x = (v - u) • c + o(∥v - u∥)` as `u` and `v` tend to `lb`.

This lemma could've been formulated using `has_strict_deriv_at_filter` if we had this definition. -/
theorem integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right {β : Type u_2} {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {lb : filter ℝ} {lb' : filter ℝ} {lt : filter β} {a : ℝ} {b : ℝ} {u : β → ℝ} {v : β → ℝ} [FTC_filter b lb lb'] (hab : interval_integrable f volume a b) (hmeas : measurable_at_filter f lb') (hf : filter.tendsto f (lb' ⊓ measure_theory.measure.ae volume) (nhds c)) (hu : filter.tendsto u lt lb) (hv : filter.tendsto v lt lb) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : ℝ) => f x) a (v t) volume - interval_integral (fun (x : ℝ) => f x) a (u t) volume -
      (v t - u t) • c)
  (v - u) lt := sorry

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `FTC_filter` pair
around `a`, and `f` has a finite limit `c` almost surely at `la'`, then
`(∫ x in v..b, f x) - ∫ x in u..b, f x = -(v - u) • c + o(∥v - u∥)` as `u` and `v` tend to `la`.

This lemma could've been formulated using `has_strict_deriv_at_filter` if we had this definition. -/
theorem integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left {β : Type u_2} {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {la : filter ℝ} {la' : filter ℝ} {lt : filter β} {a : ℝ} {b : ℝ} {u : β → ℝ} {v : β → ℝ} [FTC_filter a la la'] (hab : interval_integrable f volume a b) (hmeas : measurable_at_filter f la') (hf : filter.tendsto f (la' ⊓ measure_theory.measure.ae volume) (nhds c)) (hu : filter.tendsto u lt la) (hv : filter.tendsto v lt la) : asymptotics.is_o
  (fun (t : β) =>
    interval_integral (fun (x : ℝ) => f x) (v t) b volume - interval_integral (fun (x : ℝ) => f x) (u t) b volume +
      (v t - u t) • c)
  (v - u) lt := sorry

/-!
#### Strict differentiability

In this section we prove that for a measurable function `f` integrable on `a..b`,

* `integral_has_strict_fderiv_at_of_tendsto_ae`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)` in the sense of strict differentiability
  provided that `f` tends to `ca` and `cb` almost surely as `x` tendsto to `a` and `b`,
  respectively;

* `integral_has_strict_fderiv_at`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • f b - u • f a` at `(a, b)` in the sense of strict differentiability
  provided that `f` is continuous at `a` and `b`;

* `integral_has_strict_deriv_at_of_tendsto_ae_right`: the function `u ↦ ∫ x in a..u, f x` has
  derivative `c` at `b` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `b`;

* `integral_has_strict_deriv_at_right`: the function `u ↦ ∫ x in a..u, f x` has derivative `f b` at
  `b` in the sense of strict differentiability provided that `f` is continuous at `b`;

* `integral_has_strict_deriv_at_of_tendsto_ae_left`: the function `u ↦ ∫ x in u..b, f x` has
  derivative `-c` at `a` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `a`;

* `integral_has_strict_deriv_at_left`: the function `u ↦ ∫ x in u..b, f x` has derivative `-f a` at
  `a` in the sense of strict differentiability provided that `f` is continuous at `a`.
-/

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`
in the sense of strict differentiability. -/
theorem integral_has_strict_fderiv_at_of_tendsto_ae {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {ca : E} {cb : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas_a : measurable_at_filter f (nhds a)) (hmeas_b : measurable_at_filter f (nhds b)) (ha : filter.tendsto f (nhds a ⊓ measure_theory.measure.ae volume) (nhds ca)) (hb : filter.tendsto f (nhds b ⊓ measure_theory.measure.ae volume) (nhds cb)) : has_strict_fderiv_at (fun (p : ℝ × ℝ) => interval_integral (fun (x : ℝ) => f x) (prod.fst p) (prod.snd p) volume)
  (continuous_linear_map.smul_right (continuous_linear_map.snd ℝ ℝ ℝ) cb -
    continuous_linear_map.smul_right (continuous_linear_map.fst ℝ ℝ ℝ) ca)
  (a, b) := sorry

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca`
at `(a, b)` in the sense of strict differentiability. -/
theorem integral_has_strict_fderiv_at {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas_a : measurable_at_filter f (nhds a)) (hmeas_b : measurable_at_filter f (nhds b)) (ha : continuous_at f a) (hb : continuous_at f b) : has_strict_fderiv_at (fun (p : ℝ × ℝ) => interval_integral (fun (x : ℝ) => f x) (prod.fst p) (prod.snd p) volume)
  (continuous_linear_map.smul_right (continuous_linear_map.snd ℝ ℝ ℝ) (f b) -
    continuous_linear_map.smul_right (continuous_linear_map.fst ℝ ℝ ℝ) (f a))
  (a, b) :=
  integral_has_strict_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b (filter.tendsto.mono_left ha inf_le_left)
    (filter.tendsto.mono_left hb inf_le_left)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b` in the sense
of strict differentiability. -/
theorem integral_has_strict_deriv_at_of_tendsto_ae_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds b)) (hb : filter.tendsto f (nhds b ⊓ measure_theory.measure.ae volume) (nhds c)) : has_strict_deriv_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) c b :=
  integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hf hmeas hb continuous_at_snd continuous_at_fst

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b` in the sense of strict
differentiability. -/
theorem integral_has_strict_deriv_at_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds b)) (hb : continuous_at f b) : has_strict_deriv_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) (f b) b :=
  integral_has_strict_deriv_at_of_tendsto_ae_right hf hmeas (filter.tendsto.mono_left hb inf_le_left)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-c` at `a` in the sense
of strict differentiability. -/
theorem integral_has_strict_deriv_at_of_tendsto_ae_left {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds a)) (ha : filter.tendsto f (nhds a ⊓ measure_theory.measure.ae volume) (nhds c)) : has_strict_deriv_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) u b volume) (-c) a := sorry

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a` in the sense of strict
differentiability. -/
theorem integral_has_strict_deriv_at_left {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds a)) (ha : continuous_at f a) : has_strict_deriv_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) u b volume) (-f a) a := sorry

/-!
#### Fréchet differentiability

In this subsection we restate results from the previous subsection in terms of `has_fderiv_at`,
`has_deriv_at`, `fderiv`, and `deriv`.
-/

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`. -/
theorem integral_has_fderiv_at_of_tendsto_ae {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {ca : E} {cb : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas_a : measurable_at_filter f (nhds a)) (hmeas_b : measurable_at_filter f (nhds b)) (ha : filter.tendsto f (nhds a ⊓ measure_theory.measure.ae volume) (nhds ca)) (hb : filter.tendsto f (nhds b ⊓ measure_theory.measure.ae volume) (nhds cb)) : has_fderiv_at (fun (p : ℝ × ℝ) => interval_integral (fun (x : ℝ) => f x) (prod.fst p) (prod.snd p) volume)
  (continuous_linear_map.smul_right (continuous_linear_map.snd ℝ ℝ ℝ) cb -
    continuous_linear_map.smul_right (continuous_linear_map.fst ℝ ℝ ℝ) ca)
  (a, b) :=
  has_strict_fderiv_at.has_fderiv_at (integral_has_strict_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca`
at `(a, b)`. -/
theorem integral_has_fderiv_at {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas_a : measurable_at_filter f (nhds a)) (hmeas_b : measurable_at_filter f (nhds b)) (ha : continuous_at f a) (hb : continuous_at f b) : has_fderiv_at (fun (p : ℝ × ℝ) => interval_integral (fun (x : ℝ) => f x) (prod.fst p) (prod.snd p) volume)
  (continuous_linear_map.smul_right (continuous_linear_map.snd ℝ ℝ ℝ) (f b) -
    continuous_linear_map.smul_right (continuous_linear_map.fst ℝ ℝ ℝ) (f a))
  (a, b) :=
  has_strict_fderiv_at.has_fderiv_at (integral_has_strict_fderiv_at hf hmeas_a hmeas_b ha hb)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then `fderiv`
derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦ v • cb - u • ca`. -/
theorem fderiv_integral_of_tendsto_ae {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {ca : E} {cb : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas_a : measurable_at_filter f (nhds a)) (hmeas_b : measurable_at_filter f (nhds b)) (ha : filter.tendsto f (nhds a ⊓ measure_theory.measure.ae volume) (nhds ca)) (hb : filter.tendsto f (nhds b ⊓ measure_theory.measure.ae volume) (nhds cb)) : fderiv ℝ (fun (p : ℝ × ℝ) => interval_integral (fun (x : ℝ) => f x) (prod.fst p) (prod.snd p) volume) (a, b) =
  continuous_linear_map.smul_right (continuous_linear_map.snd ℝ ℝ ℝ) cb -
    continuous_linear_map.smul_right (continuous_linear_map.fst ℝ ℝ ℝ) ca :=
  has_fderiv_at.fderiv (integral_has_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `fderiv` derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦
v • cb - u • ca`. -/
theorem fderiv_integral {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas_a : measurable_at_filter f (nhds a)) (hmeas_b : measurable_at_filter f (nhds b)) (ha : continuous_at f a) (hb : continuous_at f b) : fderiv ℝ (fun (p : ℝ × ℝ) => interval_integral (fun (x : ℝ) => f x) (prod.fst p) (prod.snd p) volume) (a, b) =
  continuous_linear_map.smul_right (continuous_linear_map.snd ℝ ℝ ℝ) (f b) -
    continuous_linear_map.smul_right (continuous_linear_map.fst ℝ ℝ ℝ) (f a) :=
  has_fderiv_at.fderiv (integral_has_fderiv_at hf hmeas_a hmeas_b ha hb)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b`. -/
theorem integral_has_deriv_at_of_tendsto_ae_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds b)) (hb : filter.tendsto f (nhds b ⊓ measure_theory.measure.ae volume) (nhds c)) : has_deriv_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) c b :=
  has_strict_deriv_at.has_deriv_at (integral_has_strict_deriv_at_of_tendsto_ae_right hf hmeas hb)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b`. -/
theorem integral_has_deriv_at_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds b)) (hb : continuous_at f b) : has_deriv_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) (f b) b :=
  has_strict_deriv_at.has_deriv_at (integral_has_strict_deriv_at_right hf hmeas hb)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
theorem deriv_integral_of_tendsto_ae_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds b)) (hb : filter.tendsto f (nhds b ⊓ measure_theory.measure.ae volume) (nhds c)) : deriv (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) b = c :=
  has_deriv_at.deriv (integral_has_deriv_at_of_tendsto_ae_right hf hmeas hb)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
theorem deriv_integral_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds b)) (hb : continuous_at f b) : deriv (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) b = f b :=
  has_deriv_at.deriv (integral_has_deriv_at_right hf hmeas hb)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-c` at `a`. -/
theorem integral_has_deriv_at_of_tendsto_ae_left {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds a)) (ha : filter.tendsto f (nhds a ⊓ measure_theory.measure.ae volume) (nhds c)) : has_deriv_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) u b volume) (-c) a :=
  has_strict_deriv_at.has_deriv_at (integral_has_strict_deriv_at_of_tendsto_ae_left hf hmeas ha)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a`. -/
theorem integral_has_deriv_at_left {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds a)) (ha : continuous_at f a) : has_deriv_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) u b volume) (-f a) a :=
  has_strict_deriv_at.has_deriv_at (integral_has_strict_deriv_at_left hf hmeas ha)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
theorem deriv_integral_of_tendsto_ae_left {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds a)) (hb : filter.tendsto f (nhds a ⊓ measure_theory.measure.ae volume) (nhds c)) : deriv (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) u b volume) a = -c :=
  has_deriv_at.deriv (integral_has_deriv_at_of_tendsto_ae_left hf hmeas hb)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
theorem deriv_integral_left {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (nhds a)) (hb : continuous_at f a) : deriv (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) u b volume) a = -f a :=
  has_deriv_at.deriv (integral_has_deriv_at_left hf hmeas hb)

/-!
#### One-sided derivatives
-/

/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • cb - u • ca` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to `ca`
and `cb` almost surely at the filters `la` and `lb` from the following table.

| `s`     | `la`         | `t`     | `lb`         |
| ------- | ----         | ---     | ----         |
| `Iic a` | `𝓝[Iic a] a` | `Iic b` | `𝓝[Iic b] b` |
| `Ici a` | `𝓝[Ioi a] a` | `Ici b` | `𝓝[Ioi b] b` |
| `{a}`   | `⊥`          | `{b}`   | `⊥`          |
| `univ`  | `𝓝 a`        | `univ`  | `𝓝 b`        |
-/
theorem integral_has_fderiv_within_at_of_tendsto_ae {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {ca : E} {cb : E} {la : filter ℝ} {lb : filter ℝ} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) {s : set ℝ} {t : set ℝ} [FTC_filter a (nhds_within a s) la] [FTC_filter b (nhds_within b t) lb] (hmeas_a : measurable_at_filter f la) (hmeas_b : measurable_at_filter f lb) (ha : filter.tendsto f (la ⊓ measure_theory.measure.ae volume) (nhds ca)) (hb : filter.tendsto f (lb ⊓ measure_theory.measure.ae volume) (nhds cb)) : has_fderiv_within_at (fun (p : ℝ × ℝ) => interval_integral (fun (x : ℝ) => f x) (prod.fst p) (prod.snd p) volume)
  (continuous_linear_map.smul_right (continuous_linear_map.snd ℝ ℝ ℝ) cb -
    continuous_linear_map.smul_right (continuous_linear_map.fst ℝ ℝ ℝ) ca)
  (set.prod s t) (a, b) := sorry

/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • f b - u • f a` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to
`f a` and `f b` at the filters `la` and `lb` from the following table. In most cases this assumption
is definitionally equal `continuous_at f _` or `continuous_within_at f _ _`.

| `s`     | `la`         | `t`     | `lb`         |
| ------- | ----         | ---     | ----         |
| `Iic a` | `𝓝[Iic a] a` | `Iic b` | `𝓝[Iic b] b` |
| `Ici a` | `𝓝[Ioi a] a` | `Ici b` | `𝓝[Ioi b] b` |
| `{a}`   | `⊥`          | `{b}`   | `⊥`          |
| `univ`  | `𝓝 a`        | `univ`  | `𝓝 b`        |
-/
theorem integral_has_fderiv_within_at {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {la : filter ℝ} {lb : filter ℝ} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas_a : measurable_at_filter f la) (hmeas_b : measurable_at_filter f lb) {s : set ℝ} {t : set ℝ} [FTC_filter a (nhds_within a s) la] [FTC_filter b (nhds_within b t) lb] (ha : filter.tendsto f la (nhds (f a))) (hb : filter.tendsto f lb (nhds (f b))) : has_fderiv_within_at (fun (p : ℝ × ℝ) => interval_integral (fun (x : ℝ) => f x) (prod.fst p) (prod.snd p) volume)
  (continuous_linear_map.smul_right (continuous_linear_map.snd ℝ ℝ ℝ) (f b) -
    continuous_linear_map.smul_right (continuous_linear_map.fst ℝ ℝ ℝ) (f a))
  (set.prod s t) (a, b) :=
  integral_has_fderiv_within_at_of_tendsto_ae hf hmeas_a hmeas_b (filter.tendsto.mono_left ha inf_le_left)
    (filter.tendsto.mono_left hb inf_le_left)

/-- An auxiliary tactic closing goals `unique_diff_within_at ℝ s a` where
`s ∈ {Iic a, Ici a, univ}`. -/
/-- Let `f` be a measurable function integrable on `a..b`. Choose `s ∈ {Iic a, Ici a, univ}`
and `t ∈ {Iic b, Ici b, univ}`. Suppose that `f` tends to `ca` and `cb` almost surely at the filters
`la` and `lb` from the table below. Then `fderiv_within ℝ (λ p, ∫ x in p.1..p.2, f x) (s.prod t)`
is equal to `(u, v) ↦ u • cb - v • ca`.

| `s`     | `la`         | `t`     | `lb`         |
| ------- | ----         | ---     | ----         |
| `Iic a` | `𝓝[Iic a] a` | `Iic b` | `𝓝[Iic b] b` |
| `Ici a` | `𝓝[Ioi a] a` | `Ici b` | `𝓝[Ioi b] b` |
| `univ`  | `𝓝 a`        | `univ`  | `𝓝 b`        |

-/
theorem fderiv_within_integral_of_tendsto_ae {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {ca : E} {cb : E} {la : filter ℝ} {lb : filter ℝ} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) (hmeas_a : measurable_at_filter f la) (hmeas_b : measurable_at_filter f lb) {s : set ℝ} {t : set ℝ} [FTC_filter a (nhds_within a s) la] [FTC_filter b (nhds_within b t) lb] (ha : filter.tendsto f (la ⊓ measure_theory.measure.ae volume) (nhds ca)) (hb : filter.tendsto f (lb ⊓ measure_theory.measure.ae volume) (nhds cb)) (hs : autoParam (unique_diff_within_at ℝ s a)
  (Lean.Syntax.ident Lean.SourceInfo.none
    (String.toSubstring "Mathlib.interval_integral.unique_diff_within_at_Ici_Iic_univ")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "interval_integral")
      "unique_diff_within_at_Ici_Iic_univ")
    [])) (ht : autoParam (unique_diff_within_at ℝ t b)
  (Lean.Syntax.ident Lean.SourceInfo.none
    (String.toSubstring "Mathlib.interval_integral.unique_diff_within_at_Ici_Iic_univ")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "interval_integral")
      "unique_diff_within_at_Ici_Iic_univ")
    [])) : fderiv_within ℝ (fun (p : ℝ × ℝ) => interval_integral (fun (x : ℝ) => f x) (prod.fst p) (prod.snd p) volume)
    (set.prod s t) (a, b) =
  continuous_linear_map.smul_right (continuous_linear_map.snd ℝ ℝ ℝ) cb -
    continuous_linear_map.smul_right (continuous_linear_map.fst ℝ ℝ ℝ) ca :=
  has_fderiv_within_at.fderiv_within (integral_has_fderiv_within_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb)
    (unique_diff_within_at.prod hs ht)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left,
then `u ↦ ∫ x in a..u, f x` has right (resp., left) derivative `c` at `b`. -/
theorem integral_has_deriv_within_at_of_tendsto_ae_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) {s : set ℝ} {t : set ℝ} [FTC_filter b (nhds_within b s) (nhds_within b t)] (hmeas : measurable_at_filter f (nhds_within b t)) (hb : filter.tendsto f (nhds_within b t ⊓ measure_theory.measure.ae volume) (nhds c)) : has_deriv_within_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) c s b :=
  integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hf hmeas hb
    (filter.tendsto.mono_right filter.tendsto_const_pure FTC_filter.pure_le) filter.tendsto_id

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `b`, then `u ↦ ∫ x in a..u, f x` has left (resp., right)
derivative `f b` at `b`. -/
theorem integral_has_deriv_within_at_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) {s : set ℝ} {t : set ℝ} [FTC_filter b (nhds_within b s) (nhds_within b t)] (hmeas : measurable_at_filter f (nhds_within b t)) (hb : continuous_within_at f t b) : has_deriv_within_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) (f b) s b :=
  integral_has_deriv_within_at_of_tendsto_ae_right hf hmeas (filter.tendsto.mono_left hb inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
theorem deriv_within_integral_of_tendsto_ae_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) {s : set ℝ} {t : set ℝ} [FTC_filter b (nhds_within b s) (nhds_within b t)] (hmeas : measurable_at_filter f (nhds_within b t)) (hb : filter.tendsto f (nhds_within b t ⊓ measure_theory.measure.ae volume) (nhds c)) (hs : autoParam (unique_diff_within_at ℝ s b)
  (Lean.Syntax.ident Lean.SourceInfo.none
    (String.toSubstring "Mathlib.interval_integral.unique_diff_within_at_Ici_Iic_univ")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "interval_integral")
      "unique_diff_within_at_Ici_Iic_univ")
    [])) : deriv_within (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) s b = c :=
  has_deriv_within_at.deriv_within (integral_has_deriv_within_at_of_tendsto_ae_right hf hmeas hb) hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `b`, then the right (resp., left) derivative of
`u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
theorem deriv_within_integral_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) {s : set ℝ} {t : set ℝ} [FTC_filter b (nhds_within b s) (nhds_within b t)] (hmeas : measurable_at_filter f (nhds_within b t)) (hb : continuous_within_at f t b) (hs : autoParam (unique_diff_within_at ℝ s b)
  (Lean.Syntax.ident Lean.SourceInfo.none
    (String.toSubstring "Mathlib.interval_integral.unique_diff_within_at_Ici_Iic_univ")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "interval_integral")
      "unique_diff_within_at_Ici_Iic_univ")
    [])) : deriv_within (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) s b = f b :=
  has_deriv_within_at.deriv_within (integral_has_deriv_within_at_right hf hmeas hb) hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left,
then `u ↦ ∫ x in u..b, f x` has right (resp., left) derivative `-c` at `a`. -/
theorem integral_has_deriv_within_at_of_tendsto_ae_left {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) {s : set ℝ} {t : set ℝ} [FTC_filter a (nhds_within a s) (nhds_within a t)] (hmeas : measurable_at_filter f (nhds_within a t)) (ha : filter.tendsto f (nhds_within a t ⊓ measure_theory.measure.ae volume) (nhds c)) : has_deriv_within_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) u b volume) (-c) s a := sorry

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `a`, then `u ↦ ∫ x in u..b, f x` has left (resp., right)
derivative `-f a` at `a`. -/
theorem integral_has_deriv_within_at_left {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) {s : set ℝ} {t : set ℝ} [FTC_filter a (nhds_within a s) (nhds_within a t)] (hmeas : measurable_at_filter f (nhds_within a t)) (ha : continuous_within_at f t a) : has_deriv_within_at (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) u b volume) (-f a) s a :=
  integral_has_deriv_within_at_of_tendsto_ae_left hf hmeas (filter.tendsto.mono_left ha inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
theorem deriv_within_integral_of_tendsto_ae_left {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {c : E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) {s : set ℝ} {t : set ℝ} [FTC_filter a (nhds_within a s) (nhds_within a t)] (hmeas : measurable_at_filter f (nhds_within a t)) (ha : filter.tendsto f (nhds_within a t ⊓ measure_theory.measure.ae volume) (nhds c)) (hs : autoParam (unique_diff_within_at ℝ s a)
  (Lean.Syntax.ident Lean.SourceInfo.none
    (String.toSubstring "Mathlib.interval_integral.unique_diff_within_at_Ici_Iic_univ")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "interval_integral")
      "unique_diff_within_at_Ici_Iic_univ")
    [])) : deriv_within (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) u b volume) s a = -c :=
  has_deriv_within_at.deriv_within (integral_has_deriv_within_at_of_tendsto_ae_left hf hmeas ha) hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `a`, then the right (resp., left) derivative of
`u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
theorem deriv_within_integral_left {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hf : interval_integrable f volume a b) {s : set ℝ} {t : set ℝ} [FTC_filter a (nhds_within a s) (nhds_within a t)] (hmeas : measurable_at_filter f (nhds_within a t)) (ha : continuous_within_at f t a) (hs : autoParam (unique_diff_within_at ℝ s a)
  (Lean.Syntax.ident Lean.SourceInfo.none
    (String.toSubstring "Mathlib.interval_integral.unique_diff_within_at_Ici_Iic_univ")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "interval_integral")
      "unique_diff_within_at_Ici_Iic_univ")
    [])) : deriv_within (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) u b volume) s a = -f a :=
  has_deriv_within_at.deriv_within (integral_has_deriv_within_at_left hf hmeas ha) hs

/-!
### Fundamental theorem of calculus, part 2

This section contains theorems pertaining to FTC-2 for interval integrals. -/

/-- The integral of a continuous function is differentiable on a real set `s`. -/
theorem differentiable_on_integral_of_continuous {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {s : set ℝ} (hintg : ∀ (x : ℝ), x ∈ s → interval_integrable f volume a x) (hcont : continuous f) : differentiable_on ℝ (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) s := sorry

/-- The integral of a continuous function is continuous on a real set `s`. This is true even
  without the assumption of continuity, but a proof of that fact does not yet exist in mathlib. -/
theorem continuous_on_integral_of_continuous {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {s : set ℝ} (hintg : ∀ (x : ℝ), x ∈ s → interval_integrable f volume a x) (hcont : continuous f) : continuous_on (fun (u : ℝ) => interval_integral (fun (x : ℝ) => f x) a u volume) s :=
  differentiable_on.continuous_on (differentiable_on_integral_of_continuous hintg hcont)

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` and has a right
  derivative at `f' x` for all `x` in `[a, b)`, and `f'` is continuous on `[a, b]`, then
  `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_right_of_le {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} {f' : ℝ → E} (hab : a ≤ b) (hcont : continuous_on f (set.Icc a b)) (hderiv : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f (f' x) (set.Ici x) x) (hcont' : continuous_on f' (set.Icc a b)) : interval_integral (fun (y : ℝ) => f' y) a b volume = f b - f a := sorry

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`) and
  has a right derivative at `f' x` for all `x` in `[a, b)`, and `f'` is continuous on `[a, b]` then
  `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_right {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} {f' : ℝ → E} (hcont : continuous_on f (set.interval a b)) (hderiv : ∀ (x : ℝ), x ∈ set.Ico (min a b) (max a b) → has_deriv_within_at f (f' x) (set.Ici x) x) (hcont' : continuous_on f' (set.interval a b)) : interval_integral (fun (y : ℝ) => f' y) a b volume = f b - f a := sorry

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` and has a derivative
  at `f' x` for all `x` in `(a, b)`, and `f'` is continuous on `[a, b]`, then `∫ y in a..b, f' y`
  equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_at' {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} {f' : ℝ → E} (hcont : continuous_on f (set.interval a b)) (hderiv : ∀ (x : ℝ), x ∈ set.Ioo (min a b) (max a b) → has_deriv_at f (f' x) x) (hcont' : continuous_on f' (set.interval a b)) : interval_integral (fun (y : ℝ) => f' y) a b volume = f b - f a := sorry

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` has a derivative at `f' x` for all `x` in
  `[a, b]` and `f'` is continuous on `[a, b]`, then `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_at {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} {f' : ℝ → E} (hderiv : ∀ (x : ℝ), x ∈ set.interval a b → has_deriv_at f (f' x) x) (hcont' : continuous_on f' (set.interval a b)) : interval_integral (fun (y : ℝ) => f' y) a b volume = f b - f a := sorry

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is differentiable at every `x` in `[a, b]` and
  its derivative is continuous on `[a, b]`, then `∫ y in a..b, deriv f y` equals `f b - f a`. -/
theorem integral_deriv_eq_sub {E : Type u_4} [measurable_space E] [normed_group E] [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E] {f : ℝ → E} {a : ℝ} {b : ℝ} (hderiv : ∀ (x : ℝ), x ∈ set.interval a b → differentiable_at ℝ f x) (hcont' : continuous_on (deriv f) (set.interval a b)) : interval_integral (fun (y : ℝ) => deriv f y) a b volume = f b - f a :=
  integral_eq_sub_of_has_deriv_at
    (fun (x : ℝ) (hx : x ∈ set.interval a b) => differentiable_at.has_deriv_at (hderiv x hx)) hcont'

/-!
### Integration by parts
-/

theorem integral_deriv_mul_eq_sub {a : ℝ} {b : ℝ} {u : ℝ → ℝ} {v : ℝ → ℝ} {u' : ℝ → ℝ} {v' : ℝ → ℝ} (hu : ∀ (x : ℝ), x ∈ set.interval a b → has_deriv_at u (u' x) x) (hv : ∀ (x : ℝ), x ∈ set.interval a b → has_deriv_at v (v' x) x) (hcu' : continuous_on u' (set.interval a b)) (hcv' : continuous_on v' (set.interval a b)) : interval_integral (fun (x : ℝ) => u' x * v x + u x * v' x) a b volume = u b * v b - u a * v a := sorry

theorem integral_mul_deriv_eq_deriv_mul {a : ℝ} {b : ℝ} {u : ℝ → ℝ} {v : ℝ → ℝ} {u' : ℝ → ℝ} {v' : ℝ → ℝ} (hu : ∀ (x : ℝ), x ∈ set.interval a b → has_deriv_at u (u' x) x) (hv : ∀ (x : ℝ), x ∈ set.interval a b → has_deriv_at v (v' x) x) (hcu' : continuous_on u' (set.interval a b)) (hcv' : continuous_on v' (set.interval a b)) : interval_integral (fun (x : ℝ) => u x * v' x) a b volume =
  u b * v b - u a * v a - interval_integral (fun (x : ℝ) => v x * u' x) a b volume := sorry

