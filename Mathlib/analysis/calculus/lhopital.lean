/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.calculus.mean_value
import Mathlib.PostPort

namespace Mathlib

/-!
# L'Hôpital's rule for 0/0 indeterminate forms

In this file, we prove several forms of "L'Hopital's rule" for computing 0/0
indeterminate forms. The proof of `has_deriv_at.lhopital_zero_right_on_Ioo`
is based on the one given in the corresponding
[Wikibooks](https://en.wikibooks.org/wiki/Calculus/L%27H%C3%B4pital%27s_Rule)
chapter, and all other statements are derived from this one by composing by
carefully chosen functions.

Note that the filter `f'/g'` tends to isn't required to be one of `𝓝 a`,
`at_top` or `at_bot`. In fact, we give a slightly stronger statement by
allowing it to be any filter on `ℝ`.

Each statement is available in a `has_deriv_at` form and a `deriv` form, which
is denoted by each statement being in either the `has_deriv_at` or the `deriv`
namespace.
-/

/-!
## Interval-based versions

We start by proving statements where all conditions (derivability, `g' ≠ 0`) have
to be satisfied on an explicitely-provided interval.
-/

namespace has_deriv_at


theorem lhopital_zero_right_on_Ioo {a : ℝ} {b : ℝ} (hab : a < b) {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at f (f' x) x) (hgg' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at g (g' x) x) (hg' : ∀ (x : ℝ), x ∈ set.Ioo a b → g' x ≠ 0) (hfa : filter.tendsto f (nhds_within a (set.Ioi a)) (nhds 0)) (hga : filter.tendsto g (nhds_within a (set.Ioi a)) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) (nhds_within a (set.Ioi a)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.Ioi a)) l := sorry

theorem lhopital_zero_right_on_Ico {a : ℝ} {b : ℝ} (hab : a < b) {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at f (f' x) x) (hgg' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at g (g' x) x) (hcf : continuous_on f (set.Ico a b)) (hcg : continuous_on g (set.Ico a b)) (hg' : ∀ (x : ℝ), x ∈ set.Ioo a b → g' x ≠ 0) (hfa : f a = 0) (hga : g a = 0) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) (nhds_within a (set.Ioi a)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.Ioi a)) l := sorry

theorem lhopital_zero_left_on_Ioo {a : ℝ} {b : ℝ} (hab : a < b) {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at f (f' x) x) (hgg' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at g (g' x) x) (hg' : ∀ (x : ℝ), x ∈ set.Ioo a b → g' x ≠ 0) (hfb : filter.tendsto f (nhds_within b (set.Iio b)) (nhds 0)) (hgb : filter.tendsto g (nhds_within b (set.Iio b)) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) (nhds_within b (set.Iio b)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within b (set.Iio b)) l := sorry

theorem lhopital_zero_left_on_Ioc {a : ℝ} {b : ℝ} (hab : a < b) {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at f (f' x) x) (hgg' : ∀ (x : ℝ), x ∈ set.Ioo a b → has_deriv_at g (g' x) x) (hcf : continuous_on f (set.Ioc a b)) (hcg : continuous_on g (set.Ioc a b)) (hg' : ∀ (x : ℝ), x ∈ set.Ioo a b → g' x ≠ 0) (hfb : f b = 0) (hgb : g b = 0) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) (nhds_within b (set.Iio b)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within b (set.Iio b)) l := sorry

theorem lhopital_zero_at_top_on_Ioi {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : ∀ (x : ℝ), x ∈ set.Ioi a → has_deriv_at f (f' x) x) (hgg' : ∀ (x : ℝ), x ∈ set.Ioi a → has_deriv_at g (g' x) x) (hg' : ∀ (x : ℝ), x ∈ set.Ioi a → g' x ≠ 0) (hftop : filter.tendsto f filter.at_top (nhds 0)) (hgtop : filter.tendsto g filter.at_top (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) filter.at_top l) : filter.tendsto (fun (x : ℝ) => f x / g x) filter.at_top l := sorry

theorem lhopital_zero_at_bot_on_Iio {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : ∀ (x : ℝ), x ∈ set.Iio a → has_deriv_at f (f' x) x) (hgg' : ∀ (x : ℝ), x ∈ set.Iio a → has_deriv_at g (g' x) x) (hg' : ∀ (x : ℝ), x ∈ set.Iio a → g' x ≠ 0) (hfbot : filter.tendsto f filter.at_bot (nhds 0)) (hgbot : filter.tendsto g filter.at_bot (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) filter.at_bot l) : filter.tendsto (fun (x : ℝ) => f x / g x) filter.at_bot l := sorry

end has_deriv_at


namespace deriv


theorem lhopital_zero_right_on_Ioo {a : ℝ} {b : ℝ} (hab : a < b) {l : filter ℝ} {f : ℝ → ℝ} {g : ℝ → ℝ} (hdf : differentiable_on ℝ f (set.Ioo a b)) (hg' : ∀ (x : ℝ), x ∈ set.Ioo a b → deriv g x ≠ 0) (hfa : filter.tendsto f (nhds_within a (set.Ioi a)) (nhds 0)) (hga : filter.tendsto g (nhds_within a (set.Ioi a)) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => deriv f x / deriv g x) (nhds_within a (set.Ioi a)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.Ioi a)) l := sorry

theorem lhopital_zero_right_on_Ico {a : ℝ} {b : ℝ} (hab : a < b) {l : filter ℝ} {f : ℝ → ℝ} {g : ℝ → ℝ} (hdf : differentiable_on ℝ f (set.Ioo a b)) (hcf : continuous_on f (set.Ico a b)) (hcg : continuous_on g (set.Ico a b)) (hg' : ∀ (x : ℝ), x ∈ set.Ioo a b → deriv g x ≠ 0) (hfa : f a = 0) (hga : g a = 0) (hdiv : filter.tendsto (fun (x : ℝ) => deriv f x / deriv g x) (nhds_within a (set.Ioi a)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.Ioi a)) l := sorry

theorem lhopital_zero_left_on_Ioo {a : ℝ} {b : ℝ} (hab : a < b) {l : filter ℝ} {f : ℝ → ℝ} {g : ℝ → ℝ} (hdf : differentiable_on ℝ f (set.Ioo a b)) (hg' : ∀ (x : ℝ), x ∈ set.Ioo a b → deriv g x ≠ 0) (hfb : filter.tendsto f (nhds_within b (set.Iio b)) (nhds 0)) (hgb : filter.tendsto g (nhds_within b (set.Iio b)) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => deriv f x / deriv g x) (nhds_within b (set.Iio b)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within b (set.Iio b)) l := sorry

theorem lhopital_zero_at_top_on_Ioi {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {g : ℝ → ℝ} (hdf : differentiable_on ℝ f (set.Ioi a)) (hg' : ∀ (x : ℝ), x ∈ set.Ioi a → deriv g x ≠ 0) (hftop : filter.tendsto f filter.at_top (nhds 0)) (hgtop : filter.tendsto g filter.at_top (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => deriv f x / deriv g x) filter.at_top l) : filter.tendsto (fun (x : ℝ) => f x / g x) filter.at_top l := sorry

theorem lhopital_zero_at_bot_on_Iio {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {g : ℝ → ℝ} (hdf : differentiable_on ℝ f (set.Iio a)) (hg' : ∀ (x : ℝ), x ∈ set.Iio a → deriv g x ≠ 0) (hfbot : filter.tendsto f filter.at_bot (nhds 0)) (hgbot : filter.tendsto g filter.at_bot (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => deriv f x / deriv g x) filter.at_bot l) : filter.tendsto (fun (x : ℝ) => f x / g x) filter.at_bot l := sorry

end deriv


/-!
## Generic versions

The following statements no longer any explicit interval, as they only require
conditions holding eventually.
-/

namespace has_deriv_at


/-- L'Hôpital's rule for approaching a real from the right, `has_deriv_at` version -/
theorem lhopital_zero_nhds_right {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : filter.eventually (fun (x : ℝ) => has_deriv_at f (f' x) x) (nhds_within a (set.Ioi a))) (hgg' : filter.eventually (fun (x : ℝ) => has_deriv_at g (g' x) x) (nhds_within a (set.Ioi a))) (hg' : filter.eventually (fun (x : ℝ) => g' x ≠ 0) (nhds_within a (set.Ioi a))) (hfa : filter.tendsto f (nhds_within a (set.Ioi a)) (nhds 0)) (hga : filter.tendsto g (nhds_within a (set.Ioi a)) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) (nhds_within a (set.Ioi a)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.Ioi a)) l := sorry

/-- L'Hôpital's rule for approaching a real from the left, `has_deriv_at` version -/
theorem lhopital_zero_nhds_left {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : filter.eventually (fun (x : ℝ) => has_deriv_at f (f' x) x) (nhds_within a (set.Iio a))) (hgg' : filter.eventually (fun (x : ℝ) => has_deriv_at g (g' x) x) (nhds_within a (set.Iio a))) (hg' : filter.eventually (fun (x : ℝ) => g' x ≠ 0) (nhds_within a (set.Iio a))) (hfa : filter.tendsto f (nhds_within a (set.Iio a)) (nhds 0)) (hga : filter.tendsto g (nhds_within a (set.Iio a)) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) (nhds_within a (set.Iio a)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.Iio a)) l := sorry

/-- L'Hôpital's rule for approaching a real, `has_deriv_at` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds' {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : filter.eventually (fun (x : ℝ) => has_deriv_at f (f' x) x) (nhds_within a (set.univ \ singleton a))) (hgg' : filter.eventually (fun (x : ℝ) => has_deriv_at g (g' x) x) (nhds_within a (set.univ \ singleton a))) (hg' : filter.eventually (fun (x : ℝ) => g' x ≠ 0) (nhds_within a (set.univ \ singleton a))) (hfa : filter.tendsto f (nhds_within a (set.univ \ singleton a)) (nhds 0)) (hga : filter.tendsto g (nhds_within a (set.univ \ singleton a)) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) (nhds_within a (set.univ \ singleton a)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.univ \ singleton a)) l := sorry

/-- L'Hôpital's rule for approaching a real, `has_deriv_at` version -/
theorem lhopital_zero_nhds {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : filter.eventually (fun (x : ℝ) => has_deriv_at f (f' x) x) (nhds a)) (hgg' : filter.eventually (fun (x : ℝ) => has_deriv_at g (g' x) x) (nhds a)) (hg' : filter.eventually (fun (x : ℝ) => g' x ≠ 0) (nhds a)) (hfa : filter.tendsto f (nhds a) (nhds 0)) (hga : filter.tendsto g (nhds a) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) (nhds a) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.univ \ singleton a)) l :=
  lhopital_zero_nhds' (eventually_nhds_within_of_eventually_nhds hff') (eventually_nhds_within_of_eventually_nhds hgg')
    (eventually_nhds_within_of_eventually_nhds hg') (tendsto_nhds_within_of_tendsto_nhds hfa)
    (tendsto_nhds_within_of_tendsto_nhds hga) (tendsto_nhds_within_of_tendsto_nhds hdiv)

/-- L'Hôpital's rule for approaching +∞, `has_deriv_at` version -/
theorem lhopital_zero_at_top {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : filter.eventually (fun (x : ℝ) => has_deriv_at f (f' x) x) filter.at_top) (hgg' : filter.eventually (fun (x : ℝ) => has_deriv_at g (g' x) x) filter.at_top) (hg' : filter.eventually (fun (x : ℝ) => g' x ≠ 0) filter.at_top) (hftop : filter.tendsto f filter.at_top (nhds 0)) (hgtop : filter.tendsto g filter.at_top (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) filter.at_top l) : filter.tendsto (fun (x : ℝ) => f x / g x) filter.at_top l := sorry

/-- L'Hôpital's rule for approaching -∞, `has_deriv_at` version -/
theorem lhopital_zero_at_bot {l : filter ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} (hff' : filter.eventually (fun (x : ℝ) => has_deriv_at f (f' x) x) filter.at_bot) (hgg' : filter.eventually (fun (x : ℝ) => has_deriv_at g (g' x) x) filter.at_bot) (hg' : filter.eventually (fun (x : ℝ) => g' x ≠ 0) filter.at_bot) (hfbot : filter.tendsto f filter.at_bot (nhds 0)) (hgbot : filter.tendsto g filter.at_bot (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => f' x / g' x) filter.at_bot l) : filter.tendsto (fun (x : ℝ) => f x / g x) filter.at_bot l := sorry

end has_deriv_at


namespace deriv


/-- L'Hôpital's rule for approaching a real from the right, `deriv` version -/
theorem lhopital_zero_nhds_right {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {g : ℝ → ℝ} (hdf : filter.eventually (fun (x : ℝ) => differentiable_at ℝ f x) (nhds_within a (set.Ioi a))) (hg' : filter.eventually (fun (x : ℝ) => deriv g x ≠ 0) (nhds_within a (set.Ioi a))) (hfa : filter.tendsto f (nhds_within a (set.Ioi a)) (nhds 0)) (hga : filter.tendsto g (nhds_within a (set.Ioi a)) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => deriv f x / deriv g x) (nhds_within a (set.Ioi a)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.Ioi a)) l := sorry

/-- L'Hôpital's rule for approaching a real from the left, `deriv` version -/
theorem lhopital_zero_nhds_left {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {g : ℝ → ℝ} (hdf : filter.eventually (fun (x : ℝ) => differentiable_at ℝ f x) (nhds_within a (set.Iio a))) (hg' : filter.eventually (fun (x : ℝ) => deriv g x ≠ 0) (nhds_within a (set.Iio a))) (hfa : filter.tendsto f (nhds_within a (set.Iio a)) (nhds 0)) (hga : filter.tendsto g (nhds_within a (set.Iio a)) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => deriv f x / deriv g x) (nhds_within a (set.Iio a)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.Iio a)) l := sorry

/-- L'Hôpital's rule for approaching a real, `deriv` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds' {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {g : ℝ → ℝ} (hdf : filter.eventually (fun (x : ℝ) => differentiable_at ℝ f x) (nhds_within a (set.univ \ singleton a))) (hg' : filter.eventually (fun (x : ℝ) => deriv g x ≠ 0) (nhds_within a (set.univ \ singleton a))) (hfa : filter.tendsto f (nhds_within a (set.univ \ singleton a)) (nhds 0)) (hga : filter.tendsto g (nhds_within a (set.univ \ singleton a)) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => deriv f x / deriv g x) (nhds_within a (set.univ \ singleton a)) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.univ \ singleton a)) l := sorry

/-- L'Hôpital's rule for approaching a real, `deriv` version -/
theorem lhopital_zero_nhds {a : ℝ} {l : filter ℝ} {f : ℝ → ℝ} {g : ℝ → ℝ} (hdf : filter.eventually (fun (x : ℝ) => differentiable_at ℝ f x) (nhds a)) (hg' : filter.eventually (fun (x : ℝ) => deriv g x ≠ 0) (nhds a)) (hfa : filter.tendsto f (nhds a) (nhds 0)) (hga : filter.tendsto g (nhds a) (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => deriv f x / deriv g x) (nhds a) l) : filter.tendsto (fun (x : ℝ) => f x / g x) (nhds_within a (set.univ \ singleton a)) l :=
  lhopital_zero_nhds' (eventually_nhds_within_of_eventually_nhds hdf) (eventually_nhds_within_of_eventually_nhds hg')
    (tendsto_nhds_within_of_tendsto_nhds hfa) (tendsto_nhds_within_of_tendsto_nhds hga)
    (tendsto_nhds_within_of_tendsto_nhds hdiv)

/-- L'Hôpital's rule for approaching +∞, `deriv` version -/
theorem lhopital_zero_at_top {l : filter ℝ} {f : ℝ → ℝ} {g : ℝ → ℝ} (hdf : filter.eventually (fun (x : ℝ) => differentiable_at ℝ f x) filter.at_top) (hg' : filter.eventually (fun (x : ℝ) => deriv g x ≠ 0) filter.at_top) (hftop : filter.tendsto f filter.at_top (nhds 0)) (hgtop : filter.tendsto g filter.at_top (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => deriv f x / deriv g x) filter.at_top l) : filter.tendsto (fun (x : ℝ) => f x / g x) filter.at_top l := sorry

/-- L'Hôpital's rule for approaching -∞, `deriv` version -/
theorem lhopital_zero_at_bot {l : filter ℝ} {f : ℝ → ℝ} {g : ℝ → ℝ} (hdf : filter.eventually (fun (x : ℝ) => differentiable_at ℝ f x) filter.at_bot) (hg' : filter.eventually (fun (x : ℝ) => deriv g x ≠ 0) filter.at_bot) (hfbot : filter.tendsto f filter.at_bot (nhds 0)) (hgbot : filter.tendsto g filter.at_bot (nhds 0)) (hdiv : filter.tendsto (fun (x : ℝ) => deriv f x / deriv g x) filter.at_bot l) : filter.tendsto (fun (x : ℝ) => f x / g x) filter.at_bot l := sorry

