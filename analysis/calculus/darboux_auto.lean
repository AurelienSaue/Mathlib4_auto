/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.calculus.mean_value
import PostPort

namespace Mathlib

/-!
# Darboux's theorem

In this file we prove that the derivative of a differentiable function on an interval takes all
intermediate values. The proof is based on the
[Wikipedia](https://en.wikipedia.org/wiki/Darboux%27s_theorem_(analysis)) page about this theorem.
-/

/-- Darboux's theorem: if `a ≤ b` and `f' a < m < f' b`, then `f' c = m` for some `c ∈ [a, b]`. -/
theorem exists_has_deriv_within_at_eq_of_gt_of_lt {a : ℝ} {b : ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} (hab : a ≤ b) (hf : ∀ (x : ℝ), x ∈ set.Icc a b → has_deriv_within_at f (f' x) (set.Icc a b) x) {m : ℝ} (hma : f' a < m) (hmb : m < f' b) : m ∈ f' '' set.Icc a b := sorry

/-- Darboux's theorem: if `a ≤ b` and `f' a > m > f' b`, then `f' c = m` for some `c ∈ [a, b]`. -/
theorem exists_has_deriv_within_at_eq_of_lt_of_gt {a : ℝ} {b : ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} (hab : a ≤ b) (hf : ∀ (x : ℝ), x ∈ set.Icc a b → has_deriv_within_at f (f' x) (set.Icc a b) x) {m : ℝ} (hma : m < f' a) (hmb : f' b < m) : m ∈ f' '' set.Icc a b := sorry

/-- Darboux's theorem: the image of a convex set under `f'` is a convex set. -/
theorem convex_image_has_deriv_at {f : ℝ → ℝ} {f' : ℝ → ℝ} {s : set ℝ} (hs : convex s) (hf : ∀ (x : ℝ), x ∈ s → has_deriv_at f (f' x) x) : convex (f' '' s) := sorry

/-- If the derivative of a function is never equal to `m`, then either
it is always greater than `m`, or it is always less than `m`. -/
theorem deriv_forall_lt_or_forall_gt_of_forall_ne {f : ℝ → ℝ} {f' : ℝ → ℝ} {s : set ℝ} (hs : convex s) (hf : ∀ (x : ℝ), x ∈ s → has_deriv_at f (f' x) x) {m : ℝ} (hf' : ∀ (x : ℝ), x ∈ s → f' x ≠ m) : (∀ (x : ℝ), x ∈ s → f' x < m) ∨ ∀ (x : ℝ), x ∈ s → m < f' x := sorry

