/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.filter.at_top_bot
import Mathlib.algebra.archimedean
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# `at_top` filter and archimedean (semi)rings/fields

In this file we prove that for a linear ordered archimedean semiring `R` and a function `f : α → ℕ`,
the function `coe ∘ f : α → R` tends to `at_top` along a filter `l` if and only if so does `f`.
We also prove that `coe : ℕ → R` tends to `at_top` along `at_top`, as well as version of these
two results for `ℤ` (and a ring `R`) and `ℚ` (and a field `R`).
-/

theorem tendsto_coe_nat_at_top_iff {α : Type u_1} {R : Type u_2} [ordered_semiring R] [nontrivial R] [archimedean R] {f : α → ℕ} {l : filter α} : filter.tendsto (fun (n : α) => ↑(f n)) l filter.at_top ↔ filter.tendsto f l filter.at_top :=
  filter.tendsto_at_top_embedding (fun (a₁ a₂ : ℕ) => nat.cast_le) exists_nat_ge

theorem tendsto_coe_nat_at_top_at_top {R : Type u_2} [ordered_semiring R] [archimedean R] : filter.tendsto coe filter.at_top filter.at_top :=
  monotone.tendsto_at_top_at_top nat.mono_cast exists_nat_ge

theorem tendsto_coe_int_at_top_iff {α : Type u_1} {R : Type u_2} [ordered_ring R] [nontrivial R] [archimedean R] {f : α → ℤ} {l : filter α} : filter.tendsto (fun (n : α) => ↑(f n)) l filter.at_top ↔ filter.tendsto f l filter.at_top := sorry

theorem tendsto_coe_int_at_top_at_top {R : Type u_2} [ordered_ring R] [archimedean R] : filter.tendsto coe filter.at_top filter.at_top := sorry

theorem tendsto_coe_rat_at_top_iff {α : Type u_1} {R : Type u_2} [linear_ordered_field R] [archimedean R] {f : α → ℚ} {l : filter α} : filter.tendsto (fun (n : α) => ↑(f n)) l filter.at_top ↔ filter.tendsto f l filter.at_top := sorry

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the left) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `filter.tendsto.const_mul_at_top`). -/
theorem filter.tendsto.const_mul_at_top' {α : Type u_1} {R : Type u_2} [linear_ordered_semiring R] [archimedean R] {l : filter α} {f : α → R} {r : R} (hr : 0 < r) (hf : filter.tendsto f l filter.at_top) : filter.tendsto (fun (x : α) => r * f x) l filter.at_top := sorry

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the right) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `filter.tendsto.at_top_mul_const`). -/
theorem filter.tendsto.at_top_mul_const' {α : Type u_1} {R : Type u_2} [linear_ordered_semiring R] [archimedean R] {l : filter α} {f : α → R} {r : R} (hr : 0 < r) (hf : filter.tendsto f l filter.at_top) : filter.tendsto (fun (x : α) => f x * r) l filter.at_top := sorry

