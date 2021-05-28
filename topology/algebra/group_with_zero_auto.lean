/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.algebra.monoid
import Mathlib.algebra.group.pi
import PostPort

universes u_1 u_2 u_3 l 

namespace Mathlib

/-!
# Topological group with zero

In this file we define `has_continuous_inv'` to be a mixin typeclass a type with `has_inv` and
`has_zero` (e.g., a `group_with_zero`) such that `λ x, x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. Currently the only example of `has_continuous_inv'` in
`mathlib` which is not a normed field is the type `nnnreal` (a.k.a. `ℝ≥0`) of nonnegative real
numbers.

Then we prove lemmas about continuity of `x ↦ x⁻¹` and `f / g` providing dot-style `*.inv'` and
`*.div` operations on `filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`,
and `continuous`. As a special case, we provide `*.div_const` operations that require only
`group_with_zero` and `has_continuous_mul` instances.

All lemmas about `(⁻¹)` use `inv'` in their names because lemmas without `'` are used for
`topological_group`s. We also use `'` in the typeclass name `has_continuous_inv'` for the sake of
consistency of notation.
-/

/-!
### A group with zero with continuous multiplication

If `G₀` is a group with zero with continuous `(*)`, then `(/y)` is continuous for any `y`. In this
section we prove lemmas that immediately follow from this fact providing `*.div_const` dot-style
operations on `filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`, and
`continuous`.
-/

theorem filter.tendsto.div_const {α : Type u_1} {G₀ : Type u_2} [group_with_zero G₀] [topological_space G₀] [has_continuous_mul G₀] {f : α → G₀} {l : filter α} {x : G₀} {y : G₀} (hf : filter.tendsto f l (nhds x)) : filter.tendsto (fun (a : α) => f a / y) l (nhds (x / y)) := sorry

theorem continuous_at.div_const {α : Type u_1} {G₀ : Type u_2} [group_with_zero G₀] [topological_space G₀] [has_continuous_mul G₀] {f : α → G₀} [topological_space α] (hf : continuous f) {y : G₀} : continuous fun (x : α) => f x / y := sorry

theorem continuous_within_at.div_const {α : Type u_1} {G₀ : Type u_2} [group_with_zero G₀] [topological_space G₀] [has_continuous_mul G₀] {f : α → G₀} {s : set α} [topological_space α] {a : α} (hf : continuous_within_at f s a) {y : G₀} : continuous_within_at (fun (x : α) => f x / y) s a :=
  filter.tendsto.div_const hf

theorem continuous_on.div_const {α : Type u_1} {G₀ : Type u_2} [group_with_zero G₀] [topological_space G₀] [has_continuous_mul G₀] {f : α → G₀} {s : set α} [topological_space α] (hf : continuous_on f s) {y : G₀} : continuous_on (fun (x : α) => f x / y) s := sorry

theorem continuous.div_const {α : Type u_1} {G₀ : Type u_2} [group_with_zero G₀] [topological_space G₀] [has_continuous_mul G₀] {f : α → G₀} [topological_space α] (hf : continuous f) {y : G₀} : continuous fun (x : α) => f x / y := sorry

/-- A type with `0` and `has_inv` such that `λ x, x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. -/
class has_continuous_inv' (G₀ : Type u_3) [HasZero G₀] [has_inv G₀] [topological_space G₀] 
where
  continuous_at_inv' : ∀ {x : G₀}, x ≠ 0 → continuous_at has_inv.inv x

/-!
### Continuity of `λ x, x⁻¹` at a non-zero point

We define `topological_group_with_zero` to be a `group_with_zero` such that the operation `x ↦ x⁻¹`
is continuous at all nonzero points. In this section we prove dot-style `*.inv'` lemmas for
`filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`, and `continuous`.
-/

theorem tendsto_inv' {G₀ : Type u_2} [HasZero G₀] [has_inv G₀] [topological_space G₀] [has_continuous_inv' G₀] {x : G₀} (hx : x ≠ 0) : filter.tendsto has_inv.inv (nhds x) (nhds (x⁻¹)) :=
  continuous_at_inv' hx

theorem continuous_on_inv' {G₀ : Type u_2} [HasZero G₀] [has_inv G₀] [topological_space G₀] [has_continuous_inv' G₀] : continuous_on has_inv.inv (singleton 0ᶜ) :=
  fun (x : G₀) (hx : x ∈ (singleton 0ᶜ)) => continuous_at.continuous_within_at (continuous_at_inv' hx)

/-- If a function converges to a nonzero value, its inverse converges to the inverse of this value.
We use the name `tendsto.inv'` as `tendsto.inv` is already used in multiplicative topological
groups. -/
theorem filter.tendsto.inv' {α : Type u_1} {G₀ : Type u_2} [HasZero G₀] [has_inv G₀] [topological_space G₀] [has_continuous_inv' G₀] {l : filter α} {f : α → G₀} {a : G₀} (hf : filter.tendsto f l (nhds a)) (ha : a ≠ 0) : filter.tendsto (fun (x : α) => f x⁻¹) l (nhds (a⁻¹)) :=
  filter.tendsto.comp (tendsto_inv' ha) hf

theorem continuous_within_at.inv' {α : Type u_1} {G₀ : Type u_2} [HasZero G₀] [has_inv G₀] [topological_space G₀] [has_continuous_inv' G₀] {f : α → G₀} {s : set α} {a : α} [topological_space α] (hf : continuous_within_at f s a) (ha : f a ≠ 0) : continuous_within_at (fun (x : α) => f x⁻¹) s a :=
  filter.tendsto.inv' hf ha

theorem continuous_at.inv' {α : Type u_1} {G₀ : Type u_2} [HasZero G₀] [has_inv G₀] [topological_space G₀] [has_continuous_inv' G₀] {f : α → G₀} {a : α} [topological_space α] (hf : continuous_at f a) (ha : f a ≠ 0) : continuous_at (fun (x : α) => f x⁻¹) a :=
  filter.tendsto.inv' hf ha

theorem continuous.inv' {α : Type u_1} {G₀ : Type u_2} [HasZero G₀] [has_inv G₀] [topological_space G₀] [has_continuous_inv' G₀] {f : α → G₀} [topological_space α] (hf : continuous f) (h0 : ∀ (x : α), f x ≠ 0) : continuous fun (x : α) => f x⁻¹ :=
  iff.mpr continuous_iff_continuous_at fun (x : α) => filter.tendsto.inv' (continuous.tendsto hf x) (h0 x)

theorem continuous_on.inv' {α : Type u_1} {G₀ : Type u_2} [HasZero G₀] [has_inv G₀] [topological_space G₀] [has_continuous_inv' G₀] {f : α → G₀} {s : set α} [topological_space α] (hf : continuous_on f s) (h0 : ∀ (x : α), x ∈ s → f x ≠ 0) : continuous_on (fun (x : α) => f x⁻¹) s :=
  fun (x : α) (hx : x ∈ s) => continuous_within_at.inv' (hf x hx) (h0 x hx)

/-!
### Continuity of division

If `G₀` is a `group_with_zero` with `x ↦ x⁻¹` continuous at all nonzero points and `(*)`, then
division `(/)` is continuous at any point where the denominator is continuous.
-/

theorem filter.tendsto.div {α : Type u_1} {G₀ : Type u_2} [group_with_zero G₀] [topological_space G₀] [has_continuous_inv' G₀] [has_continuous_mul G₀] {f : α → G₀} {g : α → G₀} {l : filter α} {a : G₀} {b : G₀} (hf : filter.tendsto f l (nhds a)) (hg : filter.tendsto g l (nhds b)) (hy : b ≠ 0) : filter.tendsto (f / g) l (nhds (a / b)) := sorry

theorem continuous_within_at.div {α : Type u_1} {G₀ : Type u_2} [group_with_zero G₀] [topological_space G₀] [has_continuous_inv' G₀] [has_continuous_mul G₀] {f : α → G₀} {g : α → G₀} [topological_space α] {s : set α} {a : α} (hf : continuous_within_at f s a) (hg : continuous_within_at g s a) (h₀ : g a ≠ 0) : continuous_within_at (f / g) s a :=
  filter.tendsto.div hf hg h₀

theorem continuous_on.div {α : Type u_1} {G₀ : Type u_2} [group_with_zero G₀] [topological_space G₀] [has_continuous_inv' G₀] [has_continuous_mul G₀] {f : α → G₀} {g : α → G₀} [topological_space α] {s : set α} (hf : continuous_on f s) (hg : continuous_on g s) (h₀ : ∀ (x : α), x ∈ s → g x ≠ 0) : continuous_on (f / g) s :=
  fun (x : α) (hx : x ∈ s) => continuous_within_at.div (hf x hx) (hg x hx) (h₀ x hx)

/-- Continuity at a point of the result of dividing two functions continuous at that point, where
the denominator is nonzero. -/
theorem continuous_at.div {α : Type u_1} {G₀ : Type u_2} [group_with_zero G₀] [topological_space G₀] [has_continuous_inv' G₀] [has_continuous_mul G₀] {f : α → G₀} {g : α → G₀} [topological_space α] {a : α} (hf : continuous_at f a) (hg : continuous_at g a) (h₀ : g a ≠ 0) : continuous_at (f / g) a :=
  filter.tendsto.div hf hg h₀

theorem continuous.div {α : Type u_1} {G₀ : Type u_2} [group_with_zero G₀] [topological_space G₀] [has_continuous_inv' G₀] [has_continuous_mul G₀] {f : α → G₀} {g : α → G₀} [topological_space α] (hf : continuous f) (hg : continuous g) (h₀ : ∀ (x : α), g x ≠ 0) : continuous (f / g) :=
  eq.mpr
    (id ((fun (f f_1 : α → G₀) (e_3 : f = f_1) => congr_arg continuous e_3) (f / g) (f * (g⁻¹)) (div_eq_mul_inv f g)))
    (eq.mp (Eq.refl (continuous fun (x : α) => f x * (g x⁻¹))) (continuous.mul hf (continuous.inv' hg h₀)))

theorem continuous_on_div {G₀ : Type u_2} [group_with_zero G₀] [topological_space G₀] [has_continuous_inv' G₀] [has_continuous_mul G₀] : continuous_on (fun (p : G₀ × G₀) => prod.fst p / prod.snd p) (set_of fun (p : G₀ × G₀) => prod.snd p ≠ 0) :=
  continuous_on.div continuous_on_fst continuous_on_snd fun (_x : G₀ × G₀) => id

