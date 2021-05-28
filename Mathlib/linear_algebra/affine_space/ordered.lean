/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.affine_space.midpoint
import Mathlib.algebra.module.ordered
import Mathlib.tactic.field_simp
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Ordered modules as affine spaces

In this file we define the slope of a function `f : k → PE` taking values in an affine space over
`k` and prove some theorems about `slope` and `line_map` in the case when `PE` is an ordered
semimodule over `k`. The `slope` function naturally appears in the Mean Value Theorem, and in the
proof of the fact that a function with nonnegative second derivative on an interval is convex on
this interval. In the third part of this file we prove inequalities that will be used in
`analysis.convex.basic` to link convexity of a function on an interval to monotonicity of the slope,
see section docstring below for details.

## Implementation notes

We do not introduce the notion of ordered affine spaces (yet?). Instead, we prove various theorems
for an ordered semimodule interpreted as an affine space.

## Tags

affine space, ordered semimodule, slope
-/

/-!
### Definition of `slope` and basic properties

In this section we define `slope f a b` and prove some properties that do not require order on the
codomain.  -/

/-- `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` is the slope of a function `f` on the interval
`[a, b]`. Note that `slope f a a = 0`, not the derivative of `f` at `a`. -/
def slope {k : Type u_1} {E : Type u_2} {PE : Type u_3} [field k] [add_comm_group E] [semimodule k E] [add_torsor E PE] (f : k → PE) (a : k) (b : k) : E :=
  b - a⁻¹ • (f b -ᵥ f a)

theorem slope_def_field {k : Type u_1} [field k] (f : k → k) (a : k) (b : k) : slope f a b = (f b - f a) / (b - a) :=
  Eq.symm div_eq_inv_mul

@[simp] theorem slope_same {k : Type u_1} {E : Type u_2} {PE : Type u_3} [field k] [add_comm_group E] [semimodule k E] [add_torsor E PE] (f : k → PE) (a : k) : slope f a a = 0 := sorry

theorem eq_of_slope_eq_zero {k : Type u_1} {E : Type u_2} {PE : Type u_3} [field k] [add_comm_group E] [semimodule k E] [add_torsor E PE] {f : k → PE} {a : k} {b : k} (h : slope f a b = 0) : f a = f b := sorry

theorem slope_comm {k : Type u_1} {E : Type u_2} {PE : Type u_3} [field k] [add_comm_group E] [semimodule k E] [add_torsor E PE] (f : k → PE) (a : k) (b : k) : slope f a b = slope f b a := sorry

/-- `slope f a c` is a linear combination of `slope f a b` and `slope f b c`. This version
explicitly provides coefficients. If `a ≠ c`, then the sum of the coefficients is `1`, so it is
actually an affine combination, see `line_map_slope_slope_sub_div_sub`. -/
theorem sub_div_sub_smul_slope_add_sub_div_sub_smul_slope {k : Type u_1} {E : Type u_2} {PE : Type u_3} [field k] [add_comm_group E] [semimodule k E] [add_torsor E PE] (f : k → PE) (a : k) (b : k) (c : k) : ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slope f a c := sorry

/-- `slope f a c` is an affine combination of `slope f a b` and `slope f b c`. This version uses
`line_map` to express this property. -/
theorem line_map_slope_slope_sub_div_sub {k : Type u_1} {E : Type u_2} {PE : Type u_3} [field k] [add_comm_group E] [semimodule k E] [add_torsor E PE] (f : k → PE) (a : k) (b : k) (c : k) (h : a ≠ c) : coe_fn (affine_map.line_map (slope f a b) (slope f b c)) ((c - b) / (c - a)) = slope f a c := sorry

/-- `slope f a b` is an affine combination of `slope f a (line_map a b r)` and
`slope f (line_map a b r) b`. We use `line_map` to express this property. -/
theorem line_map_slope_line_map_slope_line_map {k : Type u_1} {E : Type u_2} {PE : Type u_3} [field k] [add_comm_group E] [semimodule k E] [add_torsor E PE] (f : k → PE) (a : k) (b : k) (r : k) : coe_fn
    (affine_map.line_map (slope f (coe_fn (affine_map.line_map a b) r) b)
      (slope f a (coe_fn (affine_map.line_map a b) r)))
    r =
  slope f a b := sorry

/-!
### Monotonicity of `line_map`

In this section we prove that `line_map a b r` is monotone (strictly or not) in its arguments if
other arguments belong to specific domains.
-/

theorem line_map_mono_left {k : Type u_1} {E : Type u_2} [ordered_ring k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {a' : E} {b : E} {r : k} (ha : a ≤ a') (hr : r ≤ 1) : coe_fn (affine_map.line_map a b) r ≤ coe_fn (affine_map.line_map a' b) r := sorry

theorem line_map_strict_mono_left {k : Type u_1} {E : Type u_2} [ordered_ring k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {a' : E} {b : E} {r : k} (ha : a < a') (hr : r < 1) : coe_fn (affine_map.line_map a b) r < coe_fn (affine_map.line_map a' b) r := sorry

theorem line_map_mono_right {k : Type u_1} {E : Type u_2} [ordered_ring k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {b' : E} {r : k} (hb : b ≤ b') (hr : 0 ≤ r) : coe_fn (affine_map.line_map a b) r ≤ coe_fn (affine_map.line_map a b') r := sorry

theorem line_map_strict_mono_right {k : Type u_1} {E : Type u_2} [ordered_ring k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {b' : E} {r : k} (hb : b < b') (hr : 0 < r) : coe_fn (affine_map.line_map a b) r < coe_fn (affine_map.line_map a b') r := sorry

theorem line_map_mono_endpoints {k : Type u_1} {E : Type u_2} [ordered_ring k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {a' : E} {b : E} {b' : E} {r : k} (ha : a ≤ a') (hb : b ≤ b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) : coe_fn (affine_map.line_map a b) r ≤ coe_fn (affine_map.line_map a' b') r :=
  has_le.le.trans (line_map_mono_left ha h₁) (line_map_mono_right hb h₀)

theorem line_map_strict_mono_endpoints {k : Type u_1} {E : Type u_2} [ordered_ring k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {a' : E} {b : E} {b' : E} {r : k} (ha : a < a') (hb : b < b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) : coe_fn (affine_map.line_map a b) r < coe_fn (affine_map.line_map a' b') r := sorry

theorem line_map_lt_line_map_iff_of_lt {k : Type u_1} {E : Type u_2} [ordered_ring k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {r : k} {r' : k} (h : r < r') : coe_fn (affine_map.line_map a b) r < coe_fn (affine_map.line_map a b) r' ↔ a < b := sorry

theorem left_lt_line_map_iff_lt {k : Type u_1} {E : Type u_2} [ordered_ring k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {r : k} (h : 0 < r) : a < coe_fn (affine_map.line_map a b) r ↔ a < b := sorry

theorem line_map_lt_left_iff_lt {k : Type u_1} {E : Type u_2} [ordered_ring k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {r : k} (h : 0 < r) : coe_fn (affine_map.line_map a b) r < a ↔ b < a :=
  left_lt_line_map_iff_lt h

theorem line_map_lt_right_iff_lt {k : Type u_1} {E : Type u_2} [ordered_ring k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {r : k} (h : r < 1) : coe_fn (affine_map.line_map a b) r < b ↔ a < b := sorry

theorem right_lt_line_map_iff_lt {k : Type u_1} {E : Type u_2} [ordered_ring k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {r : k} (h : r < 1) : b < coe_fn (affine_map.line_map a b) r ↔ b < a :=
  line_map_lt_right_iff_lt h

theorem line_map_le_line_map_iff_of_lt {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {r : k} {r' : k} (h : r < r') : coe_fn (affine_map.line_map a b) r ≤ coe_fn (affine_map.line_map a b) r' ↔ a ≤ b := sorry

theorem left_le_line_map_iff_le {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {r : k} (h : 0 < r) : a ≤ coe_fn (affine_map.line_map a b) r ↔ a ≤ b := sorry

@[simp] theorem left_le_midpoint {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} : a ≤ midpoint k a b ↔ a ≤ b :=
  left_le_line_map_iff_le (iff.mpr inv_pos zero_lt_two)

theorem line_map_le_left_iff_le {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {r : k} (h : 0 < r) : coe_fn (affine_map.line_map a b) r ≤ a ↔ b ≤ a :=
  left_le_line_map_iff_le h

@[simp] theorem midpoint_le_left {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} : midpoint k a b ≤ a ↔ b ≤ a :=
  line_map_le_left_iff_le (iff.mpr inv_pos zero_lt_two)

theorem line_map_le_right_iff_le {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {r : k} (h : r < 1) : coe_fn (affine_map.line_map a b) r ≤ b ↔ a ≤ b := sorry

@[simp] theorem midpoint_le_right {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} : midpoint k a b ≤ b ↔ a ≤ b :=
  line_map_le_right_iff_le (inv_lt_one one_lt_two)

theorem right_le_line_map_iff_le {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} {r : k} (h : r < 1) : b ≤ coe_fn (affine_map.line_map a b) r ↔ b ≤ a :=
  line_map_le_right_iff_le h

@[simp] theorem right_le_midpoint {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {a : E} {b : E} : b ≤ midpoint k a b ↔ b ≤ a :=
  right_le_line_map_iff_le (inv_lt_one one_lt_two)

/-!
### Convexity and slope

Given an interval `[a, b]` and a point `c ∈ (a, b)`, `c = line_map a b r`, there are a few ways to
say that the point `(c, f c)` is above/below the segment `[(a, f a), (b, f b)]`:

* compare `f c` to `line_map (f a) (f b) r`;
* compare `slope f a c` to `slope `f a b`;
* compare `slope f c b` to `slope f a b`;
* compare `slope f a c` to `slope f c b`.

In this section we prove equivalence of these four approaches. In order to make the statements more
readable, we introduce local notation `c = line_map a b r`. Then we prove lemmas like

```
lemma map_le_line_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
  f c ≤ line_map (f a) (f b) r ↔ slope f a c ≤ slope f a b :=
```

For each inequality between `f c` and `line_map (f a) (f b) r` we provide 3 lemmas:

* `*_left` relates it to an inequality on `slope f a c` and `slope f a b`;
* `*_right` relates it to an inequality on `slope f a b` and `slope f c b`;
* no-suffix version relates it to an inequality on `slope f a c` and `slope f c b`.

Later these inequalities will be used in to restate `convex_on` in terms of monotonicity of the
slope.
-/

/-- Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f a b`. -/
theorem map_le_line_map_iff_slope_le_slope_left {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (h : 0 < r * (b - a)) : f (coe_fn (affine_map.line_map a b) r) ≤ coe_fn (affine_map.line_map (f a) (f b)) r ↔
  slope f a (coe_fn (affine_map.line_map a b) r) ≤ slope f a b := sorry

/-- Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f a c`. -/
theorem line_map_le_map_iff_slope_le_slope_left {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (h : 0 < r * (b - a)) : coe_fn (affine_map.line_map (f a) (f b)) r ≤ f (coe_fn (affine_map.line_map a b) r) ↔
  slope f a b ≤ slope f a (coe_fn (affine_map.line_map a b) r) :=
  map_le_line_map_iff_slope_le_slope_left h

/-- Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f a b`. -/
theorem map_lt_line_map_iff_slope_lt_slope_left {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (h : 0 < r * (b - a)) : f (coe_fn (affine_map.line_map a b) r) < coe_fn (affine_map.line_map (f a) (f b)) r ↔
  slope f a (coe_fn (affine_map.line_map a b) r) < slope f a b :=
  lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope_left h) (map_le_line_map_iff_slope_le_slope_left h)

/-- Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f a c`. -/
theorem line_map_lt_map_iff_slope_lt_slope_left {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (h : 0 < r * (b - a)) : coe_fn (affine_map.line_map (f a) (f b)) r < f (coe_fn (affine_map.line_map a b) r) ↔
  slope f a b < slope f a (coe_fn (affine_map.line_map a b) r) :=
  map_lt_line_map_iff_slope_lt_slope_left h

/-- Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f c b`. -/
theorem map_le_line_map_iff_slope_le_slope_right {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (h : 0 < (1 - r) * (b - a)) : f (coe_fn (affine_map.line_map a b) r) ≤ coe_fn (affine_map.line_map (f a) (f b)) r ↔
  slope f a b ≤ slope f (coe_fn (affine_map.line_map a b) r) b := sorry

/-- Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a b`. -/
theorem line_map_le_map_iff_slope_le_slope_right {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (h : 0 < (1 - r) * (b - a)) : coe_fn (affine_map.line_map (f a) (f b)) r ≤ f (coe_fn (affine_map.line_map a b) r) ↔
  slope f (coe_fn (affine_map.line_map a b) r) b ≤ slope f a b :=
  map_le_line_map_iff_slope_le_slope_right h

/-- Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f c b`. -/
theorem map_lt_line_map_iff_slope_lt_slope_right {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (h : 0 < (1 - r) * (b - a)) : f (coe_fn (affine_map.line_map a b) r) < coe_fn (affine_map.line_map (f a) (f b)) r ↔
  slope f a b < slope f (coe_fn (affine_map.line_map a b) r) b :=
  lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope_right h) (map_le_line_map_iff_slope_le_slope_right h)

/-- Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a b`. -/
theorem line_map_lt_map_iff_slope_lt_slope_right {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (h : 0 < (1 - r) * (b - a)) : coe_fn (affine_map.line_map (f a) (f b)) r < f (coe_fn (affine_map.line_map a b) r) ↔
  slope f (coe_fn (affine_map.line_map a b) r) b < slope f a b :=
  map_lt_line_map_iff_slope_lt_slope_right h

/-- Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f c b`. -/
theorem map_le_line_map_iff_slope_le_slope {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) : f (coe_fn (affine_map.line_map a b) r) ≤ coe_fn (affine_map.line_map (f a) (f b)) r ↔
  slope f a (coe_fn (affine_map.line_map a b) r) ≤ slope f (coe_fn (affine_map.line_map a b) r) b := sorry

/-- Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a c`. -/
theorem line_map_le_map_iff_slope_le_slope {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) : coe_fn (affine_map.line_map (f a) (f b)) r ≤ f (coe_fn (affine_map.line_map a b) r) ↔
  slope f (coe_fn (affine_map.line_map a b) r) b ≤ slope f a (coe_fn (affine_map.line_map a b) r) :=
  map_le_line_map_iff_slope_le_slope hab h₀ h₁

/-- Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f c b`. -/
theorem map_lt_line_map_iff_slope_lt_slope {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) : f (coe_fn (affine_map.line_map a b) r) < coe_fn (affine_map.line_map (f a) (f b)) r ↔
  slope f a (coe_fn (affine_map.line_map a b) r) < slope f (coe_fn (affine_map.line_map a b) r) b :=
  lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope hab h₀ h₁) (map_le_line_map_iff_slope_le_slope hab h₀ h₁)

/-- Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a c`. -/
theorem line_map_lt_map_iff_slope_lt_slope {k : Type u_1} {E : Type u_2} [linear_ordered_field k] [ordered_add_comm_group E] [semimodule k E] [ordered_semimodule k E] {f : k → E} {a : k} {b : k} {r : k} (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) : coe_fn (affine_map.line_map (f a) (f b)) r < f (coe_fn (affine_map.line_map a b) r) ↔
  slope f (coe_fn (affine_map.line_map a b) r) b < slope f a (coe_fn (affine_map.line_map a b) r) :=
  map_lt_line_map_iff_slope_lt_slope hab h₀ h₁

