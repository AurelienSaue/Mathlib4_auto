/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.invertible
import Mathlib.linear_algebra.affine_space.affine_equiv
import Mathlib.PostPort

universes u_1 u_2 u_4 u_3 u_5 

namespace Mathlib

/-!
# Midpoint of a segment

## Main definitions

* `midpoint R x y`: midpoint of the segment `[x, y]`. We define it for `x` and `y`
  in a module over a ring `R` with invertible `2`.
* `add_monoid_hom.of_map_midpoint`: construct an `add_monoid_hom` given a map `f` such that
  `f` sends zero to zero and midpoints to midpoints.

## Main theorems

* `midpoint_eq_iff`: `z` is the midpoint of `[x, y]` if and only if `x + y = z + z`,
* `midpoint_unique`: `midpoint R x y` does not depend on `R`;
* `midpoint x y` is linear both in `x` and `y`;
* `point_reflection_midpoint_left`, `point_reflection_midpoint_right`:
  `equiv.point_reflection (midpoint R x y)` swaps `x` and `y`.

We do not mark most lemmas as `@[simp]` because it is hard to tell which side is simpler.

## Tags

midpoint, add_monoid_hom
-/

/-- `midpoint x y` is the midpoint of the segment `[x, y]`. -/
def midpoint (R : Type u_1) {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (x : P) (y : P) : P :=
  coe_fn (affine_map.line_map x y) ⅟

@[simp] theorem affine_map.map_midpoint {R : Type u_1} {V : Type u_2} {V' : Type u_3} {P : Type u_4} {P' : Type u_5} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] [add_comm_group V'] [semimodule R V'] [add_torsor V' P'] (f : affine_map R P P') (a : P) (b : P) : coe_fn f (midpoint R a b) = midpoint R (coe_fn f a) (coe_fn f b) :=
  affine_map.apply_line_map f a b ⅟

@[simp] theorem affine_equiv.map_midpoint {R : Type u_1} {V : Type u_2} {V' : Type u_3} {P : Type u_4} {P' : Type u_5} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] [add_comm_group V'] [semimodule R V'] [add_torsor V' P'] (f : affine_equiv R P P') (a : P) (b : P) : coe_fn f (midpoint R a b) = midpoint R (coe_fn f a) (coe_fn f b) :=
  affine_equiv.apply_line_map f a b ⅟

@[simp] theorem affine_equiv.point_reflection_midpoint_left {R : Type u_1} {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (x : P) (y : P) : coe_fn (affine_equiv.point_reflection R (midpoint R x y)) x = y := sorry

theorem midpoint_comm {R : Type u_1} {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (x : P) (y : P) : midpoint R x y = midpoint R y x := sorry

@[simp] theorem affine_equiv.point_reflection_midpoint_right {R : Type u_1} {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (x : P) (y : P) : coe_fn (affine_equiv.point_reflection R (midpoint R x y)) y = x := sorry

theorem midpoint_vsub_midpoint {R : Type u_1} {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P) : midpoint R p₁ p₂ -ᵥ midpoint R p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) :=
  affine_map.line_map_vsub_line_map p₁ p₂ p₃ p₄ ⅟

theorem midpoint_vadd_midpoint {R : Type u_1} {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (v : V) (v' : V) (p : P) (p' : P) : midpoint R v v' +ᵥ midpoint R p p' = midpoint R (v +ᵥ p) (v' +ᵥ p') :=
  affine_map.line_map_vadd_line_map v v' p p' ⅟

theorem midpoint_eq_iff {R : Type u_1} {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] {x : P} {y : P} {z : P} : midpoint R x y = z ↔ coe_fn (affine_equiv.point_reflection R z) x = y := sorry

@[simp] theorem midpoint_vsub_left {R : Type u_1} {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (p₁ : P) (p₂ : P) : midpoint R p₁ p₂ -ᵥ p₁ = ⅟ • (p₂ -ᵥ p₁) :=
  affine_map.line_map_vsub_left p₁ p₂ ⅟

@[simp] theorem midpoint_vsub_right {R : Type u_1} {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (p₁ : P) (p₂ : P) : midpoint R p₁ p₂ -ᵥ p₂ = ⅟ • (p₁ -ᵥ p₂) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (midpoint R p₁ p₂ -ᵥ p₂ = ⅟ • (p₁ -ᵥ p₂))) (midpoint_comm p₁ p₂)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (midpoint R p₂ p₁ -ᵥ p₂ = ⅟ • (p₁ -ᵥ p₂))) (midpoint_vsub_left p₂ p₁)))
      (Eq.refl (⅟ • (p₁ -ᵥ p₂))))

@[simp] theorem left_vsub_midpoint {R : Type u_1} {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (p₁ : P) (p₂ : P) : p₁ -ᵥ midpoint R p₁ p₂ = ⅟ • (p₁ -ᵥ p₂) :=
  affine_map.left_vsub_line_map p₁ p₂ ⅟

@[simp] theorem right_vsub_midpoint {R : Type u_1} {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (p₁ : P) (p₂ : P) : p₂ -ᵥ midpoint R p₁ p₂ = ⅟ • (p₂ -ᵥ p₁) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (p₂ -ᵥ midpoint R p₁ p₂ = ⅟ • (p₂ -ᵥ p₁))) (midpoint_comm p₁ p₂)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (p₂ -ᵥ midpoint R p₂ p₁ = ⅟ • (p₂ -ᵥ p₁))) (left_vsub_midpoint p₂ p₁)))
      (Eq.refl (⅟ • (p₂ -ᵥ p₁))))

@[simp] theorem midpoint_sub_left {R : Type u_1} {V : Type u_2} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] (v₁ : V) (v₂ : V) : midpoint R v₁ v₂ - v₁ = ⅟ • (v₂ - v₁) :=
  midpoint_vsub_left v₁ v₂

@[simp] theorem midpoint_sub_right {R : Type u_1} {V : Type u_2} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] (v₁ : V) (v₂ : V) : midpoint R v₁ v₂ - v₂ = ⅟ • (v₁ - v₂) :=
  midpoint_vsub_right v₁ v₂

@[simp] theorem left_sub_midpoint {R : Type u_1} {V : Type u_2} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] (v₁ : V) (v₂ : V) : v₁ - midpoint R v₁ v₂ = ⅟ • (v₁ - v₂) :=
  left_vsub_midpoint v₁ v₂

@[simp] theorem right_sub_midpoint {R : Type u_1} {V : Type u_2} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] (v₁ : V) (v₂ : V) : v₂ - midpoint R v₁ v₂ = ⅟ • (v₂ - v₁) :=
  right_vsub_midpoint v₁ v₂

theorem midpoint_eq_midpoint_iff_vsub_eq_vsub (R : Type u_1) {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] {x : P} {x' : P} {y : P} {y' : P} : midpoint R x y = midpoint R x' y' ↔ x -ᵥ x' = y' -ᵥ y := sorry

theorem midpoint_eq_iff' (R : Type u_1) {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] {x : P} {y : P} {z : P} : midpoint R x y = z ↔ coe_fn (equiv.point_reflection z) x = y :=
  midpoint_eq_iff

/-- `midpoint` does not depend on the ring `R`. -/
theorem midpoint_unique (R : Type u_1) {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (R' : Type u_3) [ring R'] [invertible (bit0 1)] [semimodule R' V] (x : P) (y : P) : midpoint R x y = midpoint R' x y :=
  iff.mpr (midpoint_eq_iff' R) (iff.mp (midpoint_eq_iff' R') rfl)

@[simp] theorem midpoint_self (R : Type u_1) {V : Type u_2} {P : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (x : P) : midpoint R x x = x :=
  affine_map.line_map_same_apply x ⅟

@[simp] theorem midpoint_add_self (R : Type u_1) {V : Type u_2} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] (x : V) (y : V) : midpoint R x y + midpoint R x y = x + y := sorry

theorem midpoint_zero_add (R : Type u_1) {V : Type u_2} [ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] (x : V) (y : V) : midpoint R 0 (x + y) = midpoint R x y := sorry

theorem line_map_inv_two {R : Type u_1} {V : Type u_2} {P : Type u_3} [division_ring R] [char_zero R] [add_comm_group V] [semimodule R V] [add_torsor V P] (a : P) (b : P) : coe_fn (affine_map.line_map a b) (bit0 1⁻¹) = midpoint R a b :=
  rfl

theorem line_map_one_half {R : Type u_1} {V : Type u_2} {P : Type u_3} [division_ring R] [char_zero R] [add_comm_group V] [semimodule R V] [add_torsor V P] (a : P) (b : P) : coe_fn (affine_map.line_map a b) (1 / bit0 1) = midpoint R a b := sorry

theorem homothety_inv_of_two {R : Type u_1} {V : Type u_2} {P : Type u_3} [comm_ring R] [invertible (bit0 1)] [add_comm_group V] [semimodule R V] [add_torsor V P] (a : P) (b : P) : coe_fn (affine_map.homothety a ⅟) b = midpoint R a b :=
  rfl

theorem homothety_inv_two {k : Type u_1} {V : Type u_2} {P : Type u_3} [field k] [char_zero k] [add_comm_group V] [semimodule k V] [add_torsor V P] (a : P) (b : P) : coe_fn (affine_map.homothety a (bit0 1⁻¹)) b = midpoint k a b :=
  rfl

theorem homothety_one_half {k : Type u_1} {V : Type u_2} {P : Type u_3} [field k] [char_zero k] [add_comm_group V] [semimodule k V] [add_torsor V P] (a : P) (b : P) : coe_fn (affine_map.homothety a (1 / bit0 1)) b = midpoint k a b := sorry

@[simp] theorem pi_midpoint_apply {k : Type u_1} {ι : Type u_2} {V : ι → Type u_3} {P : ι → Type u_4} [field k] [invertible (bit0 1)] [(i : ι) → add_comm_group (V i)] [(i : ι) → semimodule k (V i)] [(i : ι) → add_torsor (V i) (P i)] (f : (i : ι) → P i) (g : (i : ι) → P i) (i : ι) : midpoint k f g i = midpoint k (f i) (g i) :=
  rfl

namespace add_monoid_hom


/-- A map `f : E → F` sending zero to zero and midpoints to midpoints is an `add_monoid_hom`. -/
def of_map_midpoint (R : Type u_1) (R' : Type u_2) {E : Type u_3} {F : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group E] [semimodule R E] [ring R'] [invertible (bit0 1)] [add_comm_group F] [semimodule R' F] (f : E → F) (h0 : f 0 = 0) (hm : ∀ (x y : E), f (midpoint R x y) = midpoint R' (f x) (f y)) : E →+ F :=
  mk f h0 sorry

@[simp] theorem coe_of_map_midpoint (R : Type u_1) (R' : Type u_2) {E : Type u_3} {F : Type u_4} [ring R] [invertible (bit0 1)] [add_comm_group E] [semimodule R E] [ring R'] [invertible (bit0 1)] [add_comm_group F] [semimodule R' F] (f : E → F) (h0 : f 0 = 0) (hm : ∀ (x y : E), f (midpoint R x y) = midpoint R' (f x) (f y)) : ⇑(of_map_midpoint R R' f h0 hm) = f :=
  rfl

