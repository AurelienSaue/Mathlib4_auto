/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Some proofs and docs came from `algebra/commute` (c) Neil Strickland
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.units
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Semiconjugate elements of a semigroup

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`semiconj_by a x y`), if `a * x = y * a`.
In this file we  provide operations on `semiconj_by _ _ _`.

In the names of these operations, we treat `a` as the “left” argument, and both `x` and `y` as
“right” arguments. This way most names in this file agree with the names of the corresponding lemmas
for `commute a b = semiconj_by a b b`. As a side effect, some lemmas have only `_right` version.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(h.pow_right 5).eq]` rather than just `rw [h.pow_right 5]`.

This file provides only basic operations (`mul_left`, `mul_right`, `inv_right` etc). Other
operations (`pow_right`, field inverse etc) are in the files that define corresponding notions.
-/

/-- `x` is semiconjugate to `y` by `a`, if `a * x = y * a`. -/
def add_semiconj_by {M : Type u} [Add M] (a : M) (x : M) (y : M)  :=
  a + x = y + a

namespace semiconj_by


/-- Equality behind `semiconj_by a x y`; useful for rewriting. -/
protected theorem eq {S : Type u} [Mul S] {a : S} {x : S} {y : S} (h : semiconj_by a x y) : a * x = y * a :=
  h

/-- If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x * x'` to `y * y'`. -/
@[simp] theorem Mathlib.add_semiconj_by.add_right {S : Type u} [add_semigroup S] {a : S} {x : S} {y : S} {x' : S} {y' : S} (h : add_semiconj_by a x y) (h' : add_semiconj_by a x' y') : add_semiconj_by a (x + x') (y + y') := sorry

/-- If both `a` and `b` semiconjugate `x` to `y`, then so does `a * b`. -/
theorem Mathlib.add_semiconj_by.add_left {S : Type u} [add_semigroup S] {a : S} {b : S} {x : S} {y : S} {z : S} (ha : add_semiconj_by a y z) (hb : add_semiconj_by b x y) : add_semiconj_by (a + b) x z := sorry

/-- Any element semiconjugates `1` to `1`. -/
@[simp] theorem one_right {M : Type u} [monoid M] (a : M) : semiconj_by a 1 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (semiconj_by a 1 1)) (equations._eqn_1 a 1 1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * 1 = 1 * a)) (mul_one a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a = 1 * a)) (one_mul a))) (Eq.refl a)))

/-- One semiconjugates any element to itself. -/
@[simp] theorem one_left {M : Type u} [monoid M] (x : M) : semiconj_by 1 x x :=
  Eq.symm (one_right x)

/-- If `a` semiconjugates a unit `x` to a unit `y`, then it semiconjugates `x⁻¹` to `y⁻¹`. -/
theorem Mathlib.add_semiconj_by.units_neg_right {M : Type u} [add_monoid M] {a : M} {x : add_units M} {y : add_units M} (h : add_semiconj_by a ↑x ↑y) : add_semiconj_by a ↑(-x) ↑(-y) := sorry

@[simp] theorem units_inv_right_iff {M : Type u} [monoid M] {a : M} {x : units M} {y : units M} : semiconj_by a ↑(x⁻¹) ↑(y⁻¹) ↔ semiconj_by a ↑x ↑y :=
  { mp := units_inv_right, mpr := units_inv_right }

/-- If a unit `a` semiconjugates `x` to `y`, then `a⁻¹` semiconjugates `y` to `x`. -/
theorem Mathlib.add_semiconj_by.units_neg_symm_left {M : Type u} [add_monoid M] {a : add_units M} {x : M} {y : M} (h : add_semiconj_by (↑a) x y) : add_semiconj_by (↑(-a)) y x := sorry

@[simp] theorem Mathlib.add_semiconj_by.units_neg_symm_left_iff {M : Type u} [add_monoid M] {a : add_units M} {x : M} {y : M} : add_semiconj_by (↑(-a)) y x ↔ add_semiconj_by (↑a) x y :=
  { mp := add_semiconj_by.units_neg_symm_left, mpr := add_semiconj_by.units_neg_symm_left }

theorem Mathlib.add_semiconj_by.units_coe {M : Type u} [add_monoid M] {a : add_units M} {x : add_units M} {y : add_units M} (h : add_semiconj_by a x y) : add_semiconj_by ↑a ↑x ↑y :=
  congr_arg add_units.val h

theorem units_of_coe {M : Type u} [monoid M] {a : units M} {x : units M} {y : units M} (h : semiconj_by ↑a ↑x ↑y) : semiconj_by a x y :=
  units.ext h

@[simp] theorem units_coe_iff {M : Type u} [monoid M] {a : units M} {x : units M} {y : units M} : semiconj_by ↑a ↑x ↑y ↔ semiconj_by a x y :=
  { mp := units_of_coe, mpr := units_coe }

@[simp] theorem inv_right_iff {G : Type u} [group G] {a : G} {x : G} {y : G} : semiconj_by a (x⁻¹) (y⁻¹) ↔ semiconj_by a x y :=
  units_inv_right_iff

theorem Mathlib.add_semiconj_by.neg_right {G : Type u} [add_group G] {a : G} {x : G} {y : G} : add_semiconj_by a x y → add_semiconj_by a (-x) (-y) :=
  iff.mpr add_semiconj_by.neg_right_iff

@[simp] theorem inv_symm_left_iff {G : Type u} [group G] {a : G} {x : G} {y : G} : semiconj_by (a⁻¹) y x ↔ semiconj_by a x y :=
  units_inv_symm_left_iff

theorem Mathlib.add_semiconj_by.neg_symm_left {G : Type u} [add_group G] {a : G} {x : G} {y : G} : add_semiconj_by a x y → add_semiconj_by (-a) y x :=
  iff.mpr add_semiconj_by.neg_symm_left_iff

theorem Mathlib.add_semiconj_by.neg_neg_symm {G : Type u} [add_group G] {a : G} {x : G} {y : G} (h : add_semiconj_by a x y) : add_semiconj_by (-a) (-y) (-x) :=
  add_semiconj_by.neg_symm_left (add_semiconj_by.neg_right h)

-- this is not a simp lemma because it can be deduced from other simp lemmas

theorem inv_inv_symm_iff {G : Type u} [group G] {a : G} {x : G} {y : G} : semiconj_by (a⁻¹) (y⁻¹) (x⁻¹) ↔ semiconj_by a x y :=
  iff.trans inv_right_iff inv_symm_left_iff

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
theorem conj_mk {G : Type u} [group G] (a : G) (x : G) : semiconj_by a x (a * x * (a⁻¹)) := sorry

end semiconj_by


/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
theorem add_units.mk_semiconj_by {M : Type u} [add_monoid M] (u : add_units M) (x : M) : add_semiconj_by (↑u) x (↑u + x + ↑(-u)) :=
  eq.mpr (id (add_semiconj_by.equations._eqn_1 (↑u) x (↑u + x + ↑(-u))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑u + x = ↑u + x + ↑(-u) + ↑u)) (add_units.neg_add_cancel_right (↑u + x) u)))
      (Eq.refl (↑u + x)))

