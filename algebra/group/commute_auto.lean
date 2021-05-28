/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group.semiconj
import PostPort

universes u_1 

namespace Mathlib

/-!
# Commuting pairs of elements in monoids

We define the predicate `commute a b := a * b = b * a` and provide some operations on terms `(h :
commute a b)`. E.g., if `a`, `b`, and c are elements of a semiring, and that `hb : commute a b` and
`hc : commute a c`.  Then `hb.pow_left 5` proves `commute (a ^ 5) b` and `(hb.pow_right 2).add_right
(hb.mul_right hc)` proves `commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(hb.pow_left 5).eq]` rather than just `rw [hb.pow_left 5]`.

This file defines only a few operations (`mul_left`, `inv_right`, etc).  Other operations
(`pow_right`, field inverse etc) are in the files that define corresponding notions.

## Implementation details

Most of the proofs come from the properties of `semiconj_by`.
-/

/-- Two elements commute if `a * b = b * a`. -/
def commute {S : Type u_1} [Mul S] (a : S) (b : S)  :=
  semiconj_by a b b

namespace commute


/-- Equality behind `commute a b`; useful for rewriting. -/
protected theorem Mathlib.add_commute.eq {S : Type u_1} [Add S] {a : S} {b : S} (h : add_commute a b) : a + b = b + a :=
  h

/-- Any element commutes with itself. -/
@[simp] protected theorem refl {S : Type u_1} [Mul S] (a : S) : commute a a :=
  Eq.refl (a * a)

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
protected theorem Mathlib.add_commute.symm {S : Type u_1} [Add S] {a : S} {b : S} (h : add_commute a b) : add_commute b a :=
  Eq.symm h

protected theorem Mathlib.add_commute.symm_iff {S : Type u_1} [Add S] {a : S} {b : S} : add_commute a b ↔ add_commute b a :=
  { mp := add_commute.symm, mpr := add_commute.symm }

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[simp] theorem mul_right {S : Type u_1} [semigroup S] {a : S} {b : S} {c : S} (hab : commute a b) (hac : commute a c) : commute a (b * c) :=
  semiconj_by.mul_right hab hac

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[simp] theorem Mathlib.add_commute.add_left {S : Type u_1} [add_semigroup S] {a : S} {b : S} {c : S} (hac : add_commute a c) (hbc : add_commute b c) : add_commute (a + b) c :=
  add_semiconj_by.add_left hac hbc

protected theorem Mathlib.add_commute.right_comm {S : Type u_1} [add_semigroup S] {b : S} {c : S} (h : add_commute b c) (a : S) : a + b + c = a + c + b := sorry

protected theorem left_comm {S : Type u_1} [semigroup S] {a : S} {b : S} (h : commute a b) (c : S) : a * (b * c) = b * (a * c) := sorry

protected theorem Mathlib.add_commute.all {S : Type u_1} [add_comm_semigroup S] (a : S) (b : S) : add_commute a b :=
  add_comm a b

@[simp] theorem one_right {M : Type u_1} [monoid M] (a : M) : commute a 1 :=
  semiconj_by.one_right a

@[simp] theorem Mathlib.add_commute.zero_left {M : Type u_1} [add_monoid M] (a : M) : add_commute 0 a :=
  add_semiconj_by.zero_left a

theorem Mathlib.add_commute.units_neg_right {M : Type u_1} [add_monoid M] {a : M} {u : add_units M} : add_commute a ↑u → add_commute a ↑(-u) :=
  add_semiconj_by.units_neg_right

@[simp] theorem Mathlib.add_commute.units_neg_right_iff {M : Type u_1} [add_monoid M] {a : M} {u : add_units M} : add_commute a ↑(-u) ↔ add_commute a ↑u :=
  add_semiconj_by.units_neg_right_iff

theorem Mathlib.add_commute.units_neg_left {M : Type u_1} [add_monoid M] {u : add_units M} {a : M} : add_commute (↑u) a → add_commute (↑(-u)) a :=
  add_semiconj_by.units_neg_symm_left

@[simp] theorem Mathlib.add_commute.units_neg_left_iff {M : Type u_1} [add_monoid M] {u : add_units M} {a : M} : add_commute (↑(-u)) a ↔ add_commute (↑u) a :=
  add_semiconj_by.units_neg_symm_left_iff

theorem Mathlib.add_commute.units_coe {M : Type u_1} [add_monoid M] {u₁ : add_units M} {u₂ : add_units M} : add_commute u₁ u₂ → add_commute ↑u₁ ↑u₂ :=
  add_semiconj_by.units_coe

theorem Mathlib.add_commute.units_of_coe {M : Type u_1} [add_monoid M] {u₁ : add_units M} {u₂ : add_units M} : add_commute ↑u₁ ↑u₂ → add_commute u₁ u₂ :=
  add_semiconj_by.units_of_coe

@[simp] theorem units_coe_iff {M : Type u_1} [monoid M] {u₁ : units M} {u₂ : units M} : commute ↑u₁ ↑u₂ ↔ commute u₁ u₂ :=
  semiconj_by.units_coe_iff

theorem Mathlib.add_commute.neg_right {G : Type u_1} [add_group G] {a : G} {b : G} : add_commute a b → add_commute a (-b) :=
  add_semiconj_by.neg_right

@[simp] theorem Mathlib.add_commute.neg_right_iff {G : Type u_1} [add_group G] {a : G} {b : G} : add_commute a (-b) ↔ add_commute a b :=
  add_semiconj_by.neg_right_iff

theorem inv_left {G : Type u_1} [group G] {a : G} {b : G} : commute a b → commute (a⁻¹) b :=
  semiconj_by.inv_symm_left

@[simp] theorem inv_left_iff {G : Type u_1} [group G] {a : G} {b : G} : commute (a⁻¹) b ↔ commute a b :=
  semiconj_by.inv_symm_left_iff

theorem Mathlib.add_commute.neg_neg {G : Type u_1} [add_group G] {a : G} {b : G} : add_commute a b → add_commute (-a) (-b) :=
  add_semiconj_by.neg_neg_symm

@[simp] theorem inv_inv_iff {G : Type u_1} [group G] {a : G} {b : G} : commute (a⁻¹) (b⁻¹) ↔ commute a b :=
  semiconj_by.inv_inv_symm_iff

protected theorem Mathlib.add_commute.neg_add_cancel {G : Type u_1} [add_group G] {a : G} {b : G} (h : add_commute a b) : -a + b + a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-a + b + a = b)) (add_commute.eq (add_commute.neg_left h))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b + -a + a = b)) (neg_add_cancel_right b a))) (Eq.refl b))

theorem inv_mul_cancel_assoc {G : Type u_1} [group G] {a : G} {b : G} (h : commute a b) : a⁻¹ * (b * a) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ * (b * a) = b)) (Eq.symm (mul_assoc (a⁻¹) b a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ * b * a = b)) (commute.inv_mul_cancel h))) (Eq.refl b))

protected theorem mul_inv_cancel {G : Type u_1} [group G] {a : G} {b : G} (h : commute a b) : a * b * (a⁻¹) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b * (a⁻¹) = b)) (commute.eq h)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a * (a⁻¹) = b)) (mul_inv_cancel_right b a))) (Eq.refl b))

theorem mul_inv_cancel_assoc {G : Type u_1} [group G] {a : G} {b : G} (h : commute a b) : a * (b * (a⁻¹)) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (b * (a⁻¹)) = b)) (Eq.symm (mul_assoc a b (a⁻¹)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * b * (a⁻¹) = b)) (commute.mul_inv_cancel h))) (Eq.refl b))

end commute


@[simp] theorem mul_inv_cancel_comm {G : Type u_1} [comm_group G] (a : G) (b : G) : a * b * (a⁻¹) = b :=
  commute.mul_inv_cancel (commute.all a b)

@[simp] theorem add_neg_cancel_comm_assoc {G : Type u_1} [add_comm_group G] (a : G) (b : G) : a + (b + -a) = b :=
  add_commute.add_neg_cancel_assoc (add_commute.all a b)

@[simp] theorem inv_mul_cancel_comm {G : Type u_1} [comm_group G] (a : G) (b : G) : a⁻¹ * b * a = b :=
  commute.inv_mul_cancel (commute.all a b)

@[simp] theorem inv_mul_cancel_comm_assoc {G : Type u_1} [comm_group G] (a : G) (b : G) : a⁻¹ * (b * a) = b :=
  commute.inv_mul_cancel_assoc (commute.all a b)

