/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group.prod
import Mathlib.algebra.group.type_tags
import Mathlib.algebra.group.pi
import Mathlib.algebra.pointwise
import Mathlib.data.equiv.basic
import Mathlib.data.set.finite
import PostPort

universes u_1 u_2 l u_3 u_4 u v w 

namespace Mathlib

/-!
# Torsors of additive group actions

This file defines torsors of additive group actions.

## Notations

The group elements are referred to as acting on points.  This file
defines the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element.

## Implementation notes

Affine spaces are the motivating example of torsors of additive group actions. It may be appropriate
to refactor in terms of the general definition of group actions, via `to_additive`, when there is a
use for multiplicative torsors (currently mathlib only develops the theory of group actions for
multiplicative group actions).

## Notations

* `v +ᵥ p` is a notation for `has_vadd.vadd`, the left action of an additive monoid;

* `p₁ -ᵥ p₂` is a notation for `has_vsub.vsub`, difference between two points in an additive torsor
  as an element of the corresponding additive group;

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/

/-- Type class for the `+ᵥ` notation. -/
class has_vadd (G : Type u_1) (P : Type u_2) 
where
  vadd : G → P → P

/-- Type class for the `-ᵥ` notation. -/
class has_vsub (G : outParam (Type u_1)) (P : Type u_2) 
where
  vsub : P → P → G

infixl:65 " +ᵥ " => Mathlib.has_vadd.vadd

infixl:65 " -ᵥ " => Mathlib.has_vsub.vsub

/-- Type class for additive monoid actions. -/
class add_action (G : Type u_1) (P : Type u_2) [add_monoid G] 
extends has_vadd G P
where
  zero_vadd' : ∀ (p : P), 0 +ᵥ p = p
  vadd_assoc' : ∀ (g1 g2 : G) (p : P), g1 +ᵥ (g2 +ᵥ p) = g1 + g2 +ᵥ p

/-- An `add_torsor G P` gives a structure to the nonempty type `P`,
acted on by an `add_group G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space. -/
class add_torsor (G : outParam (Type u_1)) (P : Type u_2) [outParam (add_group G)] 
extends has_vsub G P, add_action G P
where
  nonempty : Nonempty P
  vsub_vadd' : ∀ (p1 p2 : P), p1 -ᵥ p2 +ᵥ p2 = p1
  vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g

/-- An `add_group G` is a torsor for itself. -/
protected instance add_group_is_add_torsor (G : Type u_1) [add_group G] : add_torsor G G :=
  add_torsor.mk Add.add sorry sorry Sub.sub sub_add_cancel add_sub_cancel

/-- Simplify addition for a torsor for an `add_group G` over
itself. -/
@[simp] theorem vadd_eq_add {G : Type u_1} [add_group G] (g1 : G) (g2 : G) : g1 +ᵥ g2 = g1 + g2 :=
  rfl

/-- Simplify subtraction for a torsor for an `add_group G` over
itself. -/
@[simp] theorem vsub_eq_sub {G : Type u_1} [add_group G] (g1 : G) (g2 : G) : g1 -ᵥ g2 = g1 - g2 :=
  rfl

/-- Adding the zero group element to a point gives the same point. -/
@[simp] theorem zero_vadd (G : Type u_1) {P : Type u_2} [add_monoid G] [A : add_action G P] (p : P) : 0 +ᵥ p = p :=
  add_action.zero_vadd' p

/-- Adding two group elements to a point produces the same result as
adding their sum. -/
theorem vadd_assoc {G : Type u_1} {P : Type u_2} [add_monoid G] [A : add_action G P] (g1 : G) (g2 : G) (p : P) : g1 +ᵥ (g2 +ᵥ p) = g1 + g2 +ᵥ p :=
  add_action.vadd_assoc' g1 g2 p

/-- Adding two group elements to a point produces the same result in either
order. -/
theorem vadd_comm (G : Type u_1) {P : Type u_2} [add_comm_monoid G] [A : add_action G P] (p : P) (g1 : G) (g2 : G) : g1 +ᵥ (g2 +ᵥ p) = g2 +ᵥ (g1 +ᵥ p) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (g1 +ᵥ (g2 +ᵥ p) = g2 +ᵥ (g1 +ᵥ p))) (vadd_assoc g1 g2 p)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (g1 + g2 +ᵥ p = g2 +ᵥ (g1 +ᵥ p))) (vadd_assoc g2 g1 p)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (g1 + g2 +ᵥ p = g2 + g1 +ᵥ p)) (add_comm g1 g2))) (Eq.refl (g2 + g1 +ᵥ p))))

/-- If the same group element added to two points produces equal results,
those points are equal. -/
theorem vadd_left_cancel {G : Type u_1} {P : Type u_2} [add_group G] [A : add_action G P] {p1 : P} {p2 : P} (g : G) (h : g +ᵥ p1 = g +ᵥ p2) : p1 = p2 := sorry

@[simp] theorem vadd_left_cancel_iff {G : Type u_1} {P : Type u_2} [add_group G] [A : add_action G P] {p₁ : P} {p₂ : P} (g : G) : g +ᵥ p₁ = g +ᵥ p₂ ↔ p₁ = p₂ :=
  { mp := vadd_left_cancel g, mpr := fun (h : p₁ = p₂) => h ▸ rfl }

/-- Adding the group element `g` to a point is an injective function. -/
theorem vadd_left_injective {G : Type u_1} (P : Type u_2) [add_group G] [A : add_action G P] (g : G) : function.injective (has_vadd.vadd g) :=
  fun (p1 p2 : P) => vadd_left_cancel g

/-- Adding the result of subtracting from another point produces that
point. -/
@[simp] theorem vsub_vadd {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (p1 : P) (p2 : P) : p1 -ᵥ p2 +ᵥ p2 = p1 :=
  add_torsor.vsub_vadd' p1 p2

/-- Adding a group element then subtracting the original point
produces that group element. -/
@[simp] theorem vadd_vsub {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (g : G) (p : P) : g +ᵥ p -ᵥ p = g :=
  add_torsor.vadd_vsub' g p

/-- If the same point added to two group elements produces equal
results, those group elements are equal. -/
theorem vadd_right_cancel {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {g1 : G} {g2 : G} (p : P) (h : g1 +ᵥ p = g2 +ᵥ p) : g1 = g2 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (g1 = g2)) (Eq.symm (vadd_vsub g1 p))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (g1 +ᵥ p -ᵥ p = g2)) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (g2 +ᵥ p -ᵥ p = g2)) (vadd_vsub g2 p))) (Eq.refl g2)))

@[simp] theorem vadd_right_cancel_iff {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {g1 : G} {g2 : G} (p : P) : g1 +ᵥ p = g2 +ᵥ p ↔ g1 = g2 :=
  { mp := vadd_right_cancel p, mpr := fun (h : g1 = g2) => h ▸ rfl }

/-- Adding a group element to the point `p` is an injective
function. -/
theorem vadd_right_injective {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (p : P) : function.injective fun (_x : G) => _x +ᵥ p :=
  fun (g1 g2 : G) => vadd_right_cancel p

/-- Adding a group element to a point, then subtracting another point,
produces the same result as subtracting the points then adding the
group element. -/
theorem vadd_vsub_assoc {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (g : G) (p1 : P) (p2 : P) : g +ᵥ p1 -ᵥ p2 = g + (p1 -ᵥ p2) := sorry

/-- Subtracting a point from itself produces 0. -/
@[simp] theorem vsub_self {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (p : P) : p -ᵥ p = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (p -ᵥ p = 0)) (Eq.symm (zero_add (p -ᵥ p)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 + (p -ᵥ p) = 0)) (Eq.symm (vadd_vsub_assoc 0 p p))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 +ᵥ p -ᵥ p = 0)) (vadd_vsub 0 p))) (Eq.refl 0)))

/-- If subtracting two points produces 0, they are equal. -/
theorem eq_of_vsub_eq_zero {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {p1 : P} {p2 : P} (h : p1 -ᵥ p2 = 0) : p1 = p2 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (p1 = p2)) (Eq.symm (vsub_vadd p1 p2))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (p1 -ᵥ p2 +ᵥ p2 = p2)) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 +ᵥ p2 = p2)) (zero_vadd G p2))) (Eq.refl p2)))

/-- Subtracting two points produces 0 if and only if they are
equal. -/
@[simp] theorem vsub_eq_zero_iff_eq {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {p1 : P} {p2 : P} : p1 -ᵥ p2 = 0 ↔ p1 = p2 :=
  { mp := eq_of_vsub_eq_zero, mpr := fun (h : p1 = p2) => h ▸ vsub_self p1 }

/-- Cancellation adding the results of two subtractions. -/
@[simp] theorem vsub_add_vsub_cancel {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (p1 : P) (p2 : P) (p3 : P) : p1 -ᵥ p2 + (p2 -ᵥ p3) = p1 -ᵥ p3 := sorry

/-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/
@[simp] theorem neg_vsub_eq_vsub_rev {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (p1 : P) (p2 : P) : -(p1 -ᵥ p2) = p2 -ᵥ p1 := sorry

/-- Subtracting the result of adding a group element produces the same result
as subtracting the points and subtracting that group element. -/
theorem vsub_vadd_eq_vsub_sub {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (p1 : P) (p2 : P) (g : G) : p1 -ᵥ (g +ᵥ p2) = p1 -ᵥ p2 - g := sorry

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] theorem vsub_sub_vsub_cancel_right {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (p1 : P) (p2 : P) (p3 : P) : p1 -ᵥ p3 - (p2 -ᵥ p3) = p1 -ᵥ p2 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (p1 -ᵥ p3 - (p2 -ᵥ p3) = p1 -ᵥ p2)) (Eq.symm (vsub_vadd_eq_vsub_sub p1 p3 (p2 -ᵥ p3)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (p1 -ᵥ (p2 -ᵥ p3 +ᵥ p3) = p1 -ᵥ p2)) (vsub_vadd p2 p3))) (Eq.refl (p1 -ᵥ p2)))

/-- Convert between an equality with adding a group element to a point
and an equality of a subtraction of two points with a group
element. -/
theorem eq_vadd_iff_vsub_eq {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (p1 : P) (g : G) (p2 : P) : p1 = g +ᵥ p2 ↔ p1 -ᵥ p2 = g :=
  { mp := fun (h : p1 = g +ᵥ p2) => Eq.symm h ▸ vadd_vsub g p2,
    mpr := fun (h : p1 -ᵥ p2 = g) => h ▸ Eq.symm (vsub_vadd p1 p2) }

theorem vadd_eq_vadd_iff_neg_add_eq_vsub {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {v₁ : G} {v₂ : G} {p₁ : P} {p₂ : P} : v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ -v₁ + v₂ = p₁ -ᵥ p₂ := sorry

namespace set


protected instance has_vsub {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] : has_vsub (set G) (set P) :=
  has_vsub.mk (image2 has_vsub.vsub)

@[simp] theorem vsub_empty {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (s : set P) : s -ᵥ ∅ = ∅ :=
  image2_empty_right

@[simp] theorem empty_vsub {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (s : set P) : ∅ -ᵥ s = ∅ :=
  image2_empty_left

@[simp] theorem singleton_vsub {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (s : set P) (p : P) : singleton p -ᵥ s = has_vsub.vsub p '' s :=
  image2_singleton_left

@[simp] theorem vsub_singleton {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (s : set P) (p : P) : s -ᵥ singleton p = (fun (_x : P) => _x -ᵥ p) '' s :=
  image2_singleton_right

@[simp] theorem singleton_vsub_self {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (p : P) : singleton p -ᵥ singleton p = singleton 0 := sorry

/-- `vsub` of a finite set is finite. -/
theorem finite.vsub {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {s : set P} {t : set P} (hs : finite s) (ht : finite t) : finite (s -ᵥ t) :=
  finite.image2 (fun (a b : P) => a -ᵥ b) hs ht

/-- Each pairwise difference is in the `vsub` set. -/
theorem vsub_mem_vsub {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {s : set P} {t : set P} {ps : P} {pt : P} (hs : ps ∈ s) (ht : pt ∈ t) : ps -ᵥ pt ∈ s -ᵥ t :=
  mem_image2_of_mem hs ht

/-- `s -ᵥ t` is monotone in both arguments. -/
theorem vsub_subset_vsub {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {s : set P} {t : set P} {s' : set P} {t' : set P} (hs : s ⊆ s') (ht : t ⊆ t') : s -ᵥ t ⊆ s' -ᵥ t' :=
  image2_subset hs ht

theorem vsub_self_mono {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {s : set P} {t : set P} (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t :=
  vsub_subset_vsub h h

theorem vsub_subset_iff {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {s : set P} {t : set P} {u : set G} : s -ᵥ t ⊆ u ↔ ∀ (x : P), x ∈ s → ∀ (y : P), y ∈ t → x -ᵥ y ∈ u :=
  image2_subset_iff

protected instance add_action {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] : add_action (set G) (set P) :=
  add_action.mk (image2 has_vadd.vadd) sorry sorry

theorem vadd_subset_vadd {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {s : set G} {s' : set G} {t : set P} {t' : set P} (hs : s ⊆ s') (ht : t ⊆ t') : s +ᵥ t ⊆ s' +ᵥ t' :=
  image2_subset hs ht

@[simp] theorem vadd_singleton {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (s : set G) (p : P) : s +ᵥ singleton p = (fun (_x : G) => _x +ᵥ p) '' s :=
  image2_singleton_right

@[simp] theorem singleton_vadd {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (v : G) (s : set P) : singleton v +ᵥ s = has_vadd.vadd v '' s :=
  image2_singleton_left

theorem finite.vadd {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {s : set G} {t : set P} (hs : finite s) (ht : finite t) : finite (s +ᵥ t) :=
  finite.image2 (fun (a : G) (b : P) => a +ᵥ b) hs ht

end set


@[simp] theorem vadd_vsub_vadd_cancel_right {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (v₁ : G) (v₂ : G) (p : P) : v₁ +ᵥ p -ᵥ (v₂ +ᵥ p) = v₁ - v₂ := sorry

/-- If the same point subtracted from two points produces equal
results, those points are equal. -/
theorem vsub_left_cancel {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {p1 : P} {p2 : P} {p : P} (h : p1 -ᵥ p = p2 -ᵥ p) : p1 = p2 :=
  eq.mp (Eq._oldrec (Eq.refl (p1 -ᵥ p2 = 0)) (propext vsub_eq_zero_iff_eq))
    (eq.mp (Eq._oldrec (Eq.refl (p1 -ᵥ p - (p2 -ᵥ p) = 0)) (vsub_sub_vsub_cancel_right p1 p2 p))
      (eq.mp (Eq._oldrec (Eq.refl (p1 -ᵥ p = p2 -ᵥ p)) (Eq.symm (propext sub_eq_zero))) h))

/-- The same point subtracted from two points produces equal results
if and only if those points are equal. -/
@[simp] theorem vsub_left_cancel_iff {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {p1 : P} {p2 : P} {p : P} : p1 -ᵥ p = p2 -ᵥ p ↔ p1 = p2 :=
  { mp := vsub_left_cancel, mpr := fun (h : p1 = p2) => h ▸ rfl }

/-- Subtracting the point `p` is an injective function. -/
theorem vsub_left_injective {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (p : P) : function.injective fun (_x : P) => _x -ᵥ p :=
  fun (p2 p3 : P) => vsub_left_cancel

/-- If subtracting two points from the same point produces equal
results, those points are equal. -/
theorem vsub_right_cancel {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {p1 : P} {p2 : P} {p : P} (h : p -ᵥ p1 = p -ᵥ p2) : p1 = p2 := sorry

/-- Subtracting two points from the same point produces equal results
if and only if those points are equal. -/
@[simp] theorem vsub_right_cancel_iff {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] {p1 : P} {p2 : P} {p : P} : p -ᵥ p1 = p -ᵥ p2 ↔ p1 = p2 :=
  { mp := vsub_right_cancel, mpr := fun (h : p1 = p2) => h ▸ rfl }

/-- Subtracting a point from the point `p` is an injective
function. -/
theorem vsub_right_injective {G : Type u_1} {P : Type u_2} [add_group G] [T : add_torsor G P] (p : P) : function.injective (has_vsub.vsub p) :=
  fun (p2 p3 : P) => vsub_right_cancel

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] theorem vsub_sub_vsub_cancel_left {G : Type u_1} {P : Type u_2} [add_comm_group G] [add_torsor G P] (p1 : P) (p2 : P) (p3 : P) : p3 -ᵥ p2 - (p3 -ᵥ p1) = p1 -ᵥ p2 := sorry

@[simp] theorem vadd_vsub_vadd_cancel_left {G : Type u_1} {P : Type u_2} [add_comm_group G] [add_torsor G P] (v : G) (p1 : P) (p2 : P) : v +ᵥ p1 -ᵥ (v +ᵥ p2) = p1 -ᵥ p2 := sorry

theorem vsub_vadd_comm {G : Type u_1} {P : Type u_2} [add_comm_group G] [add_torsor G P] (p1 : P) (p2 : P) (p3 : P) : p1 -ᵥ p2 +ᵥ p3 = p3 -ᵥ p2 +ᵥ p1 := sorry

theorem vadd_eq_vadd_iff_sub_eq_vsub {G : Type u_1} {P : Type u_2} [add_comm_group G] [add_torsor G P] {v₁ : G} {v₂ : G} {p₁ : P} {p₂ : P} : v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ v₂ - v₁ = p₁ -ᵥ p₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ v₂ - v₁ = p₁ -ᵥ p₂)) (propext vadd_eq_vadd_iff_neg_add_eq_vsub)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-v₁ + v₂ = p₁ -ᵥ p₂ ↔ v₂ - v₁ = p₁ -ᵥ p₂)) (neg_add_eq_sub v₁ v₂)))
      (iff.refl (v₂ - v₁ = p₁ -ᵥ p₂)))

theorem vsub_sub_vsub_comm {G : Type u_1} {P : Type u_2} [add_comm_group G] [add_torsor G P] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P) : p₁ -ᵥ p₂ - (p₃ -ᵥ p₄) = p₁ -ᵥ p₃ - (p₂ -ᵥ p₄) := sorry

namespace prod


protected instance add_torsor {G : Type u_1} {P : Type u_2} {G' : Type u_3} {P' : Type u_4} [add_group G] [add_group G'] [add_torsor G P] [add_torsor G' P'] : add_torsor (G × G') (P × P') :=
  add_torsor.mk (fun (v : G × G') (p : P × P') => (fst v +ᵥ fst p, snd v +ᵥ snd p)) sorry sorry
    (fun (p₁ p₂ : P × P') => (fst p₁ -ᵥ fst p₂, snd p₁ -ᵥ snd p₂)) sorry sorry

@[simp] theorem fst_vadd {G : Type u_1} {P : Type u_2} {G' : Type u_3} {P' : Type u_4} [add_group G] [add_group G'] [add_torsor G P] [add_torsor G' P'] (v : G × G') (p : P × P') : fst (v +ᵥ p) = fst v +ᵥ fst p :=
  rfl

@[simp] theorem snd_vadd {G : Type u_1} {P : Type u_2} {G' : Type u_3} {P' : Type u_4} [add_group G] [add_group G'] [add_torsor G P] [add_torsor G' P'] (v : G × G') (p : P × P') : snd (v +ᵥ p) = snd v +ᵥ snd p :=
  rfl

@[simp] theorem mk_vadd_mk {G : Type u_1} {P : Type u_2} {G' : Type u_3} {P' : Type u_4} [add_group G] [add_group G'] [add_torsor G P] [add_torsor G' P'] (v : G) (v' : G') (p : P) (p' : P') : (v, v') +ᵥ (p, p') = (v +ᵥ p, v' +ᵥ p') :=
  rfl

@[simp] theorem fst_vsub {G : Type u_1} {P : Type u_2} {G' : Type u_3} {P' : Type u_4} [add_group G] [add_group G'] [add_torsor G P] [add_torsor G' P'] (p₁ : P × P') (p₂ : P × P') : fst (p₁ -ᵥ p₂) = fst p₁ -ᵥ fst p₂ :=
  rfl

@[simp] theorem snd_vsub {G : Type u_1} {P : Type u_2} {G' : Type u_3} {P' : Type u_4} [add_group G] [add_group G'] [add_torsor G P] [add_torsor G' P'] (p₁ : P × P') (p₂ : P × P') : snd (p₁ -ᵥ p₂) = snd p₁ -ᵥ snd p₂ :=
  rfl

@[simp] theorem mk_vsub_mk {G : Type u_1} {P : Type u_2} {G' : Type u_3} {P' : Type u_4} [add_group G] [add_group G'] [add_torsor G P] [add_torsor G' P'] (p₁ : P) (p₂ : P) (p₁' : P') (p₂' : P') : (p₁, p₁') -ᵥ (p₂, p₂') = (p₁ -ᵥ p₂, p₁' -ᵥ p₂') :=
  rfl

end prod


namespace pi


/-- A product of `add_torsor`s is an `add_torsor`. -/
protected instance add_torsor {I : Type u} {fg : I → Type v} [(i : I) → add_group (fg i)] {fp : I → Type w} [T : (i : I) → add_torsor (fg i) (fp i)] : add_torsor ((i : I) → fg i) ((i : I) → fp i) :=
  add_torsor.mk (fun (g : (i : I) → fg i) (p : (i : I) → fp i) (i : I) => g i +ᵥ p i) sorry sorry
    (fun (p₁ p₂ : (i : I) → fp i) (i : I) => p₁ i -ᵥ p₂ i) sorry sorry

/-- Addition in a product of `add_torsor`s. -/
@[simp] theorem vadd_apply {I : Type u} {fg : I → Type v} [(i : I) → add_group (fg i)] {fp : I → Type w} [T : (i : I) → add_torsor (fg i) (fp i)] (x : (i : I) → fg i) (y : (i : I) → fp i) {i : I} : has_vadd.vadd x y i = x i +ᵥ y i :=
  rfl

end pi


namespace equiv


/-- `v ↦ v +ᵥ p` as an equivalence. -/
def vadd_const {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] (p : P) : G ≃ P :=
  mk (fun (v : G) => v +ᵥ p) (fun (p' : P) => p' -ᵥ p) sorry sorry

@[simp] theorem coe_vadd_const {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] (p : P) : ⇑(vadd_const p) = fun (v : G) => v +ᵥ p :=
  rfl

@[simp] theorem coe_vadd_const_symm {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] (p : P) : ⇑(equiv.symm (vadd_const p)) = fun (p' : P) => p' -ᵥ p :=
  rfl

/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
def const_vsub {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] (p : P) : P ≃ G :=
  mk (has_vsub.vsub p) (fun (v : G) => -v +ᵥ p) sorry sorry

@[simp] theorem coe_const_vsub {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] (p : P) : ⇑(const_vsub p) = has_vsub.vsub p :=
  rfl

@[simp] theorem coe_const_vsub_symm {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] (p : P) : ⇑(equiv.symm (const_vsub p)) = fun (v : G) => -v +ᵥ p :=
  rfl

/-- The permutation given by `p ↦ v +ᵥ p`. -/
def const_vadd {G : Type u_1} (P : Type u_2) [add_group G] [add_torsor G P] (v : G) : perm P :=
  mk (has_vadd.vadd v) (has_vadd.vadd (-v)) sorry sorry

@[simp] theorem coe_const_vadd {G : Type u_1} (P : Type u_2) [add_group G] [add_torsor G P] (v : G) : ⇑(const_vadd P v) = has_vadd.vadd v :=
  rfl

@[simp] theorem const_vadd_zero (G : Type u_1) (P : Type u_2) [add_group G] [add_torsor G P] : const_vadd P 0 = 1 :=
  ext (zero_vadd G)

@[simp] theorem const_vadd_add {G : Type u_1} (P : Type u_2) [add_group G] [add_torsor G P] (v₁ : G) (v₂ : G) : const_vadd P (v₁ + v₂) = const_vadd P v₁ * const_vadd P v₂ :=
  ext fun (p : P) => Eq.symm (vadd_assoc v₁ v₂ p)

/-- `equiv.const_vadd` as a homomorphism from `multiplicative G` to `equiv.perm P` -/
def const_vadd_hom {G : Type u_1} (P : Type u_2) [add_group G] [add_torsor G P] : multiplicative G →* perm P :=
  monoid_hom.mk (fun (v : multiplicative G) => const_vadd P (coe_fn multiplicative.to_add v)) (const_vadd_zero G P) sorry

/-- Point reflection in `x` as a permutation. -/
def point_reflection {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] (x : P) : perm P :=
  equiv.trans (const_vsub x) (vadd_const x)

theorem point_reflection_apply {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] (x : P) (y : P) : coe_fn (point_reflection x) y = x -ᵥ y +ᵥ x :=
  rfl

@[simp] theorem point_reflection_symm {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] (x : P) : equiv.symm (point_reflection x) = point_reflection x := sorry

@[simp] theorem point_reflection_self {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] (x : P) : coe_fn (point_reflection x) x = x :=
  vsub_vadd x x

theorem point_reflection_involutive {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] (x : P) : function.involutive ⇑(point_reflection x) := sorry

/-- `x` is the only fixed point of `point_reflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
theorem point_reflection_fixed_iff_of_injective_bit0 {G : Type u_1} {P : Type u_2} [add_group G] [add_torsor G P] {x : P} {y : P} (h : function.injective bit0) : coe_fn (point_reflection x) y = y ↔ y = x := sorry

theorem injective_point_reflection_left_of_injective_bit0 {G : Type u_1} {P : Type u_2} [add_comm_group G] [add_torsor G P] (h : function.injective bit0) (y : P) : function.injective fun (x : P) => coe_fn (point_reflection x) y := sorry

