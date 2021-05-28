/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.ring
import Mathlib.group_theory.monoid_localization
import Mathlib.ring_theory.ideal.operations
import Mathlib.ring_theory.algebraic
import Mathlib.ring_theory.integral_closure
import Mathlib.ring_theory.non_zero_divisors
import Mathlib.PostPort

universes u_1 u_2 l u_3 u_4 u_5 u_6 u_7 

namespace Mathlib

/-!
# Localizations of commutative rings

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R`, `f x = f y` iff there exists `c ∈ M` such that `x * c = y * c`.

Given such a localization map `f : R →+* S`, we can define the surjection
`localization_map.mk'` sending `(x, y) : R × M` to `f x * (f y)⁻¹`, and
`localization_map.lift`, the homomorphism from `S` induced by a homomorphism from `R` which maps
elements of `M` to invertible elements of the codomain. Similarly, given commutative rings
`P, Q`, a submonoid `T` of `P` and a localization map for `T` from `P` to `Q`, then a homomorphism
`g : R →+* P` such that `g(M) ⊆ T` induces a homomorphism of localizations,
`localization_map.map`, from `S` to `Q`.
We treat the special case of localizing away from an element in the sections `away_map` and `away`.

We show the localization as a quotient type, defined in `group_theory.monoid_localization` as
`submonoid.localization`, is a `comm_ring` and that the natural ring hom
`of : R →+* localization M` is a localization map.

We show that a localization at the complement of a prime ideal is a local ring.

We prove some lemmas about the `R`-algebra structure of `S`.

When `R` is an integral domain, we define `fraction_map R K` as an abbreviation for
`localization (non_zero_divisors R) K`, the natural map to `R`'s field of fractions.

We show that a `comm_ring` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field. We use this to show the field of fractions as a quotient type, `fraction_ring`, is
a field.

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A ring localization map is defined to be a localization map of the underlying `comm_monoid` (a
`submonoid.localization_map`) which is also a ring hom. To prove most lemmas about a
`localization_map` `f` in this file we invoke the corresponding proof for the underlying
`comm_monoid` localization map `f.to_localization_map`, which can be found in
`group_theory.monoid_localization` and the namespace `submonoid.localization_map`.

To apply a localization map `f` as a function, we use `f.to_map`, as coercions don't work well for
this structure.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → localization M` equals the surjection
`localization_map.mk'` induced by the map `of : localization_map M (localization M)`
(where `of` establishes the localization as a quotient type satisfies the characteristic
predicate). The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `localization_map.mk'` induced by any localization map.

We define a copy of the localization map `f`'s codomain `S` carrying the data of `f` so that
instances on `S` induced by `f` can 'know' the map needed to induce the instance.

The proof that "a `comm_ring` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[field K]` instead of just `[comm_ring K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

/-- The type of ring homomorphisms satisfying the characteristic predicate: if `f : R →+* S`
satisfies this predicate, then `S` is isomorphic to the localization of `R` at `M`.
We later define an instance coercing a localization map `f` to its codomain `S` so
that instances on `S` induced by `f` can 'know' the map needed to induce the instance. -/
structure localization_map {R : Type u_1} [comm_ring R] (M : submonoid R) (S : Type u_2) [comm_ring S] 
extends R →+* S, submonoid.localization_map M S
where

/-- The ring hom underlying a `localization_map`. -/
/-- The `comm_monoid` `localization_map` underlying a `comm_ring` `localization_map`.
See `group_theory.monoid_localization` for its definition. -/
namespace ring_hom


/-- Makes a localization map from a `comm_ring` hom satisfying the characteristic predicate. -/
def to_localization_map {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : R →+* S) (H1 : ∀ (y : ↥M), is_unit (coe_fn f ↑y)) (H2 : ∀ (z : S), ∃ (x : R × ↥M), z * coe_fn f ↑(prod.snd x) = coe_fn f (prod.fst x)) (H3 : ∀ (x y : R), coe_fn f x = coe_fn f y ↔ ∃ (c : ↥M), x * ↑c = y * ↑c) : localization_map M S :=
  localization_map.mk (to_fun f) sorry sorry sorry sorry H1 H2 H3

end ring_hom


/-- Makes a `comm_ring` localization map from an additive `comm_monoid` localization map of
`comm_ring`s. -/
def submonoid.localization_map.to_ring_localization {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : submonoid.localization_map M S) (h : ∀ (x y : R),
  coe_fn (submonoid.localization_map.to_map f) (x + y) =
    coe_fn (submonoid.localization_map.to_map f) x + coe_fn (submonoid.localization_map.to_map f) y) : localization_map M S :=
  localization_map.mk (ring_hom.to_fun (ring_hom.mk' (submonoid.localization_map.to_monoid_hom f) h)) sorry sorry sorry
    sorry sorry sorry sorry

namespace localization_map


/-- We define a copy of the localization map `f`'s codomain `S` carrying the data of `f` so that
instances on `S` induced by `f` can 'know` the map needed to induce the instance. -/
def codomain {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S)  :=
  S

protected instance codomain.comm_ring {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : comm_ring (codomain f) :=
  _inst_2

protected instance codomain.field {R : Type u_1} [comm_ring R] {M : submonoid R} {K : Type u_2} [field K] (f : localization_map M K) : field (codomain f) :=
  _inst_4

/-- Short for `to_ring_hom`; used for applying a localization map as a function. -/
def to_map {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : R →+* S :=
  to_ring_hom f

theorem map_units {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (y : ↥M) : is_unit (coe_fn (to_map f) ↑y) :=
  map_units' f y

theorem surj {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (z : S) : ∃ (x : R × ↥M), z * coe_fn (to_map f) ↑(prod.snd x) = coe_fn (to_map f) (prod.fst x) :=
  surj' f z

theorem eq_iff_exists {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {x : R} {y : R} : coe_fn (to_map f) x = coe_fn (to_map f) y ↔ ∃ (c : ↥M), x * ↑c = y * ↑c :=
  eq_iff_exists' f x y

theorem ext {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} {g : localization_map M S} (h : ∀ (x : R), coe_fn (to_map f) x = coe_fn (to_map g) x) : f = g := sorry

theorem ext_iff {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} {g : localization_map M S} : f = g ↔ ∀ (x : R), coe_fn (to_map f) x = coe_fn (to_map g) x :=
  { mp := fun (h : f = g) (x : R) => h ▸ rfl, mpr := ext }

theorem to_map_injective {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] : function.injective to_map :=
  fun (_x _x_1 : localization_map M S) (h : to_map _x = to_map _x_1) => ext (iff.mp ring_hom.ext_iff h)

/-- Given `a : S`, `S` a localization of `R`, `is_integer a` iff `a` is in the image of
the localization map from `R` to `S`. -/
def is_integer {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (a : S)  :=
  a ∈ set.range ⇑(to_map f)

-- TODO: define a subalgebra of `is_integer`s

theorem is_integer_zero {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : is_integer f 0 :=
  Exists.intro 0 (ring_hom.map_zero (to_map f))

theorem is_integer_one {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : is_integer f 1 :=
  Exists.intro 1 (ring_hom.map_one (to_map f))

theorem is_integer_add {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} {a : S} {b : S} (ha : is_integer f a) (hb : is_integer f b) : is_integer f (a + b) := sorry

theorem is_integer_mul {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} {a : S} {b : S} (ha : is_integer f a) (hb : is_integer f b) : is_integer f (a * b) := sorry

theorem is_integer_smul {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} {a : R} {b : S} (hb : is_integer f b) : is_integer f (coe_fn (to_map f) a * b) := sorry

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `localization_map.surj`.
-/
theorem exists_integer_multiple' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (a : S) : ∃ (b : ↥M), is_integer f (a * coe_fn (to_map f) ↑b) := sorry

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `has_scalar` instance.
-/
theorem exists_integer_multiple {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (a : S) : ∃ (b : ↥M), is_integer f (coe_fn (to_map f) ↑b * a) := sorry

/-- Given `z : S`, `f.to_localization_map.sec z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x` (so this lemma is true by definition). -/
theorem sec_spec {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (z : S) : z * coe_fn (to_map f) ↑(prod.snd (submonoid.localization_map.sec (to_localization_map f) z)) =
  coe_fn (to_map f) (prod.fst (submonoid.localization_map.sec (to_localization_map f) z)) :=
  classical.some_spec (surj f z)

/-- Given `z : S`, `f.to_localization_map.sec z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x`, so this lemma is just an application of `S`'s commutativity. -/
theorem sec_spec' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (z : S) : coe_fn (to_map f) (prod.fst (submonoid.localization_map.sec (to_localization_map f) z)) =
  coe_fn (to_map f) ↑(prod.snd (submonoid.localization_map.sec (to_localization_map f) z)) * z := sorry

/-- We can clear the denominators of a finite set of fractions. -/
theorem exist_integer_multiples_of_finset {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (s : finset S) : ∃ (b : ↥M), ∀ (a : S), a ∈ s → is_integer f (coe_fn (to_map f) ↑b * a) := sorry

theorem map_right_cancel {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {x : R} {y : R} {c : ↥M} (h : coe_fn (to_map f) (↑c * x) = coe_fn (to_map f) (↑c * y)) : coe_fn (to_map f) x = coe_fn (to_map f) y :=
  submonoid.localization_map.map_right_cancel (to_localization_map f) h

theorem map_left_cancel {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {x : R} {y : R} {c : ↥M} (h : coe_fn (to_map f) (x * ↑c) = coe_fn (to_map f) (y * ↑c)) : coe_fn (to_map f) x = coe_fn (to_map f) y :=
  submonoid.localization_map.map_left_cancel (to_localization_map f) h

theorem eq_zero_of_fst_eq_zero {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {z : S} {x : R} {y : ↥M} (h : z * coe_fn (to_map f) ↑y = coe_fn (to_map f) x) (hx : x = 0) : z = 0 :=
  iff.mp (is_unit.mul_left_eq_zero (map_units f y))
    (eq.mp (Eq._oldrec (Eq.refl (z * coe_fn (to_map f) ↑y = coe_fn (to_map f) 0)) (ring_hom.map_zero (to_map f)))
      (eq.mp (Eq._oldrec (Eq.refl (z * coe_fn (to_map f) ↑y = coe_fn (to_map f) x)) hx) h))

/-- Given a localization map `f : R →+* S`, the surjection sending `(x, y) : R × M` to
`f x * (f y)⁻¹`. -/
def mk' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : R) (y : ↥M) : S :=
  submonoid.localization_map.mk' (to_localization_map f) x y

@[simp] theorem mk'_sec {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (z : S) : mk' f (prod.fst (submonoid.localization_map.sec (to_localization_map f) z))
    (prod.snd (submonoid.localization_map.sec (to_localization_map f) z)) =
  z :=
  submonoid.localization_map.mk'_sec (to_localization_map f) z

theorem mk'_mul {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x₁ : R) (x₂ : R) (y₁ : ↥M) (y₂ : ↥M) : mk' f (x₁ * x₂) (y₁ * y₂) = mk' f x₁ y₁ * mk' f x₂ y₂ :=
  submonoid.localization_map.mk'_mul (to_localization_map f) x₁ x₂ y₁ y₂

theorem mk'_one {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : R) : mk' f x 1 = coe_fn (to_map f) x :=
  submonoid.localization_map.mk'_one (to_localization_map f) x

@[simp] theorem mk'_spec {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : R) (y : ↥M) : mk' f x y * coe_fn (to_map f) ↑y = coe_fn (to_map f) x :=
  submonoid.localization_map.mk'_spec (to_localization_map f) x y

@[simp] theorem mk'_spec' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : R) (y : ↥M) : coe_fn (to_map f) ↑y * mk' f x y = coe_fn (to_map f) x :=
  submonoid.localization_map.mk'_spec' (to_localization_map f) x y

theorem eq_mk'_iff_mul_eq {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {x : R} {y : ↥M} {z : S} : z = mk' f x y ↔ z * coe_fn (to_map f) ↑y = coe_fn (to_map f) x :=
  submonoid.localization_map.eq_mk'_iff_mul_eq (to_localization_map f)

theorem mk'_eq_iff_eq_mul {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {x : R} {y : ↥M} {z : S} : mk' f x y = z ↔ coe_fn (to_map f) x = z * coe_fn (to_map f) ↑y :=
  submonoid.localization_map.mk'_eq_iff_eq_mul (to_localization_map f)

theorem mk'_surjective {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (z : S) : ∃ (x : R), ∃ (y : ↥M), mk' f x y = z := sorry

theorem mk'_eq_iff_eq {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {x₁ : R} {x₂ : R} {y₁ : ↥M} {y₂ : ↥M} : mk' f x₁ y₁ = mk' f x₂ y₂ ↔ coe_fn (to_map f) (x₁ * ↑y₂) = coe_fn (to_map f) (x₂ * ↑y₁) :=
  submonoid.localization_map.mk'_eq_iff_eq (to_localization_map f)

theorem mk'_mem_iff {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {x : R} {y : ↥M} {I : ideal S} : mk' f x y ∈ I ↔ coe_fn (to_map f) x ∈ I := sorry

protected theorem eq {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {a₁ : R} {b₁ : R} {a₂ : ↥M} {b₂ : ↥M} : mk' f a₁ a₂ = mk' f b₁ b₂ ↔ ∃ (c : ↥M), a₁ * ↑b₂ * ↑c = b₁ * ↑a₂ * ↑c :=
  submonoid.localization_map.eq (to_localization_map f)

theorem eq_iff_eq {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) (g : localization_map M P) {x : R} {y : R} : coe_fn (to_map f) x = coe_fn (to_map f) y ↔ coe_fn (to_map g) x = coe_fn (to_map g) y :=
  submonoid.localization_map.eq_iff_eq (to_localization_map f) (to_localization_map g)

theorem mk'_eq_iff_mk'_eq {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) (g : localization_map M P) {x₁ : R} {x₂ : R} {y₁ : ↥M} {y₂ : ↥M} : mk' f x₁ y₁ = mk' f x₂ y₂ ↔ mk' g x₁ y₁ = mk' g x₂ y₂ :=
  submonoid.localization_map.mk'_eq_iff_mk'_eq (to_localization_map f) (to_localization_map g)

theorem mk'_eq_of_eq {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {a₁ : R} {b₁ : R} {a₂ : ↥M} {b₂ : ↥M} (H : b₁ * ↑a₂ = a₁ * ↑b₂) : mk' f a₁ a₂ = mk' f b₁ b₂ :=
  submonoid.localization_map.mk'_eq_of_eq (to_localization_map f) H

@[simp] theorem mk'_self {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {x : R} (hx : x ∈ M) : mk' f x { val := x, property := hx } = 1 :=
  submonoid.localization_map.mk'_self (to_localization_map f) x hx

@[simp] theorem mk'_self' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {x : ↥M} : mk' f (↑x) x = 1 :=
  submonoid.localization_map.mk'_self' (to_localization_map f) x

theorem mk'_self'' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {x : ↥M} : mk' f (subtype.val x) x = 1 :=
  mk'_self' f

theorem mul_mk'_eq_mk'_of_mul {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : R) (y : R) (z : ↥M) : coe_fn (to_map f) x * mk' f y z = mk' f (x * y) z :=
  submonoid.localization_map.mul_mk'_eq_mk'_of_mul (to_localization_map f) x y z

theorem mk'_eq_mul_mk'_one {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : R) (y : ↥M) : mk' f x y = coe_fn (to_map f) x * mk' f 1 y :=
  Eq.symm (submonoid.localization_map.mul_mk'_one_eq_mk' (to_localization_map f) x y)

@[simp] theorem mk'_mul_cancel_left {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : R) (y : ↥M) : mk' f (↑y * x) y = coe_fn (to_map f) x :=
  submonoid.localization_map.mk'_mul_cancel_left (to_localization_map f) x y

theorem mk'_mul_cancel_right {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : R) (y : ↥M) : mk' f (x * ↑y) y = coe_fn (to_map f) x :=
  submonoid.localization_map.mk'_mul_cancel_right (to_localization_map f) x y

@[simp] theorem mk'_mul_mk'_eq_one {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : ↥M) (y : ↥M) : mk' f (↑x) y * mk' f (↑y) x = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (mk' f (↑x) y * mk' f (↑y) x = 1)) (Eq.symm (mk'_mul f (↑x) (↑y) y x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (mk' f (↑x * ↑y) (y * x) = 1)) (mul_comm ↑x ↑y)))
      (mk'_self f (submonoid.has_mul._proof_1 M y x)))

theorem mk'_mul_mk'_eq_one' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : R) (y : ↥M) (h : x ∈ M) : mk' f x y * mk' f ↑y { val := x, property := h } = 1 :=
  mk'_mul_mk'_eq_one f { val := x, property := h } y

theorem is_unit_comp {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) (j : S →+* P) (y : ↥M) : is_unit (coe_fn (ring_hom.comp j (to_map f)) ↑y) :=
  submonoid.localization_map.is_unit_comp (to_localization_map f) (ring_hom.to_monoid_hom j) y

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g(M) ⊆ units P`, `f x = f y → g x = g y` for all `x y : R`. -/
theorem eq_of_eq {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} (hg : ∀ (y : ↥M), is_unit (coe_fn g ↑y)) {x : R} {y : R} (h : coe_fn (to_map f) x = coe_fn (to_map f) y) : coe_fn g x = coe_fn g y :=
  submonoid.localization_map.eq_of_eq (to_localization_map f) hg h

theorem mk'_add {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x₁ : R) (x₂ : R) (y₁ : ↥M) (y₂ : ↥M) : mk' f (x₁ * ↑y₂ + x₂ * ↑y₁) (y₁ * y₂) = mk' f x₁ y₁ + mk' f x₂ y₂ := sorry

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` sending `z : S` to `g x * (g y)⁻¹`, where `(x, y) : R × M` are such that
`z = f x * (f y)⁻¹`. -/
def lift {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} (hg : ∀ (y : ↥M), is_unit (coe_fn g ↑y)) : S →+* P :=
  ring_hom.mk' (submonoid.localization_map.lift (to_localization_map f) hg) sorry

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : R, y ∈ M`. -/
theorem lift_mk' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} (hg : ∀ (y : ↥M), is_unit (coe_fn g ↑y)) (x : R) (y : ↥M) : coe_fn (lift f hg) (mk' f x y) =
  coe_fn g x * ↑(coe_fn (is_unit.lift_right (monoid_hom.mrestrict (ring_hom.to_monoid_hom g) M) hg) y⁻¹) :=
  submonoid.localization_map.lift_mk' (to_localization_map f) hg x y

theorem lift_mk'_spec {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} (hg : ∀ (y : ↥M), is_unit (coe_fn g ↑y)) (x : R) (v : P) (y : ↥M) : coe_fn (lift f hg) (mk' f x y) = v ↔ coe_fn g x = coe_fn g ↑y * v :=
  submonoid.localization_map.lift_mk'_spec (to_localization_map f) hg x v y

@[simp] theorem lift_eq {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} (hg : ∀ (y : ↥M), is_unit (coe_fn g ↑y)) (x : R) : coe_fn (lift f hg) (coe_fn (to_map f) x) = coe_fn g x :=
  submonoid.localization_map.lift_eq (to_localization_map f) hg x

theorem lift_eq_iff {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} (hg : ∀ (y : ↥M), is_unit (coe_fn g ↑y)) {x : R × ↥M} {y : R × ↥M} : coe_fn (lift f hg) (mk' f (prod.fst x) (prod.snd x)) = coe_fn (lift f hg) (mk' f (prod.fst y) (prod.snd y)) ↔
  coe_fn g (prod.fst x * ↑(prod.snd y)) = coe_fn g (prod.fst y * ↑(prod.snd x)) :=
  submonoid.localization_map.lift_eq_iff (to_localization_map f) hg

@[simp] theorem lift_comp {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} (hg : ∀ (y : ↥M), is_unit (coe_fn g ↑y)) : ring_hom.comp (lift f hg) (to_map f) = g :=
  ring_hom.ext (iff.mp monoid_hom.ext_iff (submonoid.localization_map.lift_comp (to_localization_map f) hg))

@[simp] theorem lift_of_comp {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) (j : S →+* P) : lift f (is_unit_comp f j) = j :=
  ring_hom.ext
    (iff.mp monoid_hom.ext_iff
      (submonoid.localization_map.lift_of_comp (to_localization_map f) (ring_hom.to_monoid_hom j)))

theorem epic_of_localization_map {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {j : S →+* P} {k : S →+* P} (h : ∀ (a : R), coe_fn (ring_hom.comp j (to_map f)) a = coe_fn (ring_hom.comp k (to_map f)) a) : j = k :=
  ring_hom.ext (iff.mp monoid_hom.ext_iff (submonoid.localization_map.epic_of_localization_map (to_localization_map f) h))

theorem lift_unique {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} (hg : ∀ (y : ↥M), is_unit (coe_fn g ↑y)) {j : S →+* P} (hj : ∀ (x : R), coe_fn j (coe_fn (to_map f) x) = coe_fn g x) : lift f hg = j :=
  ring_hom.ext (iff.mp monoid_hom.ext_iff (submonoid.localization_map.lift_unique (to_localization_map f) hg hj))

@[simp] theorem lift_id {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : S) : coe_fn (lift f (map_units f)) x = x :=
  submonoid.localization_map.lift_id (to_localization_map f) x

/-- Given two localization maps `f : R →+* S, k : R →+* P` for a submonoid `M ⊆ R`,
the hom from `P` to `S` induced by `f` is left inverse to the hom from `S` to `P`
induced by `k`. -/
@[simp] theorem lift_left_inverse {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {k : localization_map M S} (z : S) : coe_fn (lift k (map_units f)) (coe_fn (lift f (map_units k)) z) = z :=
  submonoid.localization_map.lift_left_inverse (to_localization_map f) z

theorem lift_surjective_iff {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} (hg : ∀ (y : ↥M), is_unit (coe_fn g ↑y)) : function.surjective ⇑(lift f hg) ↔ ∀ (v : P), ∃ (x : R × ↥M), v * coe_fn g ↑(prod.snd x) = coe_fn g (prod.fst x) :=
  submonoid.localization_map.lift_surjective_iff (to_localization_map f) hg

theorem lift_injective_iff {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} (hg : ∀ (y : ↥M), is_unit (coe_fn g ↑y)) : function.injective ⇑(lift f hg) ↔ ∀ (x y : R), coe_fn (to_map f) x = coe_fn (to_map f) y ↔ coe_fn g x = coe_fn g y :=
  submonoid.localization_map.lift_injective_iff (to_localization_map f) hg

/-- Given a `comm_ring` homomorphism `g : R →+* P` where for submonoids `M ⊆ R, T ⊆ P` we have
`g(M) ⊆ T`, the induced ring homomorphism from the localization of `R` at `M` to the
localization of `P` at `T`: if `f : R →+* S` and `k : P →+* Q` are localization maps for `M`
and `T` respectively, we send `z : S` to `k (g x) * (k (g y))⁻¹`, where `(x, y) : R × M` are
such that `z = f x * (f y)⁻¹`. -/
def map {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} {T : submonoid P} (hy : ∀ (y : ↥M), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_ring Q] (k : localization_map T Q) : S →+* Q :=
  lift f sorry

theorem map_eq {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} {T : submonoid P} (hy : ∀ (y : ↥M), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_ring Q] {k : localization_map T Q} (x : R) : coe_fn (map f hy k) (coe_fn (to_map f) x) = coe_fn (to_map k) (coe_fn g x) :=
  lift_eq f (fun (y : ↥M) => map_units k { val := coe_fn g ↑y, property := hy y }) x

@[simp] theorem map_comp {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} {T : submonoid P} (hy : ∀ (y : ↥M), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_ring Q] {k : localization_map T Q} : ring_hom.comp (map f hy k) (to_map f) = ring_hom.comp (to_map k) g :=
  lift_comp f fun (y : ↥M) => map_units k { val := coe_fn g ↑y, property := hy y }

theorem map_mk' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} {T : submonoid P} (hy : ∀ (y : ↥M), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_ring Q] {k : localization_map T Q} (x : R) (y : ↥M) : coe_fn (map f hy k) (mk' f x y) = mk' k (coe_fn g x) { val := coe_fn g ↑y, property := hy y } :=
  submonoid.localization_map.map_mk' (to_localization_map f) hy x y

@[simp] theorem map_id {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (z : S) : coe_fn (map f (fun (y : ↥M) => (fun (this : coe_fn (ring_hom.id R) ↑y ∈ M) => this) (subtype.property y)) f) z = z :=
  lift_id f z

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_comp_map {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} {T : submonoid P} (hy : ∀ (y : ↥M), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_ring Q] {k : localization_map T Q} {A : Type u_5} [comm_ring A] {U : submonoid A} {W : Type u_6} [comm_ring W] (j : localization_map U W) {l : P →+* A} (hl : ∀ (w : ↥T), coe_fn l ↑w ∈ U) : ring_hom.comp (map k hl j) (map f hy k) =
  map f
    (fun (x : ↥M) =>
      (fun (this : coe_fn (ring_hom.comp l g) ↑x ∈ U) => this) (hl { val := coe_fn g ↑x, property := hy x }))
    j :=
  ring_hom.ext
    (iff.mp monoid_hom.ext_iff
      (submonoid.localization_map.map_comp_map (to_localization_map f) hy (to_localization_map j) hl))

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_map {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {g : R →+* P} {T : submonoid P} (hy : ∀ (y : ↥M), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_ring Q] {k : localization_map T Q} {A : Type u_5} [comm_ring A] {U : submonoid A} {W : Type u_6} [comm_ring W] (j : localization_map U W) {l : P →+* A} (hl : ∀ (w : ↥T), coe_fn l ↑w ∈ U) (x : S) : coe_fn (map k hl j) (coe_fn (map f hy k) x) =
  coe_fn
    (map f
      (fun (x : ↥M) =>
        (fun (this : coe_fn (ring_hom.comp l g) ↑x ∈ U) => this) (hl { val := coe_fn g ↑x, property := hy x }))
      j)
    x := sorry

/-- Given localization maps `f : R →+* S, k : P →+* Q` for submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
def ring_equiv_of_ring_equiv {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {T : submonoid P} {Q : Type u_4} [comm_ring Q] (k : localization_map T Q) (h : R ≃+* P) (H : submonoid.map (ring_equiv.to_monoid_hom h) M = T) : S ≃+* Q :=
  mul_equiv.to_ring_equiv
    (submonoid.localization_map.mul_equiv_of_mul_equiv (to_localization_map f) (to_localization_map k) H) sorry

@[simp] theorem ring_equiv_of_ring_equiv_eq_map_apply {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {T : submonoid P} {Q : Type u_4} [comm_ring Q] {k : localization_map T Q} {j : R ≃+* P} (H : submonoid.map (ring_equiv.to_monoid_hom j) M = T) (x : S) : coe_fn (ring_equiv_of_ring_equiv f k j H) x =
  coe_fn
    (map f
      (fun (y : ↥M) =>
        (fun (this : coe_fn (ring_equiv.to_monoid_hom j) ↑y ∈ T) => this)
          (H ▸ set.mem_image_of_mem (⇑j) (subtype.property y)))
      k)
    x :=
  rfl

theorem ring_equiv_of_ring_equiv_eq_map {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {T : submonoid P} {Q : Type u_4} [comm_ring Q] {k : localization_map T Q} {j : R ≃+* P} (H : submonoid.map (ring_equiv.to_monoid_hom j) M = T) : ring_equiv.to_monoid_hom (ring_equiv_of_ring_equiv f k j H) =
  ↑(map f
      (fun (y : ↥M) =>
        (fun (this : coe_fn (ring_equiv.to_monoid_hom j) ↑y ∈ T) => this)
          (H ▸ set.mem_image_of_mem (⇑j) (subtype.property y)))
      k) :=
  rfl

@[simp] theorem ring_equiv_of_ring_equiv_eq {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {T : submonoid P} {Q : Type u_4} [comm_ring Q] {k : localization_map T Q} {j : R ≃+* P} (H : submonoid.map (ring_equiv.to_monoid_hom j) M = T) (x : R) : coe_fn (ring_equiv_of_ring_equiv f k j H) (coe_fn (to_map f) x) = coe_fn (to_map k) (coe_fn j x) :=
  submonoid.localization_map.mul_equiv_of_mul_equiv_eq (to_localization_map f) H x

theorem ring_equiv_of_ring_equiv_mk' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (f : localization_map M S) {T : submonoid P} {Q : Type u_4} [comm_ring Q] {k : localization_map T Q} {j : R ≃+* P} (H : submonoid.map (ring_equiv.to_monoid_hom j) M = T) (x : R) (y : ↥M) : coe_fn (ring_equiv_of_ring_equiv f k j H) (mk' f x y) =
  mk' k (coe_fn j x) { val := coe_fn j ↑y, property := H ▸ set.mem_image_of_mem (⇑j) (subtype.property y) } :=
  submonoid.localization_map.mul_equiv_of_mul_equiv_mk' (to_localization_map f) H x y

/-- Given `x : R`, the type of homomorphisms `f : R →* S` such that `S`
is isomorphic to the localization of `R` at the submonoid generated by `x`. -/
def away_map {R : Type u_1} [comm_ring R] (x : R) (S' : Type u_2) [comm_ring S']  :=
  localization_map (submonoid.powers x) S'

/-- Given `x : R` and a localization map `F : R →+* S` away from `x`, `inv_self` is `(F x)⁻¹`. -/
def away_map.inv_self {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] (x : R) (F : away_map x S) : S :=
  mk' F 1 { val := x, property := sorry }

/-- Given `x : R`, a localization map `F : R →+* S` away from `x`, and a map of `comm_ring`s
`g : R →+* P` such that `g x` is invertible, the homomorphism induced from `S` to `P` sending
`z : S` to `g y * (g x)⁻ⁿ`, where `y : R, n : ℕ` are such that `z = F y * (F x)⁻ⁿ`. -/
def away_map.lift {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] {g : R →+* P} (x : R) (F : away_map x S) (hg : is_unit (coe_fn g x)) : S →+* P :=
  lift F sorry

@[simp] theorem away_map.lift_eq {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] {g : R →+* P} (x : R) (F : away_map x S) (hg : is_unit (coe_fn g x)) (a : R) : coe_fn (away_map.lift x F hg) (coe_fn (to_map F) a) = coe_fn g a :=
  lift_eq F (away_map.lift._proof_1 x hg) a

@[simp] theorem away_map.lift_comp {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] {g : R →+* P} (x : R) (F : away_map x S) (hg : is_unit (coe_fn g x)) : ring_hom.comp (away_map.lift x F hg) (to_map F) = g :=
  lift_comp F (away_map.lift._proof_1 x hg)

/-- Given `x y : R` and localization maps `F : R →+* S, G : R →+* P` away from `x` and `x * y`
respectively, the homomorphism induced from `S` to `P`. -/
def away_to_away_right {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] (x : R) (F : away_map x S) (y : R) (G : away_map (x * y) P) : S →* P :=
  ↑(away_map.lift x F sorry)

end localization_map


namespace localization


protected instance has_add {R : Type u_1} [comm_ring R] {M : submonoid R} : Add (localization M) :=
  { add :=
      fun (z w : localization M) =>
        con.lift_on₂ z w
          (fun (x y : R × ↥M) => mk (↑(prod.snd x) * prod.fst y + ↑(prod.snd y) * prod.fst x) (prod.snd x * prod.snd y))
          sorry }

protected instance has_neg {R : Type u_1} [comm_ring R] {M : submonoid R} : Neg (localization M) :=
  { neg := fun (z : localization M) => con.lift_on z (fun (x : R × ↥M) => mk (-prod.fst x) (prod.snd x)) sorry }

protected instance has_zero {R : Type u_1} [comm_ring R] {M : submonoid R} : HasZero (localization M) :=
  { zero := mk 0 1 }

protected instance comm_ring {R : Type u_1} [comm_ring R] {M : submonoid R} : comm_ring (localization M) :=
  comm_ring.mk Add.add sorry 0 sorry sorry Neg.neg (fun (x y : localization M) => x + -y) sorry sorry Mul.mul sorry 1
    sorry sorry sorry sorry sorry

/-- Natural hom sending `x : R`, `R` a `comm_ring`, to the equivalence class of
`(x, 1)` in the localization of `R` at a submonoid. -/
def of {R : Type u_1} [comm_ring R] (M : submonoid R) : localization_map M (localization M) :=
  submonoid.localization_map.to_ring_localization (monoid_of M) sorry

theorem monoid_of_eq_of {R : Type u_1} [comm_ring R] {M : submonoid R} (x : R) : coe_fn (submonoid.localization_map.to_map (monoid_of M)) x = coe_fn (localization_map.to_map (of M)) x :=
  rfl

theorem mk_one_eq_of {R : Type u_1} [comm_ring R] {M : submonoid R} (x : R) : mk x 1 = coe_fn (localization_map.to_map (of M)) x :=
  rfl

theorem mk_eq_mk'_apply {R : Type u_1} [comm_ring R] {M : submonoid R} (x : R) (y : ↥M) : mk x y = localization_map.mk' (of M) x y :=
  mk_eq_monoid_of_mk'_apply x y

@[simp] theorem mk_eq_mk' {R : Type u_1} [comm_ring R] {M : submonoid R} : mk = localization_map.mk' (of M) :=
  mk_eq_monoid_of_mk'

/-- Given a localization map `f : R →+* S` for a submonoid `M`, we get an isomorphism
between the localization of `R` at `M` as a quotient type and `S`. -/
def ring_equiv_of_quotient {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : localization M ≃+* S :=
  mul_equiv.to_ring_equiv (mul_equiv_of_quotient (localization_map.to_localization_map f)) sorry

@[simp] theorem ring_equiv_of_quotient_apply {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (x : localization M) : coe_fn (ring_equiv_of_quotient f) x = coe_fn (localization_map.lift (of M) (localization_map.map_units f)) x :=
  rfl

@[simp] theorem ring_equiv_of_quotient_mk' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (x : R) (y : ↥M) : coe_fn (ring_equiv_of_quotient f) (localization_map.mk' (of M) x y) = localization_map.mk' f x y :=
  mul_equiv_of_quotient_mk' x y

theorem ring_equiv_of_quotient_mk {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (x : R) (y : ↥M) : coe_fn (ring_equiv_of_quotient f) (mk x y) = localization_map.mk' f x y :=
  mul_equiv_of_quotient_mk x y

@[simp] theorem ring_equiv_of_quotient_of {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (x : R) : coe_fn (ring_equiv_of_quotient f) (coe_fn (localization_map.to_map (of M)) x) = coe_fn (localization_map.to_map f) x :=
  mul_equiv_of_quotient_monoid_of x

@[simp] theorem ring_equiv_of_quotient_symm_mk' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (x : R) (y : ↥M) : coe_fn (ring_equiv.symm (ring_equiv_of_quotient f)) (localization_map.mk' f x y) = localization_map.mk' (of M) x y :=
  mul_equiv_of_quotient_symm_mk' x y

theorem ring_equiv_of_quotient_symm_mk {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (x : R) (y : ↥M) : coe_fn (ring_equiv.symm (ring_equiv_of_quotient f)) (localization_map.mk' f x y) = mk x y :=
  mul_equiv_of_quotient_symm_mk x y

@[simp] theorem ring_equiv_of_quotient_symm_of {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (x : R) : coe_fn (ring_equiv.symm (ring_equiv_of_quotient f)) (coe_fn (localization_map.to_map f) x) =
  coe_fn (localization_map.to_map (of M)) x :=
  mul_equiv_of_quotient_symm_monoid_of x

/-- Given `x : R`, the natural hom sending `y : R`, `R` a `comm_ring`, to the equivalence class
of `(y, 1)` in the localization of `R` at the submonoid generated by `x`. -/
def away.of {R : Type u_1} [comm_ring R] (x : R) : localization_map.away_map x (away x) :=
  of (submonoid.powers x)

@[simp] theorem away.mk_eq_mk' {R : Type u_1} [comm_ring R] (x : R) : mk = localization_map.mk' (away.of x) :=
  mk_eq_mk'

/-- Given `x : R` and a localization map `f : R →+* S` away from `x`, we get an isomorphism between
the localization of `R` at the submonoid generated by `x` as a quotient type and `S`. -/
def away.ring_equiv_of_quotient {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] (x : R) (f : localization_map.away_map x S) : away x ≃+* S :=
  ring_equiv_of_quotient f

end localization


namespace ideal


/-- The complement of a prime ideal `I ⊆ R` is a submonoid of `R`. -/
def prime_compl {R : Type u_1} [comm_ring R] (I : ideal R) [hp : is_prime I] : submonoid R :=
  submonoid.mk (↑Iᶜ) sorry sorry

end ideal


namespace localization_map


/-- A localization map from `R` to `S` where the submonoid is the complement of a prime
ideal of `R`. -/
def at_prime {R : Type u_1} [comm_ring R] (S : Type u_2) [comm_ring S] (I : ideal R) [hp : ideal.is_prime I]  :=
  localization_map (ideal.prime_compl I) S

end localization_map


namespace localization


/-- The localization of `R` at the complement of a prime ideal, as a quotient type. -/
def at_prime {R : Type u_1} [comm_ring R] (I : ideal R) [hp : ideal.is_prime I]  :=
  localization (ideal.prime_compl I)

end localization


namespace localization_map


/-- When `f` is a localization map from `R` at the complement of a prime ideal `I`, we use a
copy of the localization map `f`'s codomain `S` carrying the data of `f` so that the `local_ring`
instance on `S` can 'know' the map needed to induce the instance. -/
protected instance at_prime.local_ring {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] {I : ideal R} [hp : ideal.is_prime I] (f : at_prime S I) : local_ring (codomain f) := sorry

end localization_map


namespace localization


/-- The localization of `R` at the complement of a prime ideal is a local ring. -/
protected instance at_prime.local_ring {R : Type u_1} [comm_ring R] (I : ideal R) [hp : ideal.is_prime I] : local_ring (localization (ideal.prime_compl I)) :=
  localization_map.at_prime.local_ring (of (ideal.prime_compl I))

end localization


namespace localization_map


/-- Explicit characterization of the ideal given by `ideal.map f.to_map I`.
In practice, this ideal differs only in that the carrier set is defined explicitly.
This definition is only meant to be used in proving `mem_map_to_map_iff`,
and any proof that needs to refer to the explicit carrier set should use that theorem. -/
theorem mem_map_to_map_iff {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {I : ideal R} {z : S} : z ∈ ideal.map (to_map f) I ↔ ∃ (x : ↥I × ↥M), z * coe_fn (to_map f) ↑(prod.snd x) = coe_fn (to_map f) ↑(prod.fst x) := sorry

theorem map_comap {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (J : ideal S) : ideal.map (to_map f) (ideal.comap (to_map f) J) = J := sorry

theorem comap_map_of_is_prime_disjoint {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (I : ideal R) (hI : ideal.is_prime I) (hM : disjoint ↑M ↑I) : ideal.comap (to_map f) (ideal.map (to_map f) I) = I := sorry

/-- If `S` is the localization of `R` at a submonoid, the ordering of ideals of `S` is
embedded in the ordering of ideals of `R`. -/
def order_embedding {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : ideal S ↪o ideal R :=
  rel_embedding.mk (function.embedding.mk (fun (J : ideal S) => ideal.comap (to_map f) J) sorry) sorry

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its comap,
see `le_rel_iso_of_prime` for the more general relation isomorphism -/
theorem is_prime_iff_is_prime_disjoint {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (J : ideal S) : ideal.is_prime J ↔ ideal.is_prime (ideal.comap (to_map f) J) ∧ disjoint ↑M ↑(ideal.comap (to_map f) J) := sorry

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its map,
see `le_rel_iso_of_prime` for the more general relation isomorphism, and the reverse implication -/
theorem is_prime_of_is_prime_disjoint {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (I : ideal R) (hp : ideal.is_prime I) (hd : disjoint ↑M ↑I) : ideal.is_prime (ideal.map (to_map f) I) := sorry

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M` -/
def order_iso_of_prime {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : (Subtype fun (p : ideal S) => ideal.is_prime p) ≃o Subtype fun (p : ideal R) => ideal.is_prime p ∧ disjoint ↑M ↑p :=
  rel_iso.mk
    (equiv.mk
      (fun (p : Subtype fun (p : ideal S) => ideal.is_prime p) =>
        { val := ideal.comap (to_map f) (subtype.val p), property := sorry })
      (fun (p : Subtype fun (p : ideal R) => ideal.is_prime p ∧ disjoint ↑M ↑p) =>
        { val := ideal.map (to_map f) (subtype.val p), property := sorry })
      sorry sorry)
    sorry

/-- `quotient_map` applied to maximal ideals of a localization is `surjective`.
  The quotient by a maximal ideal is a field, so inverses to elements already exist,
  and the localization necessarily maps the equivalence class of the inverse in the localization -/
theorem surjective_quotient_map_of_maximal_of_localization {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} {I : ideal S} [ideal.is_prime I] {J : ideal R} {H : J ≤ ideal.comap (to_map f) I} (hI : ideal.is_maximal (ideal.comap (to_map f) I)) : function.surjective ⇑(ideal.quotient_map I (to_map f) H) := sorry

/-!
### `algebra` section

Defines the `R`-algebra instance on a copy of `S` carrying the data of the localization map
`f` needed to induce the `R`-algebra structure. -/

/-- We use a copy of the localization map `f`'s codomain `S` carrying the data of `f` so that the
`R`-algebra instance on `S` can 'know' the map needed to induce the `R`-algebra structure. -/
protected instance algebra {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : algebra R (codomain f) :=
  ring_hom.to_algebra (to_map f)

end localization_map


namespace localization


protected instance algebra {R : Type u_1} [comm_ring R] {M : submonoid R} : algebra R (localization M) :=
  localization_map.algebra (of M)

end localization


namespace localization_map


@[simp] theorem of_id {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (a : R) : coe_fn (algebra.of_id R (codomain f)) a = coe_fn (to_map f) a :=
  rfl

@[simp] theorem algebra_map_eq {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : algebra_map R (codomain f) = to_map f :=
  rfl

/-- Localization map `f` from `R` to `S` as an `R`-linear map. -/
def lin_coe {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : linear_map R R (codomain f) :=
  linear_map.mk ⇑(to_map f) sorry sorry

/-- Map from ideals of `R` to submodules of `S` induced by `f`. -/
-- This was previously a `has_coe` instance, but if `f.codomain = R` then this will loop.

-- It could be a `has_coe_t` instance, but we keep it explicit here to avoid slowing down

-- the rest of the library.

def coe_submodule {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (I : ideal R) : submodule R (codomain f) :=
  submodule.map (lin_coe f) I

theorem mem_coe_submodule {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (I : ideal R) {x : S} : x ∈ coe_submodule f I ↔ ∃ (y : R), y ∈ I ∧ coe_fn (to_map f) y = x :=
  iff.rfl

@[simp] theorem lin_coe_apply {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} {x : R} : coe_fn (lin_coe f) x = coe_fn (to_map f) x :=
  rfl

theorem map_smul {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {P : Type u_3} [comm_ring P] {f : localization_map M S} {g : R →+* P} {T : submonoid P} (hy : ∀ (y : ↥M), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_ring Q] (k : localization_map T Q) (x : codomain f) (z : R) : coe_fn (map f hy k) (z • x) = coe_fn g z • coe_fn (map f hy k) x := sorry

theorem is_noetherian_ring {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (h : is_noetherian_ring R) : is_noetherian_ring (codomain f) := sorry

end localization_map


namespace localization


/-- Given a localization map `f : R →+* S` for a submonoid `M`, we get an `R`-preserving
isomorphism between the localization of `R` at `M` as a quotient type and `S`. -/
def alg_equiv_of_quotient {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : alg_equiv R (localization M) (localization_map.codomain f) :=
  alg_equiv.mk (ring_equiv.to_fun (ring_equiv_of_quotient f)) (ring_equiv.inv_fun (ring_equiv_of_quotient f)) sorry sorry
    sorry sorry sorry

theorem alg_equiv_of_quotient_apply {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : localization M) : coe_fn (alg_equiv_of_quotient f) x = coe_fn (ring_equiv_of_quotient f) x :=
  rfl

theorem alg_equiv_of_quotient_symm_apply {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (x : localization_map.codomain f) : coe_fn (alg_equiv.symm (alg_equiv_of_quotient f)) x = coe_fn (ring_equiv.symm (ring_equiv_of_quotient f)) x :=
  rfl

end localization


namespace localization_map


/-- `coeff_integer_normalization p` gives the coefficients of the polynomial
`integer_normalization p` -/
def coeff_integer_normalization {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (p : polynomial (codomain f)) (i : ℕ) : R :=
  dite (i ∈ finsupp.support p) (fun (hi : i ∈ finsupp.support p) => classical.some sorry)
    fun (hi : ¬i ∈ finsupp.support p) => 0

theorem coeff_integer_normalization_mem_support {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (p : polynomial (codomain f)) (i : ℕ) (h : coeff_integer_normalization p i ≠ 0) : i ∈ finsupp.support p := sorry

/-- `integer_normalization g` normalizes `g` to have integer coefficients
by clearing the denominators -/
def integer_normalization {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) : polynomial (codomain f) → polynomial R :=
  fun (p : polynomial (codomain f)) =>
    finsupp.on_finset (finsupp.support p) (coeff_integer_normalization p) (coeff_integer_normalization_mem_support p)

@[simp] theorem integer_normalization_coeff {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (p : polynomial (codomain f)) (i : ℕ) : polynomial.coeff (integer_normalization f p) i = coeff_integer_normalization p i :=
  rfl

theorem integer_normalization_spec {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (p : polynomial (codomain f)) : ∃ (b : ↥M),
  ∀ (i : ℕ),
    coe_fn (to_map f) (polynomial.coeff (integer_normalization f p) i) = coe_fn (to_map f) ↑b * polynomial.coeff p i := sorry

theorem integer_normalization_map_to_map {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} (p : polynomial (codomain f)) : ∃ (b : ↥M), polynomial.map (to_map f) (integer_normalization f p) = coe_fn (to_map f) ↑b • p := sorry

theorem integer_normalization_eval₂_eq_zero {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} {R' : Type u_4} [comm_ring R'] (g : codomain f →+* R') (p : polynomial (codomain f)) {x : R'} (hx : polynomial.eval₂ g x p = 0) : polynomial.eval₂ (ring_hom.comp g (to_map f)) x (integer_normalization f p) = 0 := sorry

theorem integer_normalization_aeval_eq_zero {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {f : localization_map M S} {R' : Type u_4} [comm_ring R'] [algebra R R'] [algebra (codomain f) R'] [is_scalar_tower R (codomain f) R'] (p : polynomial (codomain f)) {x : R'} (hx : coe_fn (polynomial.aeval x) p = 0) : coe_fn (polynomial.aeval x) (integer_normalization f p) = 0 := sorry

theorem to_map_eq_zero_iff {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) {x : R} (hM : M ≤ non_zero_divisors R) : coe_fn (to_map f) x = 0 ↔ x = 0 := sorry

theorem injective {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] (f : localization_map M S) (hM : M ≤ non_zero_divisors R) : function.injective ⇑(to_map f) := sorry

protected theorem to_map_ne_zero_of_mem_non_zero_divisors {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] [nontrivial R] (f : localization_map M S) (hM : M ≤ non_zero_divisors R) (x : ↥(non_zero_divisors R)) : coe_fn (to_map f) ↑x ≠ 0 :=
  map_ne_zero_of_mem_non_zero_divisors (injective f hM)

/-- A `comm_ring` `S` which is the localization of an integral domain `R` at a subset of
non-zero elements is an integral domain. -/
def integral_domain_of_le_non_zero_divisors {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] {M : submonoid A} (f : localization_map M S) (hM : M ≤ non_zero_divisors A) : integral_domain S :=
  integral_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul
    sorry comm_ring.one sorry sorry sorry sorry sorry sorry sorry

/-- The localization at of an integral domain to a set of non-zero elements is an integral domain -/
def integral_domain_localization {A : Type u_4} [integral_domain A] {M : submonoid A} (hM : M ≤ non_zero_divisors A) : integral_domain (localization M) :=
  integral_domain_of_le_non_zero_divisors (localization.of M) hM

/--
The localization of an integral domain at the complement of a prime ideal is an integral domain.
-/
protected instance integral_domain_of_local_at_prime {A : Type u_4} [integral_domain A] {P : ideal A} (hp : ideal.is_prime P) : integral_domain (localization.at_prime P) :=
  integral_domain_localization sorry

end localization_map


namespace localization


/-- The image of `P` in the localization at `P.prime_compl` is a maximal ideal, and in particular
it is the unique maximal ideal given by the local ring structure `at_prime.local_ring` -/
theorem at_prime.map_eq_maximal_ideal {R : Type u_1} [comm_ring R] {P : ideal R} [hP : ideal.is_prime P] : ideal.map (localization_map.to_map (of (ideal.prime_compl P))) P =
  local_ring.maximal_ideal (localization (ideal.prime_compl P)) := sorry

/-- The unique maximal ideal of the localization at `P.prime_compl` lies over the ideal `P`. -/
theorem at_prime.comap_maximal_ideal {R : Type u_1} [comm_ring R] {P : ideal R} [ideal.is_prime P] : ideal.comap (localization_map.to_map (of (ideal.prime_compl P)))
    (local_ring.maximal_ideal (localization (ideal.prime_compl P))) =
  P := sorry

end localization


/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
theorem localization_map_bijective_of_field {R : Type u_1} {Rₘ : Type u_2} [integral_domain R] [comm_ring Rₘ] {M : submonoid R} (hM : ¬0 ∈ M) (hR : is_field R) (f : localization_map M Rₘ) : function.bijective ⇑(localization_map.to_map f) := sorry

/-- Localization map from an integral domain `R` to its field of fractions. -/
def fraction_map (R : Type u_1) [comm_ring R] (K : Type u_5) [comm_ring K]  :=
  localization_map (non_zero_divisors R) K

namespace fraction_map


theorem to_map_eq_zero_iff {R : Type u_1} [comm_ring R] {K : Type u_5} [comm_ring K] (φ : fraction_map R K) {x : R} : coe_fn (localization_map.to_map φ) x = 0 ↔ x = 0 :=
  localization_map.to_map_eq_zero_iff φ (le_of_eq rfl)

protected theorem injective {R : Type u_1} [comm_ring R] {K : Type u_5} [comm_ring K] (φ : fraction_map R K) : function.injective ⇑(localization_map.to_map φ) :=
  localization_map.injective φ (le_of_eq rfl)

protected theorem to_map_ne_zero_of_mem_non_zero_divisors {R : Type u_1} [comm_ring R] {K : Type u_5} [nontrivial R] [comm_ring K] (φ : fraction_map R K) (x : ↥(non_zero_divisors R)) : coe_fn (localization_map.to_map φ) ↑x ≠ 0 :=
  localization_map.to_map_ne_zero_of_mem_non_zero_divisors φ (le_of_eq rfl) x

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is an
integral domain. -/
def to_integral_domain {A : Type u_4} [integral_domain A] {K : Type u_5} [comm_ring K] (φ : fraction_map A K) : integral_domain K :=
  localization_map.integral_domain_of_le_non_zero_divisors φ sorry

/-- The inverse of an element in the field of fractions of an integral domain. -/
protected def inv {A : Type u_4} [integral_domain A] {K : Type u_5} [comm_ring K] (φ : fraction_map A K) (z : K) : K :=
  dite (z = 0) (fun (h : z = 0) => 0)
    fun (h : ¬z = 0) =>
      localization_map.mk' φ ↑(prod.snd (submonoid.localization_map.sec (localization_map.to_localization_map φ) z))
        { val := prod.fst (submonoid.localization_map.sec (localization_map.to_localization_map φ) z), property := sorry }

protected theorem mul_inv_cancel {A : Type u_4} [integral_domain A] {K : Type u_5} [comm_ring K] (φ : fraction_map A K) (x : K) (hx : x ≠ 0) : x * fraction_map.inv φ x = 1 := sorry

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is a
field. -/
def to_field {A : Type u_4} [integral_domain A] {K : Type u_5} [comm_ring K] (φ : fraction_map A K) : field K :=
  field.mk integral_domain.add sorry integral_domain.zero sorry sorry integral_domain.neg integral_domain.sub sorry sorry
    integral_domain.mul sorry integral_domain.one sorry sorry sorry sorry sorry (fraction_map.inv φ) sorry
    (fraction_map.mul_inv_cancel φ) sorry

theorem mk'_eq_div {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] (f : fraction_map A K) {r : A} {s : ↥(non_zero_divisors A)} : localization_map.mk' f r s = coe_fn (localization_map.to_map f) r / coe_fn (localization_map.to_map f) ↑s :=
  iff.mpr (localization_map.mk'_eq_iff_eq_mul f)
    (Eq.symm
      (div_mul_cancel (coe_fn (localization_map.to_map f) r) (fraction_map.to_map_ne_zero_of_mem_non_zero_divisors f s)))

theorem is_unit_map_of_injective {A : Type u_4} [integral_domain A] {L : Type u_7} [field L] {g : A →+* L} (hg : function.injective ⇑g) (y : ↥(non_zero_divisors A)) : is_unit (coe_fn g ↑y) :=
  is_unit.mk0 (coe_fn g ↑y) (map_ne_zero_of_mem_non_zero_divisors hg)

/-- Given an integral domain `A`, a localization map to its fields of fractions
`f : A →+* K`, and an injective ring hom `g : A →+* L` where `L` is a field, we get a
field hom sending `z : K` to `g x * (g y)⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
def lift {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] {L : Type u_7} [field L] (f : fraction_map A K) {g : A →+* L} (hg : function.injective ⇑g) : K →+* L :=
  localization_map.lift f (is_unit_map_of_injective hg)

/-- Given an integral domain `A`, a localization map to its fields of fractions
`f : A →+* K`, and an injective ring hom `g : A →+* L` where `L` is a field,
field hom induced from `K` to `L` maps `f x / f y` to `g x / g y` for all
`x : A, y ∈ non_zero_divisors A`. -/
@[simp] theorem lift_mk' {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] {L : Type u_7} [field L] (f : fraction_map A K) {g : A →+* L} (hg : function.injective ⇑g) (x : A) (y : ↥(non_zero_divisors A)) : coe_fn (lift f hg) (localization_map.mk' f x y) = coe_fn g x / coe_fn g ↑y := sorry

/-- Given integral domains `A, B` and localization maps to their fields of fractions
`f : A →+* K, g : B →+* L` and an injective ring hom `j : A →+* B`, we get a field hom
sending `z : K` to `g (j x) * (g (j y))⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
def map {A : Type u_4} [integral_domain A] {K : Type u_5} {B : Type u_6} [integral_domain B] [field K] {L : Type u_7} [field L] (f : fraction_map A K) (g : fraction_map B L) {j : A →+* B} (hj : function.injective ⇑j) : K →+* L :=
  localization_map.map f sorry g

/-- Given integral domains `A, B` and localization maps to their fields of fractions
`f : A →+* K, g : B →+* L`, an isomorphism `j : A ≃+* B` induces an isomorphism of
fields of fractions `K ≃+* L`. -/
def field_equiv_of_ring_equiv {A : Type u_4} [integral_domain A] {K : Type u_5} {B : Type u_6} [integral_domain B] [field K] {L : Type u_7} [field L] (f : fraction_map A K) (g : fraction_map B L) (h : A ≃+* B) : K ≃+* L :=
  localization_map.ring_equiv_of_ring_equiv f g h sorry

/-- The cast from `int` to `rat` as a `fraction_map`. -/
def int.fraction_map : fraction_map ℤ ℚ :=
  localization_map.mk coe sorry sorry sorry sorry sorry sorry sorry

theorem integer_normalization_eq_zero_iff {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] (f : fraction_map A K) {p : polynomial (localization_map.codomain f)} : localization_map.integer_normalization f p = 0 ↔ p = 0 := sorry

/-- A field is algebraic over the ring `A` iff it is algebraic over the field of fractions of `A`. -/
theorem comap_is_algebraic_iff {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] {L : Type u_7} [field L] (f : fraction_map A K) [algebra A L] [algebra (localization_map.codomain f) L] [is_scalar_tower A (localization_map.codomain f) L] : algebra.is_algebraic A L ↔ algebra.is_algebraic (localization_map.codomain f) L := sorry

theorem exists_reduced_fraction {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] [unique_factorization_monoid A] (φ : fraction_map A K) (x : localization_map.codomain φ) : ∃ (a : A), ∃ (b : ↥(non_zero_divisors A)), (∀ {d : A}, d ∣ a → d ∣ ↑b → is_unit d) ∧ localization_map.mk' φ a b = x := sorry

/-- `f.num x` is the numerator of `x : f.codomain` as a reduced fraction. -/
def num {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] [unique_factorization_monoid A] (φ : fraction_map A K) (x : localization_map.codomain φ) : A :=
  classical.some (exists_reduced_fraction φ x)

/-- `f.num x` is the denominator of `x : f.codomain` as a reduced fraction. -/
def denom {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] [unique_factorization_monoid A] (φ : fraction_map A K) (x : localization_map.codomain φ) : ↥(non_zero_divisors A) :=
  classical.some sorry

theorem num_denom_reduced {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] [unique_factorization_monoid A] (φ : fraction_map A K) (x : localization_map.codomain φ) {d : A} : d ∣ num φ x → d ∣ ↑(denom φ x) → is_unit d :=
  and.left (classical.some_spec (classical.some_spec (exists_reduced_fraction φ x)))

@[simp] theorem mk'_num_denom {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] [unique_factorization_monoid A] (φ : fraction_map A K) (x : localization_map.codomain φ) : localization_map.mk' φ (num φ x) (denom φ x) = x :=
  and.right (classical.some_spec (classical.some_spec (exists_reduced_fraction φ x)))

theorem num_mul_denom_eq_num_iff_eq {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] [unique_factorization_monoid A] (φ : fraction_map A K) {x : localization_map.codomain φ} {y : localization_map.codomain φ} : x * coe_fn (localization_map.to_map φ) ↑(denom φ y) = coe_fn (localization_map.to_map φ) (num φ y) ↔ x = y := sorry

theorem num_mul_denom_eq_num_iff_eq' {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] [unique_factorization_monoid A] (φ : fraction_map A K) {x : localization_map.codomain φ} {y : localization_map.codomain φ} : y * coe_fn (localization_map.to_map φ) ↑(denom φ x) = coe_fn (localization_map.to_map φ) (num φ x) ↔ x = y := sorry

theorem num_mul_denom_eq_num_mul_denom_iff_eq {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] [unique_factorization_monoid A] (φ : fraction_map A K) {x : localization_map.codomain φ} {y : localization_map.codomain φ} : num φ y * ↑(denom φ x) = num φ x * ↑(denom φ y) ↔ x = y := sorry

theorem eq_zero_of_num_eq_zero {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] [unique_factorization_monoid A] (φ : fraction_map A K) {x : localization_map.codomain φ} (h : num φ x = 0) : x = 0 := sorry

theorem is_integer_of_is_unit_denom {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] [unique_factorization_monoid A] (φ : fraction_map A K) {x : localization_map.codomain φ} (h : is_unit ↑(denom φ x)) : localization_map.is_integer φ x := sorry

theorem is_unit_denom_of_num_eq_zero {A : Type u_4} [integral_domain A] {K : Type u_5} [field K] [unique_factorization_monoid A] (φ : fraction_map A K) {x : localization_map.codomain φ} (h : num φ x = 0) : is_unit ↑(denom φ x) :=
  num_denom_reduced φ x (Eq.symm h ▸ dvd_zero ↑(denom φ x)) (dvd_refl ↑(denom φ x))

end fraction_map


/-- Definition of the natural algebra induced by the localization of an algebra.
Given an algebra `R → S`, a submonoid `R` of `M`, and a localization `Rₘ` for `M`,
let `Sₘ` be the localization of `S` to the image of `M` under `algebra_map R S`.
Then this is the natural algebra structure on `Rₘ → Sₘ`, such that the entire square commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps -/
def localization_algebra {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] {Rₘ : Type u_6} {Sₘ : Type u_7} [comm_ring Rₘ] [comm_ring Sₘ] [algebra R S] (M : submonoid R) (f : localization_map M Rₘ) (g : localization_map (algebra.algebra_map_submonoid S M) Sₘ) : algebra Rₘ Sₘ :=
  ring_hom.to_algebra (localization_map.map f sorry g)

theorem algebra_map_mk' {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {Rₘ : Type u_6} {Sₘ : Type u_7} [comm_ring Rₘ] [comm_ring Sₘ] [algebra R S] (f : localization_map M Rₘ) (g : localization_map (algebra.algebra_map_submonoid S M) Sₘ) (r : R) (m : ↥M) : coe_fn (algebra_map Rₘ Sₘ) (localization_map.mk' f r m) =
  localization_map.mk' g (coe_fn (algebra_map R S) r)
    { val := coe_fn (algebra_map R S) ↑m, property := algebra.mem_algebra_map_submonoid_of_mem m } :=
  localization_map.map_mk' f (localization_algebra._proof_1 M) r m

/-- Injectivity of a map descends to the map induced on localizations. -/
theorem map_injective_of_injective {Rₘ : Type u_6} {Sₘ : Type u_7} [comm_ring Rₘ] [comm_ring Sₘ] {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] (ϕ : R →+* S) (hϕ : function.injective ⇑ϕ) (M : submonoid R) (f : localization_map M Rₘ) (g : localization_map (submonoid.map (↑ϕ) M) Sₘ) (hM : submonoid.map (↑ϕ) M ≤ non_zero_divisors S) : function.injective ⇑(localization_map.map f (submonoid.mem_map_of_mem M ↑ϕ) g) := sorry

/-- Injectivity of the underlying `algebra_map` descends to the algebra induced by localization. -/
theorem localization_algebra_injective {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {Rₘ : Type u_6} {Sₘ : Type u_7} [comm_ring Rₘ] [comm_ring Sₘ] [algebra R S] (f : localization_map M Rₘ) (g : localization_map (algebra.algebra_map_submonoid S M) Sₘ) (hRS : function.injective ⇑(algebra_map R S)) (hM : algebra.algebra_map_submonoid S M ≤ non_zero_divisors S) : function.injective ⇑(algebra_map Rₘ Sₘ) :=
  map_injective_of_injective (algebra_map R S) hRS M f g hM

theorem ring_hom.is_integral_elem_localization_at_leading_coeff {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] (f : R →+* S) (x : S) (p : polynomial R) (hf : polynomial.eval₂ f x p = 0) (M : submonoid R) (hM : polynomial.leading_coeff p ∈ M) {Rₘ : Type u_3} {Sₘ : Type u_4} [comm_ring Rₘ] [comm_ring Sₘ] (ϕ : localization_map M Rₘ) (ϕ' : localization_map (submonoid.map (↑f) M) Sₘ) : ring_hom.is_integral_elem (localization_map.map ϕ (submonoid.mem_map_of_mem M ↑f) ϕ')
  (coe_fn (localization_map.to_map ϕ') x) := sorry

/-- Given a particular witness to an element being algebraic over an algebra `R → S`,
We can localize to a submonoid containing the leading coefficient to make it integral.
Explicitly, the map between the localizations will be an integral ring morphism -/
theorem is_integral_localization_at_leading_coeff {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {Rₘ : Type u_6} {Sₘ : Type u_7} [comm_ring Rₘ] [comm_ring Sₘ] [algebra R S] (f : localization_map M Rₘ) (g : localization_map (algebra.algebra_map_submonoid S M) Sₘ) {x : S} (p : polynomial R) (hp : coe_fn (polynomial.aeval x) p = 0) (hM : polynomial.leading_coeff p ∈ M) : ring_hom.is_integral_elem (localization_map.map f algebra.mem_algebra_map_submonoid_of_mem g)
  (coe_fn (localization_map.to_map g) x) :=
  ring_hom.is_integral_elem_localization_at_leading_coeff (algebra_map R S) x p hp M hM f g

/-- If `R → S` is an integral extension, `M` is a submonoid of `R`,
`Rₘ` is the localization of `R` at `M`,
and `Sₘ` is the localization of `S` at the image of `M` under the extension map,
then the induced map `Rₘ → Sₘ` is also an integral extension -/
theorem is_integral_localization {R : Type u_1} [comm_ring R] {M : submonoid R} {S : Type u_2} [comm_ring S] {Rₘ : Type u_6} {Sₘ : Type u_7} [comm_ring Rₘ] [comm_ring Sₘ] [algebra R S] (f : localization_map M Rₘ) (g : localization_map (algebra.algebra_map_submonoid S M) Sₘ) (H : algebra.is_integral R S) : ring_hom.is_integral (localization_map.map f algebra.mem_algebra_map_submonoid_of_mem g) := sorry

theorem is_integral_localization' {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] {f : R →+* S} (hf : ring_hom.is_integral f) (M : submonoid R) : ring_hom.is_integral
  (localization_map.map (localization.of M) (submonoid.mem_map_of_mem M ↑f) (localization.of (submonoid.map (↑f) M))) :=
  is_integral_localization (localization.of M) (localization.of (submonoid.map (↑f) M)) hf

namespace integral_closure


/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
def fraction_map_of_algebraic {A : Type u_4} [integral_domain A] {L : Type u_6} [field L] [algebra A L] (alg : algebra.is_algebraic A L) (inj : ∀ (x : A), coe_fn (algebra_map A L) x = 0 → x = 0) : fraction_map (↥(integral_closure A L)) L :=
  ring_hom.to_localization_map (algebra_map (↥(integral_closure A L)) L) sorry sorry sorry

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
def fraction_map_of_finite_extension {A : Type u_4} [integral_domain A] {K : Type u_5} (L : Type u_6) [field K] [field L] (f : fraction_map A K) [algebra A L] [algebra (localization_map.codomain f) L] [is_scalar_tower A (localization_map.codomain f) L] [finite_dimensional (localization_map.codomain f) L] : fraction_map (↥(integral_closure A L)) L :=
  fraction_map_of_algebraic sorry sorry

end integral_closure


/-- The fraction field of an integral domain as a quotient type. -/
def fraction_ring (A : Type u_4) [integral_domain A]  :=
  localization (non_zero_divisors A)

namespace fraction_ring


/-- Natural hom sending `x : A`, `A` an integral domain, to the equivalence class of
`(x, 1)` in the field of fractions of `A`. -/
def of (A : Type u_4) [integral_domain A] : fraction_map A (localization (non_zero_divisors A)) :=
  localization.of (non_zero_divisors A)

protected instance field {A : Type u_4} [integral_domain A] : field (fraction_ring A) :=
  fraction_map.to_field (of A)

@[simp] theorem mk_eq_div {A : Type u_4} [integral_domain A] {r : A} {s : ↥(non_zero_divisors A)} : localization.mk r s = coe_fn (localization_map.to_map (of A)) r / coe_fn (localization_map.to_map (of A)) ↑s := sorry

/-- Given an integral domain `A` and a localization map to a field of fractions
`f : A →+* K`, we get an `A`-isomorphism between the field of fractions of `A` as a quotient
type and `K`. -/
def alg_equiv_of_quotient {A : Type u_4} [integral_domain A] {K : Type u_1} [field K] (f : fraction_map A K) : alg_equiv A (fraction_ring A) (localization_map.codomain f) :=
  localization.alg_equiv_of_quotient f

protected instance algebra {A : Type u_4} [integral_domain A] : algebra A (fraction_ring A) :=
  ring_hom.to_algebra (localization_map.to_map (of A))

