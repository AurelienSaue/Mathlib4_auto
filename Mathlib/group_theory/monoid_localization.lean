/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.group_theory.congruence
import Mathlib.group_theory.submonoid.default
import Mathlib.algebra.group.units
import Mathlib.algebra.punit_instances
import Mathlib.PostPort

universes u_1 u_2 l u_3 u_4 u_5 u_6 

namespace Mathlib

/-!
# Localizations of commutative monoids

Localizing a commutative ring at one of its submonoids does not rely on the ring's addition, so
we can generalize localizations to commutative monoids.

We characterize the localization of a commutative monoid `M` at a submonoid `S` up to
isomorphism; that is, a commutative monoid `N` is the localization of `M` at `S` iff we can find a
monoid homomorphism `f : M →* N` satisfying 3 properties:
1. For all `y ∈ S`, `f y` is a unit;
2. For all `z : N`, there exists `(x, y) : M × S` such that `z * f y = f x`;
3. For all `x, y : M`, `f x = f y` iff there exists `c ∈ S` such that `x * c = y * c`.

Given such a localization map `f : M →* N`, we can define the surjection
`localization_map.mk'` sending `(x, y) : M × S` to `f x * (f y)⁻¹`, and
`localization_map.lift`, the homomorphism from `N` induced by a homomorphism from `M` which maps
elements of `S` to invertible elements of the codomain. Similarly, given commutative monoids
`P, Q`, a submonoid `T` of `P` and a localization map for `T` from `P` to `Q`, then a homomorphism
`g : M →* P` such that `g(S) ⊆ T` induces a homomorphism of localizations,
`localization_map.map`, from `N` to `Q`.
We treat the special case of localizing away from an element in the sections `away_map` and `away`.

We also define the quotient of `M × S` by the unique congruence relation (equivalence relation
preserving a binary operation) `r` such that for any other congruence relation `s` on `M × S`
satisfying '`∀ y ∈ S`, `(1, 1) ∼ (y, y)` under `s`', we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s`
whenever `(x₁, y₁) ∼ (x₂, y₂)` by `r`. We show this relation is equivalent to the standard
localization relation.
This defines the localization as a quotient type, `localization`, but the majority of
subsequent lemmas in the file are given in terms of localizations up to isomorphism, using maps
which satisfy the characteristic predicate.

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

The infimum form of the localization congruence relation is chosen as 'canonical' here, since it
shortens some proofs.

To apply a localization map `f` as a function, we use `f.to_map`, as coercions don't work well for
this structure.

To reason about the localization as a quotient type, use `mk_eq_monoid_of_mk'` and associated
lemmas. These show the quotient map `mk : M → S → localization S` equals the
surjection `localization_map.mk'` induced by the map
`monoid_of : localization_map S (localization S)` (where `of` establishes the
localization as a quotient type satisfies the characteristic predicate). The lemma
`mk_eq_monoid_of_mk'` hence gives you access to the results in the rest of the file, which are
about the `localization_map.mk'` induced by any localization map.

## Tags
localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid
-/

namespace add_submonoid


/-- The type of add_monoid homomorphisms satisfying the characteristic predicate: if `f : M →+ N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
structure localization_map {M : Type u_1} [add_comm_monoid M] (S : add_submonoid M) (N : Type u_2) [add_comm_monoid N] 
extends M →+ N
where
  map_add_units' : ∀ (y : ↥S), is_add_unit (to_fun ↑y)
  surj' : ∀ (z : N), ∃ (x : M × ↥S), z + to_fun ↑(prod.snd x) = to_fun (prod.fst x)
  eq_iff_exists' : ∀ (x y : M), to_fun x = to_fun y ↔ ∃ (c : ↥S), x + ↑c = y + ↑c

/-- The add_monoid hom underlying a `localization_map` of `add_comm_monoid`s. -/
end add_submonoid


namespace submonoid


/-- The type of monoid homomorphisms satisfying the characteristic predicate: if `f : M →* N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
structure localization_map {M : Type u_1} [comm_monoid M] (S : submonoid M) (N : Type u_2) [comm_monoid N] 
extends M →* N
where
  map_units' : ∀ (y : ↥S), is_unit (to_fun ↑y)
  surj' : ∀ (z : N), ∃ (x : M × ↥S), z * to_fun ↑(prod.snd x) = to_fun (prod.fst x)
  eq_iff_exists' : ∀ (x y : M), to_fun x = to_fun y ↔ ∃ (c : ↥S), x * ↑c = y * ↑c

/-- The monoid hom underlying a `localization_map`. -/
end submonoid


namespace localization


/-- The congruence relation on `M × S`, `M` a `comm_monoid` and `S` a submonoid of `M`, whose
quotient is the localization of `M` at `S`, defined as the unique congruence relation on
`M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,
`(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
`(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/
def Mathlib.add_localization.r {M : Type u_1} [add_comm_monoid M] (S : add_submonoid M) : add_con (M × ↥S) :=
  Inf (set_of fun (c : add_con (M × ↥S)) => ∀ (y : ↥S), coe_fn c 0 (↑y, y))

/-- An alternate form of the congruence relation on `M × S`, `M` a `comm_monoid` and `S` a
submonoid of `M`, whose quotient is the localization of `M` at `S`. -/
def Mathlib.add_localization.r' {M : Type u_1} [add_comm_monoid M] (S : add_submonoid M) : add_con (M × ↥S) :=
  add_con.mk (fun (a b : M × ↥S) => ∃ (c : ↥S), prod.fst a + ↑(prod.snd b) + ↑c = prod.fst b + ↑(prod.snd a) + ↑c) sorry
    sorry

/-- The congruence relation used to localize a `comm_monoid` at a submonoid can be expressed
equivalently as an infimum (see `localization.r`) or explicitly
(see `localization.r'`). -/
theorem r_eq_r' {M : Type u_1} [comm_monoid M] (S : submonoid M) : r S = r' S := sorry

theorem Mathlib.add_localization.r_iff_exists {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {x : M × ↥S} {y : M × ↥S} : coe_fn (add_localization.r S) x y ↔ ∃ (c : ↥S), prod.fst x + ↑(prod.snd y) + ↑c = prod.fst y + ↑(prod.snd x) + ↑c := sorry

end localization


/-- The localization of a `comm_monoid` at one of its submonoids (as a quotient type). -/
def localization {M : Type u_1} [comm_monoid M] (S : submonoid M) :=
  con.quotient sorry

namespace localization


protected instance inhabited {M : Type u_1} [comm_monoid M] (S : submonoid M) : Inhabited (localization S) :=
  con.quotient.inhabited

protected instance comm_monoid {M : Type u_1} [comm_monoid M] (S : submonoid M) : comm_monoid (localization S) :=
  con.comm_monoid (r S)

/-- Given a `comm_monoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to the equivalence
class of `(x, y)` in the localization of `M` at `S`. -/
def Mathlib.add_localization.mk {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} (x : M) (y : ↥S) : add_localization S :=
  coe_fn (add_con.mk' (add_localization.r S)) (x, y)

theorem Mathlib.add_localization.ind {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {p : add_localization S → Prop} (H : ∀ (y : M × ↥S), p (add_localization.mk (prod.fst y) (prod.snd y))) (x : add_localization S) : p x := sorry

theorem Mathlib.add_localization.induction_on {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {p : add_localization S → Prop} (x : add_localization S) (H : ∀ (y : M × ↥S), p (add_localization.mk (prod.fst y) (prod.snd y))) : p x :=
  add_localization.ind H x

theorem induction_on₂ {M : Type u_1} [comm_monoid M] {S : submonoid M} {p : localization S → localization S → Prop} (x : localization S) (y : localization S) (H : ∀ (x y : M × ↥S), p (mk (prod.fst x) (prod.snd x)) (mk (prod.fst y) (prod.snd y))) : p x y :=
  induction_on x fun (x : M × ↥S) => induction_on y (H x)

theorem induction_on₃ {M : Type u_1} [comm_monoid M] {S : submonoid M} {p : localization S → localization S → localization S → Prop} (x : localization S) (y : localization S) (z : localization S) (H : ∀ (x y z : M × ↥S), p (mk (prod.fst x) (prod.snd x)) (mk (prod.fst y) (prod.snd y)) (mk (prod.fst z) (prod.snd z))) : p x y z :=
  induction_on₂ x y fun (x y : M × ↥S) => induction_on z (H x y)

theorem one_rel {M : Type u_1} [comm_monoid M] {S : submonoid M} (y : ↥S) : coe_fn (r S) 1 (↑y, y) :=
  fun (b : con (M × ↥S)) (hb : b ∈ set_of fun (c : con (M × ↥S)) => ∀ (y : ↥S), coe_fn c 1 (↑y, y)) => hb y

theorem Mathlib.add_localization.r_of_eq {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {x : M × ↥S} {y : M × ↥S} (h : prod.fst y + ↑(prod.snd x) = prod.fst x + ↑(prod.snd y)) : coe_fn (add_localization.r S) x y := sorry

end localization


namespace monoid_hom


/-- Makes a localization map from a `comm_monoid` hom satisfying the characteristic predicate. -/
def Mathlib.add_monoid_hom.to_localization_map {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : M →+ N) (H1 : ∀ (y : ↥S), is_add_unit (coe_fn f ↑y)) (H2 : ∀ (z : N), ∃ (x : M × ↥S), z + coe_fn f ↑(prod.snd x) = coe_fn f (prod.fst x)) (H3 : ∀ (x y : M), coe_fn f x = coe_fn f y ↔ ∃ (c : ↥S), x + ↑c = y + ↑c) : add_submonoid.localization_map S N :=
  add_submonoid.localization_map.mk (add_monoid_hom.to_fun f) sorry sorry H1 H2 H3

end monoid_hom


namespace submonoid


namespace localization_map


/-- Short for `to_monoid_hom`; used to apply a localization map as a function. -/
def to_map {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) : M →* N :=
  to_monoid_hom f

theorem Mathlib.add_submonoid.localization_map.ext {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {f : add_submonoid.localization_map S N} {g : add_submonoid.localization_map S N} (h : ∀ (x : M), coe_fn (add_submonoid.localization_map.to_map f) x = coe_fn (add_submonoid.localization_map.to_map g) x) : f = g := sorry

theorem ext_iff {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {f : localization_map S N} {g : localization_map S N} : f = g ↔ ∀ (x : M), coe_fn (to_map f) x = coe_fn (to_map g) x :=
  { mp := fun (h : f = g) (x : M) => h ▸ rfl, mpr := ext }

theorem to_map_injective {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] : function.injective to_map :=
  fun (_x _x_1 : localization_map S N) (h : to_map _x = to_map _x_1) => ext (iff.mp monoid_hom.ext_iff h)

theorem map_units {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) (y : ↥S) : is_unit (coe_fn (to_map f) ↑y) :=
  map_units' f y

theorem surj {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) (z : N) : ∃ (x : M × ↥S), z * coe_fn (to_map f) ↑(prod.snd x) = coe_fn (to_map f) (prod.fst x) :=
  surj' f z

theorem eq_iff_exists {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) {x : M} {y : M} : coe_fn (to_map f) x = coe_fn (to_map f) y ↔ ∃ (c : ↥S), x * ↑c = y * ↑c :=
  eq_iff_exists' f x y

/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
def sec {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) (z : N) : M × ↥S :=
  classical.some (surj f z)

theorem Mathlib.add_submonoid.localization_map.sec_spec {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {f : add_submonoid.localization_map S N} (z : N) : z + coe_fn (add_submonoid.localization_map.to_map f) ↑(prod.snd (add_submonoid.localization_map.sec f z)) =
  coe_fn (add_submonoid.localization_map.to_map f) (prod.fst (add_submonoid.localization_map.sec f z)) :=
  classical.some_spec (add_submonoid.localization_map.surj f z)

theorem Mathlib.add_submonoid.localization_map.sec_spec' {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {f : add_submonoid.localization_map S N} (z : N) : coe_fn (add_submonoid.localization_map.to_map f) (prod.fst (add_submonoid.localization_map.sec f z)) =
  coe_fn (add_submonoid.localization_map.to_map f) ↑(prod.snd (add_submonoid.localization_map.sec f z)) + z := sorry

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`w : M, z : N` and `y ∈ S`, we have `w * (f y)⁻¹ = z ↔ w = f y * z`. -/
theorem Mathlib.add_submonoid.localization_map.add_neg_left {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {f : M →+ N} (h : ∀ (y : ↥S), is_add_unit (coe_fn f ↑y)) (y : ↥S) (w : N) (z : N) : w + ↑(-coe_fn (is_add_unit.lift_right (add_monoid_hom.mrestrict f S) h) y) = z ↔ w = coe_fn f ↑y + z := sorry

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`w : M, z : N` and `y ∈ S`, we have `z = w * (f y)⁻¹ ↔ z * f y = w`. -/
theorem mul_inv_right {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {f : M →* N} (h : ∀ (y : ↥S), is_unit (coe_fn f ↑y)) (y : ↥S) (w : N) (z : N) : z = w * ↑(coe_fn (is_unit.lift_right (monoid_hom.mrestrict f S) h) y⁻¹) ↔ z * coe_fn f ↑y = w := sorry

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that
`f(S) ⊆ units N`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have
`f x₁ * (f y₁)⁻¹ = f x₂ * (f y₂)⁻¹ ↔ f (x₁ * y₂) = f (x₂ * y₁)`. -/
@[simp] theorem mul_inv {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {f : M →* N} (h : ∀ (y : ↥S), is_unit (coe_fn f ↑y)) {x₁ : M} {x₂ : M} {y₁ : ↥S} {y₂ : ↥S} : coe_fn f x₁ * ↑(coe_fn (is_unit.lift_right (monoid_hom.mrestrict f S) h) y₁⁻¹) =
    coe_fn f x₂ * ↑(coe_fn (is_unit.lift_right (monoid_hom.mrestrict f S) h) y₂⁻¹) ↔
  coe_fn f (x₁ * ↑y₂) = coe_fn f (x₂ * ↑y₁) := sorry

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`y, z ∈ S`, we have `(f y)⁻¹ = (f z)⁻¹ → f y = f z`. -/
theorem Mathlib.add_submonoid.localization_map.neg_inj {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {f : M →+ N} (hf : ∀ (y : ↥S), is_add_unit (coe_fn f ↑y)) {y : ↥S} {z : ↥S} (h : -coe_fn (is_add_unit.lift_right (add_monoid_hom.mrestrict f S) hf) y =
  -coe_fn (is_add_unit.lift_right (add_monoid_hom.mrestrict f S) hf) z) : coe_fn f ↑y = coe_fn f ↑z := sorry

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`y ∈ S`, `(f y)⁻¹` is unique. -/
theorem Mathlib.add_submonoid.localization_map.neg_unique {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {f : M →+ N} (h : ∀ (y : ↥S), is_add_unit (coe_fn f ↑y)) {y : ↥S} {z : N} (H : coe_fn f ↑y + z = 0) : ↑(-coe_fn (is_add_unit.lift_right (add_monoid_hom.mrestrict f S) h) y) = z := sorry

theorem map_right_cancel {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) {x : M} {y : M} {c : ↥S} (h : coe_fn (to_map f) (↑c * x) = coe_fn (to_map f) (↑c * y)) : coe_fn (to_map f) x = coe_fn (to_map f) y := sorry

theorem Mathlib.add_submonoid.localization_map.map_left_cancel {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) {x : M} {y : M} {c : ↥S} (h : coe_fn (add_submonoid.localization_map.to_map f) (x + ↑c) = coe_fn (add_submonoid.localization_map.to_map f) (y + ↑c)) : coe_fn (add_submonoid.localization_map.to_map f) x = coe_fn (add_submonoid.localization_map.to_map f) y := sorry

/-- Given a localization map `f : M →* N`, the surjection sending `(x, y) : M × S` to
`f x * (f y)⁻¹`. -/
def mk' {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) (x : M) (y : ↥S) : N :=
  coe_fn (to_map f) x * ↑(coe_fn (is_unit.lift_right (monoid_hom.mrestrict (to_map f) S) (map_units f)) y⁻¹)

theorem Mathlib.add_submonoid.localization_map.mk'_add {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) (x₁ : M) (x₂ : M) (y₁ : ↥S) (y₂ : ↥S) : add_submonoid.localization_map.mk' f (x₁ + x₂) (y₁ + y₂) =
  add_submonoid.localization_map.mk' f x₁ y₁ + add_submonoid.localization_map.mk' f x₂ y₂ := sorry

theorem mk'_one {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) (x : M) : mk' f x 1 = coe_fn (to_map f) x := sorry

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, for all `z : N` we have that if
`x : M, y ∈ S` are such that `z * f y = f x`, then `f x * (f y)⁻¹ = z`. -/
@[simp] theorem Mathlib.add_submonoid.localization_map.mk'_sec {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) (z : N) : add_submonoid.localization_map.mk' f (prod.fst (add_submonoid.localization_map.sec f z))
    (prod.snd (add_submonoid.localization_map.sec f z)) =
  z := sorry

theorem mk'_surjective {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) (z : N) : ∃ (x : M), ∃ (y : ↥S), mk' f x y = z :=
  Exists.intro (prod.fst (sec f z)) (Exists.intro (prod.snd (sec f z)) (mk'_sec f z))

theorem mk'_spec {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) (x : M) (y : ↥S) : mk' f x y * coe_fn (to_map f) ↑y = coe_fn (to_map f) x := sorry

theorem mk'_spec' {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) (x : M) (y : ↥S) : coe_fn (to_map f) ↑y * mk' f x y = coe_fn (to_map f) x := sorry

theorem eq_mk'_iff_mul_eq {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) {x : M} {y : ↥S} {z : N} : z = mk' f x y ↔ z * coe_fn (to_map f) ↑y = coe_fn (to_map f) x := sorry

theorem Mathlib.add_submonoid.localization_map.mk'_eq_iff_eq_add {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) {x : M} {y : ↥S} {z : N} : add_submonoid.localization_map.mk' f x y = z ↔
  coe_fn (add_submonoid.localization_map.to_map f) x = z + coe_fn (add_submonoid.localization_map.to_map f) ↑y := sorry

theorem Mathlib.add_submonoid.localization_map.mk'_eq_iff_eq {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) {x₁ : M} {x₂ : M} {y₁ : ↥S} {y₂ : ↥S} : add_submonoid.localization_map.mk' f x₁ y₁ = add_submonoid.localization_map.mk' f x₂ y₂ ↔
  coe_fn (add_submonoid.localization_map.to_map f) (x₁ + ↑y₂) =
    coe_fn (add_submonoid.localization_map.to_map f) (x₂ + ↑y₁) := sorry

protected theorem eq {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) {a₁ : M} {b₁ : M} {a₂ : ↥S} {b₂ : ↥S} : mk' f a₁ a₂ = mk' f b₁ b₂ ↔ ∃ (c : ↥S), a₁ * ↑b₂ * ↑c = b₁ * ↑a₂ * ↑c :=
  iff.trans (mk'_eq_iff_eq f) (eq_iff_exists f)

protected theorem eq' {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) {a₁ : M} {b₁ : M} {a₂ : ↥S} {b₂ : ↥S} : mk' f a₁ a₂ = mk' f b₁ b₂ ↔ coe_fn (localization.r S) (a₁, a₂) (b₁, b₂) := sorry

theorem Mathlib.add_submonoid.localization_map.eq_iff_eq {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) (g : add_submonoid.localization_map S P) {x : M} {y : M} : coe_fn (add_submonoid.localization_map.to_map f) x = coe_fn (add_submonoid.localization_map.to_map f) y ↔
  coe_fn (add_submonoid.localization_map.to_map g) x = coe_fn (add_submonoid.localization_map.to_map g) y :=
  iff.trans (add_submonoid.localization_map.eq_iff_exists f) (iff.symm (add_submonoid.localization_map.eq_iff_exists g))

theorem mk'_eq_iff_mk'_eq {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) (g : localization_map S P) {x₁ : M} {x₂ : M} {y₁ : ↥S} {y₂ : ↥S} : mk' f x₁ y₁ = mk' f x₂ y₂ ↔ mk' g x₁ y₁ = mk' g x₂ y₂ :=
  iff.trans (localization_map.eq' f) (iff.symm (localization_map.eq' g))

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, for all `x₁ : M` and `y₁ ∈ S`,
if `x₂ : M, y₂ ∈ S` are such that `f x₁ * (f y₁)⁻¹ * f y₂ = f x₂`, then there exists `c ∈ S`
such that `x₁ * y₂ * c = x₂ * y₁ * c`. -/
theorem Mathlib.add_submonoid.localization_map.exists_of_sec_mk' {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) (x : M) (y : ↥S) : ∃ (c : ↥S),
  x + ↑(prod.snd (add_submonoid.localization_map.sec f (add_submonoid.localization_map.mk' f x y))) + ↑c =
    prod.fst (add_submonoid.localization_map.sec f (add_submonoid.localization_map.mk' f x y)) + ↑y + ↑c :=
  iff.mp (add_submonoid.localization_map.eq_iff_exists f)
    (iff.mp (add_submonoid.localization_map.mk'_eq_iff_eq f)
      (Eq.symm (add_submonoid.localization_map.mk'_sec f (add_submonoid.localization_map.mk' f x y))))

theorem mk'_eq_of_eq {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) {a₁ : M} {b₁ : M} {a₂ : ↥S} {b₂ : ↥S} (H : b₁ * ↑a₂ = a₁ * ↑b₂) : mk' f a₁ a₂ = mk' f b₁ b₂ :=
  iff.mpr (mk'_eq_iff_eq f) (H ▸ rfl)

@[simp] theorem Mathlib.add_submonoid.localization_map.mk'_self' {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) (y : ↥S) : add_submonoid.localization_map.mk' f (↑y) y = 0 := sorry

@[simp] theorem mk'_self {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) (x : M) (H : x ∈ S) : mk' f x { val := x, property := H } = 1 := sorry

theorem mul_mk'_eq_mk'_of_mul {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) (x₁ : M) (x₂ : M) (y : ↥S) : coe_fn (to_map f) x₁ * mk' f x₂ y = mk' f (x₁ * x₂) y := sorry

theorem Mathlib.add_submonoid.localization_map.mk'_add_eq_mk'_of_add {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) (x₁ : M) (x₂ : M) (y : ↥S) : add_submonoid.localization_map.mk' f x₂ y + coe_fn (add_submonoid.localization_map.to_map f) x₁ =
  add_submonoid.localization_map.mk' f (x₁ + x₂) y := sorry

theorem Mathlib.add_submonoid.localization_map.add_mk'_zero_eq_mk' {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) (x : M) (y : ↥S) : coe_fn (add_submonoid.localization_map.to_map f) x + add_submonoid.localization_map.mk' f 0 y =
  add_submonoid.localization_map.mk' f x y := sorry

@[simp] theorem mk'_mul_cancel_right {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) (x : M) (y : ↥S) : mk' f (x * ↑y) y = coe_fn (to_map f) x := sorry

theorem Mathlib.add_submonoid.localization_map.mk'_add_cancel_left {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) (x : M) (y : ↥S) : add_submonoid.localization_map.mk' f (↑y + x) y = coe_fn (add_submonoid.localization_map.to_map f) x := sorry

theorem is_unit_comp {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) (j : N →* P) (y : ↥S) : is_unit (coe_fn (monoid_hom.comp j (to_map f)) ↑y) := sorry

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
`g : M →* P` such that `g(S) ⊆ units P`, `f x = f y → g x = g y` for all `x y : M`. -/
theorem eq_of_eq {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} (hg : ∀ (y : ↥S), is_unit (coe_fn g ↑y)) {x : M} {y : M} (h : coe_fn (to_map f) x = coe_fn (to_map f) y) : coe_fn g x = coe_fn g y := sorry

/-- Given `comm_monoid`s `M, P`, localization maps `f : M →* N, k : P →* Q` for submonoids
`S, T` respectively, and `g : M →* P` such that `g(S) ⊆ T`, `f x = f y` implies
`k (g x) = k (g y)`. -/
theorem comp_eq_of_eq {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} {T : submonoid P} {Q : Type u_4} [comm_monoid Q] (hg : ∀ (y : ↥S), coe_fn g ↑y ∈ T) (k : localization_map T Q) {x : M} {y : M} (h : coe_fn (to_map f) x = coe_fn (to_map f) y) : coe_fn (to_map k) (coe_fn g x) = coe_fn (to_map k) (coe_fn g y) := sorry

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S` are such that
`z = f x * (f y)⁻¹`. -/
def lift {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} (hg : ∀ (y : ↥S), is_unit (coe_fn g ↑y)) : N →* P :=
  monoid_hom.mk
    (fun (z : N) =>
      coe_fn g (prod.fst (sec f z)) * ↑(coe_fn (is_unit.lift_right (monoid_hom.mrestrict g S) hg) (prod.snd (sec f z))⁻¹))
    sorry sorry

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : M, y ∈ S`. -/
theorem lift_mk' {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} (hg : ∀ (y : ↥S), is_unit (coe_fn g ↑y)) (x : M) (y : ↥S) : coe_fn (lift f hg) (mk' f x y) = coe_fn g x * ↑(coe_fn (is_unit.lift_right (monoid_hom.mrestrict g S) hg) y⁻¹) := sorry

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v : P`, we have
`f.lift hg z = v ↔ g x = g y * v`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
theorem Mathlib.add_submonoid.localization_map.lift_spec {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {g : M →+ P} (hg : ∀ (y : ↥S), is_add_unit (coe_fn g ↑y)) (z : N) (v : P) : coe_fn (add_submonoid.localization_map.lift f hg) z = v ↔
  coe_fn g (prod.fst (add_submonoid.localization_map.sec f z)) =
    coe_fn g ↑(prod.snd (add_submonoid.localization_map.sec f z)) + v :=
  add_submonoid.localization_map.add_neg_left hg (prod.snd (add_submonoid.localization_map.sec f z))
    (coe_fn g (prod.fst (add_submonoid.localization_map.sec f z))) v

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v w : P`, we have
`f.lift hg z * w = v ↔ g x * w = g y * v`, where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
theorem Mathlib.add_submonoid.localization_map.lift_spec_add {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {g : M →+ P} (hg : ∀ (y : ↥S), is_add_unit (coe_fn g ↑y)) (z : N) (w : P) (v : P) : coe_fn (add_submonoid.localization_map.lift f hg) z + w = v ↔
  coe_fn g (prod.fst (add_submonoid.localization_map.sec f z)) + w =
    coe_fn g ↑(prod.snd (add_submonoid.localization_map.sec f z)) + v := sorry

theorem lift_mk'_spec {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} (hg : ∀ (y : ↥S), is_unit (coe_fn g ↑y)) (x : M) (v : P) (y : ↥S) : coe_fn (lift f hg) (mk' f x y) = v ↔ coe_fn g x = coe_fn g ↑y * v :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (coe_fn (lift f hg) (mk' f x y) = v ↔ coe_fn g x = coe_fn g ↑y * v)) (lift_mk' f hg x y)))
    (mul_inv_left hg y (coe_fn g x) v)

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`f.lift hg z * g y = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
theorem lift_mul_right {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} (hg : ∀ (y : ↥S), is_unit (coe_fn g ↑y)) (z : N) : coe_fn (lift f hg) z * coe_fn g ↑(prod.snd (sec f z)) = coe_fn g (prod.fst (sec f z)) := sorry

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`g y * f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
theorem Mathlib.add_submonoid.localization_map.lift_add_left {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {g : M →+ P} (hg : ∀ (y : ↥S), is_add_unit (coe_fn g ↑y)) (z : N) : coe_fn g ↑(prod.snd (add_submonoid.localization_map.sec f z)) + coe_fn (add_submonoid.localization_map.lift f hg) z =
  coe_fn g (prod.fst (add_submonoid.localization_map.sec f z)) := sorry

@[simp] theorem lift_eq {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} (hg : ∀ (y : ↥S), is_unit (coe_fn g ↑y)) (x : M) : coe_fn (lift f hg) (coe_fn (to_map f) x) = coe_fn g x := sorry

theorem Mathlib.add_submonoid.localization_map.lift_eq_iff {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {g : M →+ P} (hg : ∀ (y : ↥S), is_add_unit (coe_fn g ↑y)) {x : M × ↥S} {y : M × ↥S} : coe_fn (add_submonoid.localization_map.lift f hg) (add_submonoid.localization_map.mk' f (prod.fst x) (prod.snd x)) =
    coe_fn (add_submonoid.localization_map.lift f hg) (add_submonoid.localization_map.mk' f (prod.fst y) (prod.snd y)) ↔
  coe_fn g (prod.fst x + ↑(prod.snd y)) = coe_fn g (prod.fst y + ↑(prod.snd x)) := sorry

@[simp] theorem Mathlib.add_submonoid.localization_map.lift_comp {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {g : M →+ P} (hg : ∀ (y : ↥S), is_add_unit (coe_fn g ↑y)) : add_monoid_hom.comp (add_submonoid.localization_map.lift f hg) (add_submonoid.localization_map.to_map f) = g :=
  add_monoid_hom.ext fun (x : M) => add_submonoid.localization_map.lift_eq f hg x

@[simp] theorem lift_of_comp {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) (j : N →* P) : lift f (is_unit_comp f j) = j := sorry

theorem epic_of_localization_map {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {j : N →* P} {k : N →* P} (h : ∀ (a : M), coe_fn (monoid_hom.comp j (to_map f)) a = coe_fn (monoid_hom.comp k (to_map f)) a) : j = k := sorry

theorem Mathlib.add_submonoid.localization_map.lift_unique {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {g : M →+ P} (hg : ∀ (y : ↥S), is_add_unit (coe_fn g ↑y)) {j : N →+ P} (hj : ∀ (x : M), coe_fn j (coe_fn (add_submonoid.localization_map.to_map f) x) = coe_fn g x) : add_submonoid.localization_map.lift f hg = j := sorry

@[simp] theorem Mathlib.add_submonoid.localization_map.lift_id {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) (x : N) : coe_fn (add_submonoid.localization_map.lift f (add_submonoid.localization_map.map_units f)) x = x :=
  iff.mp add_monoid_hom.ext_iff (add_submonoid.localization_map.lift_of_comp f (add_monoid_hom.id N)) x

/-- Given two localization maps `f : M →* N, k : M →* P` for a submonoid `S ⊆ M`,
the hom from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P`
induced by `k`. -/
@[simp] theorem lift_left_inverse {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {k : localization_map S P} (z : N) : coe_fn (lift k (map_units f)) (coe_fn (lift f (map_units k)) z) = z := sorry

theorem lift_surjective_iff {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} (hg : ∀ (y : ↥S), is_unit (coe_fn g ↑y)) : function.surjective ⇑(lift f hg) ↔ ∀ (v : P), ∃ (x : M × ↥S), v * coe_fn g ↑(prod.snd x) = coe_fn g (prod.fst x) := sorry

theorem lift_injective_iff {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} (hg : ∀ (y : ↥S), is_unit (coe_fn g ↑y)) : function.injective ⇑(lift f hg) ↔ ∀ (x y : M), coe_fn (to_map f) x = coe_fn (to_map f) y ↔ coe_fn g x = coe_fn g y := sorry

/-- Given a `comm_monoid` homomorphism `g : M →* P` where for submonoids `S ⊆ M, T ⊆ P` we have
`g(S) ⊆ T`, the induced monoid homomorphism from the localization of `M` at `S` to the
localization of `P` at `T`: if `f : M →* N` and `k : P →* Q` are localization maps for `S` and
`T` respectively, we send `z : N` to `k (g x) * (k (g y))⁻¹`, where `(x, y) : M × S` are such
that `z = f x * (f y)⁻¹`. -/
def map {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} {T : submonoid P} (hy : ∀ (y : ↥S), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_monoid Q] (k : localization_map T Q) : N →* Q :=
  lift f sorry

theorem Mathlib.add_submonoid.localization_map.map_eq {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {g : M →+ P} {T : add_submonoid P} (hy : ∀ (y : ↥S), coe_fn g ↑y ∈ T) {Q : Type u_4} [add_comm_monoid Q] {k : add_submonoid.localization_map T Q} (x : M) : coe_fn (add_submonoid.localization_map.map f hy k) (coe_fn (add_submonoid.localization_map.to_map f) x) =
  coe_fn (add_submonoid.localization_map.to_map k) (coe_fn g x) :=
  add_submonoid.localization_map.lift_eq f
    (fun (y : ↥S) => add_submonoid.localization_map.map_units k { val := coe_fn g ↑y, property := hy y }) x

@[simp] theorem Mathlib.add_submonoid.localization_map.map_comp {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {g : M →+ P} {T : add_submonoid P} (hy : ∀ (y : ↥S), coe_fn g ↑y ∈ T) {Q : Type u_4} [add_comm_monoid Q] {k : add_submonoid.localization_map T Q} : add_monoid_hom.comp (add_submonoid.localization_map.map f hy k) (add_submonoid.localization_map.to_map f) =
  add_monoid_hom.comp (add_submonoid.localization_map.to_map k) g :=
  add_submonoid.localization_map.lift_comp f
    fun (y : ↥S) => add_submonoid.localization_map.map_units k { val := coe_fn g ↑y, property := hy y }

theorem map_mk' {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} {T : submonoid P} (hy : ∀ (y : ↥S), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_monoid Q] {k : localization_map T Q} (x : M) (y : ↥S) : coe_fn (map f hy k) (mk' f x y) = mk' k (coe_fn g x) { val := coe_fn g ↑y, property := hy y } := sorry

/-- Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
`comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
`u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) * u` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
theorem map_spec {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} {T : submonoid P} (hy : ∀ (y : ↥S), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_monoid Q] {k : localization_map T Q} (z : N) (u : Q) : coe_fn (map f hy k) z = u ↔
  coe_fn (to_map k) (coe_fn g (prod.fst (sec f z))) = coe_fn (to_map k) (coe_fn g ↑(prod.snd (sec f z))) * u :=
  lift_spec f (fun (y : ↥S) => map_units k { val := coe_fn g ↑y, property := hy y }) z u

/-- Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
`comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `f.map hy k z * k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
theorem map_mul_right {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} {T : submonoid P} (hy : ∀ (y : ↥S), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_monoid Q] {k : localization_map T Q} (z : N) : coe_fn (map f hy k) z * coe_fn (to_map k) (coe_fn g ↑(prod.snd (sec f z))) =
  coe_fn (to_map k) (coe_fn g (prod.fst (sec f z))) :=
  lift_mul_right f (fun (y : ↥S) => map_units k { val := coe_fn g ↑y, property := hy y }) z

/-- Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
`comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `k (g y) * f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
theorem Mathlib.add_submonoid.localization_map.map_add_left {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {g : M →+ P} {T : add_submonoid P} (hy : ∀ (y : ↥S), coe_fn g ↑y ∈ T) {Q : Type u_4} [add_comm_monoid Q] {k : add_submonoid.localization_map T Q} (z : N) : coe_fn (add_submonoid.localization_map.to_map k) (coe_fn g ↑(prod.snd (add_submonoid.localization_map.sec f z))) +
    coe_fn (add_submonoid.localization_map.map f hy k) z =
  coe_fn (add_submonoid.localization_map.to_map k) (coe_fn g (prod.fst (add_submonoid.localization_map.sec f z))) := sorry

@[simp] theorem Mathlib.add_submonoid.localization_map.map_id {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) (z : N) : coe_fn
    (add_submonoid.localization_map.map f
      (fun (y : ↥S) => (fun (this : coe_fn (add_monoid_hom.id M) ↑y ∈ S) => this) (subtype.property y)) f)
    z =
  z :=
  add_submonoid.localization_map.lift_id f z

/-- If `comm_monoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_comp_map {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {g : M →* P} {T : submonoid P} (hy : ∀ (y : ↥S), coe_fn g ↑y ∈ T) {Q : Type u_4} [comm_monoid Q] {k : localization_map T Q} {A : Type u_5} [comm_monoid A] {U : submonoid A} {R : Type u_6} [comm_monoid R] (j : localization_map U R) {l : P →* A} (hl : ∀ (w : ↥T), coe_fn l ↑w ∈ U) : monoid_hom.comp (map k hl j) (map f hy k) =
  map f
    (fun (x : ↥S) =>
      (fun (this : coe_fn (monoid_hom.comp l g) ↑x ∈ U) => this) (hl { val := coe_fn g ↑x, property := hy x }))
    j := sorry

/-- If `comm_monoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem Mathlib.add_submonoid.localization_map.map_map {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {g : M →+ P} {T : add_submonoid P} (hy : ∀ (y : ↥S), coe_fn g ↑y ∈ T) {Q : Type u_4} [add_comm_monoid Q] {k : add_submonoid.localization_map T Q} {A : Type u_5} [add_comm_monoid A] {U : add_submonoid A} {R : Type u_6} [add_comm_monoid R] (j : add_submonoid.localization_map U R) {l : P →+ A} (hl : ∀ (w : ↥T), coe_fn l ↑w ∈ U) (x : N) : coe_fn (add_submonoid.localization_map.map k hl j) (coe_fn (add_submonoid.localization_map.map f hy k) x) =
  coe_fn
    (add_submonoid.localization_map.map f
      (fun (x : ↥S) =>
        (fun (this : coe_fn (add_monoid_hom.comp l g) ↑x ∈ U) => this) (hl { val := coe_fn g ↑x, property := hy x }))
      j)
    x := sorry

/-- Given `x : M`, the type of `comm_monoid` homomorphisms `f : M →* N` such that `N`
is isomorphic to the localization of `M` at the submonoid generated by `x`. -/
def away_map {M : Type u_1} [comm_monoid M] (x : M) (N' : Type u_2) [comm_monoid N'] :=
  localization_map (powers x) N'

/-- Given `x : M` and a localization map `F : M →* N` away from `x`, `inv_self` is `(F x)⁻¹`. -/
def away_map.inv_self {M : Type u_1} [comm_monoid M] {N : Type u_2} [comm_monoid N] (x : M) (F : away_map x N) : N :=
  mk' F 1 { val := x, property := sorry }

/-- Given `x : M`, a localization map `F : M →* N` away from `x`, and a map of `comm_monoid`s
`g : M →* P` such that `g x` is invertible, the homomorphism induced from `N` to `P` sending
`z : N` to `g y * (g x)⁻ⁿ`, where `y : M, n : ℕ` are such that `z = F y * (F x)⁻ⁿ`. -/
def away_map.lift {M : Type u_1} [comm_monoid M] {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] {g : M →* P} (x : M) (F : away_map x N) (hg : is_unit (coe_fn g x)) : N →* P :=
  lift F sorry

@[simp] theorem away_map.lift_eq {M : Type u_1} [comm_monoid M] {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] {g : M →* P} (x : M) (F : away_map x N) (hg : is_unit (coe_fn g x)) (a : M) : coe_fn (away_map.lift x F hg) (coe_fn (to_map F) a) = coe_fn g a :=
  lift_eq F (away_map.lift._proof_1 x hg) a

@[simp] theorem away_map.lift_comp {M : Type u_1} [comm_monoid M] {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] {g : M →* P} (x : M) (F : away_map x N) (hg : is_unit (coe_fn g x)) : monoid_hom.comp (away_map.lift x F hg) (to_map F) = g :=
  lift_comp F (away_map.lift._proof_1 x hg)

/-- Given `x y : M` and localization maps `F : M →* N, G : M →* P` away from `x` and `x * y`
respectively, the homomorphism induced from `N` to `P`. -/
def away_to_away_right {M : Type u_1} [comm_monoid M] {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (x : M) (F : away_map x N) (y : M) (G : away_map (x * y) P) : N →* P :=
  away_map.lift x F sorry

end localization_map


end submonoid


namespace add_submonoid


namespace localization_map


/-- Given `x : A` and a localization map `F : A →+ B` away from `x`, `neg_self` is `- (F x)`. -/
def away_map.neg_self {A : Type u_4} [add_comm_monoid A] (x : A) {B : Type u_5} [add_comm_monoid B] (F : away_map x B) : B :=
  mk' F 0 { val := x, property := sorry }

/-- Given `x : A`, a localization map `F : A →+ B` away from `x`, and a map of `add_comm_monoid`s
`g : A →+ C` such that `g x` is invertible, the homomorphism induced from `B` to `C` sending
`z : B` to `g y - n • g x`, where `y : A, n : ℕ` are such that `z = F y - n • F x`. -/
def away_map.lift {A : Type u_4} [add_comm_monoid A] (x : A) {B : Type u_5} [add_comm_monoid B] (F : away_map x B) {C : Type u_6} [add_comm_monoid C] {g : A →+ C} (hg : is_add_unit (coe_fn g x)) : B →+ C :=
  lift F sorry

@[simp] theorem away_map.lift_eq {A : Type u_4} [add_comm_monoid A] (x : A) {B : Type u_5} [add_comm_monoid B] (F : away_map x B) {C : Type u_6} [add_comm_monoid C] {g : A →+ C} (hg : is_add_unit (coe_fn g x)) (a : A) : coe_fn (away_map.lift x F hg) (coe_fn (to_map F) a) = coe_fn g a :=
  lift_eq F (away_map.lift._proof_1 x hg) a

@[simp] theorem away_map.lift_comp {A : Type u_4} [add_comm_monoid A] (x : A) {B : Type u_5} [add_comm_monoid B] (F : away_map x B) {C : Type u_6} [add_comm_monoid C] {g : A →+ C} (hg : is_add_unit (coe_fn g x)) : add_monoid_hom.comp (away_map.lift x F hg) (to_map F) = g :=
  lift_comp F (away_map.lift._proof_1 x hg)

/-- Given `x y : A` and localization maps `F : A →+ B, G : A →+ C` away from `x` and `x + y`
respectively, the homomorphism induced from `B` to `C`. -/
def away_to_away_right {A : Type u_4} [add_comm_monoid A] (x : A) {B : Type u_5} [add_comm_monoid B] (F : away_map x B) {C : Type u_6} [add_comm_monoid C] (y : A) (G : away_map (x + y) C) : B →+ C :=
  away_map.lift x F sorry

end localization_map


end add_submonoid


namespace submonoid


namespace localization_map


/-- If `f : M →* N` and `k : M →* P` are localization maps for a submonoid `S`, we get an
isomorphism of `N` and `P`. -/
def mul_equiv_of_localizations {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) (k : localization_map S P) : N ≃* P :=
  mul_equiv.mk (⇑(lift f (map_units k))) (⇑(lift k (map_units f))) (lift_left_inverse f) (lift_left_inverse k) sorry

@[simp] theorem Mathlib.add_submonoid.localization_map.add_equiv_of_localizations_apply {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {k : add_submonoid.localization_map S P} {x : N} : coe_fn (add_submonoid.localization_map.add_equiv_of_localizations f k) x =
  coe_fn (add_submonoid.localization_map.lift f (add_submonoid.localization_map.map_units k)) x :=
  rfl

@[simp] theorem Mathlib.add_submonoid.localization_map.add_equiv_of_localizations_symm_apply {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {k : add_submonoid.localization_map S P} {x : P} : coe_fn (add_equiv.symm (add_submonoid.localization_map.add_equiv_of_localizations f k)) x =
  coe_fn (add_submonoid.localization_map.lift k (add_submonoid.localization_map.map_units f)) x :=
  rfl

theorem Mathlib.add_submonoid.localization_map.add_equiv_of_localizations_symm_eq_add_equiv_of_localizations {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {k : add_submonoid.localization_map S P} : add_equiv.symm (add_submonoid.localization_map.add_equiv_of_localizations k f) =
  add_submonoid.localization_map.add_equiv_of_localizations f k :=
  rfl

/-- If `f : M →* N` is a localization map for a submonoid `S` and `k : N ≃* P` is an isomorphism
of `comm_monoid`s, `k ∘ f` is a localization map for `M` at `S`. -/
def of_mul_equiv_of_localizations {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) (k : N ≃* P) : localization_map S P :=
  monoid_hom.to_localization_map (monoid_hom.comp (mul_equiv.to_monoid_hom k) (to_map f)) sorry sorry sorry

@[simp] theorem Mathlib.add_submonoid.localization_map.of_add_equiv_of_localizations_apply {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {k : N ≃+ P} (x : M) : coe_fn (add_submonoid.localization_map.to_map (add_submonoid.localization_map.of_add_equiv_of_localizations f k)) x =
  coe_fn k (coe_fn (add_submonoid.localization_map.to_map f) x) :=
  rfl

theorem of_mul_equiv_of_localizations_eq {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {k : N ≃* P} : to_map (of_mul_equiv_of_localizations f k) = monoid_hom.comp (mul_equiv.to_monoid_hom k) (to_map f) :=
  rfl

theorem symm_comp_of_mul_equiv_of_localizations_apply {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {k : N ≃* P} (x : M) : coe_fn (mul_equiv.symm k) (coe_fn (to_map (of_mul_equiv_of_localizations f k)) x) = coe_fn (to_map f) x :=
  mul_equiv.symm_apply_apply k (coe_fn (to_map f) x)

theorem symm_comp_of_mul_equiv_of_localizations_apply' {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {k : P ≃* N} (x : M) : coe_fn k (coe_fn (to_map (of_mul_equiv_of_localizations f (mul_equiv.symm k))) x) = coe_fn (to_map f) x :=
  mul_equiv.apply_symm_apply k (coe_fn (to_map f) x)

theorem of_mul_equiv_of_localizations_eq_iff_eq {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {k : N ≃* P} {x : M} {y : P} : coe_fn (to_map (of_mul_equiv_of_localizations f k)) x = y ↔ coe_fn (to_map f) x = coe_fn (mul_equiv.symm k) y :=
  iff.symm (equiv.eq_symm_apply (mul_equiv.to_equiv k))

theorem mul_equiv_of_localizations_right_inv {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) (k : localization_map S P) : of_mul_equiv_of_localizations f (mul_equiv_of_localizations f k) = k :=
  to_map_injective (lift_comp f (map_units k))

theorem Mathlib.add_submonoid.localization_map.add_equiv_of_localizations_right_inv_apply {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {k : add_submonoid.localization_map S P} {x : M} : coe_fn
    (add_submonoid.localization_map.to_map
      (add_submonoid.localization_map.of_add_equiv_of_localizations f
        (add_submonoid.localization_map.add_equiv_of_localizations f k)))
    x =
  coe_fn (add_submonoid.localization_map.to_map k) x :=
  iff.mp add_submonoid.localization_map.ext_iff (add_submonoid.localization_map.add_equiv_of_localizations_right_inv f k)
    x

theorem Mathlib.add_submonoid.localization_map.add_equiv_of_localizations_left_neg {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) (k : N ≃+ P) : add_submonoid.localization_map.add_equiv_of_localizations f
    (add_submonoid.localization_map.of_add_equiv_of_localizations f k) =
  k :=
  add_equiv.ext
    (iff.mp add_monoid_hom.ext_iff (add_submonoid.localization_map.lift_of_comp f (add_equiv.to_add_monoid_hom k)))

@[simp] theorem mul_equiv_of_localizations_left_inv_apply {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {k : N ≃* P} (x : N) : coe_fn (mul_equiv_of_localizations f (of_mul_equiv_of_localizations f k)) x = coe_fn k x := sorry

@[simp] theorem Mathlib.add_submonoid.localization_map.of_add_equiv_of_localizations_id {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] (f : add_submonoid.localization_map S N) : add_submonoid.localization_map.of_add_equiv_of_localizations f (add_equiv.refl N) = f := sorry

theorem Mathlib.add_submonoid.localization_map.of_add_equiv_of_localizations_comp {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {Q : Type u_4} [add_comm_monoid Q] {k : N ≃+ P} {j : P ≃+ Q} : add_submonoid.localization_map.to_map
    (add_submonoid.localization_map.of_add_equiv_of_localizations f (add_equiv.trans k j)) =
  add_monoid_hom.comp (add_equiv.to_add_monoid_hom j)
    (add_submonoid.localization_map.to_map (add_submonoid.localization_map.of_add_equiv_of_localizations f k)) := sorry

/-- Given `comm_monoid`s `M, P` and submonoids `S ⊆ M, T ⊆ P`, if `f : M →* N` is a localization
map for `S` and `k : P ≃* M` is an isomorphism of `comm_monoid`s such that `k(T) = S`, `f ∘ k`
is a localization map for `T`. -/
def Mathlib.add_submonoid.localization_map.of_add_equiv_of_dom {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {T : add_submonoid P} {k : P ≃+ M} (H : add_submonoid.map (add_equiv.to_add_monoid_hom k) T = S) : add_submonoid.localization_map T N :=
  add_monoid_hom.to_localization_map
    (add_monoid_hom.comp (add_submonoid.localization_map.to_map f) (add_equiv.to_add_monoid_hom k)) sorry sorry sorry

@[simp] theorem of_mul_equiv_of_dom_apply {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {T : submonoid P} {k : P ≃* M} (H : map (mul_equiv.to_monoid_hom k) T = S) (x : P) : coe_fn (to_map (of_mul_equiv_of_dom f H)) x = coe_fn (to_map f) (coe_fn k x) :=
  rfl

theorem Mathlib.add_submonoid.localization_map.of_add_equiv_of_dom_eq {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {T : add_submonoid P} {k : P ≃+ M} (H : add_submonoid.map (add_equiv.to_add_monoid_hom k) T = S) : add_submonoid.localization_map.to_map (add_submonoid.localization_map.of_add_equiv_of_dom f H) =
  add_monoid_hom.comp (add_submonoid.localization_map.to_map f) (add_equiv.to_add_monoid_hom k) :=
  rfl

theorem of_mul_equiv_of_dom_comp_symm {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {T : submonoid P} {k : P ≃* M} (H : map (mul_equiv.to_monoid_hom k) T = S) (x : M) : coe_fn (to_map (of_mul_equiv_of_dom f H)) (coe_fn (mul_equiv.symm k) x) = coe_fn (to_map f) x :=
  congr_arg (⇑(to_map f)) (mul_equiv.apply_symm_apply k x)

theorem Mathlib.add_submonoid.localization_map.of_add_equiv_of_dom_comp {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {T : add_submonoid P} {k : M ≃+ P} (H : add_submonoid.map (add_equiv.to_add_monoid_hom (add_equiv.symm k)) T = S) (x : M) : coe_fn (add_submonoid.localization_map.to_map (add_submonoid.localization_map.of_add_equiv_of_dom f H)) (coe_fn k x) =
  coe_fn (add_submonoid.localization_map.to_map f) x :=
  congr_arg (⇑(add_submonoid.localization_map.to_map f)) (add_equiv.symm_apply_apply k x)

/-- A special case of `f ∘ id = f`, `f` a localization map. -/
@[simp] theorem of_mul_equiv_of_dom_id {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : localization_map S N) : of_mul_equiv_of_dom f
    ((fun (this : map (mul_equiv.to_monoid_hom (mul_equiv.refl M)) S = S) => this)
      (ext
        fun (x : M) =>
          { mp :=
              fun (_x : x ∈ map (mul_equiv.to_monoid_hom (mul_equiv.refl M)) S) =>
                (fun (_a : x ∈ map (mul_equiv.to_monoid_hom (mul_equiv.refl M)) S) =>
                    Exists.dcases_on _a
                      fun (w : M) (h : w ∈ ↑S ∧ coe_fn (mul_equiv.to_monoid_hom (mul_equiv.refl M)) w = x) =>
                        and.dcases_on h
                          fun (h_left : w ∈ ↑S) (h_right : coe_fn (mul_equiv.to_monoid_hom (mul_equiv.refl M)) w = x) =>
                            idRhs ((fun (_x : M) => _x ∈ S) x) (h_right ▸ h_left))
                  _x,
            mpr := fun (h : x ∈ S) => Exists.intro x { left := h, right := rfl } })) =
  f := sorry

/-- Given localization maps `f : M →* N, k : P →* U` for submonoids `S, T` respectively, an
isomorphism `j : M ≃* P` such that `j(S) = T` induces an isomorphism of localizations
`N ≃* U`. -/
def Mathlib.add_submonoid.localization_map.add_equiv_of_add_equiv {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {T : add_submonoid P} {Q : Type u_4} [add_comm_monoid Q] (k : add_submonoid.localization_map T Q) {j : M ≃+ P} (H : add_submonoid.map (add_equiv.to_add_monoid_hom j) S = T) : N ≃+ Q :=
  add_submonoid.localization_map.add_equiv_of_localizations f (add_submonoid.localization_map.of_add_equiv_of_dom k H)

@[simp] theorem Mathlib.add_submonoid.localization_map.add_equiv_of_add_equiv_eq_map_apply {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {T : add_submonoid P} {Q : Type u_4} [add_comm_monoid Q] {k : add_submonoid.localization_map T Q} {j : M ≃+ P} (H : add_submonoid.map (add_equiv.to_add_monoid_hom j) S = T) (x : N) : coe_fn (add_submonoid.localization_map.add_equiv_of_add_equiv f k H) x =
  coe_fn
    (add_submonoid.localization_map.map f
      (fun (y : ↥S) =>
        (fun (this : coe_fn (add_equiv.to_add_monoid_hom j) ↑y ∈ T) => this)
          (H ▸ set.mem_image_of_mem (⇑j) (subtype.property y)))
      k)
    x :=
  rfl

theorem mul_equiv_of_mul_equiv_eq_map {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {T : submonoid P} {Q : Type u_4} [comm_monoid Q] {k : localization_map T Q} {j : M ≃* P} (H : map (mul_equiv.to_monoid_hom j) S = T) : mul_equiv.to_monoid_hom (mul_equiv_of_mul_equiv f k H) =
  map f
    (fun (y : ↥S) =>
      (fun (this : coe_fn (mul_equiv.to_monoid_hom j) ↑y ∈ T) => this)
        (H ▸ set.mem_image_of_mem (⇑j) (subtype.property y)))
    k :=
  rfl

@[simp] theorem mul_equiv_of_mul_equiv_eq {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {P : Type u_3} [comm_monoid P] (f : localization_map S N) {T : submonoid P} {Q : Type u_4} [comm_monoid Q] {k : localization_map T Q} {j : M ≃* P} (H : map (mul_equiv.to_monoid_hom j) S = T) (x : M) : coe_fn (mul_equiv_of_mul_equiv f k H) (coe_fn (to_map f) x) = coe_fn (to_map k) (coe_fn j x) :=
  map_eq f (fun (y : ↥S) => H ▸ set.mem_image_of_mem (⇑j) (subtype.property y)) x

@[simp] theorem Mathlib.add_submonoid.localization_map.add_equiv_of_add_equiv_mk' {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {T : add_submonoid P} {Q : Type u_4} [add_comm_monoid Q] {k : add_submonoid.localization_map T Q} {j : M ≃+ P} (H : add_submonoid.map (add_equiv.to_add_monoid_hom j) S = T) (x : M) (y : ↥S) : coe_fn (add_submonoid.localization_map.add_equiv_of_add_equiv f k H) (add_submonoid.localization_map.mk' f x y) =
  add_submonoid.localization_map.mk' k (coe_fn j x)
    { val := coe_fn j ↑y, property := H ▸ set.mem_image_of_mem (⇑j) (subtype.property y) } :=
  add_submonoid.localization_map.map_mk' f (fun (y : ↥S) => H ▸ set.mem_image_of_mem (⇑j) (subtype.property y)) x y

@[simp] theorem Mathlib.add_submonoid.localization_map.of_add_equiv_of_add_equiv_apply {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {T : add_submonoid P} {Q : Type u_4} [add_comm_monoid Q] {k : add_submonoid.localization_map T Q} {j : M ≃+ P} (H : add_submonoid.map (add_equiv.to_add_monoid_hom j) S = T) (x : M) : coe_fn
    (add_submonoid.localization_map.to_map
      (add_submonoid.localization_map.of_add_equiv_of_localizations f
        (add_submonoid.localization_map.add_equiv_of_add_equiv f k H)))
    x =
  coe_fn (add_submonoid.localization_map.to_map k) (coe_fn j x) := sorry

theorem Mathlib.add_submonoid.localization_map.of_add_equiv_of_add_equiv {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {P : Type u_3} [add_comm_monoid P] (f : add_submonoid.localization_map S N) {T : add_submonoid P} {Q : Type u_4} [add_comm_monoid Q] {k : add_submonoid.localization_map T Q} {j : M ≃+ P} (H : add_submonoid.map (add_equiv.to_add_monoid_hom j) S = T) : add_submonoid.localization_map.to_map
    (add_submonoid.localization_map.of_add_equiv_of_localizations f
      (add_submonoid.localization_map.add_equiv_of_add_equiv f k H)) =
  add_monoid_hom.comp (add_submonoid.localization_map.to_map k) (add_equiv.to_add_monoid_hom j) :=
  add_monoid_hom.ext (add_submonoid.localization_map.of_add_equiv_of_add_equiv_apply f H)

end localization_map


end submonoid


namespace localization


/-- Natural hom sending `x : M`, `M` a `comm_monoid`, to the equivalence class of
`(x, 1)` in the localization of `M` at a submonoid. -/
def monoid_of {M : Type u_1} [comm_monoid M] (S : submonoid M) : submonoid.localization_map S (localization S) :=
  submonoid.localization_map.mk (monoid_hom.to_fun (monoid_hom.comp (con.mk' (r S)) (monoid_hom.inl M ↥S))) sorry sorry
    sorry sorry sorry

theorem Mathlib.add_localization.mk_zero_eq_add_monoid_of_mk {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} (x : M) : add_localization.mk x 0 = coe_fn (add_submonoid.localization_map.to_map (add_localization.add_monoid_of S)) x :=
  rfl

theorem Mathlib.add_localization.mk_eq_add_monoid_of_mk'_apply {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} (x : M) (y : ↥S) : add_localization.mk x y = add_submonoid.localization_map.mk' (add_localization.add_monoid_of S) x y := sorry

@[simp] theorem Mathlib.add_localization.mk_eq_add_monoid_of_mk' {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} : add_localization.mk = add_submonoid.localization_map.mk' (add_localization.add_monoid_of S) :=
  funext fun (_x : M) => funext fun (_x_1 : ↥S) => add_localization.mk_eq_add_monoid_of_mk'_apply _x _x_1

/-- Given a localization map `f : M →* N` for a submonoid `S`, we get an isomorphism between
the localization of `M` at `S` as a quotient type and `N`. -/
def mul_equiv_of_quotient {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] (f : submonoid.localization_map S N) : localization S ≃* N :=
  submonoid.localization_map.mul_equiv_of_localizations (monoid_of S) f

@[simp] theorem mul_equiv_of_quotient_apply {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {f : submonoid.localization_map S N} (x : localization S) : coe_fn (mul_equiv_of_quotient f) x =
  coe_fn (submonoid.localization_map.lift (monoid_of S) (submonoid.localization_map.map_units f)) x :=
  rfl

@[simp] theorem mul_equiv_of_quotient_mk' {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {f : submonoid.localization_map S N} (x : M) (y : ↥S) : coe_fn (mul_equiv_of_quotient f) (submonoid.localization_map.mk' (monoid_of S) x y) =
  submonoid.localization_map.mk' f x y :=
  submonoid.localization_map.lift_mk' (monoid_of S) (submonoid.localization_map.map_units f) x y

theorem mul_equiv_of_quotient_mk {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {f : submonoid.localization_map S N} (x : M) (y : ↥S) : coe_fn (mul_equiv_of_quotient f) (mk x y) = submonoid.localization_map.mk' f x y := sorry

@[simp] theorem Mathlib.add_localization.add_equiv_of_quotient_add_monoid_of {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {f : add_submonoid.localization_map S N} (x : M) : coe_fn (add_localization.add_equiv_of_quotient f)
    (coe_fn (add_submonoid.localization_map.to_map (add_localization.add_monoid_of S)) x) =
  coe_fn (add_submonoid.localization_map.to_map f) x :=
  add_submonoid.localization_map.lift_eq (add_localization.add_monoid_of S) (add_submonoid.localization_map.map_units f) x

@[simp] theorem Mathlib.add_localization.add_equiv_of_quotient_symm_mk' {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {f : add_submonoid.localization_map S N} (x : M) (y : ↥S) : coe_fn (add_equiv.symm (add_localization.add_equiv_of_quotient f)) (add_submonoid.localization_map.mk' f x y) =
  add_submonoid.localization_map.mk' (add_localization.add_monoid_of S) x y :=
  add_submonoid.localization_map.lift_mk' f (add_submonoid.localization_map.map_units (add_localization.add_monoid_of S))
    x y

theorem Mathlib.add_localization.add_equiv_of_quotient_symm_mk {M : Type u_1} [add_comm_monoid M] {S : add_submonoid M} {N : Type u_2} [add_comm_monoid N] {f : add_submonoid.localization_map S N} (x : M) (y : ↥S) : coe_fn (add_equiv.symm (add_localization.add_equiv_of_quotient f)) (add_submonoid.localization_map.mk' f x y) =
  add_localization.mk x y := sorry

@[simp] theorem mul_equiv_of_quotient_symm_monoid_of {M : Type u_1} [comm_monoid M] {S : submonoid M} {N : Type u_2} [comm_monoid N] {f : submonoid.localization_map S N} (x : M) : coe_fn (mul_equiv.symm (mul_equiv_of_quotient f)) (coe_fn (submonoid.localization_map.to_map f) x) =
  coe_fn (submonoid.localization_map.to_map (monoid_of S)) x :=
  submonoid.localization_map.lift_eq f (submonoid.localization_map.map_units (monoid_of S)) x

/-- Given `x : M`, the localization of `M` at the submonoid generated by `x`, as a quotient. -/
def Mathlib.add_localization.away {M : Type u_1} [add_comm_monoid M] (x : M) :=
  add_localization (add_submonoid.multiples x)

/-- Given `x : M`, `inv_self` is `x⁻¹` in the localization (as a quotient type) of `M` at the
submonoid generated by `x`. -/
def away.inv_self {M : Type u_1} [comm_monoid M] (x : M) : away x :=
  mk 1 { val := x, property := sorry }

/-- Given `x : M`, the natural hom sending `y : M`, `M` a `comm_monoid`, to the equivalence class
of `(y, 1)` in the localization of `M` at the submonoid generated by `x`. -/
def away.monoid_of {M : Type u_1} [comm_monoid M] (x : M) : submonoid.localization_map.away_map x (away x) :=
  monoid_of (submonoid.powers x)

@[simp] theorem Mathlib.add_localization.away.mk_eq_add_monoid_of_mk' {M : Type u_1} [add_comm_monoid M] (x : M) : add_localization.mk = add_submonoid.localization_map.mk' (add_localization.away.add_monoid_of x) :=
  add_localization.mk_eq_add_monoid_of_mk'

/-- Given `x : M` and a localization map `f : M →* N` away from `x`, we get an isomorphism between
the localization of `M` at the submonoid generated by `x` as a quotient type and `N`. -/
def away.mul_equiv_of_quotient {M : Type u_1} [comm_monoid M] {N : Type u_2} [comm_monoid N] (x : M) (f : submonoid.localization_map.away_map x N) : away x ≃* N :=
  mul_equiv_of_quotient f

