/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.mul_add
import Mathlib.algebra.field
import Mathlib.algebra.opposites
import Mathlib.PostPort

universes u_4 u_5 l u_1 u_2 u_3 

namespace Mathlib

/-!
# (Semi)ring equivs

In this file we define extension of `equiv` called `ring_equiv`, which is a datatype representing an
isomorphism of `semiring`s, `ring`s, `division_ring`s, or `field`s. We also introduce the
corresponding group of automorphisms `ring_aut`.

## Notations

The extended equiv have coercions to functions, and the coercion is the canonical notation when
treating the isomorphism as maps.

## Implementation notes

The fields for `ring_equiv` now avoid the unbundled `is_mul_hom` and `is_add_hom`, as these are
deprecated.

Definition of multiplication in the groups of automorphisms agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, not with
`category_theory.comp`.

## Tags

equiv, mul_equiv, add_equiv, ring_equiv, mul_aut, add_aut, ring_aut
-/

/-- An equivalence between two (semi)rings that preserves the algebraic structure. -/
structure ring_equiv (R : Type u_4) (S : Type u_5) [Mul R] [Add R] [Mul S] [Add S] 
extends R ≃* S, R ≃ S, R ≃+ S
where

infixl:25 " ≃+* " => Mathlib.ring_equiv

/-- The "plain" equivalence of types underlying an equivalence of (semi)rings. -/
/-- The equivalence of additive monoids underlying an equivalence of (semi)rings. -/
/-- The equivalence of multiplicative monoids underlying an equivalence of (semi)rings. -/
namespace ring_equiv


protected instance has_coe_to_fun {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] : has_coe_to_fun (R ≃+* S) :=
  has_coe_to_fun.mk (fun (x : R ≃+* S) => R → S) to_fun

@[simp] theorem to_fun_eq_coe_fun {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (f : R ≃+* S) : to_fun f = ⇑f :=
  rfl

/-- A ring isomorphism preserves multiplication. -/
@[simp] theorem map_mul {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (e : R ≃+* S) (x : R) (y : R) : coe_fn e (x * y) = coe_fn e x * coe_fn e y :=
  map_mul' e x y

/-- A ring isomorphism preserves addition. -/
@[simp] theorem map_add {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (e : R ≃+* S) (x : R) (y : R) : coe_fn e (x + y) = coe_fn e x + coe_fn e y :=
  map_add' e x y

/-- Two ring isomorphisms agree if they are defined by the
    same underlying function. -/
theorem ext {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] {f : R ≃+* S} {g : R ≃+* S} (h : ∀ (x : R), coe_fn f x = coe_fn g x) : f = g := sorry

protected theorem congr_arg {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] {f : R ≃+* S} {x : R} {x' : R} : x = x' → coe_fn f x = coe_fn f x' := sorry

protected theorem congr_fun {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] {f : R ≃+* S} {g : R ≃+* S} (h : f = g) (x : R) : coe_fn f x = coe_fn g x :=
  h ▸ rfl

theorem ext_iff {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] {f : R ≃+* S} {g : R ≃+* S} : f = g ↔ ∀ (x : R), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : R) => h ▸ rfl, mpr := ext }

protected instance has_coe_to_mul_equiv {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] : has_coe (R ≃+* S) (R ≃* S) :=
  has_coe.mk to_mul_equiv

protected instance has_coe_to_add_equiv {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] : has_coe (R ≃+* S) (R ≃+ S) :=
  has_coe.mk to_add_equiv

theorem coe_mul_equiv {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (f : R ≃+* S) (a : R) : coe_fn (↑f) a = coe_fn f a :=
  rfl

theorem coe_add_equiv {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (f : R ≃+* S) (a : R) : coe_fn (↑f) a = coe_fn f a :=
  rfl

/-- The identity map is a ring isomorphism. -/
protected def refl (R : Type u_1) [Mul R] [Add R] : R ≃+* R :=
  mk (mul_equiv.to_fun (mul_equiv.refl R)) (mul_equiv.inv_fun (mul_equiv.refl R)) sorry sorry sorry sorry

@[simp] theorem refl_apply (R : Type u_1) [Mul R] [Add R] (x : R) : coe_fn (ring_equiv.refl R) x = x :=
  rfl

@[simp] theorem coe_add_equiv_refl (R : Type u_1) [Mul R] [Add R] : ↑(ring_equiv.refl R) = add_equiv.refl R :=
  rfl

@[simp] theorem coe_mul_equiv_refl (R : Type u_1) [Mul R] [Add R] : ↑(ring_equiv.refl R) = mul_equiv.refl R :=
  rfl

protected instance inhabited (R : Type u_1) [Mul R] [Add R] : Inhabited (R ≃+* R) :=
  { default := ring_equiv.refl R }

/-- The inverse of a ring isomorphism is a ring isomorphism. -/
protected def symm {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (e : R ≃+* S) : S ≃+* R :=
  mk (mul_equiv.to_fun (mul_equiv.symm (to_mul_equiv e))) (mul_equiv.inv_fun (mul_equiv.symm (to_mul_equiv e))) sorry
    sorry sorry sorry

/-- See Note [custom simps projection] -/
def simps.inv_fun {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (e : R ≃+* S) : S → R :=
  ⇑(ring_equiv.symm e)

@[simp] theorem symm_symm {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (e : R ≃+* S) : ring_equiv.symm (ring_equiv.symm e) = e :=
  ext fun (x : R) => rfl

@[simp] theorem coe_symm_mk {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (f : R → S) (g : S → R) (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) (h₃ : ∀ (x y : R), f (x * y) = f x * f y) (h₄ : ∀ (x y : R), f (x + y) = f x + f y) : ⇑(ring_equiv.symm (mk f g h₁ h₂ h₃ h₄)) = g :=
  rfl

/-- Transitivity of `ring_equiv`. -/
protected def trans {R : Type u_1} {S : Type u_2} {S' : Type u_3} [Mul R] [Add R] [Mul S] [Add S] [Mul S'] [Add S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') : R ≃+* S' :=
  mk (mul_equiv.to_fun (mul_equiv.trans (to_mul_equiv e₁) (to_mul_equiv e₂)))
    (mul_equiv.inv_fun (mul_equiv.trans (to_mul_equiv e₁) (to_mul_equiv e₂))) sorry sorry sorry sorry

@[simp] theorem trans_apply {A : Type u_1} {B : Type u_2} {C : Type u_3} [semiring A] [semiring B] [semiring C] (e : A ≃+* B) (f : B ≃+* C) (a : A) : coe_fn (ring_equiv.trans e f) a = coe_fn f (coe_fn e a) :=
  rfl

protected theorem bijective {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (e : R ≃+* S) : function.bijective ⇑e :=
  equiv.bijective (to_equiv e)

protected theorem injective {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (e : R ≃+* S) : function.injective ⇑e :=
  equiv.injective (to_equiv e)

protected theorem surjective {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (e : R ≃+* S) : function.surjective ⇑e :=
  equiv.surjective (to_equiv e)

@[simp] theorem apply_symm_apply {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (e : R ≃+* S) (x : S) : coe_fn e (coe_fn (ring_equiv.symm e) x) = x :=
  equiv.apply_symm_apply (to_equiv e)

@[simp] theorem symm_apply_apply {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (e : R ≃+* S) (x : R) : coe_fn (ring_equiv.symm e) (coe_fn e x) = x :=
  equiv.symm_apply_apply (to_equiv e)

theorem image_eq_preimage {R : Type u_1} {S : Type u_2} [Mul R] [Add R] [Mul S] [Add S] (e : R ≃+* S) (s : set R) : ⇑e '' s = ⇑(ring_equiv.symm e) ⁻¹' s :=
  equiv.image_eq_preimage (to_equiv e) s

/-- A commutative ring is isomorphic to its opposite. -/
def to_opposite (R : Type u_1) [comm_semiring R] : R ≃+* (Rᵒᵖ) :=
  mk (equiv.to_fun opposite.equiv_to_opposite) (equiv.inv_fun opposite.equiv_to_opposite) sorry sorry sorry sorry

@[simp] theorem to_opposite_apply (R : Type u_1) [comm_semiring R] (r : R) : coe_fn (to_opposite R) r = opposite.op r :=
  rfl

@[simp] theorem to_opposite_symm_apply (R : Type u_1) [comm_semiring R] (r : Rᵒᵖ) : coe_fn (ring_equiv.symm (to_opposite R)) r = opposite.unop r :=
  rfl

/-- A ring isomorphism sends one to one. -/
@[simp] theorem map_one {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R ≃+* S) : coe_fn f 1 = 1 :=
  mul_equiv.map_one ↑f

/-- A ring isomorphism sends zero to zero. -/
@[simp] theorem map_zero {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R ≃+* S) : coe_fn f 0 = 0 :=
  add_equiv.map_zero ↑f

@[simp] theorem map_eq_one_iff {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R ≃+* S) {x : R} : coe_fn f x = 1 ↔ x = 1 :=
  mul_equiv.map_eq_one_iff ↑f

@[simp] theorem map_eq_zero_iff {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R ≃+* S) {x : R} : coe_fn f x = 0 ↔ x = 0 :=
  add_equiv.map_eq_zero_iff ↑f

theorem map_ne_one_iff {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R ≃+* S) {x : R} : coe_fn f x ≠ 1 ↔ x ≠ 1 :=
  mul_equiv.map_ne_one_iff ↑f

theorem map_ne_zero_iff {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R ≃+* S) {x : R} : coe_fn f x ≠ 0 ↔ x ≠ 0 :=
  add_equiv.map_ne_zero_iff ↑f

/-- Produce a ring isomorphism from a bijective ring homomorphism. -/
def of_bijective {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R →+* S) (hf : function.bijective ⇑f) : R ≃+* S :=
  mk (equiv.to_fun (equiv.of_bijective (⇑f) hf)) (equiv.inv_fun (equiv.of_bijective (⇑f) hf)) sorry sorry
    (ring_hom.map_mul' f) (ring_hom.map_add' f)

@[simp] theorem map_neg {R : Type u_1} {S : Type u_2} [ring R] [ring S] (f : R ≃+* S) (x : R) : coe_fn f (-x) = -coe_fn f x :=
  add_equiv.map_neg (↑f) x

@[simp] theorem map_sub {R : Type u_1} {S : Type u_2} [ring R] [ring S] (f : R ≃+* S) (x : R) (y : R) : coe_fn f (x - y) = coe_fn f x - coe_fn f y :=
  add_equiv.map_sub (↑f) x y

@[simp] theorem map_neg_one {R : Type u_1} {S : Type u_2} [ring R] [ring S] (f : R ≃+* S) : coe_fn f (-1) = -1 :=
  map_one f ▸ map_neg f 1

/-- Reinterpret a ring equivalence as a ring homomorphism. -/
def to_ring_hom {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (e : R ≃+* S) : R →+* S :=
  ring_hom.mk (monoid_hom.to_fun (mul_equiv.to_monoid_hom (to_mul_equiv e))) sorry sorry sorry sorry

theorem to_ring_hom_injective {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] : function.injective to_ring_hom :=
  fun (f g : R ≃+* S) (h : to_ring_hom f = to_ring_hom g) => ext (iff.mp ring_hom.ext_iff h)

protected instance has_coe_to_ring_hom {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] : has_coe (R ≃+* S) (R →+* S) :=
  has_coe.mk to_ring_hom

theorem coe_ring_hom {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R ≃+* S) (a : R) : coe_fn (↑f) a = coe_fn f a :=
  rfl

theorem coe_ring_hom_inj_iff {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R ≃+* S) (g : R ≃+* S) : f = g ↔ ↑f = ↑g :=
  { mp := congr_arg fun (f : R ≃+* S) => ↑f, mpr := fun (h : ↑f = ↑g) => ext (iff.mp ring_hom.ext_iff h) }

/-- Reinterpret a ring equivalence as a monoid homomorphism. -/
def to_monoid_hom {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (e : R ≃+* S) : R →* S :=
  ring_hom.to_monoid_hom (to_ring_hom e)

/-- Reinterpret a ring equivalence as an `add_monoid` homomorphism. -/
def to_add_monoid_hom {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (e : R ≃+* S) : R →+ S :=
  ring_hom.to_add_monoid_hom (to_ring_hom e)

@[simp] theorem to_ring_hom_refl {R : Type u_1} [semiring R] : to_ring_hom (ring_equiv.refl R) = ring_hom.id R :=
  rfl

@[simp] theorem to_monoid_hom_refl {R : Type u_1} [semiring R] : to_monoid_hom (ring_equiv.refl R) = monoid_hom.id R :=
  rfl

@[simp] theorem to_add_monoid_hom_refl {R : Type u_1} [semiring R] : to_add_monoid_hom (ring_equiv.refl R) = add_monoid_hom.id R :=
  rfl

@[simp] theorem to_ring_hom_apply_symm_to_ring_hom_apply {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (e : R ≃+* S) (y : S) : coe_fn (to_ring_hom e) (coe_fn (to_ring_hom (ring_equiv.symm e)) y) = y :=
  equiv.apply_symm_apply (to_equiv e)

@[simp] theorem symm_to_ring_hom_apply_to_ring_hom_apply {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (e : R ≃+* S) (x : R) : coe_fn (to_ring_hom (ring_equiv.symm e)) (coe_fn (to_ring_hom e) x) = x :=
  equiv.symm_apply_apply (to_equiv e)

@[simp] theorem to_ring_hom_trans {R : Type u_1} {S : Type u_2} {S' : Type u_3} [semiring R] [semiring S] [semiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') : to_ring_hom (ring_equiv.trans e₁ e₂) = ring_hom.comp (to_ring_hom e₂) (to_ring_hom e₁) :=
  rfl

@[simp] theorem to_ring_hom_comp_symm_to_ring_hom {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (e : R ≃+* S) : ring_hom.comp (to_ring_hom e) (to_ring_hom (ring_equiv.symm e)) = ring_hom.id S := sorry

@[simp] theorem symm_to_ring_hom_comp_to_ring_hom {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (e : R ≃+* S) : ring_hom.comp (to_ring_hom (ring_equiv.symm e)) (to_ring_hom e) = ring_hom.id R := sorry

/--
Construct an equivalence of rings from homomorphisms in both directions, which are inverses.
-/
def of_hom_inv {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (hom : R →+* S) (inv : S →+* R) (hom_inv_id : ring_hom.comp inv hom = ring_hom.id R) (inv_hom_id : ring_hom.comp hom inv = ring_hom.id S) : R ≃+* S :=
  mk (ring_hom.to_fun hom) ⇑inv sorry sorry (ring_hom.map_mul' hom) (ring_hom.map_add' hom)

@[simp] theorem of_hom_inv_apply {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (hom : R →+* S) (inv : S →+* R) (hom_inv_id : ring_hom.comp inv hom = ring_hom.id R) (inv_hom_id : ring_hom.comp hom inv = ring_hom.id S) (r : R) : coe_fn (of_hom_inv hom inv hom_inv_id inv_hom_id) r = coe_fn hom r :=
  rfl

@[simp] theorem of_hom_inv_symm_apply {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (hom : R →+* S) (inv : S →+* R) (hom_inv_id : ring_hom.comp inv hom = ring_hom.id R) (inv_hom_id : ring_hom.comp hom inv = ring_hom.id S) (s : S) : coe_fn (ring_equiv.symm (of_hom_inv hom inv hom_inv_id inv_hom_id)) s = coe_fn inv s :=
  rfl

end ring_equiv


namespace mul_equiv


/-- Gives a `ring_equiv` from a `mul_equiv` preserving addition.-/
def to_ring_equiv {R : Type u_1} {S : Type u_2} [Add R] [Add S] [Mul R] [Mul S] (h : R ≃* S) (H : ∀ (x y : R), coe_fn h (x + y) = coe_fn h x + coe_fn h y) : R ≃+* S :=
  ring_equiv.mk (equiv.to_fun (to_equiv h)) (equiv.inv_fun (to_equiv h)) sorry sorry (map_mul' h) sorry

end mul_equiv


namespace ring_equiv


@[simp] theorem trans_symm {R : Type u_1} {S : Type u_2} [Add R] [Add S] [Mul R] [Mul S] (e : R ≃+* S) : ring_equiv.trans e (ring_equiv.symm e) = ring_equiv.refl R :=
  ext (left_inv e)

@[simp] theorem symm_trans {R : Type u_1} {S : Type u_2} [Add R] [Add S] [Mul R] [Mul S] (e : R ≃+* S) : ring_equiv.trans (ring_equiv.symm e) e = ring_equiv.refl S :=
  ext (right_inv e)

/-- If two rings are isomorphic, and the second is an integral domain, then so is the first. -/
protected theorem is_integral_domain {A : Type u_1} (B : Type u_2) [ring A] [ring B] (hB : is_integral_domain B) (e : A ≃+* B) : is_integral_domain A := sorry

/-- If two rings are isomorphic, and the second is an integral domain, then so is the first. -/
protected def integral_domain {A : Type u_1} (B : Type u_2) [ring A] [integral_domain B] (e : A ≃+* B) : integral_domain A :=
  integral_domain.mk ring.add ring.add_assoc ring.zero ring.zero_add ring.add_zero ring.neg ring.sub ring.add_left_neg
    ring.add_comm ring.mul ring.mul_assoc ring.one ring.one_mul ring.mul_one ring.left_distrib ring.right_distrib sorry
    sorry sorry

end ring_equiv


namespace equiv


/-- In a division ring `K`, the unit group `units K`
is equivalent to the subtype of nonzero elements. -/
-- TODO: this might already exist elsewhere for `group_with_zero`

-- deduplicate or generalize

def units_equiv_ne_zero (K : Type u_4) [division_ring K] : units K ≃ ↥(set_of fun (a : K) => a ≠ 0) :=
  mk (fun (a : units K) => { val := units.val a, property := sorry })
    (fun (a : ↥(set_of fun (a : K) => a ≠ 0)) => units.mk0 (subtype.val a) sorry) sorry sorry

@[simp] theorem coe_units_equiv_ne_zero {K : Type u_4} [division_ring K] (a : units K) : ↑(coe_fn (units_equiv_ne_zero K) a) = ↑a :=
  rfl

